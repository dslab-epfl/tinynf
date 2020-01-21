// Changes by Solal Pirelli (2020): removed statistics and debug prints, formatted the code

/* apricot.c: An Apricot 82596 ethernet driver for linux. */
/*
    Apricot
        Written 1994 by Mark Evans.
        This driver is for the Apricot 82596 bus-master interface

    Driver skeleton
        Written 1993 by Donald Becker.
        Copyright 1993 United States Government as represented by the Director,
        National Security Agency.  This software may only be used and
   distributed according to the terms of the GNU Public License as modified by
   SRC, incorporated herein by reference.

        The author may be reached as becker@super.org or
        C/O Supercomputing Research Ctr., 17100 Science Dr., Bowie MD 20715


*/

static char *version = "apricot.c:v0.02 19/05/94\n";

#include <asm/bitops.h>
#include <asm/dma.h>
#include <asm/io.h>
#include <linux/config.h>
#include <linux/errno.h>
#include <linux/interrupt.h>
#include <linux/ioport.h>
#include <linux/kernel.h>
#include <linux/malloc.h>
#include <linux/ptrace.h>
#include <linux/sched.h>
#include <linux/string.h>

#include <linux/etherdevice.h>
#include <linux/netdevice.h>
#include <linux/skbuff.h>

#ifndef HAVE_PORTRESERVE
#define check_region(addr, size) 0
#define snarf_region(addr, size)                                               \
  do                                                                           \
    ;                                                                          \
  while (0)
#endif

#ifndef HAVE_ALLOC_SKB
#define alloc_skb(size, priority) (struct sk_buff *)kmalloc(size, priority)
#define kfree_skbmem(buff, size) kfree_s(buff, size)
#endif

struct device *init_etherdev(struct device *dev, int sizeof_private,
                             unsigned long *mem_start);

#define APRICOT_TOTAL_SIZE 17

#define CMD_EOL 0x8000  /* The last command of the list, stop. */
#define CMD_SUSP 0x4000 /* Suspend after doing cmd. */
#define CMD_INTR 0x2000 /* Interrupt after doing cmd. */

#define CMD_FLEX 0x0008 /* Enable flexable memory model */

enum commands {
  CmdNOp = 0,
  CmdSASetup = 1,
  CmdConfigure = 2,
  CmdMulticastList = 3,
  CmdTx = 4,
  CmdTDR = 5,
  CmdDump = 6,
  CmdDiagnose = 7
};

#define STAT_C 0x8000  /* Set to 0 after execution */
#define STAT_B 0x4000  /* Command being executed */
#define STAT_OK 0x2000 /* Command executed ok */
#define STAT_A 0x1000  /* Command aborted */

#define CUC_START 0x0100
#define CUC_RESUME 0x0200
#define CUC_SUSPEND 0x0300
#define CUC_ABORT 0x0400
#define RX_START 0x0010
#define RX_RESUME 0x0020
#define RX_SUSPEND 0x0030
#define RX_ABORT 0x0040

struct i596_cmd {
  unsigned short status;
  unsigned short command;
  struct i596_cmd *next;
};

#define EOF 0x8000
#define SIZE_MASK 0x3fff

struct i596_tbd {
  unsigned short size;
  unsigned short pad;
  struct i596_tbd *next;
  char *data;
};

struct tx_cmd {
  struct i596_cmd cmd;
  struct i596_tbd *tbd;
  unsigned short size;
  unsigned short pad;
};

struct i596_rfd {
  unsigned short stat;
  unsigned short cmd;
  struct i596_rfd *next;
  long rbd;
  unsigned short count;
  unsigned short size;
  char data[1532];
};

#define RX_RING_SIZE 16

struct i596_scb {
  unsigned short status;
  unsigned short command;
  struct i596_cmd *cmd;
  struct i596_rfd *rfd;
  unsigned long crc_err;
  unsigned long align_err;
  unsigned long resource_err;
  unsigned long over_err;
  unsigned long rcvdt_err;
  unsigned long short_err;
  unsigned short t_on;
  unsigned short t_off;
};

struct i596_iscp {
  unsigned long stat;
  struct i596_scb *scb;
};

struct i596_scp {
  unsigned long sysbus;
  unsigned long pad;
  struct i596_iscp *iscp;
};

struct i596_private {
  struct i596_scp scp;
  struct i596_iscp iscp;
  struct i596_scb scb;
  struct i596_cmd set_add;
  char eth_addr[8];
  struct i596_cmd set_conf;
  char i596_config[16];
  struct i596_cmd tdr;
  unsigned long stat;
  struct i596_rfd rx[RX_RING_SIZE];
  int last_restart;
  struct i596_rfd *rx_tail;
  struct i596_cmd *cmd_tail;
  struct i596_cmd *cmd_head;
  int cmd_backlog;
  unsigned long last_cmd;
};

char init_setup[] = {0x8E, /* length, prefetch on */
                     0xC8, /* fifo to 8, monitor off */
                     0x80, /* don't save bad frames */
                     0x2E, /* No source address insertion, 8 byte preamble */
                     0x00, /* priority and backoff defaults */
                     0x60, /* interframe spacing */
                     0x00, /* slot time LSB */
                     0xf2, /* slot time and retries */
                     0x00, /* promiscuous mode */
                     0x00, /* collision detect */
                     0x40, /* minimum frame length */
                     0xff, 0x00, 0x7f /*  *multi IA */};

char adds[] = {0x00, 0x00, 0x49, 0x20, 0x54, 0xDA,
               0x80, 0x00, 0x4e, 0x02, 0xb7, 0xb8};

static int i596_open(struct device *dev);
static int i596_start_xmit(struct sk_buff *skb, struct device *dev);
static void i596_interrupt(int reg_ptr);
static int i596_close(struct device *dev);
static void i596_add_cmd(struct device *dev, struct i596_cmd *cmd);
static void i596_cleanup_cmd(struct i596_private *lp);

static inline void init_rx_bufs(struct device *dev) {
  struct i596_private *lp = (struct i596_private *)dev->priv;
  int i;
  int boguscnt = 50;
  short ioaddr = dev->base_addr;

  for (i = 0; i < RX_RING_SIZE; i++) {
    if (i == 0) {
      lp->scb.rfd = &lp->rx[0];
    }
    if (i == (RX_RING_SIZE - 1)) {
      lp->rx_tail = &(lp->rx[i]);
      lp->rx[i].next = &lp->rx[0];
      lp->rx[i].cmd = CMD_EOL;
    } else {
      lp->rx[i].next = &lp->rx[i + 1];
      lp->rx[i].cmd = 0x0000;
    }
    lp->rx[i].stat = 0x0000;
    lp->rx[i].rbd = 0xffffffff;
    lp->rx[i].count = 0;
    lp->rx[i].size = 1532;
  }

  while (lp->scb.status, lp->scb.command)
    if (--boguscnt == 0) {
      break;
    }

  lp->scb.command = RX_START;
  outw(0, ioaddr + 4);

  return;
}

static inline void init_i596_mem(struct device *dev) {
  struct i596_private *lp = (struct i596_private *)dev->priv;
  short ioaddr = dev->base_addr;
  int boguscnt = 50;

  /* change the scp address */
  outw(0, ioaddr);
  outw(0, ioaddr);
  outb(4, ioaddr + 0xf);
  outw(((((int)&lp->scp) & 0xffff) | 2), ioaddr);
  outw((((int)&lp->scp) >> 16) & 0xffff, ioaddr);

  lp->last_cmd = jiffies;

  lp->scp.sysbus = 0x00440000;
  lp->scp.iscp = &(lp->iscp);
  lp->iscp.scb = &(lp->scb);
  lp->iscp.stat = 0x0001;
  lp->cmd_backlog = 0;

  lp->cmd_head = lp->scb.cmd = (struct i596_cmd *)-1;

  (void)inb(ioaddr + 0x10);
  outb(4, ioaddr + 0xf);
  outw(0, ioaddr + 4);

  while (lp->iscp.stat)
    if (--boguscnt == 0) {
      break;
    }

  memcpy(lp->i596_config, init_setup, 14);
  lp->set_conf.command = CmdConfigure;
  i596_add_cmd(dev, &lp->set_conf);

  memcpy(lp->eth_addr, dev->dev_addr, 6);
  lp->set_add.command = CmdSASetup;
  i596_add_cmd(dev, &lp->set_add);

  lp->tdr.command = CmdTDR;
  i596_add_cmd(dev, &lp->tdr);

  init_rx_bufs(dev);

  return;
}

static inline int i596_rx(struct device *dev) {
  struct i596_private *lp = (struct i596_private *)dev->priv;
  int frames = 0;

  while ((lp->scb.rfd->stat) & STAT_C) {
    if ((lp->scb.rfd->stat) & STAT_OK) {
      /* a good frame */
      int pkt_len = lp->scb.rfd->count & 0x3fff;
      struct sk_buff *skb = alloc_skb(pkt_len, GFP_ATOMIC);

      frames++;

      skb->len = pkt_len;
      skb->dev = dev;
      memcpy(skb->data, lp->scb.rfd->data, pkt_len);

      netif_rx(skb);
    }

    lp->scb.rfd->stat = 0;
    lp->rx_tail->cmd = 0;
    lp->rx_tail = lp->scb.rfd;
    lp->scb.rfd = lp->scb.rfd->next;
    lp->rx_tail->count = 0;
    lp->rx_tail->cmd = CMD_EOL;
  }

  return 0;
}

static void i596_add_cmd(struct device *dev, struct i596_cmd *cmd) {
  struct i596_private *lp = (struct i596_private *)dev->priv;
  int ioaddr = dev->base_addr;
  unsigned long flags;
  int boguscnt = 50;

  cmd->status = 0;
  cmd->command |= (CMD_EOL | CMD_INTR);
  cmd->next = (struct i596_cmd *)-1;

  save_flags(flags);
  cli();
  if (lp->cmd_head != (struct i596_cmd *)-1)
    lp->cmd_tail->next = cmd;
  else {
    lp->cmd_head = cmd;
    while (lp->scb.status, lp->scb.command)
      if (--boguscnt == 0) {
        break;
      }

    lp->scb.cmd = cmd;
    lp->scb.command = CUC_START;
    outw(0, ioaddr + 4);
  }
  lp->cmd_tail = cmd;
  lp->cmd_backlog++;

  lp->cmd_head = lp->scb.cmd;
  restore_flags(flags);

  if (lp->cmd_backlog > 8) {
    int tickssofar = jiffies - lp->last_cmd;
    if (tickssofar < 10)
      return;

    boguscnt = 50;
    while (lp->scb.status, lp->scb.command)
      if (--boguscnt == 0) {
        break;
      }
    lp->scb.command = CUC_ABORT | RX_ABORT;
    outw(0, ioaddr + 4);

    i596_cleanup_cmd(lp);
    i596_rx(dev);
    init_i596_mem(dev);
  }
}

static void i596_cleanup_cmd(struct i596_private *lp) {
  struct i596_cmd *ptr;
  int boguscnt = 50;

  while (lp->cmd_head != (struct i596_cmd *)-1) {
    ptr = lp->cmd_head;

    lp->cmd_head = lp->cmd_head->next;
    lp->cmd_backlog--;

    switch ((ptr->command) & 0x7) {
    case CmdTx: {
      struct tx_cmd *tx_cmd = (struct tx_cmd *)ptr;
      struct sk_buff *skb = ((struct sk_buff *)(tx_cmd->tbd->data)) - 1;

      dev_kfree_skb(skb, FREE_WRITE);

      ptr->next = (struct i596_cmd *)-1;
      kfree_s((unsigned char *)tx_cmd,
              (sizeof(struct tx_cmd) + sizeof(struct i596_tbd)));
      break;
    }
    case CmdMulticastList: {
      unsigned short count = *((unsigned short *)(ptr + 1));

      ptr->next = (struct i596_cmd *)-1;
      kfree_s((unsigned char *)ptr, (sizeof(struct i596_cmd) + count + 2));
      break;
    }
    default:
      ptr->next = (struct i596_cmd *)-1;
    }
  }

  while (lp->scb.status, lp->scb.command)
    if (--boguscnt == 0) {
      break;
    }

  lp->scb.cmd = lp->cmd_head;
}

static int i596_open(struct device *dev) {
  if (request_irq(dev->irq, &i596_interrupt)) {
    return -EAGAIN;
  }

  irq2dev_map[dev->irq] = dev;

  dev->tbusy = 0;
  dev->interrupt = 0;
  dev->start = 1;

  /* Initialize the 82596 memory */
  init_i596_mem(dev);

  return 0; /* Always succeed */
}

static int i596_start_xmit(struct sk_buff *skb, struct device *dev) {
  struct i596_private *lp = (struct i596_private *)dev->priv;
  int ioaddr = dev->base_addr;
  struct tx_cmd *tx_cmd;

  /* Transmitter timeout, serious problems. */
  if (dev->tbusy) {
    int tickssofar = jiffies - dev->trans_start;
    if (tickssofar < 5)
      return 1;
    /* Try to restart the adaptor */
    /* Shutdown and restart */

    lp->scb.command = CUC_ABORT | RX_ABORT;
    outw(0, ioaddr + 4);

    i596_cleanup_cmd(lp);
    init_i596_mem(dev);

    dev->tbusy = 0;
    dev->trans_start = jiffies;
  }

  /* If some higher level thinks we've misses a tx-done interrupt
     we are passed NULL. n.b. dev_tint handles the cli()/sti()
     itself. */
  if (skb == NULL) {
    dev_tint(dev);
    return 0;
  }

  /* shouldn't happen */
  if (skb->len <= 0)
    return 0;

  /* Block a timer-based transmit from overlapping.  This could better be
     done with atomic_swap(1, dev->tbusy), but set_bit() works as well. */
  if (set_bit(0, (void *)&dev->tbusy) != 0)
    else {
      short length = ETH_ZLEN < skb->len ? skb->len : ETH_ZLEN;
      dev->trans_start = jiffies;

      tx_cmd = (struct tx_cmd *)kmalloc(
          (sizeof(struct tx_cmd) + sizeof(struct i596_tbd)), GFP_ATOMIC);
      if (tx_cmd == NULL) {
        dev_kfree_skb(skb, FREE_WRITE);
      } else {
        tx_cmd->tbd = (struct i596_tbd *)(tx_cmd + 1);
        tx_cmd->tbd->next = (struct i596_tbd *)-1;

        tx_cmd->cmd.command = CMD_FLEX | CmdTx;

        tx_cmd->pad = 0;
        tx_cmd->size = 0;
        tx_cmd->tbd->pad = 0;
        tx_cmd->tbd->size = EOF | length;

        tx_cmd->tbd->data = skb->data;

        i596_add_cmd(dev, (struct i596_cmd *)tx_cmd);
      }
    }

  dev->tbusy = 0;

  return 0;
}

unsigned long apricot_init(unsigned long mem_start, unsigned long mem_end) {
  struct device *dev;
  int i;
  int checksum = 0;
  int ioaddr = 0x300;

  /* this is easy the ethernet interface can only be at 0x300 */
  /* first check nothing is already registered here */

  if (check_region(ioaddr, APRICOT_TOTAL_SIZE))
    return mem_start;

  for (i = 0; i < 8; i++)
    checksum += inb(ioaddr + 8 + i);

  /* checksum is a multiple of 0x100, got this wrong first time
     some machines have 0x100, some 0x200. The DOS driver doesn't
     even bother with the checksum */

  if (checksum % 0x100)
    return mem_start;

  dev = init_etherdev(0, (sizeof(struct i596_private) + 0xf), &mem_start);

  dev->base_addr = ioaddr;
  dev->irq = 10;

  snarf_region(ioaddr, APRICOT_TOTAL_SIZE);

  /* The APRICOT-specific entries in the device structure. */
  dev->open = &i596_open;
  dev->stop = &i596_close;
  dev->hard_start_xmit = &i596_start_xmit;

  /* align for scp */
  dev->priv = (void *)(((int)dev->priv + 0xf) & 0xfffffff0);

  return mem_start;
}

static void i596_interrupt(int reg_ptr) {
  int irq = -(((struct pt_regs *)reg_ptr)->orig_eax + 2);
  struct device *dev = (struct device *)(irq2dev_map[irq]);
  struct i596_private *lp;
  short ioaddr;
  int boguscnt = 100;
  unsigned short status, ack_cmd = 0;

  if (dev == NULL) {
    return;
  }

  if (dev->interrupt)

    dev->interrupt = 1;

  ioaddr = dev->base_addr;

  lp = (struct i596_private *)dev->priv;

  while (lp->scb.status, lp->scb.command)
    if (--boguscnt == 0) {
      break;
    }
  status = lp->scb.status;

  ack_cmd = status & 0xf000;

  if ((status & 0x8000) || (status & 0x2000)) {
    struct i596_cmd *ptr;

    while ((lp->cmd_head != (struct i596_cmd *)-1) &&
           (lp->cmd_head->status & STAT_C)) {
      ptr = lp->cmd_head;

      lp->cmd_head = lp->cmd_head->next;
      lp->cmd_backlog--;

      switch ((ptr->command) & 0x7) {
      case CmdTx: {
        struct tx_cmd *tx_cmd = (struct tx_cmd *)ptr;
        struct sk_buff *skb = ((struct sk_buff *)(tx_cmd->tbd->data)) - 1;

        dev_kfree_skb(skb, FREE_WRITE);

        ptr->next = (struct i596_cmd *)-1;
        kfree_s((unsigned char *)tx_cmd,
                (sizeof(struct tx_cmd) + sizeof(struct i596_tbd)));
        break;
      }
      case CmdMulticastList: {
        unsigned short count = *((unsigned short *)(ptr + 1));

        ptr->next = (struct i596_cmd *)-1;
        kfree_s((unsigned char *)ptr, (sizeof(struct i596_cmd) + count + 2));
        break;
      }
      default:
        ptr->next = (struct i596_cmd *)-1;

        lp->last_cmd = jiffies;
      }
    }

    ptr = lp->cmd_head;
    while ((ptr != (struct i596_cmd *)-1) && (ptr != lp->cmd_tail)) {
      ptr->command &= 0x1fff;
      ptr = ptr->next;
    }

    if ((lp->cmd_head != (struct i596_cmd *)-1) && (dev->start))
      ack_cmd |= CUC_START;
    lp->scb.cmd = lp->cmd_head;
  }

  if ((status & 0x1000) || (status & 0x4000)) {
    i596_rx(dev);

    if (dev->start)
      ack_cmd |= RX_START;
  }

  /* acknowlage the interrupt */

  /*
      if ((lp->scb.cmd != (struct i596_cmd *) -1) && (dev->start)) ack_cmd |=
     CUC_START;
  */
  boguscnt = 100;
  while (lp->scb.status, lp->scb.command)
    if (--boguscnt == 0) {
      break;
    }
  lp->scb.command = ack_cmd;

  (void)inb(ioaddr + 0x10);
  outb(4, ioaddr + 0xf);
  outw(0, ioaddr + 4);

  dev->interrupt = 0;
  return;
}

static int i596_close(struct device *dev) {
  int ioaddr = dev->base_addr;
  struct i596_private *lp = (struct i596_private *)dev->priv;

  dev->start = 0;
  dev->tbusy = 1;

  lp->scb.command = CUC_ABORT | RX_ABORT;
  outw(0, ioaddr + 4);

  i596_cleanup_cmd(lp);

  free_irq(dev->irq);
  irq2dev_map[dev->irq] = 0;

  return 0;
}

#ifdef HAVE_DEVLIST
static unsigned int apricot_portlist[] = {0x300, 0};
struct netdev_entry apricot_drv = {"apricot", apricot_init, APRICOT_TOTAL_SIZE,
                                   apricot_portlist};
#endif
