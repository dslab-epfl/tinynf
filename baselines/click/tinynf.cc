#include <click/config.h>
#include <click/args.hh>
#include <click/error.hh>
#include <click/packet.hh>
#include <click/standard/scheduleinfo.hh>

#include "tinynf.hh"

#include "env/memory.h"
#include "net/network.h"
#include "util/parse.h"

CLICK_DECLS
std::map<tn_pci_device, tn_net_device*, tn_pci_device_comparer> TinyNF::_devices;
std::atomic<int> TinyNF::_instance_count;

struct tn_net_device* TinyNF::get_device(String addr) {
  struct tn_pci_device pci;
  char* c_addr = const_cast<char*>(addr.c_str());
  if (!tn_util_parse_pci(1, &c_addr, &pci)) {
    return nullptr;
  }

  if (_devices.find(pci) == _devices.end()) {
    _devices[pci] = nullptr;
    if (!tn_net_device_init(pci, &(_devices[pci]))) {
      return nullptr;
    }
    if (!tn_net_device_set_promiscuous(_devices[pci])) {
      return nullptr;
    }
  }

  return _devices[pci];
}

TinyNF::TinyNF() : _agent(nullptr), _task(this), _killing(false) { }
TinyNF::~TinyNF() { }

int TinyNF::configure(Vector<String>& conf, ErrorHandler* errh) {
  String src;
  String dst;
  if (Args(conf, this, errh).read_mp("SRC", src).read_mp("DST", dst).complete() < 0) {
    return -1;
  }

  struct tn_net_device* src_dev = get_device(src);
  struct tn_net_device* dst_dev = get_device(dst);

  if (src_dev == nullptr || dst_dev == nullptr) {
    return -1;
  }

  if (!tn_net_agent_init(&_agent)
   || !tn_net_agent_set_input(_agent, src_dev)
   || !tn_net_agent_add_output(_agent, dst_dev, _instance_count++)) {
    return -1;
  }

  return 0;
}

int TinyNF::initialize(ErrorHandler* errh) {
  ScheduleInfo::initialize_task(this, &_task, true, errh);
  return 0;
}

void TinyNF::packet_destructor(unsigned char* buffer, size_t size, void* arg) {
  (void) buffer;

  TinyNF* nf = (TinyNF*) arg;
  if (!nf->_killing) {
    bool list[1];
    list[0] = false;
    tn_net_agent_transmit(nf->_agent, (uint16_t) size, list);
  }
}

bool TinyNF::run_task(Task* task) {
  uint8_t* data;
  uint16_t length;
  if (tn_net_agent_receive(_agent, &data, &length)) {
    WritablePacket* packet = Packet::make(data, length, packet_destructor, this, 0, 0);
    packet->set_packet_type_anno(Packet::HOST);
    packet->set_mac_header(data);
    output(0).push(packet);
    return true;
  } else {
    task->fast_reschedule();
    return false;
  }
}

void TinyNF::push(int port, Packet* p) {
  (void) port;

  bool list[1];
  list[0] = true;
  tn_net_agent_transmit(_agent, p->length(), list);

  _killing = true;
  p->kill();
  _killing = false;

  _task.reschedule();
}
CLICK_ENDDECLS
EXPORT_ELEMENT(TinyNF)
