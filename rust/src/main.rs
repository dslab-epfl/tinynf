// Enable non-default lints
#![warn(future_incompatible)]
#![warn(nonstandard_style)]
#![warn(rust_2018_idioms)]
#![warn(unused)]

mod env;
use env::environment::Environment;
use env::linux::LinuxEnvironment;
use env::pci::PciAddress;

mod lifed;
use lifed::LifedPtr;

mod ixgbe;
use ixgbe::agent;
use ixgbe::agent::Agent;
use ixgbe::agent_const::AgentConst;
use ixgbe::buffer_pool::{Buffer, BufferPool};
use ixgbe::device::{Device, PacketData};
use ixgbe::queues::{QueueRx, QueueTx};

fn parse_pci_address(s: &str) -> PciAddress {
    let parts: Vec<&str> = s.split(&[':', '.'][..]).collect(); // technically too lax but that's fine
    if parts.len() != 3 {
        panic!("Bad PCI address");
    }
    PciAddress {
        bus: u8::from_str_radix(parts[0], 16).unwrap(),
        device: u8::from_str_radix(parts[1], 16).unwrap(),
        function: u8::from_str_radix(parts[2], 16).unwrap(),
    }
}

#[inline(always)]
fn packet_handler(data: &mut PacketData) {
    data.write(0, 0);
    data.write(1, 0);
    data.write(2, 0);
    data.write(3, 0);
    data.write(4, 0);
    data.write(5, 1);
    data.write(6, 0);
    data.write(7, 0);
    data.write(8, 0);
    data.write(9, 0);
    data.write(10, 0);
    data.write(11, 0);
}

fn proc<const N: usize>(data: &mut PacketData, length: u64, output_lengths: &mut [u64; N]) {
    packet_handler(data);
    output_lengths[0] = length;
}

// We add no_mangle so that we can easily find the functions in the assembly

#[inline(never)]
fn run(agent0: &mut Agent<'_>, agent1: &mut Agent<'_>) {
    loop {
        agent0.run(proc::<{ agent::MAX_OUTPUTS }>);
        agent1.run(proc::<{ agent::MAX_OUTPUTS }>);
    }
}

#[inline(never)]
fn run_const<const N: usize>(agent0: &mut AgentConst<'_, N>, agent1: &mut AgentConst<'_, N>) {
    loop {
        agent0.run(proc::<N>);
        agent1.run(proc::<N>);
    }
}

#[inline(never)]
fn run_queues<'a>(rx0: &mut QueueRx<'a>, rx1: &mut QueueRx<'a>, tx0: &mut QueueTx<'a>, tx1: &mut QueueTx<'a>, env: &impl Environment<'a>) {
    // We use u8 throughout + a 256-sized array of buffers to avoid bounds checks
    // (since we cannot propagate the info that nb_rx/nb_tx are always <= buffers.len())
    const QUEUE_BATCH_SIZE: u8 = 32;

    let fake_buffers = env.allocate::<Buffer<'a>, 1>();
    let mut buffers = [LifedPtr::new(&mut fake_buffers[0]); 256];

    loop {
        {
            let nb_rx = rx0.batch(&mut buffers[0..QUEUE_BATCH_SIZE as usize]);
            for ptr in &buffers[0..nb_rx as usize] {
                ptr.map(|b| b.data.map(packet_handler));
            }
            let nb_tx = tx1.batch(&mut buffers[0..nb_rx as usize]);
            // Manual loop here, we would want 'for ptr in &buffers[nb_tx..nb_rx] but this adds a check+panic for nb_tx > nb_rx
            let mut n = nb_rx;
            while n < nb_tx {
                tx1.pool.map(|p| p.give(buffers[n as usize]));
                n = n.wrapping_add(1);
            }
        }
        {
            let nb_rx = rx1.batch(&mut buffers[0..QUEUE_BATCH_SIZE as usize]);
            for ptr in &buffers[0..nb_rx as usize] {
                ptr.map(|b| b.data.map(packet_handler));
            }
            let nb_tx = tx0.batch(&mut buffers[0..nb_rx as usize]);
            let mut n = nb_rx;
            while n < nb_tx {
                tx0.pool.map(|p| p.give(buffers[n as usize]));
                n = n.wrapping_add(1);
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        panic!("Expected 2 args (+ implicit exe name)");
    }

    let env = LinuxEnvironment::new();

    let pci0 = parse_pci_address(&args[1][..]);
    let mut dev0 = Device::init(&env, pci0);
    dev0.set_promiscuous();

    let pci1 = parse_pci_address(&args[2][..]);
    let mut dev1 = Device::init(&env, pci1);
    dev1.set_promiscuous();

    if cfg!(feature = "constgenerics") {
        let agent0array = [LifedPtr::new(&mut dev0)];
        let agent1array = [LifedPtr::new(&mut dev1)];

        let mut agent0 = AgentConst::create(&env, agent0array[0], agent1array);
        let mut agent1 = AgentConst::create(&env, agent1array[0], agent0array);

        println!("All good, running with const generics...");
        run_const::<1>(&mut agent0, &mut agent1);
    } else if cfg!(feature = "queues") {
        const QUEUE_POOL_SIZE: usize = 65535;

        let mut pool0 = BufferPool::allocate(&env, QUEUE_POOL_SIZE);
        let pool0ptr = LifedPtr::new(&mut pool0);
        let mut pool1 = BufferPool::allocate(&env, QUEUE_POOL_SIZE);
        let pool1ptr = LifedPtr::new(&mut pool1);

        let mut rx0 = QueueRx::create(&env, &mut dev0, pool0ptr);
        let mut rx1 = QueueRx::create(&env, &mut dev1, pool1ptr);

        let mut tx0 = QueueTx::create(&env, &mut dev0, pool1ptr);
        let mut tx1 = QueueTx::create(&env, &mut dev1, pool0ptr);

        println!("All good, running with queues...");
        run_queues(&mut rx0, &mut rx1, &mut tx0, &mut tx1, &env);
    } else {
        let agent0array = [LifedPtr::new(&mut dev0)];
        let agent1array = [LifedPtr::new(&mut dev1)];

        let mut agent0 = Agent::create(&env, agent0array[0], &agent1array);
        let mut agent1 = Agent::create(&env, agent1array[0], &agent0array);

        println!("All good, running...");
        run(&mut agent0, &mut agent1);
    }
}
