// Enable non-default lints
#![warn(future_incompatible)]
#![warn(nonstandard_style)]
#![warn(rust_2018_idioms)]
#![warn(unused)]

mod env;
use env::LinuxEnvironment;

mod pci;
use pci::PciAddress;

mod lifed;

mod ixgbe;
use ixgbe::agent;
use ixgbe::agent::Agent;
use ixgbe::agent_const::AgentConst;
use ixgbe::device::{Device, PacketData};


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

fn proc<const N: usize>(data: &mut PacketData, length: u64, output_lengths: &mut [u64; N]) {
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
    output_lengths[0] = length;
}

#[inline(never)]
fn run_const<const N: usize>(agent0: &mut AgentConst<'_, N>, agent1: &mut AgentConst<'_, N>) {
    loop {
        agent0.run(proc::<N>);
        agent1.run(proc::<N>);
    }
}

#[inline(never)]
fn run(agent0: &mut Agent<'_>, agent1: &mut Agent<'_>) {
    loop {
        agent0.run(proc::<{ agent::MAX_OUTPUTS }>);
        agent1.run(proc::<{ agent::MAX_OUTPUTS }>);
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

    let agent0outs = [&dev1];
    let agent1outs = [&dev0];

    if cfg!(feature="constgenerics") {
        let mut agent0 = AgentConst::create(&env, &dev0, agent0outs);
        let mut agent1 = AgentConst::create(&env, &dev1, agent1outs);

        println!("All good, running with const generics...");

        run_const::<1>(&mut agent0, &mut agent1);
    } else {
        let mut agent0 = Agent::create(&env, &dev0, &agent0outs);
        let mut agent1 = Agent::create(&env, &dev1, &agent1outs);

        println!("All good, running...");
        run(&mut agent0, &mut agent1);
    }
}
