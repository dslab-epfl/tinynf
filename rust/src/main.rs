// Enable non-default lints
#![warn(future_incompatible)]
#![warn(nonstandard_style)]
#![warn(rust_2018_idioms)]
#![warn(unused)]

mod env;
use env::LinuxEnvironment;

mod pci;
use pci::PciAddress;

mod volatile; // declare it so ixgbe can use it... weird

mod ixgbe;
use ixgbe::agent::Agent;
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

fn proc(data: &mut PacketData, length: u16, output_lengths: &mut [u16; 1]) {
    data.data[0] = 0;
    data.data[1] = 0;
    data.data[2] = 0;
    data.data[3] = 0;
    data.data[4] = 0;
    data.data[5] = 1;
    data.data[6] = 0;
    data.data[7] = 0;
    data.data[8] = 0;
    data.data[9] = 0;
    data.data[10] = 0;
    data.data[11] = 0;
    output_lengths[0] = length;
}

fn run(agent0: &mut Agent<'_, '_, 1>, agent1: &mut Agent<'_, '_, 1>) {
    loop {
        agent0.run(proc);
        agent1.run(proc);
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
    let (mut dev0in, mut dev0out) = dev0.into_inout();

    let pci1 = parse_pci_address(&args[2][..]);
    let mut dev1 = Device::init(&env, pci1);
    dev1.set_promiscuous();
    let (mut dev1in, mut dev1out) = dev1.into_inout();

    let agent0outs = [&mut dev1out];
    let mut agent0 = Agent::create(&env, &mut dev0in, agent0outs);

    let agent1outs = [&mut dev0out];
    let mut agent1 = Agent::create(&env, &mut dev1in, agent1outs);

    println!("All good, running...");

    run(&mut agent0, &mut agent1);
}
