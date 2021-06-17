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
use ixgbe::device::Device;

fn parse_pci_address(s: &str) -> PciAddress {
    let parts: Vec<&str> = s.split(&[':', '.'][..]).collect(); // technically too lax but that's fine
    if parts.len() != 3 {
        panic!("Bad PCI address");
    }
    PciAddress {
        bus: u8::from_str_radix(parts[0], 16).unwrap(),
        device: u8::from_str_radix(parts[1], 16).unwrap(),
        function: u8::from_str_radix(parts[2], 16).unwrap()
    }
}

fn proc(data: &mut [u8; ixgbe::PACKET_SIZE], length: u16, output_lengths: &mut [u16; ixgbe::MAX_OUTPUTS]) {
    data[0] = 0;
    data[1] = 0;
    data[2] = 0;
    data[3] = 0;
    data[4] = 0;
    data[5] = 1;
    data[6] = 0;
    data[7] = 0;
    data[8] = 0;
    data[9] = 0;
    data[10] = 0;
    data[11] = 0;
    output_lengths[0] = length
}

fn run(agent0: &mut Agent<'_>, agent1: &mut Agent<'_>) {
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

    let mut env = LinuxEnvironment::new();

    let mut dev0 = Device::init(&env, parse_pci_address(&args[1][..]));
    dev0.set_promiscuous();
    let (mut dev0in, mut dev0out) = dev0.into_inout();

    let mut dev1 = Device::init(&env, parse_pci_address(&args[2][..]));
    dev1.set_promiscuous();
    let (mut dev1in, mut dev1out) = dev1.into_inout();

    let mut agent0outs = [&mut dev1out];
    let mut agent0 = Agent::create(&mut env, &mut dev0in, &mut agent0outs);

    let mut agent1outs = [&mut dev0out];
    let mut agent1 = Agent::create(&mut env, &mut dev1in, &mut agent1outs);

    print!("All good, running...\n");

    run(&mut agent0, &mut agent1);
}
