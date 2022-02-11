NOTE: The 'restrict' don't seem to change anything, but we put them there just to make the code equivalent to the semantics of other langs

// All references in this file are to the Intel 82599 Data Sheet unless otherwise noted.
// It can be found at https://www.intel.com/content/www/us/en/design/products-and-solutions/networking-and-io/82599-10-gigabit-ethernet-controller/technical-library.html

// ===============
// Interpretations
// ===============

// Unfortunately, we sometimes have to interpret the specification; these are categorized as follows.

// CONTRADICTION: The data sheet contradicts itself, forcing us to make a guess.
// INCORRECT: The data sheet is plain wrong given how the hardware actually behaves.
// MISSING: Data is missing, forcing us to make a guess.
// POINTLESS: The data sheet asks to do something unambiguously pointless, such as writing 0 to a register already initialized.
// TYPO: Obvious typo in the spec that is very unlikely to be ambiguous.


// ===========
// Assumptions
// ===========

// We make the following assumptions, which we later refer to by name.

// CACHE: The cache line size is 64 bytes
// CRC: We want CRC stripped when receiving and generated on the entire packet when transmitting
// DROP: We want to drop packets if we can't process them fast enough, for predictable behavior
// NOMEMERRORS: The internal memory of the card does not get corrupted beyond repair, as Section 7.14.1 refers to.
// NOCARE: We do not care about the following:
//         - Statistics
//         - Receive Side Coalescing (RSC)
//         - NFS
// NOWANT: We do not want the following:
//         - Flexible filters
//         - VLAN handling
//         - Multicast filtering
//         - Receive checksum offloading
//         - Receive side scaling (RSS)
//         - 5-tuple filtering
//         - L2 ethertype filtering
//         - SR-IO
//         - VMDq
//         - Jumbo packet handling
//         - LinkSec packet handling
//         - Loopback
//         - Global double VLAN mode
//         - Interrupts
//         - Debugging features
//         - Direct Cache Access (DCA), supposedly improves perf but no apparent effect
// PCIBARS: The PCI BARs have been pre-configured to valid values, and will not collide with any other memory we may handle
// PCIBRIDGES: All PCI bridges can be ignored, i.e. they do not enforce power savings modes or any other limitations
// REPORT: We prefer more error reporting when faced with an explicit choice, but do not attempt to do extra configuration for this
// TRUST: We trust the defaults for low-level hardware details
// TXPAD: We want all sent frames to be at least 64 bytes
