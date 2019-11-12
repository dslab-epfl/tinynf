/*
 * This is a script based on Thomar NAT and using DPDK for I/O. One  
 * can replace the FromDPDKDevice and ToDPDKDevice with FromDevice 
 * and Queue -> ToDevice to use standard I/O.
 *
 * See also thomer-nat.click and mazu-nat.click
 *
 * Author: Hongyi Zhang <hongyiz@kth.se>
 * Modified by: Rishabh Iyer <rishabh.iyer@epfl.ch>
 * Modified by: Solal Pirelli <solal.pirelli@epfl.ch>
 */

define(
 $iface0    0,
 $iface1    1
);

AddressInfo(
    port1    192.168.6.2   10.0.0.0/8        90:e2:ba:55:14:11,
    port2    192.168.4.10  192.168.4.10/27   90:e2:ba:55:14:10
);

// Module's I/O
nicIn0  :: FromDPDKDevice($iface0, BURST $burst);
nicOut0 :: ToDPDKDevice  ($iface0, IQUEUE $burst, BURST $burst);

nicIn1  :: FromDPDKDevice($iface1, BURST $burst);
nicOut1 :: ToDPDKDevice  ($iface1, IQUEUE $burst, BURST $burst);

br :: EtherSwitch;

nicIn0 -> [0]br;
br[0]  -> nicOut0;
nicIn1 -> [1]br;
br[1]  -> nicOut1;
