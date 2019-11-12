/*
 * This is a script based on Thomar NAT and using DPDK for I/O. One  
 * can replace the FromDPDKDevice and ToDPDKDevice with FromDevice 
 * and Queue -> ToDevice to use standard I/O.
 *
 * See also thomer-nat.click and mazu-nat.click
 *
 * Author: Hongyi Zhang <hongyiz@kth.se>
 * Modified by: Rishabh Iyer <rishabh.iyer@epfl.ch>
 */

define(
 $iface0    0,
 $iface1    1
);

AddressInfo(
    lan_interface    192.168.6.2   192.168.6.2/24    90:e2:ba:55:14:11,
    wan_interface    192.168.4.10  192.168.4.10/27   90:e2:ba:55:14:10,
    backend_1	     10.1.1.1,
    backend_2        10.1.1.2,
    backend_3	     10.1.1.3,
    backend_4        10.1.1.4,
    backend_5	     10.1.1.5,
    backend_6        10.1.1.6,
    backend_7	     10.1.1.7,
    backend_8        10.1.1.8,
    backend_9	     10.1.1.9,
    backend_10       10.1.1.10,
    backend_11	     10.1.1.11,
    backend_12       10.1.1.12,
    backend_13	     10.1.1.13,
    backend_14       10.1.1.14,
    backend_15	     10.1.1.15,
    backend_16       10.1.1.16,
    backend_17	     10.1.1.17,
    backend_18       10.1.1.18,
    backend_19	     10.1.1.19,
    backend_20       10.1.1.20
);

// Module's I/O
nicIn0  :: FromDPDKDevice($iface0, BURST $burst);
nicOut0 :: ToDPDKDevice  ($iface0, IQUEUE $burst, BURST $burst);

nicIn1  :: FromDPDKDevice($iface1, BURST $burst);
nicOut1 :: ToDPDKDevice  ($iface1, IQUEUE $burst, BURST $burst);


rwpattern :: RoundRobinIPMapper(- - backend_1 - $iface0 $iface1, 
				- - backend_2 - $iface0 $iface1, 
				- - backend_3 - $iface0 $iface1, 
				- - backend_4 - $iface0 $iface1, 
				- - backend_5 - $iface0 $iface1, 
				- - backend_6 - $iface0 $iface1, 
				- - backend_7 - $iface0 $iface1, 
				- - backend_8 - $iface0 $iface1, 
				- - backend_9 - $iface0 $iface1, 
				- - backend_10 - $iface0 $iface1, 
				- - backend_11 - $iface0 $iface1, 
				- - backend_12 - $iface0 $iface1, 
				- - backend_13 - $iface0 $iface1, 
				- - backend_14 - $iface0 $iface1, 
				- - backend_15 - $iface0 $iface1, 
				- - backend_16 - $iface0 $iface1, 
				- - backend_17 - $iface0 $iface1, 
				- - backend_18 - $iface0 $iface1, 
				- - backend_19 - $iface0 $iface1, 
				- - backend_20 - $iface0 $iface1, 
				);

ee_left :: EnsureEther(0x0800, 1:1:1:1:1:0,90:e2:ba:55:14:10);
ee_right :: EnsureEther(0x0800, 1:1:1:1:1:1,90:e2:ba:55:14:11); 

ip_rw :: IPRewriter(rwpattern, drop, MAPPING_CAPACITY 65536);

nicIn0 -> Strip(14) -> CheckIPHeader -> [0]ip_rw;
ip_rw[0] -> ee_left[0] -> nicOut1;


nicIn1 -> Strip(14) -> CheckIPHeader -> [1]ip_rw;
ip_rw[1] -> ee_right[0] -> nicOut0;
