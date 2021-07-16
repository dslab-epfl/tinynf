using DataStructures;
using TinyNF.Environment;
using Time = System.UInt64;

namespace TinyNF.Functions
{
    public ref struct Firewall
    {
        private readonly byte _externalDevice;
        private FlowTable _table;

        public Firewall(IEnvironment env)
        {
            // hardcoding config, easier
            _externalDevice = 1;
            _table = new FlowTable(env, 4ul * 1000ul * 1000ul * 1000ul, 65536);
        }

        public bool Process(in Packet packet)
        {
            ref IPv4Header ipv4Header = ref IPv4Header.Parse(in packet, out var ipv4Success);
            if (!ipv4Success)
            {
                // Not IPv4
                return false;
            }
            ref TcpUdpHeader tcpUdpHeader = ref TcpUdpHeader.Parse(in packet, out var tcpUdpSuccess);
            if (!tcpUdpSuccess)
            {
                // Not TCP/UDP
                return false;
            }

            if (packet.Device == _externalDevice)
            {
                // inverted!
                var flow = new Flow(
                    srcIp: ipv4Header.DstAddr,
                    dstIp: ipv4Header.SrcAddr,
                    srcPort: tcpUdpHeader.DstPort,
                    dstPort: tcpUdpHeader.SrcPort,
                    protocol: ipv4Header.NextProtoId
                );
                if (!_table.HasExternal(packet.Time, in flow))
                {
                    // Unknown flow
                    return false;
                }
            }
            else
            {
                var flow = new Flow(
                    srcIp: ipv4Header.SrcAddr,
                    dstIp: ipv4Header.DstAddr,
                    srcPort: tcpUdpHeader.SrcPort,
                    dstPort: tcpUdpHeader.DstPort,
                    protocol: ipv4Header.NextProtoId
                );
                _table.LearnInternal(packet.Time, in flow);
            }

            return true;
        }

        private readonly struct Flow
        {
            public readonly uint SrcIp;
            public readonly uint DstIp;
            public readonly ushort SrcPort;
            public readonly ushort DstPort;
            public readonly byte Protocol;

            public Flow(uint srcIp, uint dstIp, ushort srcPort, ushort dstPort, byte protocol)
            {
                SrcIp = srcIp;
                DstIp = dstIp;
                SrcPort = srcPort;
                DstPort = dstPort;
                Protocol = protocol;
            }
        }

        private ref struct FlowTable
        {
            private readonly Map<Flow> _flows;
            private IndexPool _portAllocator;

            public FlowTable(IEnvironment env, Time expirationTime, int maxFlows)
            {
                _flows = new Map<Flow>(env, maxFlows);
                _portAllocator = new IndexPool(env, maxFlows, expirationTime);
            }

            public void LearnInternal(Time time, in Flow flow)
            {
                int index = 0;
                bool wasUsed = false;
                if (_flows.Get(in flow, ref index))
                {
                    _portAllocator.Refresh(time, (ushort)index);
                }
                else if (_portAllocator.Borrow(time, ref index, ref wasUsed))
                {
                    if (wasUsed)
                    {
                     //   _flows.Remove(in _flows[(ushort)index]);
                    }

                   // _flows[(ushort)index] = flow;
                    _flows.Set(in flow, index);
                }
            }

            public readonly bool HasExternal(Time time, in Flow flow)
            {
                int index = 0;
                if (_flows.Get(in flow, ref index) && _portAllocator.IsUsed(time, (ushort)index))
                {
                    _portAllocator.Refresh(time, (ushort)index);
                    return true;
                }

                return false;
            }
        }
    }
}
