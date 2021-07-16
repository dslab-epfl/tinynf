using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace TinyNF
{
    [StructLayout(LayoutKind.Sequential)]
    public struct EthernetAddress
    {
        // No fixed-size buffers in safe C#...
        public byte B0;
        public byte B1;
        public byte B2;
        public byte B3;
        public byte B4;
        public byte B5;
    }

    [StructLayout(LayoutKind.Sequential)]
    public struct EthernetHeader
    {
        public EthernetAddress DstAddr;
        public EthernetAddress Srcddr;
        public ushort EtherType;

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static ref EthernetHeader Parse(in Packet packet)
        {
            return ref packet.Data.Get().Cast<EthernetHeader>(0);
        }
    }

    [StructLayout(LayoutKind.Sequential)]
    public struct IPv4Header
    {
        public byte VersionIhl;
        public byte TypeOfService;
        public ushort TotalLength;
        public ushort PacketId;
        public ushort FragmentOffset;
        public byte TimeToLive;
        public byte NextProtoId;
        public ushort Checksum;
        public uint SrcAddr;
        public uint DstAddr;

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static ref IPv4Header Parse(in Packet packet, out bool success)
        {
            ref EthernetHeader etherHeader = ref EthernetHeader.Parse(in packet);
            success = etherHeader.EtherType == (BitConverter.IsLittleEndian ? 0x0008 : 0x0800);
            return ref packet.Data.Get().Cast<IPv4Header>(14); // valid regardless given minimal packet size
        }
    }

    [StructLayout(LayoutKind.Sequential)]
    public struct TcpUdpHeader
    {
        public ushort SrcPort;
        public ushort DstPort;

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static ref TcpUdpHeader Parse(in Packet packet, out bool success)
        {
            ref IPv4Header ipv4Header = ref IPv4Header.Parse(in packet, out var ipv4Success);
            success = ipv4Success && (ipv4Header.NextProtoId == 6 || ipv4Header.NextProtoId == 17);
            return ref packet.Data.Get().Cast<TcpUdpHeader>(14 + 20);
        }
    }
}
