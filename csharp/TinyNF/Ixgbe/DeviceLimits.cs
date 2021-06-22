namespace TinyNF.Ixgbe
{
    internal static class DeviceLimits
    {
        public const uint FiveTupleFiltersCount = 128u;

        public const uint InterruptRegistersCount = 3u;

        public const uint MulticastTableArraySize = 4u * 1024u;

        public const uint PoolsCount = 64u;

        public const uint ReceiveAddressesCount = 128u;

        public const uint ReceiveQueuesCount = 128u;

        public const uint TransmitQueuesCount = 128u;

        public const uint TrafficClassesCount = 8u;

        public const uint UnicastTableArraySize = 4u * 1024u;
    }
}
