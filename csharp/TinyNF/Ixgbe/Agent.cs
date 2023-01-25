using System;
using System.Runtime.CompilerServices;
using System.Threading;
using TinyNF.Environment;
using TinyNF.Unsafe;

namespace TinyNF.Ixgbe;

internal interface IPacketProcessor
{
    abstract static void Process(ref PacketData data, ulong length, Array256<ulong> outputs);
}

internal ref struct Agent
{
    private const uint FlushPeriod = 8;
    private const uint RecyclePeriod = 64;

    private static uint _fakeTail; // default value when initiailizing TransmitTails

    private readonly Array256<PacketData> _buffers;
    // OVERHEAD: keep a separate reference to the receive ring to avoid bounds checks during run
    private readonly Array256<Descriptor> _receiveRing;
    private readonly Array256Array<Descriptor> _transmitRings;
    private readonly ref uint _receiveTailAddr;
    private readonly Span<TransmitHead> _transmitHeads;
    private readonly RefArray<uint> _transmitTailAddrs;
    private readonly Array256<ulong> _outputs; // trade off a tiny bit of unused space for no bounds checks
    private byte _processedDelimiter;


    public Agent(IEnvironment env, Device inputDevice, Device[] outputDevices)
    {
        _processedDelimiter = 0;
        _outputs = new Array256<ulong>(env.Allocate<ulong>);

        _buffers = new Array256<PacketData>(env.Allocate<PacketData>);

        _transmitRings = new Array256Array<Descriptor>(outputDevices.Length, env.Allocate<Descriptor>);
        for (int r = 0; r < _transmitRings.Length; r++)
        {
            for (int n = 0; n < _transmitRings[r].Length; n++)
            {
                _transmitRings[r][(byte)n].Addr = Endianness.ToLittle(env.GetPhysicalAddress(ref _buffers[(byte)n]));
            }
        }

        _receiveRing = _transmitRings[0];
        _receiveTailAddr = ref inputDevice.SetInput(env, _receiveRing.AsSpan()).Span[0];

        _transmitHeads = env.Allocate<TransmitHead>(outputDevices.Length).Span;
        _transmitTailAddrs = new RefArray<uint>(outputDevices.Length, n => ref _fakeTail);
        for (byte n = 0; n < outputDevices.Length; n++)
        {
            _transmitTailAddrs.Set(n, ref outputDevices[n].AddOutput(env, _transmitRings[n].AsSpan(), ref _transmitHeads[n]).Span[0]);
        }
    }

    // Allow the JIT to inline the processor by making it a struct, since the JIT generates a specialized version of the method per value type
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public void Run<T>() where T : struct, IPacketProcessor
    {
        nint n;
        for (n = 0; n < FlushPeriod; n++)
        {
            ulong receiveMetadata = Endianness.FromLittle(Volatile.Read(ref _receiveRing[_processedDelimiter].Metadata));
            if ((receiveMetadata & Device.RxMetadataDD) == 0)
            {
                break;
            }

            ulong length = Device.RxMetadataLength(receiveMetadata);
            T.Process(ref _buffers[_processedDelimiter], length, _outputs);

            ulong rsBit = ((_processedDelimiter % RecyclePeriod) == (RecyclePeriod - 1)) ? Device.TxMetadataRS : 0;

            // not clear why we have to copy _transmitRings here (its only member is an array), but this is necessary for the bounds check to be eliminated
            // might be https://github.com/dotnet/runtime/issues/72004
            var _transmitRings = this._transmitRings;
            for (int b = 0; b < _transmitRings.Length; b++)
            {
                Volatile.Write(
                    ref _transmitRings[b][_processedDelimiter].Metadata,
                    Endianness.ToLittle(Device.TxMetadataLength(_outputs[(byte)b]) | rsBit | Device.TxMetadataIFCS | Device.TxMetadataEOP)
                );
                _outputs[(byte)b] = 0;
            }

            _processedDelimiter++; // modulo implicit since it's a byte

            if (rsBit != 0)
            {
                uint earliestTransmitHead = _processedDelimiter;
                ulong minDiff = ulong.MaxValue;
                foreach (ref var headRef in _transmitHeads)
                {
                    uint head = Endianness.FromLittle(Volatile.Read(ref headRef.Value));
                    ulong diff = head - _processedDelimiter;
                    if (diff <= minDiff)
                    {
                        earliestTransmitHead = head;
                        minDiff = diff;
                    }
                }

                Volatile.Write(ref _receiveTailAddr, Endianness.ToLittle(earliestTransmitHead));
            }
        }
        if (n != 0)
        {
            foreach (ref var tail in _transmitTailAddrs)
            {
                Volatile.Write(ref tail, Endianness.ToLittle(_processedDelimiter));
            }
        }
    }
}
