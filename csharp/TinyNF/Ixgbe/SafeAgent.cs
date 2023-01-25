using System;
using System.Runtime.CompilerServices;
using System.Threading;
using TinyNF.Environment;

// Safe version of Agent (i.e., does not use any unsafe code even transitively)
// See the comments in Agent for some explanations

namespace TinyNF.Ixgbe;

internal interface ISafePacketProcessor
{
    static abstract void Process(ref PacketData data, ulong length, Span<ulong> outputs);
}

internal ref struct SafeAgent
{
    private const uint FlushPeriod = 8;
    private const uint RecyclePeriod = 64;

    private readonly Span<PacketData> _buffers;
    private readonly Span<Descriptor> _receiveRing;
    private readonly Memory<Descriptor>[] _transmitRings;
    private readonly Span<uint> _receiveTailAddr;
    private readonly Span<TransmitHead> _transmitHeads;
    private readonly Memory<uint>[] _transmitTailAddrs;
    private readonly Span<ulong> _outputs;
    private byte _processedDelimiter;


    public SafeAgent(IEnvironment env, Device inputDevice, Device[] outputDevices)
    {
        _processedDelimiter = 0;
        _outputs = env.Allocate<ulong>(outputDevices.Length).Span;

        _buffers = env.Allocate<PacketData>(Device.RingSize).Span;

        _transmitRings = new Memory<Descriptor>[outputDevices.Length];
        for (int n = 0; n < _transmitRings.Length; n++)
        {
            _transmitRings[n] = env.Allocate<Descriptor>(Device.RingSize);
            for (int m = 0; m < _transmitRings[n].Length; m++)
            {
                _transmitRings[n].Span[m].Addr = Endianness.ToLittle(env.GetPhysicalAddress(ref _buffers[m]));
            }
        }

        _receiveRing = _transmitRings[0].Span;
        _receiveTailAddr = inputDevice.SetInput(env, _receiveRing).Span;

        _transmitHeads = env.Allocate<TransmitHead>(outputDevices.Length).Span;
        _transmitTailAddrs = new Memory<uint>[outputDevices.Length];
        for (byte n = 0; n < outputDevices.Length; n++)
        {
            _transmitTailAddrs[n] = outputDevices[n].AddOutput(env, _transmitRings[n].Span, ref _transmitHeads[n]);
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public void Run<T>() where T : struct, ISafePacketProcessor
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
            var transmitRings = _transmitRings;
            for (int r = 0; r < transmitRings.Length; r++)
            {
                Volatile.Write(
                    ref transmitRings[r].Span[_processedDelimiter].Metadata,
                    Endianness.ToLittle(Device.TxMetadataLength(_outputs[r]) | rsBit | Device.TxMetadataIFCS | Device.TxMetadataEOP)
                );
                _outputs[r] = 0;
            }

            _processedDelimiter++;

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

                Volatile.Write(ref _receiveTailAddr[0], Endianness.ToLittle(earliestTransmitHead));
            }
        }
        if (n != 0)
        {
            foreach (var tail in _transmitTailAddrs)
            {
                Volatile.Write(ref tail.Span[0], Endianness.ToLittle(_processedDelimiter));
            }
        }
    }
}
