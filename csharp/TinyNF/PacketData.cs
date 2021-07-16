using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using CSUnsafe = System.Runtime.CompilerServices.Unsafe;

namespace TinyNF
{
    /// <summary>
    /// Packet data.
    /// This struct uses evil tricks to mimick a fixed-size buffer without explicitly using unsafe code,
    /// since C# doesn't support that yet.
    /// See https://github.com/dotnet/csharplang/blob/main/proposals/fixed-sized-buffers.md
    /// and https://github.com/dotnet/csharplang/issues/1314
    /// </summary>
    [StructLayout(LayoutKind.Explicit, Size = Size)]
    public struct PacketData
    {
        public const int Size = 2048;

        // The compiler doesn't currently coalesce byte writes, so one can use span casts to e.g. ulong or uint instead of byte
        // as a workaround, but this doesn't seem to improve perf in practice, guess the CPU is smart
        public byte this[int index]
        {
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            get
            {
                return MemoryMarshal.Cast<PacketData, byte>(MemoryMarshal.CreateSpan(ref this, 1))[index];
            }
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            set
            {
                MemoryMarshal.Cast<PacketData, byte>(MemoryMarshal.CreateSpan(ref this, 1))[index] = value;
            }
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public ref T Cast<T>(int offset)
            where T : unmanaged
        {
            if (offset + CSUnsafe.SizeOf<T>() >= Size)
            {
                throw new ArgumentOutOfRangeException(nameof(offset));
            }

            return ref CSUnsafe.AddByteOffset<T>(ref MemoryMarshal.AsRef<T>(MemoryMarshal.AsBytes(MemoryMarshal.CreateSpan(ref this, 1))), (nuint)(uint)offset);
        }
    }
}
