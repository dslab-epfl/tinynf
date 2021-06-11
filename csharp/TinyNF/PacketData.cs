using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

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

        public byte this[int index]
        {
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            get
            {
                return MemoryMarshal.AsBytes(MemoryMarshal.CreateSpan(ref this, 1))[index];
            }
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            set
            {
                MemoryMarshal.AsBytes(MemoryMarshal.CreateSpan(ref this, 1))[index] = value;
            }
        }

        // Workaround for the compiler not coalescing byte writes
/*        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public T Read<T>(int index)
            where T : struct
        {
            return MemoryMarshal.Read<T>(MemoryMarshal.AsBytes(MemoryMarshal.CreateSpan(ref this, 1))[index..]);
        }
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void Write<T>(int index, T value)
            where T : struct
        {
            MemoryMarshal.Write(MemoryMarshal.AsBytes(MemoryMarshal.CreateSpan(ref this, 1))[index..], ref value);
        }*/
    }
}
