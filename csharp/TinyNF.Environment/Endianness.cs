using System;
using System.Buffers.Binary;

namespace TinyNF.Environment;

public static class Endianness
{
    public static ulong FromLittle(ulong value)
    {
        if (BitConverter.IsLittleEndian)
        {
            return value;
        }
        return BinaryPrimitives.ReverseEndianness(value);
    }

    public static uint FromLittle(uint value)
    {
        if (BitConverter.IsLittleEndian)
        {
            return value;
        }
        return BinaryPrimitives.ReverseEndianness(value);
    }

    public static ulong ToLittle(ulong value)
    {
        if (BitConverter.IsLittleEndian)
        {
            return value;
        }
        return BinaryPrimitives.ReverseEndianness(value);
    }

    public static uint ToLittle(uint value)
    {
        if (BitConverter.IsLittleEndian)
        {
            return value;
        }
        return BinaryPrimitives.ReverseEndianness(value);
    }
}
