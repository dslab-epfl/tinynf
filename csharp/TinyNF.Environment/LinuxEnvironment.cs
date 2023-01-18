using System;
using System.Buffers;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

// This class uses more OS interop than is necessary;
// .NET can handle sleeps, file I/O and memory-mapped files just fine.
// But .NET doesn't support mmapping hugepages nor port-mapped I/O (to be fair, not exactly common scenarios).
// We do everything through interop to minimize dependencies on the .NET framework itself,
// which will help if we ever manage a "no .NET runtime" build.

// We only use blittable imports
[assembly: DisableRuntimeMarshalling]

namespace TinyNF.Environment;

/// <summary>
/// Fundamentally unsafe since it interacts with Linux.
/// </summary>
public sealed partial class LinuxEnvironment : IEnvironment
{
    private const int HugepageLog = 30; // 1 GB hugepages
    private const int HugepageSize = 1 << HugepageLog;

    private static unsafe partial class OSInterop
    {
        public const int _SC_PAGESIZE = 30;

        public const int PROT_READ = 0x1;
        public const int PROT_WRITE = 0x2;

        public const int MAP_SHARED = 0x01;
        public const int MAP_ANONYMOUS = 0x20;
        public const int MAP_POPULATE = 0x8000;
        public const int MAP_HUGETLB = 0x40000;
        public const int MAP_HUGE_SHIFT = 26;
        public static readonly void* MAP_FAILED = (void*)-1;

        public const int O_RDONLY = 0;
        public const int O_RDWR = 0x2;
        public const int O_SYNC = 0x101000;

        public const int SEEK_SET = 0;

        [StructLayout(LayoutKind.Sequential)]
        public struct TimeSpec
        {
            public long Seconds;
            public long Nanoseconds;
        }

        [LibraryImport("libc")]
        public static partial long sysconf(int name);

        [LibraryImport("libc")]
        public static partial void* mmap(nuint addr, nuint length, int prot, int flags, int fd, nint offset);

        [LibraryImport("libc", StringMarshalling = StringMarshalling.Utf8)]
        public static partial int open(string pathName, int flags);

        [LibraryImport("libc")]
        public static partial nint lseek(int fd, nint offset, int whence);

        [LibraryImport("libc")]
        public static partial nint read(int fd, void* buf, nuint count);

        [LibraryImport("libc")]
        public static partial int close(int fd);

        [LibraryImport("libc")]
        public static partial int nanosleep(in TimeSpec req, out TimeSpec rem);
    }

    private static partial class PortInterop
    {
        public const ushort PCI_CONFIG_ADDR = 0xCF8;
        public const ushort PCI_CONFIG_DATA = 0xCFC;

        [LibraryImport("cwrapper")]
        public static partial uint port_out_32(ushort port, uint value);

        [LibraryImport("cwrapper")]
        public static partial uint port_in_32(ushort port);
    }

    private Memory<byte> _allocatedPage;
    private long _usedBytes;

    public unsafe LinuxEnvironment()
    {
        void* page = OSInterop.mmap(
            0,
            HugepageSize,
            OSInterop.PROT_READ | OSInterop.PROT_WRITE,
            OSInterop.MAP_HUGETLB | (HugepageLog << OSInterop.MAP_HUGE_SHIFT) | OSInterop.MAP_ANONYMOUS | OSInterop.MAP_SHARED | OSInterop.MAP_POPULATE,
            -1,
            0
        );
        if (page == OSInterop.MAP_FAILED)
        {
            throw new Exception("mmap failed");
        }
        _allocatedPage = new UnmanagedMemoryManager<byte>((byte*)page, HugepageSize).Memory;
        _usedBytes = 0;
    }

    public unsafe Memory<T> Allocate<T>(int count)
        where T : unmanaged
    {
        long alignDiff = _usedBytes % (sizeof(T) + 64 - (sizeof(T) % 64));
        _allocatedPage = _allocatedPage[(int)alignDiff..];
        _usedBytes += alignDiff;

        int fullSize = count * sizeof(T);
        var result = _allocatedPage[0..fullSize];
        _allocatedPage = _allocatedPage[fullSize..];
        _usedBytes += fullSize;

        return new CastMemoryManager<byte, T>(result).Memory;
    }

    public unsafe Memory<T> MapPhysicalMemory<T>(ulong addr, int count)
        where T : unmanaged
    {
        int memFd = OSInterop.open("/dev/mem", OSInterop.O_SYNC | OSInterop.O_RDWR);
        if (memFd == -1)
        {
            throw new Exception("Could not open /dev/mem");
        }

        void* mapped = OSInterop.mmap(
            0,
            (uint)(count * sizeof(T)),
            OSInterop.PROT_READ | OSInterop.PROT_WRITE,
            OSInterop.MAP_SHARED,
            memFd,
            (nint)addr
        );
        if (mapped == OSInterop.MAP_FAILED)
        {
            throw new Exception("Phys-to-virt mmap failed");
        }

        return new UnmanagedMemoryManager<T>((T*)mapped, count).Memory;
    }

    public unsafe nuint GetPhysicalAddress<T>(ref T value)
    {
        long pageSize = OSInterop.sysconf(OSInterop._SC_PAGESIZE);
        if (pageSize <= 0)
        {
            throw new Exception("Could not get the page size");
        }
        nint addr = (nint)Unsafe.AsPointer(ref value);
        nint page = addr / (nint)pageSize;
        nint mapOffset = page * sizeof(ulong);
        // Cannot check for off_t roundtrip here since we don't know what it is

        int mapFd = OSInterop.open("/proc/self/pagemap", OSInterop.O_RDONLY);
        if (mapFd < 0)
        {
            throw new Exception("Could not open the pagemap");
        }

        if (OSInterop.lseek(mapFd, mapOffset, OSInterop.SEEK_SET) == -1)
        {
            throw new Exception("Could not seek the pagemap");
        }

        Span<byte> readBytes = stackalloc byte[sizeof(ulong)];
        fixed (byte* bs = readBytes)
        {
            var readResult = OSInterop.read(mapFd, bs, sizeof(ulong));
            if (OSInterop.close(mapFd) != 0)
            {
                throw new Exception("Close failed, all hope is lost");
            }
            if (readResult != readBytes.Length)
            {
                throw new Exception("Could not read enough bytes from the pagemap");
            }
        }

        ulong metadata = MemoryMarshal.Cast<byte, ulong>(readBytes)[0];
        if ((metadata & 0x8000000000000000ul) == 0)
        {
            throw new Exception("Page not present");
        }
        ulong pfn = metadata & 0x7FFFFFFFFFFFFFul;
        if (pfn == 0)
        {
            throw new Exception("Page not mapped");
        }

        nint addrOffset = addr % (nint)pageSize;
        return (nuint)pfn * (nuint)pageSize + (nuint)addrOffset;
    }

    private static void PciTarget(PciAddress address, byte reg)
    {
        uint regAddr = 0x80000000u | ((uint)address.Bus << 16) | ((uint)address.Device << 11) | ((uint)address.Function << 8) | reg;
        if (PortInterop.port_out_32(PortInterop.PCI_CONFIG_ADDR, regAddr) == 0)
        {
            throw new Exception("Could not target the PCI addr");
        }
    }

    public uint PciRead(PciAddress address, byte register)
    {
        PciTarget(address, register);
        return PortInterop.port_in_32(PortInterop.PCI_CONFIG_DATA);
    }

    public void PciWrite(PciAddress address, byte register, uint value)
    {
        PciTarget(address, register);
        if (PortInterop.port_out_32(PortInterop.PCI_CONFIG_DATA, value) == 0)
        {
            throw new Exception("Could not write to PCI");
        }
    }

    public void Sleep(TimeSpan duration)
    {
        var nanos = duration.Ticks * 100;
        var request = new OSInterop.TimeSpec { Seconds = (long)(nanos / 1_000_000_000), Nanoseconds = nanos % 1_000_000_000 };
        for (int n = 0; n < 1000; n++)
        {
            int ret = OSInterop.nanosleep(request, out var remain);
            if (ret == 0)
            {
                return;
            }

            request = remain;
        }
        throw new Exception("Could not sleep");
    }

    // From Marc Gravell, see https://stackoverflow.com/a/52191681
    private sealed unsafe class UnmanagedMemoryManager<T> : MemoryManager<T>
        where T : unmanaged
    {
        private readonly T* _pointer;
        private readonly int _length;

        public UnmanagedMemoryManager(T* pointer, int length)
        {
            if (length < 0)
            {
                throw new ArgumentException("Length cannot be negative");
            }
            _pointer = pointer;
            _length = length;
        }

        public override Span<T> GetSpan() => new(_pointer, _length);

        public override MemoryHandle Pin(int elementIndex = 0)
        {
            throw new NotSupportedException();
        }

        public override void Unpin() { }

        protected override void Dispose(bool disposing) { }
    }

    // From Marc Gravell, see  https://stackoverflow.com/a/54512940
    private sealed class CastMemoryManager<TFrom, TTo> : MemoryManager<TTo>
        where TFrom : struct
        where TTo : struct
    {
        private readonly Memory<TFrom> _from;

        public CastMemoryManager(Memory<TFrom> from) => _from = from;

        public override Span<TTo> GetSpan() => MemoryMarshal.Cast<TFrom, TTo>(_from.Span);

        public override MemoryHandle Pin(int elementIndex = 0)
        {
            throw new NotSupportedException();
        }

        public override void Unpin() { }

        protected override void Dispose(bool disposing) { }
    }
}
