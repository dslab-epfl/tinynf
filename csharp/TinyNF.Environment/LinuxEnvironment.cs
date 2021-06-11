using System;
using System.Buffers;
using System.IO;
using System.IO.MemoryMappedFiles;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;

namespace TinyNF.Environment
{
    /// <summary>
    /// Fundamentally unsafe since it interacts with Linux.
    /// </summary>
    public sealed class LinuxEnvironment : IEnvironment
    {
        private const int HugepageSize = 1024 * 1024 * 1024; // 1 GB hugepages

        // Necessary because .NET has no explicit support for hugepages and MemoryMappedFile doesn't allow us to pass the hugepage flag
        private static unsafe class OSInterop
        {
            public const int PROT_READ = 0x1;
            public const int PROT_WRITE = 0x2;

            public const int MAP_SHARED = 0x01;
            public const int MAP_ANONYMOUS = 0x20;
            public const int MAP_POPULATE = 0x8000;
            public const int MAP_HUGETLB = 0x40000;
            public const int MAP_HUGE_SHIFT = 26;
            public static readonly void* MAP_FAILED = (void*)-1;

            [DllImport("libc")]
            public static extern void* mmap(nuint addr, nuint length, int prot, int flags, int fd, nint offset);
        }

        // Necessary because .NET has no port I/O intrinsics
        private static unsafe class PortInterop
        {
            public const uint PCI_CONFIG_ADDR = 0xCF8;
            public const uint PCI_CONFIG_DATA = 0xCFC;

            [DllImport("cwrapper")]
            public static extern bool port_out_32(uint port, uint value);

            [DllImport("cwrapper")]
            public static extern uint port_in_32(uint port);
        }

        private Memory<byte>? _allocatedPage;
        private ulong _usedBytes;

        public unsafe Memory<T> Allocate<T>(uint size)
            where T : unmanaged
        {
            if (_allocatedPage == null)
            {
                void* page = OSInterop.mmap(
                    // No specific address
                    0,
                    // Size of the mapping
                    HugepageSize,
                    // R/W page
                    OSInterop.PROT_READ | OSInterop.PROT_WRITE,
                    // Hugepage, not backed by a file (and thus zero-initialized); note that without MAP_SHARED the call fails
                    // MAP_POPULATE means the page table will be populated already (without the need for a page fault later),
                    // which is required if the calling code tries to get the physical address of the page without accessing it first.
                    OSInterop.MAP_HUGETLB | ((int)Math.Log2(HugepageSize) << OSInterop.MAP_HUGE_SHIFT) | OSInterop.MAP_ANONYMOUS | OSInterop.MAP_SHARED | OSInterop.MAP_POPULATE,
                    // Required on MAP_ANONYMOUS
                    -1,
                    // Required on MAP_ANONYMOUS
                    0
                );
                if (page == OSInterop.MAP_FAILED)
                {
                    throw new Exception("mmap failed");
                }

                _allocatedPage = new UnmanagedMemoryManager<byte>((byte*)page, HugepageSize).Memory;
                _usedBytes = 0;
            }

            var fullSize = size * (uint) Marshal.SizeOf<T>();

            // Return and align to at least one full cache line
            if (fullSize < 64) {
                fullSize = 64;
            }

            // Align as required by the contract
            var alignDiff = _usedBytes % fullSize;
            _allocatedPage = _allocatedPage.Value[(int) alignDiff..];
            _usedBytes += alignDiff;

            var result = _allocatedPage.Value.Slice(0, (int)fullSize);
            _allocatedPage = _allocatedPage.Value[(int)fullSize..];
            _usedBytes += fullSize;

            return new CastMemoryManager<byte, T>(result).Memory;
        }

        // See https://www.kernel.org/doc/Documentation/vm/pagemap.txt
        public unsafe nuint GetPhysicalAddress<T>(ref T value)
        {
            nuint pageSize = (nuint)System.Environment.SystemPageSize;
            nuint addr = (nuint)Unsafe.AsPointer(ref value);
            nuint page = addr / pageSize;
            nuint mapOffset = page * sizeof(ulong);
            // Cannot check for off_t roundtrip here since we don't know what it is

            using var pagemap = File.OpenRead("/proc/self/pagemap");
            pagemap.Seek((long)mapOffset, SeekOrigin.Current);

            Span<byte> readBytes = stackalloc byte[sizeof(ulong)];
            if (pagemap.Read(readBytes) != readBytes.Length)
            {
                throw new Exception("Could not read enough bytes from the pagemap");
            }

            ulong metadata = MemoryMarshal.Cast<byte, ulong>(readBytes)[0];
            // We want the PFN, but it's only meaningful if the page is present; bit 63 indicates whether it is
            if ((metadata & 0x8000000000000000ul) == 0)
            {
                throw new Exception("Page not present");
            }
            // PFN = bits 0-54
            ulong pfn = metadata & 0x7FFFFFFFFFFFFFul;
            if (pfn == 0)
            {
                throw new Exception("Page not mapped");
            }

            nuint addrOffset = addr % pageSize;
            return (nuint)(pfn * pageSize + addrOffset);
        }

        public unsafe Memory<T> MapPhysicalMemory<T>(nuint addr, uint size)
            where T : unmanaged
        {
            if (size > int.MaxValue)
            {
                throw new ArgumentOutOfRangeException(nameof(size), "Cannot map this much memory");
            }

            byte* ptr = null;
            // we'll never call ReleasePointer, but that's ok, the memory will be released when we exit
            MemoryMappedFile.CreateFromFile("/dev/mem", FileMode.Open, null, GC.GetGCMemoryInfo().TotalAvailableMemoryBytes)
                            .CreateViewAccessor((long)addr, size * Marshal.SizeOf<T>())
                            .SafeMemoryMappedViewHandle.AcquirePointer(ref ptr);
            return new UnmanagedMemoryManager<T>((T*)ptr, (int)size).Memory;
        }

        private static void PciTarget(PciAddress address, byte reg)
        {
            uint regAddr = 0x80000000u | ((uint)address.Bus << 16) | ((uint)address.Device << 11) | ((uint)address.Function << 8) | reg;
            if (!PortInterop.port_out_32(PortInterop.PCI_CONFIG_ADDR, regAddr))
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
            if (!PortInterop.port_out_32(PortInterop.PCI_CONFIG_DATA, value))
            {
                throw new Exception("Could not write to PCI");
            }
        }

        public void Sleep(TimeSpan span)
        {
            // Very imprecise but that's fine, we'll just sleep too much
            Thread.Sleep(span);
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
                    throw new ArgumentOutOfRangeException(nameof(length));
                }
                _pointer = pointer;
                _length = length;
            }

            public override Span<T> GetSpan() => new(_pointer, _length);

            public override MemoryHandle Pin(int elementIndex = 0)
            {
                if (elementIndex < 0 || elementIndex >= _length)
                {
                    throw new ArgumentOutOfRangeException(nameof(elementIndex));
                }
                return new MemoryHandle(_pointer + elementIndex);
            }

            public override void Unpin() { }

            protected override void Dispose(bool disposing) { }
        }

        // From Marc Gravell, see  https://stackoverflow.com/a/54512940
        private sealed class CastMemoryManager<TFrom, TTo> : MemoryManager<TTo>
            where TFrom : unmanaged
            where TTo : unmanaged
        {
            private readonly Memory<TFrom> _from;

            public CastMemoryManager(Memory<TFrom> from) => _from = from;

            public override Span<TTo> GetSpan() => MemoryMarshal.Cast<TFrom, TTo>(_from.Span);

            protected override void Dispose(bool disposing) { }
            public override MemoryHandle Pin(int elementIndex = 0) => throw new NotSupportedException();
            public override void Unpin() => throw new NotSupportedException();
        }
    }
}
