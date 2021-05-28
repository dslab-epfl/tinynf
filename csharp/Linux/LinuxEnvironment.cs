﻿using System;
using System.IO;
using System.IO.MemoryMappedFiles;
using System.Runtime.InteropServices;
using System.Threading;

namespace TinyNF.Linux
{
    /// <summary>
    /// Fundamentally unsafe since it interacts with Linux.
    /// </summary>
    public sealed class LinuxEnvironment : IEnvironment
    {
        private const int HugepageSize = 2 * 1024 * 1024; // 2 MB hugepages (could also do 1 GB)

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

        public unsafe Span<T> Allocate<T>(nuint size)
        {
            if (size * (nuint)Marshal.SizeOf<T>() > HugepageSize)
            {
                throw new Exception("Cannot allocate that much");
            }

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

            return new Span<T>(page, (int)size);
        }

        // See https://www.kernel.org/doc/Documentation/vm/pagemap.txt
        public unsafe nuint GetPhysicalAddress<T>(ref T value)
        {
            nuint pageSize = (nuint)Environment.SystemPageSize;
            nuint addr = (nuint)System.Runtime.CompilerServices.Unsafe.AsPointer(ref value);
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

        public unsafe Span<T> MapPhysicalMemory<T>(nuint addr, nuint size)
        {
            byte* ptr = null;
            // we'll never call ReleasePointer, but that's ok, the memory will be released when we exit
            MemoryMappedFile.CreateFromFile("/dev/mem", FileMode.Open, null, GC.GetGCMemoryInfo().TotalAvailableMemoryBytes)
                            .CreateViewAccessor((long)addr, (long)size * Marshal.SizeOf<T>())
                            .SafeMemoryMappedViewHandle.AcquirePointer(ref ptr);
            return new Span<T>(ptr, (int)size);
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
    }
}