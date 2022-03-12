using System;
using System.Runtime.CompilerServices;
using TinyNF.Environment;
using TinyNF.Ixgbe;
using TinyNF.Unsafe;

// TODO clean up namespaces with new C# 10 syntax
namespace TinyNF
{
    public sealed class Program
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void HandleData(ref PacketData data)
        {
            data[0] = 0;
            data[1] = 0;
            data[2] = 0;
            data[3] = 0;
            data[4] = 0;
            data[5] = 1;
            data[6] = 0;
            data[7] = 0;
            data[8] = 0;
            data[9] = 0;
            data[10] = 0;
            data[11] = 0;
        }

        private struct Processor : IPacketProcessor
        {
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public void Process(ref PacketData data, ulong len, Array256<ulong> outputs)
            {
                HandleData(ref data);
                outputs[0] = len;
            }
        }

        private struct SafeProcessor : ISafePacketProcessor
        {
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public void Process(ref PacketData data, ulong len, Span<ulong> outputs)
            {
                HandleData(ref data);
                outputs[0] = len;
            }
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void Run(ref Agent agent0, ref Agent agent1)
        {
            var proc = new Processor();
            while (true)
            {
                agent0.Run(proc);
                agent1.Run(proc);
            }
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void RunQueues(ref QueueRx rx0, ref QueueRx rx1, ref QueueTx tx0, ref QueueTx tx1)
        {
            const int BatchSize = 32;

            var buffers = new RefArray256<Ixgbe.Buffer>(_ => ref Ixgbe.Buffer.Fake);
            byte nbRx, nbTx;
            while (true)
            {
                nbRx = rx0.Batch(buffers, BatchSize);
                for (byte n = 0; n < nbRx; n++)
                {
                    HandleData(ref buffers.Get(n).Data.Get());
                }
                nbTx = tx1.Batch(buffers, nbRx);
                for (byte n = nbTx; n < nbRx; n++)
                {
                    tx1.Pool.Get().Give(ref buffers.Get(n));
                }

                nbRx = rx1.Batch(buffers, BatchSize);
                for (byte n = 0; n < nbRx; n++)
                {
                    HandleData(ref buffers.Get(n).Data.Get());
                }
                nbTx = tx0.Batch(buffers, nbRx);
                for (byte n = nbTx; n < nbRx; n++)
                {
                    tx0.Pool.Get().Give(ref buffers.Get(n));
                }
            }
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void RunSafe(ref SafeAgent agent0, ref SafeAgent agent1)
        {
            var proc = new SafeProcessor();
            while (true)
            {
                agent0.Run(proc);
                agent1.Run(proc);
            }
        }

        private static PciAddress ParsePciAddress(string str)
        {
            var parts = str.Split(':', '.'); // technically too lax but that's fine
            if (parts.Length != 3)
            {
                throw new Exception("Bad PCI address");
            }
            return new PciAddress(Convert.ToByte(parts[0], 16), Convert.ToByte(parts[1], 16), Convert.ToByte(parts[2], 16));
        }

        public static void Main(string[] args)
        {
            if (args.Length != 3 || (args[2] != "safe" && args[2] != "extended"))
            {
                throw new Exception("Expected exactly 3 args: <pci dev> <pci dev> <safe/extended>");
            }

            var env = new LinuxEnvironment();

            var dev0 = new Device(env, ParsePciAddress(args[0]));
            dev0.SetPromiscuous();

            var dev1 = new Device(env, ParsePciAddress(args[1]));
            dev1.SetPromiscuous();

            Console.WriteLine("Initialized. Running...");

            if (args[2] == "safe")
            {
                var agent0 = new SafeAgent(env, dev0, new[] { dev1 });
                var agent1 = new SafeAgent(env, dev1, new[] { dev0 });
                Console.WriteLine("Safe C# mode starting...");
                RunSafe(ref agent0, ref agent1);
            }
            else if (args[2] == "queues")
            {
                const int PoolSize = 65536;

                var pool0 = new BufferPool(env, PoolSize);
                var pool1 = new BufferPool(env, PoolSize);
                var rx0 = new QueueRx(env, dev0, ref pool0);
                var rx1 = new QueueRx(env, dev1, ref pool1);
                var tx0 = new QueueTx(env, dev0, ref pool1);
                var tx1 = new QueueTx(env, dev1, ref pool0);
                Console.WriteLine("Queues C# mode starting...");
                RunQueues(ref rx0, ref rx1, ref tx0, ref tx1);
            }
            else
            {
                var agent0 = new Agent(env, dev0, new[] { dev1 });
                var agent1 = new Agent(env, dev1, new[] { dev0 });
                Console.WriteLine("'Extended' C# mode starting...");
                Run(ref agent0, ref agent1);
            }
        }
    }
}
