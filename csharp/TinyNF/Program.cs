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
            public void Process(ref PacketData data, ushort len, Array256<ushort> outputs)
            {
                HandleData(ref data);
                outputs[0] = len;
            }
        }

        private struct SafeProcessor : ISafePacketProcessor
        {
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public void Process(ref PacketData data, ushort len, Span<ushort> outputs)
            {
                HandleData(ref data);
                outputs[0] = len;
            }
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void Run(Agent agent0, Agent agent1)
        {
            var proc = new Processor();
            while (true)
            {
                agent0.Run(proc);
                agent1.Run(proc);
            }
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void SafeRun(SafeAgent agent0, SafeAgent agent1)
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
                Console.WriteLine("Safe C# mode starting...");
                var agent0 = new SafeAgent(env, dev0, new[] { dev1 });
                var agent1 = new SafeAgent(env, dev1, new[] { dev0 });
                SafeRun(agent0, agent1);
            }
            else
            {
                Console.WriteLine("'Extended' C# mode starting...");
                var agent0 = new Agent(env, dev0, new[] { dev1 });
                var agent1 = new Agent(env, dev1, new[] { dev0 });
                Run(agent0, agent1);
            }
        }
    }
}
