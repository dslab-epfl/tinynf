using System;
using TinyNF.Linux;
using TinyNF.Network;

namespace TinyNF
{
    public sealed class Program
    {
        public static void Main(string[] args)
        {
            if (args.Length != 2)
            {
                throw new Exception("Expected exactly 2 args");
            }

            var env = new LinuxEnvironment();

            var dev0 = new IxgbeDevice(env, ParsePciAddress(args[0]));
            dev0.SetPromiscuous();

            var dev1 = new IxgbeDevice(env, ParsePciAddress(args[1]));
            dev1.SetPromiscuous();

            Console.WriteLine("Initialized devices");

            var agent0 = new IxgbeAgent(env, dev0, dev1);
            var agent1 = new IxgbeAgent(env, dev1, dev0);

            Console.WriteLine("Initialized agents. Running...");

            new Program().Run(agent0, agent1);
        }

        private static uint Processor(ref PacketData data, uint len)
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
            return len;
        }

        // Run must be an instance method so that _processor is known to be initialized without having to call the cctor
        private readonly PacketProcessor _processor = Processor;
        private void Run(IxgbeAgent agent0, IxgbeAgent agent1)
        {
            while (true)
            {
                agent0.Run(_processor);
                agent1.Run(_processor);
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

    }
}
