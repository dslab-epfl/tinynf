﻿using System;
using TinyNF.Environment;
using TinyNF.Ixgbe;
using TinyNF.Unsafe;

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

            var dev0 = new Device(env, ParsePciAddress(args[0]));
            dev0.SetPromiscuous();

            var dev1 = new Device(env, ParsePciAddress(args[1]));
            dev1.SetPromiscuous();

            Console.WriteLine("Initialized devices");

            var agent0 = new Agent(env, dev0, new[] { dev1 });
            var agent1 = new Agent(env, dev1, new[] { dev0 });

            Console.WriteLine("Initialized agents. Running...");

            Run(agent0, agent1);
        }

        private static uint Processor(ref PacketData data, uint len, Array256<bool> outputs)
        {
            /*data[0] = 0;
            data[1] = 0;
            data[2] = 0;
            data[3] = 0;
            data[4] = 0;
            data[5] = 1;
            data[6] = 0;
            data[7] = 0;*/
            data.Write64(0, 0x00_00_01_00_00_00_00_00u);
            /*data[8] = 0;
            data[9] = 0;
            data[10] = 0;
            data[11] = 0;*/
            data.Write32(8, 0);
            outputs[0] = true;
            return len;
        }
        // Separated into its own method just to make it easy to disassemble separately to observe optimizations
        private static void Run(Agent agent0, Agent agent1)
        {
            // The compiler and runtime could do better here, there's no reason not to do this pre-init outside the loop automatically...
            PacketProcessor proc = Processor;
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
    }
}
