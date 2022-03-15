#!/bin/sh

if ! which cloc >/dev/null ; then
  echo 'cloc not found, please install it'
  exit 1
fi

cd '../..'

# $1: the cloc arguments
# Prints the count of lines of code
loc_count()
{
  cloc $1 --quiet | tail -n 2 | head -n 1 | awk '{print $5}'
}

loc_c="$(loc_count '--force-lang=C,h --include-lang=C c')"

loc_rust="$(loc_count '--not-match-f=agent_const.rs --not-match-f=lifed.rs rust/src')"
loc_rust_ext="$(loc_count '--match-f=lifed.rs rust/src')"

loc_cwrapper="$(loc_count '--exclude-lang=make csharp/cwrapper')"
loc_csharp="$(loc_count '--include-lang=C# --not-match-f=SafeAgent.cs csharp/TinyNF csharp/TinyNF.Environment')"
loc_csharp_ext="$(loc_count '--include-lang=C# csharp/TinyNF.Unsafe')"

loc_ada="$(loc_count '--include-lang=Ada --not-match-f=ixgbe_agent_const ada')"


# $1: function name
# $2: file name
# Prints the count of assembly instructions
asm_count()
{
  gdb -batch -ex 'set disassembly-flavor intel' -ex "disassemble $1" "$2" | tail -n+2 | head -n-1 | wc -l
}

# C
if ! TN_MODE=0 make -f Makefile.benchmarking -C c >/dev/null ; then exit $? ; fi
asm_c="$(asm_count 'run' 'c/tinynf')"
if ! TN_MODE=2 make -f Makefile.benchmarking -C c >/dev/null ; then exit $? ; fi
asm_c_queues="$(asm_count 'run' 'c/tinynf')"

# Rust is harder due to name mangling, we find the symbol first
if ! TN_MODE=0 make -f Makefile.benchmarking -C rust >/dev/null 2>&1 ; then exit $? ; fi
run_symbol="$(nm rust/target/release/tinynf | grep run | grep tinynf | cut -d ' ' -f 3)"
asm_rust="$(asm_count "$run_symbol" 'rust/target/release/tinynf')"

if ! TN_MODE=2 make -f Makefile.benchmarking -C rust >/dev/null 2>&1 ; then exit $? ; fi
run_queues_symbol="$(nm rust/target/release/tinynf | grep run | grep queues | grep tinynf | cut -d ' ' -f 3)"
asm_rust_queues="$(asm_count "$run_queues_symbol" 'rust/target/release/tinynf')"


printf 'C\t%s\t%s\t%s\n' "$loc_c" "$asm_c" "$asm_c_queues"
printf 'Rust\t%s\t%s\t%s\n' "$loc_rust" "$asm_rust" "$asm_rust_queues"
printf 'C#\t%s\n' "$loc_csharp"
printf 'Ada\t%s\n' "$loc_ada"

printf '\n'
printf 'Rust extensions: %s lines of code\n' "$loc_rust_ext"
printf 'C# extensions: %s lines of code\n' "$loc_csharp_ext"

printf '\n'
printf 'C# also includes %s lines of code for port-mapped I/O\n' "$loc_cwrapper"
