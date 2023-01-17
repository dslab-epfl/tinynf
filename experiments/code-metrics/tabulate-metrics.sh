#!/bin/sh

if ! which cloc >/dev/null ; then
  echo 'cloc not found, please install it'
  exit 1
fi

cd '../..'

printf 'This should take less than a minute...\n\n'

# $1: the cloc arguments
# Prints the count of lines of code
loc_count()
{
  cloc --exclude-lang=make,Markdown,JSON,'MSBuild script' --quiet $1 | tail -n 2 | head -n 1 | awk '{print $5}'
}

loc_c="$(loc_count 'c')"

loc_rust="$(loc_count '--not-match-f=agent_const.rs --not-match-f=lifed.rs rust/src')"
loc_rust_ext="$(loc_count '--match-f=lifed.rs rust/src')"

loc_cwrapper="$(loc_count 'csharp/cwrapper')"
loc_csharp="$(loc_count '--not-match-f=SafeAgent.cs csharp/TinyNF csharp/TinyNF.Environment')"
loc_csharp_ext="$(loc_count 'csharp/TinyNF.Unsafe')"

loc_ada="$(loc_count '--not-match-f=ixgbe_agent_const ada')"


# $1: function name
# $2: file name
# Prints the count of assembly instructions
asm_count()
{
  # this is the easy way but sometimes it aborts on the Ada binary with no other message than 'Aborted' so...
  # skip 1st and last line, which state beginning/end of dump
  #gdb -batch -ex 'set disassembly-flavor intel' -ex "disassemble $1" "$2" | tail -n+2 | head -n-1 | wc -l

  # let's do it the hard way: https://stackoverflow.com/a/31138400
  # set insn-width otherwise we get newlines for no good reason (seems to default to just 1 less than some 'mov' instructions)
  # (and skip the 1st line which is the function name)
  objdump --insn-width=30 -d "$2" | awk -v RS= '/^[[:xdigit:]]+ <'"$1"'>/' | tail -n+2 | wc -l
}

# C
if ! TN_MODE=0 TN_CC=clang make -f Makefile.benchmarking -C c >/dev/null ; then exit $? ; fi
asm_c="$(asm_count 'run' 'c/tinynf')"
if ! TN_MODE=2 TN_CC=clang make -f Makefile.benchmarking -C c >/dev/null ; then exit $? ; fi
asm_c_queues="$(asm_count 'run' 'c/tinynf')"

# Rust is harder due to name mangling, we find the symbol first
if ! TN_MODE=0 make -f Makefile.benchmarking -C rust >/dev/null 2>&1 ; then exit $? ; fi
run_symbol="$(nm rust/target/release/tinynf | grep run | grep tinynf | cut -d ' ' -f 3)"
asm_rust="$(asm_count "$run_symbol" 'rust/target/release/tinynf')"

if ! TN_MODE=2 make -f Makefile.benchmarking -C rust >/dev/null 2>&1 ; then exit $? ; fi
run_queues_symbol="$(nm rust/target/release/tinynf | grep run | grep queues | grep tinynf | cut -d ' ' -f 3)"
asm_rust_queues="$(asm_count "$run_queues_symbol" 'rust/target/release/tinynf')"

# CSharp always has both compiled so we only compile once
# There's also like 3 asm lines for the lambda initializing the default value of the buffer references for queues; it does not matter at this scale
if ! TN_CSHARP_AOT=y make -f Makefile.benchmarking -C csharp >/dev/null 2>&1 ; then exit $? ; fi
asm_csharp="$(asm_count 'TinyNF_TinyNF_Program__Run' csharp/out/TinyNF)"
asm_csharp_queues="$(asm_count 'TinyNF_TinyNF_Program__RunQueues' csharp/out/TinyNF)"

# Ada also has both
if ! make -f Makefile.benchmarking -C ada >/dev/null 2>&1 ; then exit $? ; fi
asm_ada="$(asm_count 'nf__run' 'ada/tinynf')"
asm_ada_queues="$(asm_count 'nf_queues__run' 'ada/tinynf')"

printf '\t\tasm\n'
printf 'Lang\tLoC\trestr.\tflex.\n'

printf 'C\t%s\t%s\t%s\n' "$loc_c" "$asm_c" "$asm_c_queues"
printf 'Rust\t%s\t%s\t%s\n' "$loc_rust" "$asm_rust" "$asm_rust_queues"
printf 'C#\t%s\t%s\t%s\n' "$loc_csharp" "$asm_csharp" "$asm_csharp_queues"
printf 'Ada\t%s\t%s\t%s\n' "$loc_ada" "$asm_ada" "$asm_ada_queues"

printf '\n'
printf 'Rust extensions: %s lines of code\n' "$loc_rust_ext"
printf 'C# extensions: %s lines of code\n' "$loc_csharp_ext"

printf '\n'
printf 'C# also includes %s lines of code for port-mapped I/O\n' "$loc_cwrapper"
