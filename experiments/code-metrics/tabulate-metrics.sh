#!/bin/sh

if ! which cloc >/dev/null ; then
  echo 'cloc not found, please install it'
  exit 1
fi

old_dir="$(pwd)"
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
# Prints assembly instructions
print_asm()
{
  # this is the easy way but sometimes it aborts on the Ada binary with no other message than 'Aborted' so...
  # skip 1st and last line, which state beginning/end of dump
  #gdb -batch -ex 'set disassembly-flavor intel' -ex "disassemble $1" "$2" | tail -n+2 | head -n-1 | wc -l

  # let's do it the hard way: https://stackoverflow.com/a/31138400
  # set insn-width otherwise we get newlines for no good reason (seems to default to just 1 less than some 'mov' instructions)
  # (and skip the 1st line which is the function name)
  objdump --insn-width=30 -d "$2" | awk -v RS= '/^[[:xdigit:]]+ <'"$1"'>/' | tail -n+2
}

asm_dir="$old_dir/assembly"
rm -rf "$asm_dir"
mkdir "$asm_dir"
# Ã$1: function name
# Ã$2: file name
# $3: report name
# Prints the asm to $3 and returns the number of lines
asm_lines()
{
  print_asm "$1" "$2" > "$asm_dir/$3"
  cat "$asm_dir/$3" | wc -l
}

# C
TN_CC=clang make -C c >/dev/null || exit $?
asm_c="$(asm_lines 'run' 'c/tinynf' 'c-clang')"
TN_MODE=flexible TN_CC=clang make -C c >/dev/null || exit $?
asm_c_queues="$(asm_lines 'run' 'c/tinynf' 'c-flexible-clang')"

# Rust is harder due to name mangling, we find the symbol first
make -C rust >/dev/null 2>&1 || exit $?
run_symbol="$(nm rust/target/release/tinynf | grep run | grep tinynf | cut -d ' ' -f 3)"
asm_rust="$(asm_lines "$run_symbol" 'rust/target/release/tinynf' 'rust')"

TN_MODE=flexible make -C rust >/dev/null 2>&1 || exit $?
run_queues_symbol="$(nm rust/target/release/tinynf | grep run | grep queues | grep tinynf | cut -d ' ' -f 3)"
asm_rust_queues="$(asm_lines "$run_queues_symbol" 'rust/target/release/tinynf' 'rust-flexible')"

# CSharp always has both compiled so we only compile once
# There's also like 3 asm lines for the lambda initializing the default value of the buffer references for queues; it does not matter at this scale
TN_CSHARP_AOT=y make -C csharp >/dev/null 2>&1 || exit $?
asm_csharp="$(asm_lines 'TinyNF_TinyNF_Program__Run' csharp/out/TinyNF 'csharp')"
asm_csharp_queues="$(asm_lines 'TinyNF_TinyNF_Program__RunQueues' csharp/out/TinyNF 'csharp-flexible')"

# Ada also has both; the first name is very brittle though
make -C ada >/dev/null 2>&1 || exit $?
asm_ada="$(asm_lines 'main__B_1__B_2__myrun.7' 'ada/tinynf' 'ada')"
asm_ada_queues="$(asm_lines 'run__run_queues' 'ada/tinynf' 'ada-flexible')"

printf '\t\tasm\n'
printf 'Lang\tLoC\trestr.\tflex.\n'

printf 'C\t%s\t%s\t%s\n' "$loc_c" "$asm_c" "$asm_c_queues"
printf 'Rust\t%s\t%s\t%s\t + extensions: %s LoC\n' "$loc_rust" "$asm_rust" "$asm_rust_queues" "$loc_rust_ext"
printf 'C#\t%s\t%s\t%s\t + extensions: %s LoC ; + C wrapper for port-mapped IO: %s LoC\n' "$loc_csharp" "$asm_csharp" "$asm_csharp_queues" "$loc_csharp_ext" "$loc_cwrapper"
printf 'Ada\t%s\t%s\t%s\n' "$loc_ada" "$asm_ada" "$asm_ada_queues"

printf '\n'
printf 'Disassemblies are in %s\n' "$asm_dir"
