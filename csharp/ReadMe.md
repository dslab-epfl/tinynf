to disassemble a specific function when using AOT, use e.g.
`gdb TinyNF/bin/Release/net6.0/linux-x64/publish/TinyNF -batch -ex 'set disassembly-flavor intel' -ex 'disassemble TinyNF_TinyNF_Program__Run'`
