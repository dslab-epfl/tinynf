APP := tinynf

# Use -g for debug symbols, or -gnatD for detailed debugging stuff... not sure it's actually better, though

# Basic optimization stuff, same as C version
TN_CFLAGS += -O3 -march=native -flto
# Turn on overflow checks, required by the Ada spec, but GNAT doesn't do it by default (?!)
TN_CFLAGS += -gnato
# -gnatn turns on some inlining
TN_CFLAGS += -gnatn
# remove unused stuff
TN_CFLAGS += -cargs -ffunction-sections -fdata-sections -largs -Wl,--gc-sections

# Always clean, just in case
build:
	@gnatclean main
	@gnatmake -o $(APP) main $(TN_CFLAGS)

# -nM is "names mixed case" and -M is max line length
format:
	@echo 'Not formatting Ada since gnatpp does not work: https://bugs.launchpad.net/ubuntu/+source/asis/+bug/1787708'
	@#gnatpp -nM -M160 --decimal-grouping=3 --eol=unix *.ad*
