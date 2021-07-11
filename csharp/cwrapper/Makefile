# Generate files for both static (AOT) and dynamic (JIT) linking from .NET
default:
	@$(CC) cwrapper.c -shared -O3 -o cwrapper.so
	@$(CC) cwrapper.c -c -O3 -o cwrapper.o
	@ar rcs cwrapper.a cwrapper.o
