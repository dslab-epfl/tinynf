build:
	@dotnet build
	@make -C cwrapper --no-print-directory

# re-export DOTNET_ROOT in case it's not the default value
run: build
	@sudo DOTNET_ROOT=$(DOTNET_ROOT) LD_LIBRARY_PATH=$$(pwd)/cwrapper ./bin/Debug/net6.0/TinyNF 83:00.0 85:00.0
