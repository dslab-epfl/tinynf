# re-export DOTNET_ROOT in case it's not the default value
run:
	@make -C cwrapper --no-print-directory
	@taskset -c 8 sudo DOTNET_ROOT=$(DOTNET_ROOT) LD_LIBRARY_PATH=$$(pwd)/cwrapper dotnet run --configuration Release 83:00.0 85:00.0
