THIS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

OUTPUT_DIR := $(THIS_DIR)/out

ifdef TN_CSHARP_AOT
BUILD_ARGS := -p:PublishAot=true
else
BUILD_ARGS := #nothing
endif

build:
	@make -C $(THIS_DIR)/cwrapper --no-print-directory
	@dotnet publish -r linux-x64 -c Release --self-contained -o $(OUTPUT_DIR) $(BUILD_ARGS) $(THIS_DIR)
