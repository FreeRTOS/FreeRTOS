CC = arm-none-eabi-gcc
OBJCOPY = arm-none-eabi-objcopy
BUILD_DIR := build
LDFLAGS = -T $(LINKER_SCRIPT) --specs=nosys.specs 
LDFLAGS += -Xlinker -Map=${BUILD_DIR}/output.map

CFLAGS += -march=armv6-m -mcpu=cortex-m0plus -mthumb

ifeq ($(DEBUG), 1)
    CFLAGS += -ggdb3 -Og
else
    CFLAGS += -O3
endif
