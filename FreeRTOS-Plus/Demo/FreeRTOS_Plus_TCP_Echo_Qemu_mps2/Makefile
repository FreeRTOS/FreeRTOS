CC = arm-none-eabi-gcc
SIZE = arm-none-eabi-size
BIN := freertos_tcp_mps2_demo.axf

BUILD_DIR := build

FREERTOS_DIR_REL := ../../../FreeRTOS
FREERTOS_DIR := $(abspath $(FREERTOS_DIR_REL))
KERNEL_DIR := $(FREERTOS_DIR)/Source

FREERTOS_PLUS_DIR_REL := ../../../FreeRTOS-Plus
FREERTOS_PLUS_DIR := $(abspath $(FREERTOS_PLUS_DIR_REL))

INCLUDE_DIRS += -I.

FREERTOS_TCP = ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP

# Demo Source Files
SOURCE_FILES += startup.c
SOURCE_FILES += syscalls.c
SOURCE_FILES += main.c
SOURCE_FILES += main_networking.c
SOURCE_FILES += TCPEchoClient_SingleTasks.c

INCLUDE_DIRS += -ICMSIS

# FreeRTOS Kernel
INCLUDE_DIRS += -I$(KERNEL_DIR)/include

SOURCE_FILES += $(KERNEL_DIR)/tasks.c
SOURCE_FILES += $(KERNEL_DIR)/list.c
SOURCE_FILES += $(KERNEL_DIR)/queue.c
SOURCE_FILES += $(KERNEL_DIR)/event_groups.c

# FreeRTOS Kernel ARM Cortex-M3 Port
INCLUDE_DIRS += -I$(KERNEL_DIR)/portable/GCC/ARM_CM3

SOURCE_FILES += $(KERNEL_DIR)/portable/GCC/ARM_CM3/port.c
SOURCE_FILES += ${KERNEL_DIR}/portable/MemMang/heap_3.c

# FreeRTOS+TCP
INCLUDE_DIRS += -I${FREERTOS_TCP}/source/include/

SOURCE_FILES += $(wildcard ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/*.c )

# FreeRTOS+TCP Port for ARM MPS2 SoC
INCLUDE_DIRS += -I${FREERTOS_TCP}/source/portable/NetworkInterface/MPS2_AN385/ether_lan9118
INCLUDE_DIRS += -I${FREERTOS_TCP}/source/portable/Compiler/GCC

SOURCE_FILES += ${FREERTOS_TCP}/source/portable/BufferManagement/BufferAllocation_2.c
SOURCE_FILES += ${FREERTOS_TCP}/source/portable/NetworkInterface/MPS2_AN385/NetworkInterface.c
SOURCE_FILES += ${FREERTOS_TCP}/source/portable/NetworkInterface/MPS2_AN385/ether_lan9118/smsc9220_eth_drv.c

DEFINES := -DHEAP3
CPPFLAGS += $(DEFINES)

CFLAGS += -mthumb -mcpu=cortex-m3
ifeq ($(DEBUG), 1)
    CFLAGS += -g3 -Og -ffunction-sections -fdata-sections
else
    CFLAGS += -Os -ffunction-sections -fdata-sections
endif
CFLAGS += -MMD
CFLAGS += -Wall -Wextra -Wshadow
#CFLAGS += -Wpedantic -fanalyzer
#CFLAGS += -flto
CFLAGS += $(INCLUDE_DIRS)

LDFLAGS = -T mps2_m3.ld
LDFLAGS += -Xlinker -Map=${BUILD_DIR}/output.map
LDFLAGS += -Xlinker --gc-sections
LDFLAGS += -nostartfiles -specs=nano.specs -specs=nosys.specs -specs=rdimon.specs

OBJ_FILES := $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.o)

.PHONY: clean

$(BUILD_DIR)/$(BIN) : $(OBJ_FILES)
	$(CC) $(CFLAGS) $(LDFLAGS) $+ -o $(@)
	$(SIZE) $(@)

%.d: %.c
	@set -e; rm -f $@; \
	$(CC) -M $(CPPFLAGS) $< > $@.$$$$; \
	sed 's,\($*\)\.o[ :]*,\1.o $@ : ,g' < $@.$$$$ > $@; \
	rm -f $@.$$$$

INCLUDES := $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.d)
-include $(INCLUDES)

${BUILD_DIR}/%.o : %.c Makefile
	-mkdir -p $(@D)
	$(CC) $(CFLAGS) $(CPPFLAGS) -c $< -o $@

clean:
	-rm -rf build
