CC = arm-none-eabi-gcc
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
SOURCE_FILES += $(KERNEL_DIR)/timers.c
SOURCE_FILES += $(KERNEL_DIR)/event_groups.c

# FreeRTOS Kernel ARM Cortex-M3 Port
INCLUDE_DIRS += -I$(KERNEL_DIR)/portable/GCC/ARM_CM3

SOURCE_FILES += $(KERNEL_DIR)/portable/GCC/ARM_CM3/port.c
SOURCE_FILES += ${KERNEL_DIR}/portable/MemMang/heap_3.c

# FreeRTOS+TCP
INCLUDE_DIRS += -I${FREERTOS_TCP}/source/include/

SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_ARP.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_DHCP.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_DNS.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_DNS_Cache.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_DNS_Callback.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_DNS_Networking.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_DNS_Parser.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_ICMP.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_IP.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_IP_Timers.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_IP_Utils.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_Sockets.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_Stream_Buffer.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_TCP_IP.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_TCP_Reception.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_TCP_State_Handling.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_TCP_Transmission.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_TCP_Utils.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_TCP_WIN.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_Tiny_TCP.c
SOURCE_FILES += ${FREERTOS_TCP}/source/FreeRTOS_UDP_IP.c

# FreeRTOS+TCP Port for ARM MPS2 SoC
INCLUDE_DIRS += -I${FREERTOS_TCP}/source/portable/NetworkInterface/MPS2_AN385/ether_lan9118
INCLUDE_DIRS += -I${FREERTOS_TCP}/source/portable/Compiler/GCC

SOURCE_FILES += ${FREERTOS_TCP}/source/portable/BufferManagement/BufferAllocation_2.c
SOURCE_FILES += ${FREERTOS_TCP}/source/portable/NetworkInterface/MPS2_AN385/NetworkInterface.c
SOURCE_FILES += ${FREERTOS_TCP}/source/portable/NetworkInterface/MPS2_AN385/ether_lan9118/smsc9220_eth_drv.c

DEFINES := -DQEMU_SOC_MPS2 -DHEAP3

LDFLAGS = -T mps2_m3.ld -specs=nano.specs --specs=rdimon.specs -lc -lrdimon
LDFLAGS += -Xlinker -Map=${BUILD_DIR}/output.map

CFLAGS += -nostartfiles -mthumb -mcpu=cortex-m3 -Wno-error=implicit-function-declaration
CFLAGS += -Wno-builtin-declaration-mismatch -Werror

ifeq ($(DEBUG), 1)
    CFLAGS += -ggdb3 -Og
else
    CFLAGS += -O3
endif
    CFLAGS += -fstrict-aliasing -Wstrict-aliasing -Wno-error=address-of-packed-member

OBJ_FILES := $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.o)

CPPFLAGS += $(DEFINES)
CFLAGS += $(INCLUDE_DIRS)

.PHONY: clean

$(BUILD_DIR)/$(BIN) : $(OBJ_FILES)
	$(CC) -ffunction-sections -fdata-sections $(CFLAGS) $(LDFLAGS) $+ -o $(@)

%.d: %.c
	@set -e; rm -f $@; \
	$(CC) -M $(CPPFLAGS) $< > $@.$$$$; \
	sed 's,\($*\)\.o[ :]*,\1.o $@ : ,g' < $@.$$$$ > $@; \
	rm -f $@.$$$$

INCLUDES := $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.d)
-include $(INCLUDES)

${BUILD_DIR}/%.o : %.c Makefile
	-mkdir -p $(@D)
	$(CC)  $(CPPFLAGS) $(CFLAGS) -MMD -c $< -o $@

clean:
	-rm -rf build
