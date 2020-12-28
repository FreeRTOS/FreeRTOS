CC = arm-none-eabi-gcc
BIN := RTOSDemo.axf

BUILD_DIR := build

FREERTOS_DIR_REL := ../../../FreeRTOS
FREERTOS_DIR := $(abspath $(FREERTOS_DIR_REL))
KERNEL_DIR := $(FREERTOS_DIR)/Source

FREERTOS_PLUS_DIR_REL := ../../../FreeRTOS-Plus
FREERTOS_PLUS_DIR := $(abspath $(FREERTOS_PLUS_DIR_REL))

SOURCE_FILES += init/startup.c  syscall.c main.c
SOURCE_FILES += $(KERNEL_DIR)/portable/GCC/ARM_CM3/port.c
SOURCE_FILES += $(KERNEL_DIR)/tasks.c
SOURCE_FILES += $(KERNEL_DIR)/list.c
SOURCE_FILES += $(KERNEL_DIR)/queue.c
SOURCE_FILES += $(KERNEL_DIR)/timers.c
SOURCE_FILES += $(KERNEL_DIR)/event_groups.c
SOURCE_FILES += ${KERNEL_DIR}/portable/MemMang/heap_3.c

INCLUDE_DIRS += -I$(FREERTOS_PLUS_DIR)/Demo/FreeRTOS_Plus_TCP_Echo_Qemu_mps2
INCLUDE_DIRS += -I$(FREERTOS_PLUS_DIR)/Demo/FreeRTOS_Plus_TCP_Echo_Qemu_mps2/CMSIS
INCLUDE_DIRS += -I$(KERNEL_DIR)/include
INCLUDE_DIRS += -I$(KERNEL_DIR)/portable/GCC/ARM_CM3
INCLUDE_DIRS += -I.

FREERTOS_TCP = ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP

# FreeRTOS networking header directories
INCLUDE_DIRS += -I${FREERTOS_TCP}/include/
INCLUDE_DIRS += -I${FREERTOS_TCP}/portable/Compiler/GCC/

# FreeRTOS networking sources
SOURCE_FILES +=  main_networking.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_DNS.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_DHCP.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_ARP.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_TCP_WIN.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_Stream_Buffer.c
SOURCE_FILES += ${FREERTOS_TCP}/portable/BufferManagement/BufferAllocation_2.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_IP.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_TCP_IP.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_UDP_IP.c
SOURCE_FILES += ${FREERTOS_TCP}/FreeRTOS_Sockets.c
SOURCE_FILES += ${FREERTOS_TCP}/portable/NetworkInterface/MPS2_AN385/NetworkInterface.c
SOURCE_FILES += TCPEchoClient_SingleTasks.c
SOURCE_FILES += ${FREERTOS_TCP}/portable/NetworkInterface/MPS2_AN385/ether_lan9118/smsc9220_eth_drv.c

# networking specific cflags
CFLAGS := -DmainCREATE_NETWORKING_DEMO_ONLY=1
CFLAGS += -DmainCREATE_TCP_ECHO_TASKS_SINGLE=1

DEFINES := -DprojCOVERAGE_TEST -DQEMU_SOC_MPS2 -DHEAP3

LDFLAGS = -T ./scripts/mps2_m3.ld -specs=nano.specs --specs=rdimon.specs -lc -lrdimon
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

