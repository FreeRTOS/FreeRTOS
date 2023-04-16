CC := gcc
BIN := posix_tcp_demo

BUILD_DIR := build
BUILD_DIR_ABS         := $(abspath $(BUILD_DIR))

FREERTOS_DIR_REL := ../../../FreeRTOS
FREERTOS_DIR := $(abspath $(FREERTOS_DIR_REL))

FREERTOS_PLUS_DIR_REL := ../../../FreeRTOS-Plus
FREERTOS_PLUS_DIR := $(abspath $(FREERTOS_PLUS_DIR_REL))

KERNEL_DIR            := ${FREERTOS_DIR}/Source

INCLUDE_DIRS := -I.
INCLUDE_DIRS += -I./Trace_Recorder_Configuration
INCLUDE_DIRS += -I${KERNEL_DIR}/include
INCLUDE_DIRS += -I${KERNEL_DIR}/portable/ThirdParty/GCC/Posix
INCLUDE_DIRS += -I${KERNEL_DIR}/portable/ThirdParty/GCC/Posix/utils
INCLUDE_DIRS += -I${FREERTOS_DIR}/Demo/Common/include
INCLUDE_DIRS += -I${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/portable/NetworkInterface/linux/
INCLUDE_DIRS += -I${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/include/
INCLUDE_DIRS += -I${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/portable/Compiler/GCC/
INCLUDE_DIRS += -I${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/Include
INCLUDE_DIRS += -I${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/config
INCLUDE_DIRS += -I${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/streamports/File/include
INCLUDE_DIRS += -I${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/streamports/File/config

# FreeRTOS Kernel source files
SOURCE_FILES :=
SOURCE_FILES += ${FREERTOS_DIR}/Source/event_groups.c
SOURCE_FILES += ${FREERTOS_DIR}/Source/list.c
SOURCE_FILES += ${FREERTOS_DIR}/Source/queue.c
SOURCE_FILES += ${FREERTOS_DIR}/Source/stream_buffer.c
SOURCE_FILES += ${FREERTOS_DIR}/Source/tasks.c
SOURCE_FILES += ${FREERTOS_DIR}/Source/timers.c

# FreeRTOS Kernel POSIX Port
SOURCE_FILES          += ${KERNEL_DIR}/portable/ThirdParty/GCC/Posix/utils/wait_for_event.c
SOURCE_FILES          += ${KERNEL_DIR}/portable/ThirdParty/GCC/Posix/port.c

# FreeRTOS+TCP demo source file
SOURCE_FILES += SimpleTCPEchoServer.c
SOURCE_FILES += TCPEchoClient_SingleTasks.c
SOURCE_FILES += console.c
SOURCE_FILES += main.c
SOURCE_FILES += main_networking.c
SOURCE_FILES += runtime_stats_hooks.c

# Memory manager (use malloc() / free() )
SOURCE_FILES += ${FREERTOS_DIR}/Source/portable/MemMang/heap_3.c


# FreeRTOS TCP
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_ARP.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_DHCP.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_DNS.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_DNS_Cache.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_DNS_Callback.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_DNS_Networking.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_DNS_Parser.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_ICMP.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_IP.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_IP_Timers.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_IP_Utils.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_Sockets.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_Stream_Buffer.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_TCP_IP.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_TCP_Reception.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_TCP_State_Handling.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_TCP_Transmission.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_TCP_Utils.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_TCP_WIN.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_Tiny_TCP.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/FreeRTOS_UDP_IP.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/portable/BufferManagement/BufferAllocation_2.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/source/portable/NetworkInterface/linux/NetworkInterface.c


CFLAGS 			:= -ggdb3
LDFLAGS			:= -ggdb3 -pthread -lpcap
CPPFLAGS		:=    $(INCLUDE_DIRS) -DBUILD_DIR=\"$(BUILD_DIR_ABS)\"

ifeq ($(TRACE_ON_ENTER),1)
  CPPFLAGS		+= -DTRACE_ON_ENTER=1
else
  CPPFLAGS		+= -DTRACE_ON_ENTER=0
endif

ifeq ($(COVERAGE_TEST),1)
  CPPFLAGS		+= -DprojCOVERAGE_TEST=1
else
  CPPFLAGS		+= -DprojCOVERAGE_TEST=0
# Trace library.
  SOURCE_FILES	+= ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/trcKernelPort.c
  SOURCE_FILES	+= $(wildcard ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/*.c )
endif

ifdef PROFILE
  CFLAGS		+=   -pg  -O0
  LDFLAGS		+=   -pg  -O0
else
  CFLAGS		+=   -O3
  LDFLAGS		+=   -O3
endif

OBJ_FILES = $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.o)

DEP_FILE = $(OBJ_FILES:%.o=%.d)

${BIN} : $(BUILD_DIR)/$(BIN)

${BUILD_DIR}/${BIN} : ${OBJ_FILES}
	-mkdir -p ${@D}
	$(CC) $^ ${LDFLAGS} -o $@


-include ${DEP_FILE}

${BUILD_DIR}/%.o : %.c Makefile
	-mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) -MMD -c $< -o $@

.PHONY: clean

clean:
	-rm -rf $(BUILD_DIR)

GPROF_OPTIONS := --directory-path=$(INCLUDE_DIRS)
profile:
	gprof -a -p --all-lines $(GPROF_OPTIONS) $(BUILD_DIR)/$(BIN) $(BUILD_DIR)/gmon.out > $(BUILD_DIR)/prof_flat.txt
	gprof -a --graph $(GPROF_OPTIONS) $(BUILD_DIR)/$(BIN) $(BUILD_DIR)/gmon.out > $(BUILD_DIR)/prof_call_graph.txt
