CC=gcc
SOURCE_DIR := ${CURDIR}
FREERTOS_DIR := ../../../FreeRTOS
FREERTOS_PLUS_DIR := ../../../FreeRTOS-Plus
BUILD_DIR := build

INCLUDE_DIRS := -I. 
INCLUDE_DIRS += -I utils 
INCLUDE_DIRS += -I${FREERTOS_DIR}/Source/include
INCLUDE_DIRS +=	-I${FREERTOS_DIR}/Source/portable/ThirdParty/GCC/Posix
INCLUDE_DIRS +=	-I${FREERTOS_DIR}/Demo/Common/include
INCLUDE_DIRS +=	-I${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/Include
INCLUDE_DIRS +=	-I${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/portable/NetworkInterface/linux/
INCLUDE_DIRS +=	-I${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/include/
INCLUDE_DIRS += -I${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/portable/Compiler/GCC/

SOURCE_FILE := $(wildcard *.c)
SOURCE_FILE += $(wildcard utils/*.c)
SOURCE_FILE += $(wildcard ${FREERTOS_DIR}/Source/*.c)
# Memory manager (use malloc() / free() )
SOURCE_FILE += ${FREERTOS_DIR}/Source/portable/MemMang/heap_3.c
# posix port
SOURCE_FILE += ${FREERTOS_DIR}/Source/portable/ThirdParty/GCC/Posix/port.c

# FreeRTOS TCP
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/FreeRTOS_DNS.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/FreeRTOS_DHCP.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/FreeRTOS_ARP.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/FreeRTOS_TCP_WIN.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/FreeRTOS_Stream_Buffer.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/portable/BufferManagement/BufferAllocation_2.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/FreeRTOS_IP.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/FreeRTOS_TCP_IP.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/FreeRTOS_UDP_IP.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/FreeRTOS_Sockets.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-TCP/portable/NetworkInterface/linux/NetworkInterface.c

# Demo library.
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/AbortDelay.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/BlockQ.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/blocktim.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/countsem.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/death.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/dynamic.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/EventGroupsDemo.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/flop.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/GenQTest.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/integer.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/IntSemTest.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/MessageBufferAMP.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/MessageBufferDemo.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/PollQ.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/QPeek.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/QueueOverwrite.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/QueueSet.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/QueueSetPolling.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/recmutex.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/semtest.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/StaticAllocation.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/StreamBufferDemo.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/StreamBufferInterrupt.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/TaskNotify.c
SOURCE_FILE += ${FREERTOS_DIR}/Demo/Common/Minimal/TimerDemo.c

# Trace library.
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/trcKernelPort.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/trcSnapshotRecorder.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/trcStreamingRecorder.c
SOURCE_FILE += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/streamports/File/trcStreamingPort.c


CFLAGS := -ggdb3 -Og -DprojCOVERAGE_TEST=0
LDFLAGS := -ggdb3 -Og -lpthread -lpcap

COV_FLAGS := -fprofile-arcs -ftest-coverage

.PHONY: all clean depend
all: posix_demo

posix_demo: Makefile
	-mkdir $(BUILD_DIR)
	$(CC) $(SOURCE_FILE) $(INCLUDE_DIRS) $(CFLAGS) $(LDFLAGS) -o $(BUILD_DIR)/$@

coverage: Makefile
	-mkdir build
	$(CC) $(SOURCE_FILE) $(INCLUDE_DIRS) $(CFLAGS) $(LDFLAGS) $(COV_FLAGS) -o $(BUILD_DIR)/$@


depend: ${BUILD_DIR}/depend

${BUILD_DIR}/depend: $(SOURCE_FILE)
	-mkdir $(BUILD_DIR)
	rm -f ${BUILD_DIR}/depend
	$(CC) $(CFLAGS) $(INCLUDE_DIRS) -MM $^ > $(BUILD_DIR)/depend;

clean:
	-rm -rf $(BUILD_DIR)


include ${BUILD_DIR}/depend





