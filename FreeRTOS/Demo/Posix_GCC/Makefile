CC := gcc
BIN := posix_demo

BUILD_DIR := build

FREERTOS_DIR_REL := ../../../FreeRTOS
FREERTOS_DIR := $(abspath $(FREERTOS_DIR_REL))

FREERTOS_PLUS_DIR_REL := ../../../FreeRTOS-Plus
FREERTOS_PLUS_DIR := $(abspath $(FREERTOS_PLUS_DIR_REL))

INCLUDE_DIRS := -I.
INCLUDE_DIRS += -I${FREERTOS_DIR}/Source/include
INCLUDE_DIRS += -I${FREERTOS_DIR}/Source/portable/ThirdParty/GCC/Posix
INCLUDE_DIRS += -I${FREERTOS_DIR}/Source/portable/ThirdParty/GCC/Posix/utils
INCLUDE_DIRS += -I${FREERTOS_DIR}/Demo/Common/include
INCLUDE_DIRS += -I${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/Include

SOURCE_FILES := $(wildcard *.c)
SOURCE_FILES += $(wildcard ${FREERTOS_DIR}/Source/*.c)
# Memory manager (use malloc() / free() )
SOURCE_FILES += ${FREERTOS_DIR}/Source/portable/MemMang/heap_3.c
# posix port
SOURCE_FILES += ${FREERTOS_DIR}/Source/portable/ThirdParty/GCC/Posix/utils/wait_for_event.c
SOURCE_FILES += ${FREERTOS_DIR}/Source/portable/ThirdParty/GCC/Posix/port.c

# Demo library.
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/AbortDelay.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/BlockQ.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/blocktim.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/countsem.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/death.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/dynamic.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/EventGroupsDemo.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/flop.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/GenQTest.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/integer.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/IntSemTest.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/MessageBufferAMP.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/MessageBufferDemo.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/PollQ.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/QPeek.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/QueueOverwrite.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/QueueSet.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/QueueSetPolling.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/recmutex.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/semtest.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/StaticAllocation.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/StreamBufferDemo.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/StreamBufferInterrupt.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/TaskNotify.c
SOURCE_FILES += ${FREERTOS_DIR}/Demo/Common/Minimal/TimerDemo.c

# Trace library.
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/trcKernelPort.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/trcSnapshotRecorder.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/trcStreamingRecorder.c
SOURCE_FILES += ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace/streamports/File/trcStreamingPort.c


CFLAGS := -ggdb3 -O0 -DprojCOVERAGE_TEST=0 -D_WINDOWS_
LDFLAGS := -ggdb3 -O0 -pthread -lpcap

OBJ_FILES = $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.o)

DEP_FILE = $(OBJ_FILES:%.o=%.d)

${BIN} : $(BUILD_DIR)/$(BIN)

${BUILD_DIR}/${BIN} : ${OBJ_FILES}
	-mkdir -p ${@D}
	$(CC) $^ $(CFLAGS) $(INCLUDE_DIRS) ${LDFLAGS} -o $@


-include ${DEP_FILE}

${BUILD_DIR}/%.o : %.c
	-mkdir -p $(@D)
	$(CC) $(CFLAGS) ${INCLUDE_DIRS} -MMD -c $< -o $@

.PHONY: clean

clean:
	-rm -rf $(BUILD_DIR)







