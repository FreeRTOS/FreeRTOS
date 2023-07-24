
TARGET = XCORE-AI-EXPLORER

APP_NAME = RTOSDemo

BUILD_DIR = build
OUT_DIR = bin

DEMO_ROOT = src
KERNEL_ROOT = ../../../../../Source
COMMON_DEMO_ROOT = ../../../../Common
MINIMAL_DEMO_ROOT = $(COMMON_DEMO_ROOT)/Minimal
PORTABLE_ROOT = $(KERNEL_ROOT)/portable
MEMMANG_ROOT = $(PORTABLE_ROOT)/MemMang
XCORE_PORT_ROOT = $(PORTABLE_ROOT)/ThirdParty/xClang/XCOREAI
RTOS_SUPPORT_ROOT = ../lib_rtos_support

INCLUDE_DIRS = $(DEMO_ROOT) $(DEMO_ROOT)/IntQueueTimer $(DEMO_ROOT)/regtest \
               $(KERNEL_ROOT)/include $(XCORE_PORT_ROOT) \
               $(COMMON_DEMO_ROOT)/include \
               $(RTOS_SUPPORT_ROOT)/api $(RTOS_SUPPORT_ROOT)/src

APP_SOURCES = $(DEMO_ROOT)/main.xc \
              $(DEMO_ROOT)/test.c \
              $(DEMO_ROOT)/IntQueueTimer/IntQueueTimer.c \
              $(DEMO_ROOT)/partest/mab_led_driver.xc \
              $(DEMO_ROOT)/partest/partest.c \
              $(DEMO_ROOT)/regtest/prvRegisterCheck_asm1.S \
              $(DEMO_ROOT)/regtest/prvRegisterCheck_asm2.S \
              $(DEMO_ROOT)/regtest/regtest.c

COMMON_DEMO_SOURCES = $(MINIMAL_DEMO_ROOT)/AbortDelay.c \
                      $(MINIMAL_DEMO_ROOT)/BlockQ.c \
                      $(MINIMAL_DEMO_ROOT)/blocktim.c \
                      $(MINIMAL_DEMO_ROOT)/countsem.c \
                      $(MINIMAL_DEMO_ROOT)/death.c \
                      $(MINIMAL_DEMO_ROOT)/dynamic.c \
                      $(MINIMAL_DEMO_ROOT)/EventGroupsDemo.c \
                      $(MINIMAL_DEMO_ROOT)/flop.c \
                      $(MINIMAL_DEMO_ROOT)/GenQTest.c \
                      $(MINIMAL_DEMO_ROOT)/integer.c \
                      $(MINIMAL_DEMO_ROOT)/IntQueue.c \
                      $(MINIMAL_DEMO_ROOT)/IntSemTest.c \
                      $(MINIMAL_DEMO_ROOT)/MessageBufferDemo.c \
                      $(MINIMAL_DEMO_ROOT)/PollQ.c \
                      $(MINIMAL_DEMO_ROOT)/QPeek.c \
                      $(MINIMAL_DEMO_ROOT)/QueueOverwrite.c \
                      $(MINIMAL_DEMO_ROOT)/QueueSet.c \
                      $(MINIMAL_DEMO_ROOT)/QueueSetPolling.c \
                      $(MINIMAL_DEMO_ROOT)/recmutex.c \
                      $(MINIMAL_DEMO_ROOT)/semtest.c \
                      $(MINIMAL_DEMO_ROOT)/StreamBufferDemo.c \
                      $(MINIMAL_DEMO_ROOT)/StreamBufferInterrupt.c \
                      $(MINIMAL_DEMO_ROOT)/TaskNotify.c \
                      $(MINIMAL_DEMO_ROOT)/TaskNotifyArray.c \
                      $(MINIMAL_DEMO_ROOT)/TimerDemo.c

RTOS_SUPPORT_SOURCES = $(RTOS_SUPPORT_ROOT)/src/rtos_cores.c \
                       $(RTOS_SUPPORT_ROOT)/src/rtos_interrupt.c \
                       $(RTOS_SUPPORT_ROOT)/src/rtos_irq.c \
                       $(RTOS_SUPPORT_ROOT)/src/rtos_locks.c \
                       $(RTOS_SUPPORT_ROOT)/src/rtos_printf.c \
                       $(RTOS_SUPPORT_ROOT)/src/rtos_time.c

KERNEL_SOURCES = $(KERNEL_ROOT)/event_groups.c \
                 $(KERNEL_ROOT)/list.c \
                 $(KERNEL_ROOT)/queue.c \
                 $(KERNEL_ROOT)/stream_buffer.c \
                 $(KERNEL_ROOT)/tasks.c \
                 $(KERNEL_ROOT)/timers.c \
                 $(MEMMANG_ROOT)/heap_4.c \
                 $(XCORE_PORT_ROOT)/port.c \
                 $(XCORE_PORT_ROOT)/port.xc \
                 $(XCORE_PORT_ROOT)/portasm.S

SOURCES = $(APP_SOURCES) $(COMMON_DEMO_SOURCES) $(RTOS_SUPPORT_SOURCES) $(KERNEL_SOURCES)

OBJS = $(addprefix $(BUILD_DIR)/,$(notdir $(addsuffix .o,$(SOURCES))))

ROOT_DIRS = $(DEMO_ROOT) $(DEMO_ROOT)/IntQueueTimer $(DEMO_ROOT)/partest \
            $(DEMO_ROOT)/regtest $(DEMO_ROOT)/TimerDemoISR \
            $(MINIMAL_DEMO_ROOT) $(KERNEL_ROOT) $(MEMMANG_ROOT) \
            $(XCORE_PORT_ROOT) $(RTOS_SUPPORT_ROOT)/src

vpath %.c $(ROOT_DIRS)
vpath %.xc $(ROOT_DIRS)
vpath %.S $(ROOT_DIRS)

FLAGS = -Wall -O2 -g -report -fxscope \
        $(DEMO_ROOT)/$(TARGET).xn \
        $(DEMO_ROOT)/config.xscope \
        $(addprefix -I,$(INCLUDE_DIRS))

XCLANG = xcc

.PHONY: all clean run

all: $(OUT_DIR)/$(APP_NAME).xe

# Include the header file dependencies for all the sources
-include $(patsubst %.o,%.d,$(OBJS))

$(BUILD_DIR)/%.o: %
	@"mkdir" -p $(@D)
	$(XCLANG) -c -MT"$@" -MMD -MP -MF"$(patsubst %.o,%.d,$@)" -MT"$(patsubst %.o,%.d,$@)" -o $@ $< $(FLAGS)

$(OUT_DIR)/$(APP_NAME).xe: $(OBJS)
	@"mkdir" -p $(@D)
	$(XCLANG) -o $@ $^ $(FLAGS)
	
clean:
	$(RM) -r $(OUT_DIR) $(BUILD_DIR)

run: $(OUT_DIR)/$(APP_NAME).xe
	xrun --xscope $(OUT_DIR)/$(APP_NAME).xe

