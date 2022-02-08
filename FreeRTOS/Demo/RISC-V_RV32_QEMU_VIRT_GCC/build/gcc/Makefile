OUTPUT_DIR := ./output
IMAGE := RTOSDemo.elf

# The directory that contains the /source and /demo sub directories.
FREERTOS_ROOT = ./../../../..

CC = riscv64-unknown-elf-gcc
LD = riscv64-unknown-elf-gcc
SIZE = riscv64-unknown-elf-size
MAKE = make

CFLAGS += $(INCLUDE_DIRS) -DportasmHANDLE_INTERRUPT=handle_trap -fmessage-length=0 \
          -march=rv32imac -mabi=ilp32 -mcmodel=medlow -ffunction-sections -fdata-sections \
          --specs=nano.specs -fno-builtin-printf  -Wno-unused-parameter -nostartfiles -g3 -Os
          
LDFLAGS += -nostartfiles -Xlinker --gc-sections -Wl,-Map,$(OUTPUT_DIR)/RTOSDemo.map \
           -T./fake_rom.ld -march=rv32imac -mabi=ilp32 -mcmodel=medlow -Xlinker \
           --defsym=__stack_size=350 -Wl,--start-group -Wl,--end-group -Wl,--wrap=malloc \
           -Wl,--wrap=free -Wl,--wrap=open -Wl,--wrap=lseek -Wl,--wrap=read -Wl,--wrap=write \
           -Wl,--wrap=fstat -Wl,--wrap=stat -Wl,--wrap=close -Wl,--wrap=link -Wl,--wrap=unlink \
           -Wl,--wrap=execve -Wl,--wrap=fork -Wl,--wrap=getpid -Wl,--wrap=kill -Wl,--wrap=wait \
           -Wl,--wrap=isatty -Wl,--wrap=times -Wl,--wrap=sbrk -Wl,--wrap=puts -Wl,--wrap=_malloc \
           -Wl,--wrap=_free -Wl,--wrap=_open -Wl,--wrap=_lseek -Wl,--wrap=_read -Wl,--wrap=_write \
           -Wl,--wrap=_fstat -Wl,--wrap=_stat -Wl,--wrap=_close -Wl,--wrap=_link -Wl,--wrap=_unlink \
           -Wl,--wrap=_execve -Wl,--wrap=_fork -Wl,--wrap=_getpid -Wl,--wrap=_kill -Wl,--wrap=_wait \
           -Wl,--wrap=_isatty -Wl,--wrap=_times -Wl,--wrap=_sbrk -Wl,--wrap=__exit -Wl,--wrap=_puts

# -Wl,--wrap=_exit
#
# Kernel build.
#
KERNEL_DIR = $(FREERTOS_ROOT)/Source
KERNEL_PORT_DIR += $(KERNEL_DIR)/portable/GCC/RISC-V
INCLUDE_DIRS += -I$(KERNEL_DIR)/include \
				-I$(KERNEL_PORT_DIR) \
				-I$(KERNEL_PORT_DIR)/chip_specific_extensions/RV32I_CLINT_no_extensions
VPATH += $(KERNEL_DIR) $(KERNEL_PORT_DIR) $(KERNEL_DIR)/portable/MemMang
SOURCE_FILES += $(KERNEL_DIR)/tasks.c
SOURCE_FILES += $(KERNEL_DIR)/list.c
SOURCE_FILES += $(KERNEL_DIR)/queue.c
SOURCE_FILES += $(KERNEL_DIR)/timers.c
SOURCE_FILES += $(KERNEL_DIR)/event_groups.c
SOURCE_FILES += $(KERNEL_DIR)/stream_buffer.c
SOURCE_FILES += $(KERNEL_DIR)/portable/MemMang/heap_4.c
SOURCE_FILES += $(KERNEL_DIR)/portable/GCC/RISC-V/port.c
ASM_SOURCE_FILES += $(KERNEL_DIR)/portable/GCC/RISC-V/portASM.S

#
# Common demo files for the "full" build, as opposed to the "blinky" build -
# these files are build by all the FreeRTOS kernel demos.
#
DEMO_ROOT = $(FREERTOS_ROOT)/Demo
COMMON_DEMO_FILES = $(DEMO_ROOT)/Common/Minimal
INCLUDE_DIRS += -I$(DEMO_ROOT)/Common/include
VPATH += $(COMMON_DEMO_FILES)
SOURCE_FILES += (COMMON_DEMO_FILES)/AbortDelay.c
SOURCE_FILES += (COMMON_DEMO_FILES)/BlockQ.c
SOURCE_FILES += (COMMON_DEMO_FILES)/blocktim.c
SOURCE_FILES += (COMMON_DEMO_FILES)/countsem.c
SOURCE_FILES += (COMMON_DEMO_FILES)/death.c
SOURCE_FILES += (COMMON_DEMO_FILES)/dynamic.c
SOURCE_FILES += (COMMON_DEMO_FILES)/EventGroupsDemo.c
SOURCE_FILES += (COMMON_DEMO_FILES)/GenQTest.c
SOURCE_FILES += (COMMON_DEMO_FILES)/integer.c
SOURCE_FILES += (COMMON_DEMO_FILES)/IntSemTest.c
SOURCE_FILES += (COMMON_DEMO_FILES)/MessageBufferAMP.c
SOURCE_FILES += (COMMON_DEMO_FILES)/MessageBufferDemo.c
SOURCE_FILES += (COMMON_DEMO_FILES)/PollQ.c
SOURCE_FILES += (COMMON_DEMO_FILES)/QPeek.c
SOURCE_FILES += (COMMON_DEMO_FILES)/QueueOverwrite.c
SOURCE_FILES += (COMMON_DEMO_FILES)/QueueSet.c
SOURCE_FILES += (COMMON_DEMO_FILES)/QueueSetPolling.c
SOURCE_FILES += (COMMON_DEMO_FILES)/recmutex.c
SOURCE_FILES += (COMMON_DEMO_FILES)/semtest.c
SOURCE_FILES += (COMMON_DEMO_FILES)/StaticAllocation.c
SOURCE_FILES += (COMMON_DEMO_FILES)/StreamBufferDemo.c
SOURCE_FILES += (COMMON_DEMO_FILES)/StreamBufferInterrupt.c
SOURCE_FILES += (COMMON_DEMO_FILES)/TaskNotify.c
SOURCE_FILES += (COMMON_DEMO_FILES)/TaskNotifyArray.c
SOURCE_FILES += (COMMON_DEMO_FILES)/TimerDemo.c

#
# Application entry point.  main_blinky is self contained.  main_full builds
# the above common demo (and test) files too.
#
DEMO_PROJECT = $(DEMO_ROOT)/RISC-V_RV32_QEMU_VIRT_GCC
VPATH += $(DEMO_PROJECT)
INCLUDE_DIRS += -I$(DEMO_PROJECT)
SOURCE_FILES += (DEMO_PROJECT)/main.c
SOURCE_FILES += (DEMO_PROJECT)/main_blinky.c
SOURCE_FILES += (DEMO_PROJECT)/main_full.c
SOURCE_FILES += (DEMO_PROJECT)/ns16550.c
SOURCE_FILES += (DEMO_PROJECT)/riscv-virt.c
# Lightweight print formatting to use in place of the heavier GCC equivalent.
SOURCE_FILES += ./printf-stdarg.c
ASM_SOURCE_FILES += ./start.S
ASM_SOURCE_FILES += ./RegTest.S
ASM_SOURCE_FILES += ./vector.S


#Create a list of object files with the desired output directory path.
OBJS = $(SOURCE_FILES:%.c=%.o) $(ASM_SOURCE_FILES:%.S=%.o)
OBJS_NO_PATH = $(notdir $(OBJS))
OBJS_OUTPUT = $(OBJS_NO_PATH:%.o=$(OUTPUT_DIR)/%.o)

#Create a list of dependency files with the desired output directory path.
DEP_FILES := $(SOURCE_FILES:%.c=$(OUTPUT_DIR)/%.d) $(ASM_SOURCE_FILES:%.S=$(OUTPUT_DIR)/%.d)
DEP_FILES_NO_PATH = $(notdir $(DEP_FILES))
DEP_OUTPUT = $(DEP_FILES_NO_PATH:%.d=$(OUTPUT_DIR)/%.d)

all: $(OUTPUT_DIR)/$(IMAGE)

%.o : %.c
$(OUTPUT_DIR)/%.o : %.c $(OUTPUT_DIR)/%.d Makefile
	$(CC) $(CFLAGS) -MMD -MP -c $< -o $@

%.o : %.S
$(OUTPUT_DIR)/%.o: %.S $(OUTPUT_DIR)/%.d Makefile
	$(CC) $(CFLAGS) -MMD -MP -c $< -o $@

$(OUTPUT_DIR)/$(IMAGE): $(OBJS_OUTPUT) Makefile
	@echo ""
	@echo ""
	@echo "--- Final linking ---"
	@echo ""
	$(LD) $(OBJS_OUTPUT) $(LDFLAGS) -o $(OUTPUT_DIR)/$(IMAGE)
	$(SIZE) $(OUTPUT_DIR)/$(IMAGE)

$(DEP_OUTPUT):
include $(wildcard $(DEP_OUTPUT))

clean:
	rm -f $(OUTPUT_DIR)/$(IMAGE) $(OUTPUT_DIR)/*.o $(OUTPUT_DIR)/*.d $(OUTPUT_DIR)/*.map

#use "make print-[VARIABLE_NAME] to print the value of a variable generated by
#this makefile.
print-%  : ; @echo $* = $($*)

.PHONY: all clean


