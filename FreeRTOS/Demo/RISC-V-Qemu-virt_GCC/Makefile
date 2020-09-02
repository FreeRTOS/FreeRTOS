CROSS=riscv64-unknown-elf-
CC=$(CROSS)gcc
OBJCOPY=$(CROSS)objcopy
ARCH=$(CROSS)ar

RTOS_SOURCE_DIR=../../Source
DEMO_SOURCE_DIR=../Common/Minimal
LIBWRAP_SOURCE_DIR=./freedom-e-sdk/libwrap

CPPFLAGS = \
	-g -O2 -Wall \
	-fmessage-length=0 \
	-ffunction-sections \
	-fdata-sections \
	-fno-builtin-printf \
	-D__riscv_float_abi_soft \
	-DportasmHANDLE_INTERRUPT=handle_trap \
	-I . -I ../Common/include \
	-I $(RTOS_SOURCE_DIR)/include \
	-I $(RTOS_SOURCE_DIR)/portable/GCC/RISC-V \
	-I $(RTOS_SOURCE_DIR)/portable/GCC/RISC-V/chip_specific_extensions/RV32I_CLINT_no_extensions
CFLAGS  = -march=rv32ima -mabi=ilp32 -mcmodel=medany
ASFLAGS = -march=rv32ima -mabi=ilp32 -mcmodel=medany
LDFLAGS = -nostartfiles -Tfake_rom.lds \
	-Xlinker --gc-sections \
	-Xlinker --defsym=__stack_size=300

SRCS = main.c riscv-virt.c ns16550.c \
	$(DEMO_SOURCE_DIR)/EventGroupsDemo.c \
	$(DEMO_SOURCE_DIR)/TaskNotify.c \
	$(DEMO_SOURCE_DIR)/TimerDemo.c \
	$(DEMO_SOURCE_DIR)/blocktim.c \
	$(DEMO_SOURCE_DIR)/dynamic.c \
	$(DEMO_SOURCE_DIR)/recmutex.c \
	$(RTOS_SOURCE_DIR)/event_groups.c \
	$(RTOS_SOURCE_DIR)/list.c \
	$(RTOS_SOURCE_DIR)/queue.c \
	$(RTOS_SOURCE_DIR)/stream_buffer.c \
	$(RTOS_SOURCE_DIR)/tasks.c \
	$(RTOS_SOURCE_DIR)/timers.c \
	$(RTOS_SOURCE_DIR)/portable/MemMang/heap_4.c \
	$(RTOS_SOURCE_DIR)/portable/GCC/RISC-V/port.c

ASMS = start.S \
	$(RTOS_SOURCE_DIR)/portable/GCC/RISC-V/portASM.S

OBJS = $(SRCS:.c=.o) $(ASMS:.S=.o)

demo.elf: $(OBJS) fake_rom.lds Makefile
	$(CC) $(CFLAGS) $(LDFLAGS) $(OBJS) -o $@

clean:
	rm -rf demo.elf $(OBJS)
