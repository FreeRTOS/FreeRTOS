TARGET=riscv32-unknown-elf-
GCC	= $(TARGET)gcc
OBJCOPY	= $(TARGET)objcopy
OBJDUMP	= $(TARGET)objdump
AR	= $(TARGET)ar
RANLIB	= $(TARGET)ranlib
XLEN = 32
MARCH = rv32imac 
MABI = ilp32
OPENOCD = $(shell which openocd)
INTERFACE = $(BSP_DIR)/third_party/parashu/ftdi

PROG	= freeRtos-e32-100t

FREERTOS_SOURCE_DIR	= ../../../Source
BSP_DIR = ../bsp

filepath = .

#-----------------------------------------------------------
WARNINGS= -Wall -Wextra -Wshadow -Wpointer-arith -Wbad-function-cast -Wcast-align -Wsign-compare -Waggregate-return -Wstrict-prototypes -Wmissing-prototypes -Wmissing-declarations -Wunused

FREERTOS_SRC = \
	$(FREERTOS_SOURCE_DIR)/croutine.c \
	$(FREERTOS_SOURCE_DIR)/list.c \
	$(FREERTOS_SOURCE_DIR)/queue.c \
	$(FREERTOS_SOURCE_DIR)/tasks.c \
	$(FREERTOS_SOURCE_DIR)/timers.c \
	$(FREERTOS_SOURCE_DIR)/event_groups.c \
	$(FREERTOS_SOURCE_DIR)/portable/MemMang/heap_2.c \

PORT_SRC = $(FREERTOS_SOURCE_DIR)/portable/GCC/RISC-V/port.c
PORT_ASM = $(FREERTOS_SOURCE_DIR)/portable/GCC/RISC-V/portASM.S

DEMO_SRC = \
        $(BSP_DIR)/drivers/uart/uart.c \
	$(BSP_DIR)/drivers/spi/spi_spansion.c \
	$(BSP_DIR)/drivers/i2c/i2c_driver.c \
	$(BSP_DIR)/drivers/plic/plic_driver.c \
	$(BSP_DIR)/drivers/pwm/pwm_driver.c \
	$(BSP_DIR)/libs/util.c \
	$(BSP_DIR)/libs/printf.c \
	$(BSP_DIR)/libs/log.c \
	$(BSP_DIR)/core/traps.c \
	$(BSP_DIR)/core/init.c \
	./main.c

DEMO_ASM = \
	$(BSP_DIR)/core/start.S

INCLUDES = \
	-I./conf \
	-I$(BSP_DIR)/include \
	-I$(BSP_DIR)/third_party/parashu \
	-I$(FREERTOS_SOURCE_DIR)/include \
	-I$(FREERTOS_SOURCE_DIR)/portable/GCC/RISC-V/chip_specific_extensions/RV32I_CLINT_no_extensions \
	-I$(FREERTOS_SOURCE_DIR)/portable/GCC/RISC-V/
 
CFLAGS = \
	$(WARNINGS) $(INCLUDES) -g -march=rv32imac -mabi=ilp32 \
	-fomit-frame-pointer -fno-strict-aliasing -fno-builtin \
	-D__gracefulExit -DportasmHANDLE_INTERRUPT=mach_plic_handler -mcmodel=medany

GCCVER 	= $(shell $(GCC) --version | grep gcc | cut -d" " -f9)

#
# Define all object files.
#
DEMO_ASM_OBJ = $(DEMO_ASM:.S=.o)
PORT_ASM_OBJ = $(PORT_ASM:.S=.o)
DEMO_OBJ = $(DEMO_SRC:.c=.o)
PORT_OBJ = $(PORT_SRC:.c=.o)
RTOS_OBJ = $(FREERTOS_SRC:.c=.o)

OBJS = $(DEMO_ASM_OBJ) $(PORT_OBJ) $(PORT_ASM_OBJ) $(RTOS_OBJ) $(DEMO_OBJ) 

LDFLAGS	 = -march=rv32imac -mabi=ilp32 -T $(BSP_DIR)/third_party/parashu/link.ld -nostartfiles -static -nostdlib

LIBS	 = -lc -lgcc
%.o: %.c
	@echo "    CC $<"
	@$(GCC) -c $(CFLAGS) -o $@ $<

%.o: %.S
	@echo "    CC $<"
	@$(GCC) -c $(CFLAGS) -o $@ $<

all: $(PROG).elf

$(PROG).elf  : $(OBJS) Makefile 
	@echo Linking....
	@$(GCC) -o $@ $(LDFLAGS) $(OBJS) $(LIBS)
	@$(OBJDUMP) -S $(PROG).elf > $(PROG).asm	
	@echo Completed $@

clean :
	@rm -f $(OBJS)
	@rm -f $(PROG).elf 
	@rm -f $(PROG).asm
	@rm -fr $(filepath)/output
	@echo cleaned

force_true:
	@true

upload: $(PROG).elf  path do1 
path:
FILEPATH:='"$(filepath)"'
do1:
	@mkdir -p ./output
	@elf2hex 4 16384 $(filepath)/$(PROG).elf 2147483648 > $(filepath)/output/code.mem
	@gcc -g -w -D FILEPATH='"$(FILEPATH)"' $(BSP_DIR)/utils/uploader/elf_to_header.c -o $(filepath)/output/elf_to_header
	@$(filepath)/output/elf_to_header
	@riscv$(XLEN)-unknown-elf-gcc -w $(DC) -mcmodel=medany -static -std=gnu99 -fno-builtin-printf -I$(BSP_DIR)/include -I$(BSP_DIR)/third_party/parashu/ -I$(filepath)/output -c $(BSP_DIR)/utils/uploader/spansion/deploy.c -o $(filepath)/output/deploy.o -march=$(MARCH) -mabi=$(MABI) -lm -lgcc
	@riscv$(XLEN)-unknown-elf-ar rcs $(filepath)/output/libshakti$(XLEN).a $(OBJS) 
	@riscv$(XLEN)-unknown-elf-gcc -T $(BSP_DIR)/third_party/parashu/link.ld $(filepath)/output/deploy.o $(filepath)/output/libshakti$(XLEN).a -o $(filepath)/output/deploy.shakti -static -nostartfiles -march=$(MARCH) -mabi=$(MABI) -lm -lgcc
	@riscv$(XLEN)-unknown-elf-objdump -D $(filepath)/output/deploy.shakti > $(filepath)/output/deploy.dump
	@echo -e "Upload elf to Flash"
	@riscv$(XLEN)-unknown-elf-objcopy -O ihex $(filepath)/output/deploy.shakti $(filepath)/output/deploy.hex
	@sudo $(OPENOCD) -f $(INTERFACE).cfg -c "reset init" -c "load_image $(filepath)/output/deploy.hex ;resume 0x80000000;shutdown"


