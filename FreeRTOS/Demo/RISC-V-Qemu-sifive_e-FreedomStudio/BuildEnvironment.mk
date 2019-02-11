BUILD_DIR = ./build
CROSS_COMPILE_PREFIX = riscv32-unknown-elf

SDK_DIR = ./freedom-e-sdk

LINKER_SCRIPT = $(SDK_DIR)/env/freedom-e300-hifive1/flash.lds
#-----------------------------------------------------------
GCC     = $(CROSS_COMPILE_PREFIX)-gcc
OBJCOPY = $(CROSS_COMPILE_PREFIX)-objcopy
OBJDUMP = $(CROSS_COMPILE_PREFIX)-objdump
AR      = $(CROSS_COMPILE_PREFIX)-ar
RANLIB  = $(CROSS_COMPILE_PREFIX)-ranlib
GDB     = $(CROSS_COMPILE_PREFIX)-gdb

# if using the multi-arch (riscv64-unknown-elf-gcc):
ARCH_FLAGS = -march=rv32imac -mabi=ilp32 -mcmodel=medany
# Basic CFLAGS:
CFLAGS  = -Wall -Wextra -O0 -g3 -msmall-data-limit=8 -std=gnu11
CFLAGS += -ffunction-sections -fdata-sections -fno-builtin-printf
CFLAGS += -DDONT_USE_PLIC -DDONT_USE_M_TIME
CFLAGS += -include sys/cdefs.h
CFLAGS += $(ARCH_FLAGS)
# These flags are for outputing *.d dependency files for make
CFLAGS += -MT"$@" -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)"

ASMFLAGS =  -O0 -g3
ASMFLAGS += $(ARCH_FLAGS)
ASMFLAGS += -DportasmHANDLE_INTERRUPT=handle_trap
ASMFLAGS += -msmall-data-limit=8
ASMFLAGS += -ffunction-sections -fdata-sections
ASMFLAGS += -x assembler-with-cpp
ASMFLAGS += -MT"$@" -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)"

# Linker arguments __________________________________________
LDFLAGS :=  -Xlinker --gc-sections -Xlinker --defsym=__stack_size=1K
LDFLAGS += -O0 -g3
LDFLAGS += -ffunction-sections -fdata-sections --specs=nano.specs
LDFLAGS += -nostartfiles
LDFLAGS += -T $(LINKER_SCRIPT)
LDFLAGS += -L../
LDFLAGS += -Wl,--start-group -Wl,--end-group
LDFLAGS += -Wl,--wrap=malloc -Wl,--wrap=free -Wl,--wrap=open -Wl,--wrap=lseek -Wl,--wrap=read -Wl,--wrap=write
LDFLAGS += -Wl,--wrap=fstat -Wl,--wrap=stat -Wl,--wrap=close -Wl,--wrap=link -Wl,--wrap=unlink -Wl,--wrap=execve
LDFLAGS += -Wl,--wrap=fork -Wl,--wrap=getpid -Wl,--wrap=kill -Wl,--wrap=wait -Wl,--wrap=isatty -Wl,--wrap=times
LDFLAGS += -Wl,--wrap=sbrk -Wl,--wrap=_exit -Wl,--wrap=puts -Wl,--wrap=_malloc -Wl,--wrap=_free -Wl,--wrap=_open
LDFLAGS += -Wl,--wrap=_lseek -Wl,--wrap=_read -Wl,--wrap=_write -Wl,--wrap=_fstat -Wl,--wrap=_stat -Wl,--wrap=_close
LDFLAGS += -Wl,--wrap=_link -Wl,--wrap=_unlink -Wl,--wrap=_execve -Wl,--wrap=_fork -Wl,--wrap=_getpid -Wl,--wrap=_kill
LDFLAGS += -Wl,--wrap=_wait -Wl,--wrap=_isatty -Wl,--wrap=_times -Wl,--wrap=_sbrk -Wl,--wrap=__exit -Wl,--wrap=_puts
