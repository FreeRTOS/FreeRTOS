CC = arm-none-eabi-gcc
BIN := blinky.elf
TARGET_BASE := $(basename $(BIN))

FREERTOS_DIR_REL := ../../../FreeRTOS
FREERTOS_DIR := $(abspath $(FREERTOS_DIR_REL))
KERNEL_DIR := $(FREERTOS_DIR)/Source

FREERTOS_PLUS_DIR_REL := ../../../FreeRTOS-Plus
FREERTOS_PLUS_DIR := $(abspath $(FREERTOS_PLUS_DIR_REL))

SOURCE_FILES += $(KERNEL_DIR)/portable/GCC/ARM_CM0/port.c
SOURCE_FILES += $(KERNEL_DIR)/tasks.c
SOURCE_FILES += $(KERNEL_DIR)/list.c
SOURCE_FILES += $(KERNEL_DIR)/queue.c
SOURCE_FILES += $(KERNEL_DIR)/timers.c
SOURCE_FILES += $(KERNEL_DIR)/event_groups.c
SOURCE_FILES += ${KERNEL_DIR}/portable/MemMang/heap_3.c

INCLUDE_DIRS += -I$(FREERTOS_DIR)/Demo/CORTEX_M0+_RaspberryPiPico_GCC
INCLUDE_DIRS += -I$(KERNEL_DIR)/include
INCLUDE_DIRS += -I$(KERNEL_DIR)/portable/GCC/ARM_CM0

INCLUDE_DIRS += -I includes
LINKER_SCRIPT = linker_scripts/memmap_default.ld

include common.mk

SOURCE_FILES += bootrom.c
SOURCE_FILES += clocks.c
SOURCE_FILES += gpio.c
SOURCE_FILES += pll.c
SOURCE_FILES += startup.c
SOURCE_FILES += xosc.c

# Blinky Demo
SOURCE_FILES += blinky.c

DEFINES :=  -DHEAP3

OBJ_FILES := $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.o)

CPPFLAGS += $(DEFINES)
CFLAGS += $(INCLUDE_DIRS)

.PHONY: clean elf2uf2

$(BUILD_DIR)/$(BIN): boot_stage2 $(OBJ_FILES) $(BUILD_DIR)/crt0.o elf2uf2
	$(CC) $(CFLAGS) $(LDFLAGS) -Wl,--build-id=none -Wl,--gc-sections $(OBJ_FILES) $(BUILD_DIR)/crt0.o -o $(@) boot2/build/boot2/boot2_checksummed.S
	elf2uf2/build/elf2uf2/elf2uf2 $(BUILD_DIR)/$(BIN) $(BUILD_DIR)/$(TARGET_BASE).uf2


$(BUILD_DIR)/crt0.o: crt0.S
	$(CC) $(CFLAGS) $(LDFLAGS) -c $< -o $@

boot_stage2:
	$(MAKE) -C boot2

elf2uf2:
	$(MAKE) -C elf2uf2

%.d: %.c
	@set -e; rm -f $@; \
	$(CC) -M $(CPPFLAGS) $< > $@.$$$$; \
	sed 's,\($*\)\.o[ :]*,\1.o $@ : ,g' < $@.$$$$ > $@; \
	rm -f $@.$$$$

INCLUDES := $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.d)
-include $(INCLUDES)

${BUILD_DIR}/%.o: %.c Makefile
	-mkdir -p $(@D)
	$(CC) $(CFLAGS) $(CPPFLAGS) -MMD -c $< -o $@

clean:
	$(MAKE) -C boot2 clean
	$(MAKE) -C elf2uf2 clean
	-rm -rf build
