 # Makefile
 #
 # Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 #
 # SPDX-License-Identifier: MIT
 #
 # Permission is hereby granted, free of charge, to any person obtaining a copy of
 # this software and associated documentation files (the "Software"), to deal in
 # the Software without restriction, including without limitation the rights to
 # use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 # the Software, and to permit persons to whom the Software is furnished to do so,
 # subject to the following conditions:
 #
 # The above copyright notice and this permission notice shall be included in all
 # copies or substantial portions of the Software.
 #
 # THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 # IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 # FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 # COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 # IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 # CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 #

.PHONY: default
default:	build-x86_32

# Set this variable to define total heap size
TOTAL_HEAP_AVAILABLE  := 30000000

CC                    := gcc
AR                    := ar
FREERTOS_LIB          := libfreertos.a

BUILD_DIR             := ./build
BUILD_DIR_ABS         := $(abspath $(BUILD_DIR))
ACPICA_DIR            := ../acpica
BRANCH_NAME           := $(shell git rev-parse --abbrev-ref HEAD)

ifeq ($(FREERTOS_DIR),)
   $(error FREERTOS_DIR environment variable must be defined)
endif
FREERTOS_DIR          := $(abspath $(FREERTOS_DIR))
PROJECT_ROOT          := $(abspath .)

FREERTOS_PORTABLE_DIR := $(FREERTOS_DIR)/Source/portable/GCC/XEN_x86/IA32

include ../Makefile.common
INCLUDE_DIRS          += -I${PROJECT_ROOT}/../xen/include/x86/x86_32
INCLUDE_DIRS          += -I${FREERTOS_PORTABLE_DIR}
SOURCE_FILES          += ${FREERTOS_PORTABLE_DIR}/port.c
ASM_SOURCE_FILES      += ${FREERTOS_PORTABLE_DIR}/startup.S
ASM_SOURCE_FILES      += ${FREERTOS_PORTABLE_DIR}/portASM.S
SOURCE_FILES          += ${KERNEL_DIR}/portable/MemMang/heap_4.c
SOURCE_FILES          += ${XEN_SRC}/arch/x86/mm.c
SOURCE_FILES          += ${XEN_SRC}/arch/x86/freertos_mm.c
SOURCE_FILES          += ${XEN_SRC}/arch/x86/gnttab.c

CFLAGS                :=  -O3 -fno-stack-protector -fno-builtin -nostdlib -m32 -std=gnu99 -ffreestanding  -U_FORTIFY_SOURCE -D_FORTIFY_SOURCE=0 -DTOTAL_HEAP_SIZE=${TOTAL_HEAP_AVAILABLE} -D__XEN_INTERFACE_VERSION__=0x00030205 -D__INSIDE_MINIOS__ -DCONFIG_XENBUS
CPPFLAGS              :=  $(INCLUDE_DIRS) -DBUILD_DIR=\"$(BUILD_DIR_ABS)\" -D__XEN_INTERFACE_VERSION__=0x00030205

OBJ_FILES             := $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.o)
ASM_OBJ_FILES         := $(ASM_SOURCE_FILES:%.S=$(BUILD_DIR)/%.o)
OBJ_FILES             := $(OBJ_FILES) $(ASM_OBJ_FILES)
DEP_FILE               = $(OBJ_FILES:%.o=%.d)

${FREERTOS_LIB} : $(VERSION_HEADER) $(BUILD_DIR)/$(FREERTOS_LIB)

${BUILD_DIR}/${FREERTOS_LIB} : ${OBJ_FILES} acpica
	-mkdir -p ${@D}
	$(AR) -rcs $@ ${OBJ_FILES}  $(shell find $(BUILD_DIR)/acpi_lib/  -name *.o)

-include ${DEP_FILE}

${BUILD_DIR}/%.o : %.c Makefile
	-mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) -MMD -c $< -o $@

${BUILD_DIR}/%.o : %.S Makefile
	-mkdir -p $(@D)
	$(CC) -m32 -ffreestanding $(CPPFLAGS) $(CFLAGS) -MMD -c $< -o $@

${BUILD_DIR}/%.o : %.asm Makefile
	-mkdir -p $(@D)
	nasm -f elf32 $< -o $@

.PHONY: clean


acpica:
	cd $(ACPICA_DIR) && M32=TRUE NOFORTIFY=TRUE NOWERROR=TRUE make
	mkdir -p $(BUILD_DIR)/acpi_lib
	cp $(ACPICA_DIR)/generate/unix/libacpi/obj/*.o $(BUILD_DIR)/acpi_lib

clean:
	-cd $(ACPICA_DIR) && make clean
	-rm -rf ./build
	-rm -rf ./output
	-rm -f ./freertos32_${BRANCH_NAME}.objdump
	-rm -f ./freertos32_${BRANCH_NAME}.bin
	-rm -f  $(VERSION_HEADER)

	-rm -f  $(VERSION_HEADER)

build-x86_32: $(FREERTOS_LIB) elf_ia32_efi.lds acpica
	-rm -f  $(VERSION_HEADER)
	cp -rf isobuild output
	ld -n -o ./freertos32_${BRANCH_NAME}.bin -m elf_i386 -T elf_ia32_efi.lds -nostdlib ${BUILD_DIR}/${FREERTOS_LIB}
	cp ./freertos32_${BRANCH_NAME}.bin ./output/iso/boot/freertos32.bin
	grub-mkrescue /usr/lib/grub/i386-pc -o ./output/freertos-${BRANCH_NAME}-x86_32.iso ./output/iso 
	objdump -d ./freertos32_${BRANCH_NAME}.bin > freertos32_${BRANCH_NAME}.objdump

