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
default:	build-x86_64
.PHONY: FREERTOS_VERSION

CC                    := gcc
AR                    := ar
FREERTOS_LIB          := libfreertos.a

BUILD_DIR             := ./build
BUILD_DIR_ABS         := $(abspath $(BUILD_DIR))
ACPICA_DIR            := ../acpica

ifeq ($(FREERTOS_DIR),)
   $(error FREERTOS_DIR environment variable must be defined)
endif

FREERTOS_DIR          := $(abspath $(FREERTOS_DIR))
PROJECT_ROOT          := $(abspath .)

FREERTOS_PORTABLE_DIR := $(FREERTOS_DIR)/Source/portable/GCC/XEN_x86/x86-64

include ../Makefile.common

INCLUDE_DIRS          += -I${PROJECT_ROOT}/../xen/include/x86/x86_64
INCLUDE_DIRS          += -I${FREERTOS_PORTABLE_DIR}
SOURCE_FILES          += ${FREERTOS_PORTABLE_DIR}/trap.c
SOURCE_FILES          += ${FREERTOS_PORTABLE_DIR}/syscall.c
SOURCE_FILES          += ${FREERTOS_PORTABLE_DIR}/page_allocate.c
SOURCE_FILES          += ${FREERTOS_PORTABLE_DIR}/x86_64_init.c
SOURCE_FILES          += ${FREERTOS_PORTABLE_DIR}/port.c
SOURCE_FILES          += ${FREERTOS_PORTABLE_DIR}/mpu_wrappers_x86_64.c
SOURCE_FILES          += ${KERNEL_DIR}/portable/MemMang/heap_5.c
SOURCE_FILES          += ${XEN_SRC}/arch/x86/mm.c
SOURCE_FILES          += ${XEN_SRC}/arch/x86/freertos_mm.c
SOURCE_FILES          += ${XEN_SRC}/arch/x86/gnttab.c

# 64 bit specific tests
SOURCE_FILES          += ${PROJECT_ROOT}/../tests/usertask.c

NASM_SOURCE_FILES     := $(shell find portable/asm_src/ -name *.asm)
NASM_OBJECT_FILES     := $(patsubst portable/asm_src/%.asm, build/portable/asm_src/%.o, $(NASM_SOURCE_FILES))

ASM_SOURCE_FILES     := portable/asm_src/xennote.S
ASM_OBJECT_FILES     := $(patsubst portable/asm_src/%.S, build/portable/asm_src/%.o, $(ASM_SOURCE_FILES))


CFLAGS                :=    -O3 -mstackrealign -fno-stack-protector -fno-builtin -nostdlib -std=gnu99 -ffreestanding -U_FORTIFY_SOURCE -D_FORTIFY_SOURCE=0 -D__XEN_INTERFACE_VERSION__=0x00030205 -D__INSIDE_MINIOS__ -DCONFIG_XENBUS
CPPFLAGS              :=    $(INCLUDE_DIRS) -D__XEN_INTERFACE_VERSION__=0x00030205

# Extra

OBJ_FILES := $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.o)

OBJ_FILES := $(OBJ_FILES)


DEP_FILE = $(OBJ_FILES:%.o=%.d)

${FREERTOS_LIB} : $(VERSION_HEADER) $(BUILD_DIR)/$(FREERTOS_LIB)

${BUILD_DIR}/${FREERTOS_LIB} : ${OBJ_FILES} acpica
	-mkdir -p ${@D}
	$(AR) -rcs $@ $(OBJ_FILES) $(shell find $(BUILD_DIR)/acpi_lib/  -name *.o)

-include ${DEP_FILE}
${BUILD_DIR}/%.o : %.c Makefile ../Makefile.common
	-mkdir -p $(@D)
	$(CC)  $(CPPFLAGS) $(CFLAGS) -MMD -c $< -o $@

${BUILD_DIR}/%.o : %.S Makefile
	-mkdir -p $(@D)
	$(CC) -D__ASSEMBLY__ -Wa,--noexecstack -m64 -DCONFIG_NETFRONT -DCONFIG_XENBUS -DCONFIG_LIBXS -D__XEN_INTERFACE_VERSION__=0x00030205 $(CPPFLAGS) -c $< -o $@


$(NASM_OBJECT_FILES): build/portable/asm_src/%.o : portable/asm_src/%.asm
	mkdir -p $(dir $@) && \
	nasm -f elf64 $(patsubst build/portable/asm_src/%.o, portable/asm_src/%.asm, $@) -o $@

$(ASM_OBJECT_FILES): build/portable/asm_src/%.o : portable/asm_src/%.S
	mkdir -p $(dir $@) && \
	$(CC)  $(CPPFLAGS) $(CFLAGS) -c $(patsubst build/portable/asm_src/%.o, portable/asm_src/%.S, $@) -o $@

.PHONY: clean


clean:
	-rm -rf $(BUILD_DIR)
	-rm -rf output
	-rm -f ./freertos64_${BRANCH_NAME}.objdump
	-cd $(ACPICA_DIR) && make clean
	-rm -f ./freertos64_${BRANCH_NAME}.bin
	-rm -f  $(VERSION_HEADER)

.PHONY: acpica driver

acpica:
	cd $(ACPICA_DIR) && NOWERROR=TRUE make
	mkdir -p $(BUILD_DIR)/acpi_lib
	cp $(ACPICA_DIR)/generate/unix/libacpi/obj/*.o $(BUILD_DIR)/acpi_lib

build-x86_64: $(FREERTOS_LIB) $(NASM_OBJECT_FILES) $(ASM_OBJECT_FILES)  acpica
	-rm -f  $(VERSION_HEADER)
	cp -rf isobuild output
	ld -n -o freertos64_${BRANCH_NAME}.bin -T linker.ld  $(NASM_OBJECT_FILES) $(ASM_OBJECT_FILES) ${BUILD_DIR}/${FREERTOS_LIB}
	cp freertos64_${BRANCH_NAME}.bin output/iso/boot/freertos64.bin
	grub-mkrescue /usr/lib/grub/i386-pc -o output/freertos-${BRANCH_NAME}-x86_64.iso output/iso
	objdump -t freertos64_${BRANCH_NAME}.bin > freertos64_${BRANCH_NAME}.objdump
