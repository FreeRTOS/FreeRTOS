#/*
# * FreeRTOS Kernel V10.2.0
# * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
# *
# * Permission is hereby granted, free of charge, to any person obtaining a copy of
# * this software and associated documentation files (the "Software"), to deal in
# * the Software without restriction, including without limitation the rights to
# * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
# * the Software, and to permit persons to whom the Software is furnished to do so,
# * subject to the following conditions:
# *
# * The above copyright notice and this permission notice shall be included in all
# * copies or substantial portions of the Software.
# *
# * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
# * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
# * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
# * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
# *
# * http://www.FreeRTOS.org
# * http://aws.amazon.com/freertos
# *
# * 1 tab == 4 spaces!
# */

CC=arm-elf-gcc
OBJCOPY=arm-elf-objcopy
ARCH=arm-elf-ar
CRT0=boot.s

#
# CFLAGS common to both the THUMB and ARM mode builds
#
CFLAGS=-Wall -Wextra -D $(RUN_MODE) -D GCC_AT91FR40008 -I. -I../../Source/include \
		-I../Common/include $(DEBUG) -mcpu=arm7tdmi -T$(LDSCRIPT) \
		-Wcast-align $(OPTIM) -fomit-frame-pointer -fno-strict-aliasing \
		-fno-dwarf2-cfi-asm

ifeq ($(USE_THUMB_MODE),YES)
	CFLAGS += -mthumb-interwork -D THUMB_INTERWORK
	THUMB_FLAGS=-mthumb
endif


LINKER_FLAGS=-Xlinker -ortosdemo.elf -Xlinker -M -Xlinker -Map=rtosdemo.map

#
# Source files that can be built to THUMB mode.
#
THUMB_SRC = \
main.c \
serial/serial.c \
ParTest/ParTest.c \
../Common/Minimal/integer.c \
../Common/Minimal/flash.c \
../Common/Minimal/PollQ.c \
../Common/Minimal/comtest.c \
../Common/Minimal/flop.c \
../Common/Minimal/semtest.c \
../Common/Minimal/dynamic.c \
../Common/Minimal/BlockQ.c \
../../Source/tasks.c \
../../Source/queue.c \
../../Source/list.c \
../../Source/portable/MemMang/heap_2.c \
../../Source/portable/GCC/ARM7_AT91FR40008/port.c

#
# Source files that must be built to ARM mode.
#
ARM_SRC = \
../../Source/portable/GCC/ARM7_AT91FR40008/portISR.c \
serial/serialISR.c

#
# Define all object files.
#
ARM_OBJ = $(ARM_SRC:.c=.o)
THUMB_OBJ = $(THUMB_SRC:.c=.o)

rtosdemo.hex : rtosdemo.elf
	$(OBJCOPY) rtosdemo.elf -O ihex rtosdemo.hex

rtosdemo.elf : $(ARM_OBJ) $(THUMB_OBJ) $(CRT0) Makefile
	$(CC) $(CFLAGS) $(ARM_OBJ) $(THUMB_OBJ) -nostartfiles $(CRT0) $(LINKER_FLAGS)

$(THUMB_OBJ) : %.o : %.c $(LDSCRIPT) Makefile
	$(CC) -c $(THUMB_FLAGS) $(CFLAGS) $< -o $@

$(ARM_OBJ) : %.o : %.c $(LDSCRIPT) Makefile
	$(CC) -c $(CFLAGS) $< -o $@

clean :
	touch Makefile
	rm $(ARM_OBJ)
	rm $(THUMB_OBJ)

