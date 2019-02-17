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
USE_THUMB_MODE=YES
DEBUG=-g
OPTIM=-Os
RUN_MODE=RUN_FROM_ROM
LDSCRIPT=lpc2106-rom.ld


#
# CFLAGS common to both the THUMB and ARM mode builds
#
CFLAGS=-Wall -D $(RUN_MODE) -D GCC_ARM7 -I. -I../../Source/include \
		-I../Common/include $(DEBUG) -mcpu=arm7tdmi -T$(LDSCRIPT) \
		-Wcast-align $(OPTIM) -fomit-frame-pointer

ifeq ($(USE_THUMB_MODE),YES)
	CFLAGS += -mthumb-interwork -D THUMB_INTERWORK
	THUMB_FLAGS=-mthumb
endif


LINKER_FLAGS=-Xlinker -oWebServeDemo.elf -Xlinker -M -Xlinker -Map=WebServeDemo.map

#
# Source files that can be built to THUMB mode.
#
THUMB_SRC = \
../../Source/tasks.c \
../../Source/queue.c \
../../Source/list.c \
../../Source/portable/MemMang/heap_2.c \
../../Source/portable/GCC/ARM7_LPC2000/port.c \
../Common/Minimal/flash.c \
../Common/Minimal/dynamic.c \
../Common/Minimal/semtest.c \
../Common/Minimal/PollQ.c \
../Common/Minimal/BlockQ.c \
../Common/Minimal/integer.c \
../ARM7_LPC2106_GCC/ParTest/ParTest.c \
main.c \
TCP.c \
HTTP_Serv.c \
i2c.c

#
# Source files that must be built to ARM mode.
#
ARM_SRC = \
../../Source/portable/GCC/ARM7_LPC2000/portISR.c \
i2cISR.c \
TCPISR.c

#
# Define all object files.
#
ARM_OBJ = $(ARM_SRC:.c=.o)
THUMB_OBJ = $(THUMB_SRC:.c=.o)

WebServeDemo.hex : WebServeDemo.elf
	$(OBJCOPY) WebServeDemo.elf -O ihex WebServeDemo.hex

WebServeDemo.elf : $(ARM_OBJ) $(THUMB_OBJ) $(CRT0) Makefile
	$(CC) $(CFLAGS) $(ARM_OBJ) $(THUMB_OBJ) -nostartfiles $(CRT0) $(LINKER_FLAGS)

$(THUMB_OBJ) : %.o : %.c $(LDSCRIPT) Makefile
	$(CC) -c $(THUMB_FLAGS) $(CFLAGS) $< -o $@

$(ARM_OBJ) : %.o : %.c $(LDSCRIPT) Makefile
	$(CC) -c $(CFLAGS) $< -o $@

clean :
	touch makefile







	


