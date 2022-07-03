#/*
# * FreeRTOS V202112.00
# * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
# * https://www.FreeRTOS.org
# * https://aws.amazon.com/freertos
# *
# * 1 tab == 4 spaces!
# */

CC = arm-none-eabi-gcc
LD = arm-none-eabi-ld
OBJCOPY = arm-none-eabi-objcopy
MCU = TM4C123GH6PM
BIN = RTOSDemo.bin

BUILD_DIR := build

DEBUG = -g
OPT = -Os
WARNINGS = -Wall -Wunused -Wmissing-prototypes -Wmissing-declarations -Wstrict-prototypes -Wbad-function-cast -Wcast-align -Wsign-compare -Wshadow -Wpointer-arith
INCLUDE = -I. -I./driverlib -I../../Source/include -I../Common/include -I$(PORT_PATH) -I$(FULL_DEMO)
CFLAGS = -mthumb -mcpu=cortex-m4 -mfpu=fpv4-sp-d16 -mfloat-abi=softfp $(OPT) $(DEBUG) -ffunction-sections -fdata-sections -MD -std=c99 $(DEBUG) $(WARNINGS) -pedantic $(INCLUDE) 
CFLAGS += -DPART_$(MCU) -Dgcc -DTARGET_IS_BLIZZARD_RA1

LDFLAGS = -T $(MCU).ld --entry ResetISR --gc-sections 

LIBC = ${shell ${CC} -mthumb -march=armv6t2 -print-file-name=libc.a}



FREERTOS_DIR_REL := ../../../FreeRTOS
FREERTOS_DIR := $(abspath $(FREERTOS_DIR_REL))
KERNEL_PATH := $(FREERTOS_DIR)/Source
PORT_PATH := $(KERNEL_PATH)/portable/GCC/ARM_CM4F
DEMO_PATH = ../Common/Minimal
FULL_DEMO = ./Full_Demo

SOURCE_FILES = \
main.c \
main_blinky.c \
startup_gcc.c \
driverlib/sysctl.c \
driverlib/gpio.c \
driverlib/uart.c \
driverlib/interrupt.c \
$(KERNEL_PATH)/tasks.c \
$(KERNEL_PATH)/queue.c \
$(KERNEL_PATH)/list.c \
$(KERNEL_PATH)/timers.c \
$(KERNEL_PATH)/portable/MemMang/heap_1.c \
$(PORT_PATH)/port.c


OBJ = $(SOURCE_FILES:%.c=$(BUILD_DIR)/%.o)

.PHONY: clean

#
# Rules for all object files.
#

$(BUILD_DIR)/$(BIN) : $(BUILD_DIR)/a.out
	$(OBJCOPY) -O binary $< $@

$(BUILD_DIR)/a.out : $(OBJ)
	$(LD) $(LDFLAGS) -o $@ $^ $(LIBC)

${BUILD_DIR}/%.o : %.c Makefile
	-mkdir -p $(@D)
	$(CC) $(CFLAGS) -c $< -o $@

clean :
	-rm -rf $(BUILD_DIR)
