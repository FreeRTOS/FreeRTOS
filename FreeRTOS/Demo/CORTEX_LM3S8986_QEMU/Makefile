#/*
#* FreeRTOS Kernel V10.3.1
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
# * http://www.FreeRTOS.org
# * http://aws.amazon.com/freertos
# *
# * 1 tab == 4 spaces!
# */


#/*************************************************************************
# * Please ensure to read http://www.freertos.org/portLM3Sxxxx_Eclipse.html
# * which provides information on configuring and running this demo for the
# * various Luminary Micro EKs.
# *************************************************************************/

RTOS_SOURCE_DIR=../../../Source
DEMO_COMMON_DIR=../../Common/Minimal
DEMO_INCLUDE_DIR=../../Common/include
UIP_COMMON_DIR=../../Common/ethernet/uIP/uip-1.0/uip
LUMINARY_DRIVER_DIR=../../Common/drivers/LuminaryMicro

CC=arm-none-eabi-gcc
OBJCOPY=arm-none-eabi-objcopy
LDSCRIPT=standalone.ld

# should use --gc-sections but the debugger does not seem to be able to cope with the option.
LINKER_FLAGS=-nostartfiles -Xlinker -oRTOSDemo.axf -Xlinker -M -Xlinker -Map=rtosdemo.map -Xlinker --no-gc-sections

DEBUG=-g
OPTIM=-O0


CFLAGS=$(DEBUG) -I . \
				-I $(RTOS_SOURCE_DIR)/include \
				-I $(RTOS_SOURCE_DIR)/portable/GCC/ARM_CM3 \
				-I $(DEMO_INCLUDE_DIR)  \
				-mthumb \
				-mcpu=cortex-m3 \
				$(OPTIM) \
				-T$(LDSCRIPT) \
				-ffunction-sections \
				-fdata-sections \
				-Wextra \
				-Wall \

SOURCE=	main.c \
		$(DEMO_COMMON_DIR)/BlockQ.c \
		$(DEMO_COMMON_DIR)/blocktim.c \
		$(DEMO_COMMON_DIR)/death.c \
		$(DEMO_COMMON_DIR)/integer.c \
		$(DEMO_COMMON_DIR)/PollQ.c \
		$(DEMO_COMMON_DIR)/semtest.c \
		$(DEMO_COMMON_DIR)/GenQTest.c \
		$(DEMO_COMMON_DIR)/QPeek.c \
		$(DEMO_COMMON_DIR)/recmutex.c \
		$(DEMO_COMMON_DIR)/IntQueue.c \
		$(RTOS_SOURCE_DIR)/list.c \
		$(RTOS_SOURCE_DIR)/queue.c \
		$(RTOS_SOURCE_DIR)/tasks.c \
		$(RTOS_SOURCE_DIR)/portable/GCC/ARM_CM3/port.c \
		$(RTOS_SOURCE_DIR)/portable/MemMang/heap_4.c


LIBS= $(LUMINARY_DRIVER_DIR)/arm-none-eabi-gcc/libdriver.a $(LUMINARY_DRIVER_DIR)/arm-none-eabi-gcc/libgr.a

OBJS = $(SOURCE:.c=.o)

all: RTOSDemo.bin

RTOSDemo.bin : RTOSDemo.axf
	$(OBJCOPY) RTOSDemo.axf -O binary RTOSDemo.bin

RTOSDemo.axf : $(OBJS) startup.o Makefile
	$(CC) $(CFLAGS) $(OBJS) startup.o $(LIBS) $(LINKER_FLAGS)

$(OBJS) : %.o : %.c Makefile FreeRTOSConfig.h
	$(CC) -c $(CFLAGS) $< -o $@

startup.o : startup.c Makefile
	$(CC) -c $(CFLAGS) -O1 startup.c -o startup.o

clean :
	touch Makefile
	del $(OBJS)




