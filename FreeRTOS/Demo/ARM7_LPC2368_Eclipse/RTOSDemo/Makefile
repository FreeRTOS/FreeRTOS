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


RTOS_SOURCE_DIR=../../../Source
DEMO_COMMON_DIR=../../Common/Minimal
DEMO_INCLUDE_DIR=../../Common/include
UIP_COMMON_DIR=../../Common/ethernet/uIP/uip-1.0/uip

CC=arm-elf-gcc
OBJCOPY=arm-elf-objcopy
LDSCRIPT=lpc2368.ld

LINKER_FLAGS=-mthumb -nostartfiles -Xlinker -oRTOSDemo.elf -Xlinker -M -Xlinker -Map=rtosdemo.map

DEBUG=-g
OPTIM=-O0


CFLAGS= $(DEBUG) \
		$(OPTIM) \
		-T$(LDSCRIPT) \
		-I . \
		-I $(RTOS_SOURCE_DIR)/include \
		-I $(RTOS_SOURCE_DIR)/portable/GCC/ARM7_LPC23xx \
		-I $(DEMO_INCLUDE_DIR) \
		-I ./webserver \
		-I $(UIP_COMMON_DIR) \
		-D ROWLEY_LPC23xx \
		-D THUMB_INTERWORK \
		-mcpu=arm7tdmi \
		-D PACK_STRUCT_END=__attribute\(\(packed\)\) \
		-D ALIGN_STRUCT_END=__attribute\(\(aligned\(4\)\)\) \
		-fomit-frame-pointer \
		-mthumb-interwork \
		-fno-dwarf2-cfi-asm \
		-fno-strict-aliasing
		
THUMB_SOURCE= \
		main.c \
		./ParTest/ParTest.c \
		./LCD/portlcd.c \
		$(DEMO_COMMON_DIR)/BlockQ.c \
		$(DEMO_COMMON_DIR)/blocktim.c \
		$(DEMO_COMMON_DIR)/flash.c \
		$(DEMO_COMMON_DIR)/integer.c \
		$(DEMO_COMMON_DIR)/GenQTest.c \
		$(DEMO_COMMON_DIR)/QPeek.c \
		$(DEMO_COMMON_DIR)/dynamic.c \
		./webserver/uIP_Task.c \
		./webserver/emac.c \
		./webserver/httpd.c \
		./webserver/httpd-cgi.c \
		./webserver/httpd-fs.c \
		./webserver/http-strings.c \
		$(UIP_COMMON_DIR)/uip_arp.c \
		$(UIP_COMMON_DIR)/psock.c \
		$(UIP_COMMON_DIR)/timer.c \
		$(UIP_COMMON_DIR)/uip.c \
		$(RTOS_SOURCE_DIR)/list.c \
		$(RTOS_SOURCE_DIR)/queue.c \
		$(RTOS_SOURCE_DIR)/tasks.c \
		$(RTOS_SOURCE_DIR)/portable/GCC/ARM7_LPC23xx/port.c \
		$(RTOS_SOURCE_DIR)/portable/MemMang/heap_2.c \
		syscalls.c

ARM_SOURCE= \
		$(RTOS_SOURCE_DIR)/portable/GCC/ARM7_LPC23xx/portISR.c \
		./webserver/EMAC_ISR.c

THUMB_OBJS = $(THUMB_SOURCE:.c=.o)
ARM_OBJS = $(ARM_SOURCE:.c=.o)


all: RTOSDemo.bin

RTOSDemo.bin : RTOSDemo.hex
	$(OBJCOPY) RTOSDemo.elf -O binary RTOSDemo.bin
	 
RTOSDemo.hex : RTOSDemo.elf
	$(OBJCOPY) RTOSDemo.elf -O ihex RTOSDemo.hex

RTOSDemo.elf : $(THUMB_OBJS) $(ARM_OBJS) boot.s Makefile
	$(CC) $(CFLAGS) $(ARM_OBJS) $(THUMB_OBJS) $(LIBS) boot.s $(LINKER_FLAGS) 

$(THUMB_OBJS) : %.o : %.c Makefile FreeRTOSConfig.h
	$(CC) -c $(CFLAGS) -mthumb $< -o $@

$(ARM_OBJS) : %.o : %.c Makefile FreeRTOSConfig.h
	$(CC) -c $(CFLAGS) $< -o $@

clean :
	rm $(THUMB_OBJS)
	rm $(ARM_OBJS)
	touch Makefile
	rm RTOSDemo.elf
	rm RTOSDemo.hex
	
	
	




