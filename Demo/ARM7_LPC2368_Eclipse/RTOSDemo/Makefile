#/*
#    FreeRTOS V6.0.0 - Copyright (C) 2009 Real Time Engineers Ltd.
#
#    This file is part of the FreeRTOS distribution.
#
#    FreeRTOS is free software; you can redistribute it and/or modify it    under
#    the terms of the GNU General Public License (version 2) as published by the
#    Free Software Foundation and modified by the FreeRTOS exception.
#    **NOTE** The exception to the GPL is included to allow you to distribute a
#    combined work that includes FreeRTOS without being obliged to provide the
#    source code for proprietary components outside of the FreeRTOS kernel.
#    Alternative commercial license and support terms are also available upon
#    request.  See the licensing section of http://www.FreeRTOS.org for full
#    license details.
#
#    FreeRTOS is distributed in the hope that it will be useful,    but WITHOUT
#    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
#    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
#    more details.
#
#    You should have received a copy of the GNU General Public License along
#    with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
#    Temple Place, Suite 330, Boston, MA  02111-1307  USA.
#
#
#    ***************************************************************************
#    *                                                                         *
#    * The FreeRTOS eBook and reference manual are available to purchase for a *
#    * small fee. Help yourself get started quickly while also helping the     *
#    * FreeRTOS project! See http://www.FreeRTOS.org/Documentation for details *
#    *                                                                         *
#    ***************************************************************************
#
#    1 tab == 4 spaces!
#
#    Please ensure to read the configuration and relevant port sections of the
#    online documentation.
#
#    http://www.FreeRTOS.org - Documentation, latest information, license and
#    contact details.
#
#    http://www.SafeRTOS.com - A version that is certified for use in safety
#    critical systems.
#
#    http://www.OpenRTOS.com - Commercial support, development, porting,
#    licensing and training services.
#*/


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
	
	
	




