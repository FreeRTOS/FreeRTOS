#/*
#    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.
#	
#
#    ***************************************************************************
#     *                                                                       *
#     *    FreeRTOS tutorial books are available in pdf and paperback.        *
#     *    Complete, revised, and edited pdf reference manuals are also       *
#     *    available.                                                         *
#     *                                                                       *
#     *    Purchasing FreeRTOS documentation will not only help you, by       *
#     *    ensuring you get running as quickly as possible and with an        *
#     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
#     *    the FreeRTOS project to continue with its mission of providing     *
#     *    professional grade, cross platform, de facto standard solutions    *
#     *    for microcontrollers - completely free of charge!                  *
#     *                                                                       *
#     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
#     *                                                                       *
#     *    Thank you for using FreeRTOS, and thank you for your support!      *
#     *                                                                       *
#    ***************************************************************************
#
#
#    This file is part of the FreeRTOS distribution.
#
#    FreeRTOS is free software; you can redistribute it and/or modify it under
#    the terms of the GNU General Public License (version 2) as published by the
#    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
#    >>>NOTE<<< The modification to the GPL is included to allow you to
#    distribute a combined work that includes FreeRTOS without being obliged to
#    provide the source code for proprietary components outside of the FreeRTOS
#    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
#    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
#    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
#    more details. You should have received a copy of the GNU General Public
#    License and the FreeRTOS license exception along with FreeRTOS; if not it
#    can be viewed here: http://www.freertos.org/a00114.html and also obtained
#    by writing to Richard Barry, contact details for whom are available on the
#    FreeRTOS WEB site.
#
#    1 tab == 4 spaces!
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

