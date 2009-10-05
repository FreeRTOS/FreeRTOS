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







	


