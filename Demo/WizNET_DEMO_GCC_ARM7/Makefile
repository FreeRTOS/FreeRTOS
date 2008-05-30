#	FreeRTOS.org V5.0.2 - Copyright (C) 2003-2008 Richard Barry.
#
#	This file is part of the FreeRTOS.org distribution.
#
#	FreeRTOS.org is free software; you can redistribute it and/or modify
#	it under the terms of the GNU General Public License as published by
#	the Free Software Foundation; either version 2 of the License, or
#	(at your option) any later version.
#
#	FreeRTOS.org is distributed in the hope that it will be useful,
#	but WITHOUT ANY WARRANTY; without even the implied warranty of
#	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#	GNU General Public License for more details.
#
#	You should have received a copy of the GNU General Public License
#	along with FreeRTOS.org; if not, write to the Free Software
#	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
#
#	A special exception to the GPL can be applied should you wish to distribute
#	a combined work that includes FreeRTOS.org, without being obliged to provide
#	the source code for any proprietary components.  See the licensing section 
#	of http://www.FreeRTOS.org for full details of how and when the exception
#	can be applied.
#
#	***************************************************************************
#	See http://www.FreeRTOS.org for documentation, latest information, license 
#	and contact details.  Please ensure to read the configuration and relevant 
#	port sections of the online documentation.
#	***************************************************************************


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







	


