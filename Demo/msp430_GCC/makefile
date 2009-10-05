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


CC=msp430-gcc
OBJCOPY=msp430-objcopy
DEBUG=-g
OPT=-Os
WARNINGS=-Wall -Wshadow -Wpointer-arith -Wbad-function-cast -Wcast-align -Wsign-compare \
		-Waggregate-return -Wstrict-prototypes -Wmissing-prototypes -Wmissing-declarations -Wunused

CFLAGS=-mmcu=msp430x449 $(OPT) $(DEBUG) -I. -I../../Source/include -I../Common/include -DGCC_MSP430 $(WARNINGS)

# Setup paths to source code
SOURCE_PATH = ../../Source
PORT_PATH = ../../Source/portable/GCC/MSP430F449
DEMO_PATH = ../Common/Minimal

#
# Source files that can be built to THUMB mode.
#
SRC = \
main.c \
ParTest/ParTest.c \
serial/serial.c \
$(SOURCE_PATH)/tasks.c \
$(SOURCE_PATH)/list.c \
$(SOURCE_PATH)/queue.c \
$(SOURCE_PATH)/portable/MemMang/heap_1.c \
$(PORT_PATH)/port.c \
$(DEMO_PATH)/flash.c \
$(DEMO_PATH)/integer.c \
$(DEMO_PATH)/comtest.c \
$(DEMO_PATH)/PollQ.c

#
# Define all object files.
#
OBJ = $(SRC:.c=.o)

a.out : $(OBJ) makefile
	$(CC) $(OBJ) $(CFLAGS)

$(OBJ) : %.o : %.c makefile
	$(CC) -c $(CFLAGS) $< -o $@	
	
clean :
	touch makefile
	








	


