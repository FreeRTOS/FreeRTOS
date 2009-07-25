#/*
#	FreeRTOS V5.4.1 - Copyright (C) 2009 Real Time Engineers Ltd.
#
#	This file is part of the FreeRTOS distribution.
#
#	FreeRTOS is free software; you can redistribute it and/or modify it	under 
#	the terms of the GNU General Public License (version 2) as published by the 
#	Free Software Foundation and modified by the FreeRTOS exception.
#	**NOTE** The exception to the GPL is included to allow you to distribute a
#	combined work that includes FreeRTOS without being obliged to provide the 
#	source code for proprietary components outside of the FreeRTOS kernel.  
#	Alternative commercial license and support terms are also available upon 
#	request.  See the licensing section of http://www.FreeRTOS.org for full 
#	license details.
#
#	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
#	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
#	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
#	more details.
#
#	You should have received a copy of the GNU General Public License along
#	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
#	Temple Place, Suite 330, Boston, MA  02111-1307  USA.
#
#
#	***************************************************************************
#	*                                                                         *
#	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
#	* See http://www.FreeRTOS.org/Documentation for details                   *
#	*                                                                         *
#	***************************************************************************
#
#	1 tab == 4 spaces!
#
#	Please ensure to read the configuration and relevant port sections of the
#	online documentation.
#
#	http://www.FreeRTOS.org - Documentation, latest information, license and
#	contact details.
#
#	http://www.SafeRTOS.com - A version that is certified for use in safety
#	critical systems.
#
#	http://www.OpenRTOS.com - Commercial support, development, porting,
#	licensing and training services.
#*/


CC=sdcc
NO_OPT=--nogcse --noinvariant --noinduction --nojtbound --noloopreverse --nolabelopt --nooverlay --peep-asm
DEBUG=--debug

CFLAGS=--model-large -I. -I../Common/include -I../include -I../../Source/include \
		-DSDCC_CYGNAL $(DEBUG) --less-pedantic --xram-size 8448 --stack-auto \
		--no-peep --int-long-reent --float-reent

DEMO_DIR = ../Common
SOURCE_DIR = ../../Source
PORT_DIR = ../../Source/portable/SDCC/Cygnal

SRC	= \
ParTest/ParTest.c \
serial/serial.c \
$(DEMO_DIR)/Full/flash.c \
$(DEMO_DIR)/Full/print.c \
$(DEMO_DIR)/Minimal/integer.c \
$(DEMO_DIR)/Minimal/PollQ.c \
$(DEMO_DIR)/Minimal/comtest.c \
$(DEMO_DIR)/Full/semtest.c \
$(SOURCE_DIR)/tasks.c \
$(SOURCE_DIR)/queue.c \
$(SOURCE_DIR)/list.c \
$(SOURCE_DIR)/portable/MemMang/heap_1.c \
$(PORT_DIR)/port.c


# Define all object files.
OBJ = $(SRC:.c=.rel)





######################################
# THIS VERSION WILL ONLY BUILD FILES THAT HAVE CHANGED, BUT MAY HAVE A DANGEROUS
# COMMAND LINE.  IT WORKS FINE UNDER WINDOWS, BUT I HAVE COMMENTED IT OUT IN
# CASE IT CAUSES PROBLEMS ON OTHER SYSTEMS.

#main : main.c Makefile ../../Source/portable/SDCC/Cygnal/portmacro.h $(OBJ)
#	$(CC) $(CFLAGS) main.c $(OBJ)

#%.rel : %.c Makefile ../../Source/portable/SDCC/Cygnal/portmacro.h
#	$(CC) -c $(CFLAGS) -o$< $<





######################################
# INSTEAD OF THE FOUR LINES ABOVE, THIS VERSION CAN BE USED BUT WILL CAUSE ALL
# FILES TO BUILD EVERY TIME.

main : main.c Makefile ../../Source/portable/SDCC/Cygnal/portmacro.h $(OBJ)
	$(CC) $(CFLAGS) main.c $(OBJ)

%.rel : %.c Makefile ../../Source/portable/SDCC/Cygnal/portmacro.h
	$(CC) -c $(CFLAGS) $<








	


