#/*
#	FreeRTOS.org V5.3.0 - Copyright (C) 2003-2009 Richard Barry.
#
#	This file is part of the FreeRTOS.org distribution.
#
#	FreeRTOS.org is free software; you can redistribute it and/or modify it
#	under the terms of the GNU General Public License (version 2) as published
#	by the Free Software Foundation and modified by the FreeRTOS exception.
#	**NOTE** The exception to the GPL is included to allow you to distribute a
#	combined work that includes FreeRTOS.org without being obliged to provide
#	the source code for any proprietary components.  Alternative commercial
#	license and support terms are also available upon request.  See the 
#	licensing section of http://www.FreeRTOS.org for full details.
#
#	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
#	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
#	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
#	more details.
#
#	You should have received a copy of the GNU General Public License along
#	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
#	Temple Place, Suite 330, Boston, MA  02111-1307  USA.
#
#
#	***************************************************************************
#	*                                                                         *
#	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
#	*                                                                         *
#	* This is a concise, step by step, 'hands on' guide that describes both   *
#	* general multitasking concepts and FreeRTOS specifics. It presents and   *
#	* explains numerous examples that are written using the FreeRTOS API.     *
#	* Full source code for all the examples is provided in an accompanying    *
#	* .zip file.                                                              *
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








	


