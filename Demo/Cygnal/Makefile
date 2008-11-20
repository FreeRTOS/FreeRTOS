#	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2008 Richard Barry.
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








	


