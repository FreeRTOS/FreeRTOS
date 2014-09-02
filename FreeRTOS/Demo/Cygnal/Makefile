#/*
#    FreeRTOS V8.1.2 - Copyright (C) 2014 Real Time Engineers Ltd.
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








	


