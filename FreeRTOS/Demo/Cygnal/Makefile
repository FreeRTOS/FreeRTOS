#/*
# * FreeRTOS V202012.00
# * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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








	


