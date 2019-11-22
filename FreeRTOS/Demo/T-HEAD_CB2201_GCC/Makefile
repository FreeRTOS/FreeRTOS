#
# FreeRTOS - T-HEAD CK802T port
#
# Copyright (c) 2019 Vincent Cui, Vienna 2019.
#
# Date: 2019/11/21 22:45:48
#
# ---------------------------------------------------------------------------
CC=csky-abiv2-elf-gcc
OBJCOPY=csky-abiv2-elf-objcopy
DEBUG=-g
OPT=-Os

CFLAGS=-c -mcpu=ck802t -Wall $(OPT) $(DEBUG) -Tflash.ld -I. -I./include/cb2201 -I../../Source/include -I../Common/include

# Setup paths to source code
SOURCE_PATH = ../../Source
PORT_PATH = ../../Source/portable/GCC/T-HEAD_CK802T
DEMO_PATH = ../Common/Minimal

#
# Source files
#
SRC = \
main.c \
./cb2201/board.c \
./cb2201/board_sysinit.c \
./cb2201/coretime.c \
./cb2201/isr.c \
./cb2201/minilibc_critical.c \
./cb2201/misc.c \
./cb2201/serial.c \
./cb2201/pinmux.c \
./cb2201/startup.c \
./cb2201/sysinit.c \
./cb2201/vic.c \
$(SOURCE_PATH)/tasks.c \
$(SOURCE_PATH)/list.c \
$(SOURCE_PATH)/queue.c \
$(SOURCE_PATH)/portable/MemMang/heap_3.c \
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


