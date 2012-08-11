# Demo for GCC/HCS12 port of FreeRTOS
#   Author Jefferson Smith
#
SRCDIR=../..
RTOS_BASEDIR=$(SRCDIR)/Source

# what board to compile for
TARGET_BOARD ?= dragon12-rom
CPU=m68hcs12

DEVC_PREFIX=m6811-elf-
CC=$(DEVC_PREFIX)gcc
AS=$(DEVC_PREFIX)as
AR=$(DEVC_PREFIX)ar
OBJCOPY=$(DEVC_PREFIX)objcopy
OBJDUMP=$(DEVC_PREFIX)objdump

CPPFLAGS+=-I. -I./asm-$(CPU)/arch-dragon12 -I../Common/include \
  -I$(RTOS_BASEDIR)/include -DGCC_HCS12 -DM6812_DEF_SCI=1 -DPORT_LED=M6811_PORTB

CFLAGS+=-$(CPU) -mshort -mlong-calls -g -Os -Wall -Wmissing-prototypes \
  -Wno-char-subscripts -fomit-frame-pointer -msoft-reg-count=0 -mauto-incdec
#-Os -fomit-frame-pointer

LDFLAGS+=-$(CPU) -mshort -mlong-calls -Wl,-T,ldscript-rtos.x

OBJCOPY_FLAGS=--srec-len=0x20 --change-addresses 0xffff0000

CSRCS=main.c startup.c vectors.c serial.c sci.c ParTest.c gelfunc.c \
  ../Common/Minimal/flash.c \
  ../Common/Minimal/dynamic.c \
  ../Common/Minimal/BlockQ.c \
  ../Common/Minimal/PollQ.c \
  ../Common/Minimal/comtest.c \
  ../Common/Minimal/integer.c \
  ../Common/Minimal/death.c \

RTOS_OBJS = $(RTOS_BASEDIR)/portable/GCC/HCS12/port.c \
  $(RTOS_BASEDIR)/portable/MemMang/heap_2.c \
  $(RTOS_BASEDIR)/list.c \
  $(RTOS_BASEDIR)/tasks.c \
  $(RTOS_BASEDIR)/queue.c

OBJS=$(CSRCS:.c=.o) $(RTOS_OBJS:.c=.o)

#
# *.elf for the simulator and gdb
# *.s19 is original S Records from ld
# *.s2 is S2 Records (from SRecCvt.exe)
#
all::	main.elf main.lst main.s19

main.elf:	$(OBJS)
	$(CC) $(LDFLAGS) -o $@ $^ -lc -lbcc -lc

%.lst:	%.elf
	$(OBJDUMP) -htS $< >$@

%.s19:	%.elf
	$(OBJCOPY) --output-target=srec $(OBJCOPY_FLAGS) $< $*.s19

clean::
	$(RM) $(OBJS) *.elf *.s19

