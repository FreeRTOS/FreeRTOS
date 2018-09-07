#/*
# * FreeRTOS Kernel V10.1.1
# * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

CC=arm-elf-gcc
OBJCOPY=arm-elf-objcopy
ARCH=arm-elf-ar
CRT0=boot.s
DEBUG=-g
OPTIM=-O0
LDSCRIPT=atmel-rom.ld

#
# CFLAGS common to both the THUMB and ARM mode builds
#

CFLAGS= \
-I.  \
-I./EMAC  \
-I../Common/include  \
-I./USB  \
-I./lwip-1.1.0/src/include  \
-I./lwip-1.1.0/contrib/port/FreeRTOS/AT91SAM7X  \
-I../../Source/include  \
-I../../Source/portable/GCC/ARM7_AT91SAM7S  \
-I./lwip-1.1.0/src/include/ipv4 \
-Wall  \
-Wextra  \
-Wstrict-prototypes  \
-Wmissing-prototypes  \
-Wmissing-declarations  \
-Wno-strict-aliasing  \
-D SAM7_GCC  \
-D THUMB_INTERWORK \
-mthumb-interwork \
-mcpu=arm7tdmi  \
-T$(LDSCRIPT) \
$(DEBUG)  \
$(OPTIM) \
-fomit-frame-pointer

THUMB_FLAGS=-mthumb
LINKER_FLAGS=-Xlinker -ortosdemo.elf -Xlinker -M -Xlinker -Map=rtosdemo.map

#
# Source files that can be built to THUMB mode.
#
FREERTOS_THUMB_SRC= \
  ../../Source/tasks.c \
  ../../Source/queue.c \
  ../../Source/list.c \
  ../../Source/portable/GCC/ARM7_AT91SAM7S/port.c

DEMO_APP_THMUB_SRC= \
  ../../Source/portable/MemMang/heap_2.c \
  ParTest/ParTest.c \
  main.c \
  ../Common/Minimal/flash.c \
  ../Common/Minimal/BlockQ.c \
  ../Common/Minimal/integer.c \
  ../Common/Minimal/PollQ.c \
  ../Common/Minimal/semtest.c \
  BasicWEB.c \
  USB/USB-CDC.c 

LWIP_THUMB_SRC= \
  lwip-1.1.0/src/core/tcp_out.c \
  lwip-1.1.0/src/core/inet.c \
  lwip-1.1.0/src/core/mem.c \
  lwip-1.1.0/src/core/memp.c \
  lwip-1.1.0/src/core/netif.c \
  lwip-1.1.0/src/core/pbuf.c \
  lwip-1.1.0/src/core/raw.c \
  lwip-1.1.0/src/core/stats.c \
  lwip-1.1.0/src/core/sys.c \
  lwip-1.1.0/src/core/tcp.c \
  lwip-1.1.0/src/core/tcp_in.c \
  lwip-1.1.0/src/core/ipv4/ip.c \
  lwip-1.1.0/src/core/ipv4/ip_addr.c \
  lwip-1.1.0/src/core/ipv4/icmp.c \
  lwip-1.1.0/src/api/tcpip.c \
  lwip-1.1.0/src/api/api_msg.c \
  lwip-1.1.0/src/api/err.c \
  lwip-1.1.0/src/api/api_lib.c \
  lwip-1.1.0/src/netif/etharp.c \
  lwip-1.1.0/contrib/port/FreeRTOS/AT91SAM7X/sys_arch.c \
  lwip-1.1.0/src/netif/ethernetif.c \
  EMAC/SAM7_EMAC.c \
  lwip-1.1.0/src/core/udp.c \
  lwip-1.1.0/src/core/ipv4/ip_frag.c

#
# Source files that must be built to ARM mode.
#
ARM_SRC= \
  ../../Source/portable/GCC/ARM7_AT91SAM7S/portISR.c \
  EMAC/SAM7_EMAC_ISR.c \
  USB/USBIsr.c \
  Cstartup_SAM7.c  


#
# Define all object files.
#
ARM_OBJ = $(ARM_SRC:.c=.o)
FREERTOS_THUMB_OBJ = $(FREERTOS_THUMB_SRC:.c=.o)
DEMO_APP_THMUB_OBJ = $(DEMO_APP_THMUB_SRC:.c=.o)
LWIP_THUMB_OBJ = $(LWIP_THUMB_SRC:.c=.o)

rtosdemo.bin : rtosdemo.elf
	$(OBJCOPY) rtosdemo.elf -O binary rtosdemo.bin

rtosdemo.hex : rtosdemo.elf
	$(OBJCOPY) rtosdemo.elf -O ihex rtosdemo.hex

rtosdemo.elf : $(ARM_OBJ) $(DEMO_APP_THMUB_OBJ) $(LWIP_THUMB_OBJ) $(FREERTOS_THUMB_OBJ) $(CRT0) Makefile FreeRTOSConfig.h
	$(CC) $(CFLAGS) $(ARM_OBJ) $(DEMO_APP_THMUB_OBJ) $(LWIP_THUMB_OBJ) $(FREERTOS_THUMB_OBJ) -nostartfiles $(CRT0) $(LINKER_FLAGS)

$(DEMO_APP_THMUB_OBJ)  : %.o : %.c $(LDSCRIPT) Makefile FreeRTOSConfig.h
	$(CC) -c $(THUMB_FLAGS) $(CFLAGS) $< -o $@

$(LWIP_THUMB_OBJ)  : %.o : %.c $(LDSCRIPT) Makefile FreeRTOSConfig.h
	$(CC) -c $(THUMB_FLAGS) $(CFLAGS) $< -o $@

$(FREERTOS_THUMB_OBJ)  : %.o : %.c $(LDSCRIPT) Makefile FreeRTOSConfig.h
	$(CC) -c $(THUMB_FLAGS) $(CFLAGS) $< -o $@

$(ARM_OBJ) : %.o : %.c $(LDSCRIPT) Makefile FreeRTOSConfig.h
	$(CC) -c $(CFLAGS) $< -o $@

clean :
	touch Makefile

