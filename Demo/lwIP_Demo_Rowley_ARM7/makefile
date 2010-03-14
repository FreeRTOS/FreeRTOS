#/*
#    FreeRTOS V6.0.4 - Copyright (C) 2010 Real Time Engineers Ltd.
#
#    ***************************************************************************
#    *                                                                         *
#    * If you are:                                                             *
#    *                                                                         *
#    *    + New to FreeRTOS,                                                   *
#    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
#    *    + Looking for basic training,                                        *
#    *    + Wanting to improve your FreeRTOS skills and productivity           *
#    *                                                                         *
#    * then take a look at the FreeRTOS eBook                                  *
#    *                                                                         *
#    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
#    *                  http://www.FreeRTOS.org/Documentation                  *
#    *                                                                         *
#    * A pdf reference manual is also available.  Both are usually delivered   *
#    * to your inbox within 20 minutes to two hours when purchased between 8am *
#    * and 8pm GMT (although please allow up to 24 hours in case of            *
#    * exceptional circumstances).  Thank you for your support!                *
#    *                                                                         *
#    ***************************************************************************
#
#    This file is part of the FreeRTOS distribution.
#
#    FreeRTOS is free software; you can redistribute it and/or modify it under
#    the terms of the GNU General Public License (version 2) as published by the
#    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
#    ***NOTE*** The exception to the GPL is included to allow you to distribute
#    a combined work that includes FreeRTOS without being obliged to provide the
#    source code for proprietary components outside of the FreeRTOS kernel.
#    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
#    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
#    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

