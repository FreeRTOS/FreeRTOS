# Hey Emacs, this is a -*- makefile -*-

# The purpose of this file is to define the build configuration variables used
# by the generic Makefile. See Makefile header for further information.

# Copyright (c) 2007, Atmel Corporation All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# 1. Redistributions of source code must retain the above copyright notice, this
# list of conditions and the following disclaimer.
#
# 2. Redistributions in binary form must reproduce the above copyright notice,
# this list of conditions and the following disclaimer in the documentation and/
# or other materials provided with the distribution.
#
# 3. The name of ATMEL may not be used to endorse or promote products derived
# from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
# WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
# SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
# INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
# BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY
# OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
# NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
# EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.


# Base paths
PRJ_PATH = ../..
APPS_PATH = $(PRJ_PATH)/APPLICATIONS
BRDS_PATH = $(PRJ_PATH)/BOARDS
COMP_PATH = $(PRJ_PATH)/COMPONENTS
DRVR_PATH = $(PRJ_PATH)/DRIVERS
SERV_PATH = $(PRJ_PATH)/SERVICES
UTIL_PATH = $(PRJ_PATH)/UTILS

# Demo paths
FREERTOS_PATH = ../../../..
FREERTOS_PORT_PATH = $(FREERTOS_PATH)/Source/portable/GCC/AVR32_UC3
FREERTOS_MEM_PATH = $(FREERTOS_PATH)/Source/portable/MemMang
DEMO_PATH = ../..
ETH_PATH = $(DEMO_PATH)/NETWORK
WEB_PATH = $(ETH_PATH)/BasicWEB
TFTP_PATH = $(ETH_PATH)/BasicTFTP
SMTP_PATH = $(ETH_PATH)/BasicSMTP
LWIP_PATH = $(FREERTOS_PATH)/Demo/Common/ethernet/lwIP
LWIP_PORT_PATH = $(ETH_PATH)/lwip-port/AT32UC3A

# CPU architecture: {ap|uc}
ARCH = uc

# Part: {none|ap7xxx|uc3xxxxx}
PART = uc3a0512

# Flash memories: [{cfi|internal}@address,size]...
FLASH = internal@0x80000000,512Kb

# Clock source to use when programming: [{xtal|extclk|int}]
PROG_CLOCK = xtal

# Device/Platform/Board include path
PLATFORM_INC_PATH = \
  $(BRDS_PATH)/

# Target name: {*.a|*.elf}
TARGET = lwipdemo.elf

# Definitions: [-D name[=definition]...] [-U name...]
# Things that might be added to DEFS:
#   BOARD             Board used: {EVKxxxx}
#   EXT_BOARD         Extension board used (if any): {EXTxxxx}
DEFS = -D BOARD=EVK1100 -D FREERTOS_USED -D HTTP_USED=1 -D TFTP_USED=1 -D SMTP_USED=0

# Include path
INC_PATH = \
  $(UTIL_PATH)/ \
  $(UTIL_PATH)/PREPROCESSOR/ \
  $(SERV_PATH)/USB/CLASS/DFU/EXAMPLES/ISP/BOOT/ \
  $(DRVR_PATH)/INTC/ \
  $(DRVR_PATH)/TC/ \
  $(DRVR_PATH)/PM/ \
  $(DRVR_PATH)/GPIO/ \
  $(DRVR_PATH)/FLASHC/ \
  $(DRVR_PATH)/MACB/ \
  $(DEMO_PATH)/ \
  $(FREERTOS_PATH)/Source/include/ \
  $(FREERTOS_PATH)/Demo/Common/include/ \
  $(FREERTOS_PORT_PATH)/ \
  $(FREERTOS_MEM_PATH)/ \
  $(ETH_PATH)/ \
  $(LWIP_PATH)/include/ \
  $(LWIP_PATH)/include/ipv4/ \
  $(LWIP_PORT_PATH)/ \
  $(WEB_PATH)/ \
  $(TFTP_PATH)/ \
  $(SMTP_PATH)/

# C source files

LWIP_SRC = \
  $(LWIP_PATH)/core/inet.c \
  $(LWIP_PATH)/core/mem.c \
  $(LWIP_PATH)/core/memp.c \
  $(LWIP_PATH)/core/netif.c \
  $(LWIP_PATH)/core/pbuf.c \
  $(LWIP_PATH)/core/raw.c \
  $(LWIP_PATH)/core/stats.c \
  $(LWIP_PATH)/core/sys.c \
  $(LWIP_PATH)/core/tcp.c \
  $(LWIP_PATH)/core/tcp_in.c \
  $(LWIP_PATH)/core/tcp_out.c \
  $(LWIP_PATH)/core/ipv4/ip.c \
  $(LWIP_PATH)/core/ipv4/ip_addr.c \
  $(LWIP_PATH)/core/ipv4/icmp.c \
  $(LWIP_PATH)/api/sockets.c \
  $(LWIP_PATH)/api/tcpip.c \
  $(LWIP_PATH)/api/api_msg.c \
  $(LWIP_PATH)/api/err.c \
  $(LWIP_PATH)/api/api_lib.c \
  $(LWIP_PATH)/netif/etharp.c \
  $(LWIP_PATH)/core/udp.c \
  $(LWIP_PATH)/core/ipv4/ip_frag.c

CSRCS = \
  $(BRDS_PATH)/EVK1100/led.c \
  $(DRVR_PATH)/INTC/intc.c \
  $(DRVR_PATH)/TC/tc.c \
  $(DRVR_PATH)/PM/pm.c \
  $(DRVR_PATH)/MACB/macb.c \
  $(DRVR_PATH)/GPIO/gpio.c \
  $(DRVR_PATH)/FLASHC/flashc.c \
  $(DEMO_PATH)/main.c \
  $(DEMO_PATH)/PARTEST/ParTest.c \
  $(DEMO_PATH)/SERIAL/serial.c \
  $(FREERTOS_PATH)/Source/tasks.c \
  $(FREERTOS_PATH)/Source/queue.c \
  $(FREERTOS_PATH)/Source/list.c \
  $(FREERTOS_PATH)/Source/croutine.c \
  $(FREERTOS_PATH)/Demo/Common/Minimal/flash.c \
  $(FREERTOS_PORT_PATH)/port.c \
  $(FREERTOS_MEM_PATH)/heap_3.c \
  $(LWIP_SRC) \
  $(LWIP_PORT_PATH)/sys_arch.c \
  $(LWIP_PORT_PATH)/ethernetif.c \
  $(WEB_PATH)/BasicWEB.c \
  $(TFTP_PATH)/BasicTFTP.c \
  $(SMTP_PATH)/BasicSMTP.c \
  $(ETH_PATH)/ethernet.c \
  $(DEMO_PATH)/printf-stdarg.c

# Assembler source files
ASSRCS = \
  $(SERV_PATH)/USB/CLASS/DFU/EXAMPLES/ISP/BOOT/trampoline.S \
  $(FREERTOS_PORT_PATH)/exception.S

# Library path
LIB_PATH =

# Libraries to link with the project
LIBS =

# Linker script file if any
LINKER_SCRIPT = $(UTIL_PATH)/LINKER_SCRIPTS/AT32UC3A/0512/GCC/link_uc3a0512.lds

# Options to request or suppress warnings: [-fsyntax-only] [-pedantic[-errors]] [-w] [-Wwarning...]
# For further details, refer to the chapter "GCC Command Options" of the GCC manual.
WARNINGS = -Wall

# Options for debugging: [-g]...
# For further details, refer to the chapter "GCC Command Options" of the GCC manual.
DEBUG = -g

# Options that control optimization: [-O[0|1|2|3|s]]...
# For further details, refer to the chapter "GCC Command Options" of the GCC manual.
OPTIMIZATION = -O0 -ffunction-sections -fdata-sections

# Extra flags to use when preprocessing
CPP_EXTRA_FLAGS =

# Extra flags to use when compiling
C_EXTRA_FLAGS =

# Extra flags to use when assembling
AS_EXTRA_FLAGS =

# Extra flags to use when linking
LD_EXTRA_FLAGS = -Wl,--gc-sections -Wl,-e,_trampoline

# Documentation path
DOC_PATH = ./DOC/

# Documentation configuration file
DOC_CFG = ./doxyfile.doxygen
