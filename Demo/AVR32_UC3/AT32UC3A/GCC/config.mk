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

# CPU architecture: {ap|uc}
ARCH = uc

# Part: {none|ap7000|ap7010|ap7020|uc3a0256|uc3a0512|uc3a1128|uc3a1256|uc3a1512}
PART = uc3a0512

# Flash memories: [type@address,size]...
FLASH = internal@0x80000000,512Kb

# Device/Platform/Board include path
PLATFORM_INC_PATH = \
  $(BRDS_PATH)/

# Target name: {*.a|*.elf}
TARGET = rtosdemo.elf

# Definitions: [-D name[=definition]...] [-U name...]
# Things that might be added to DEFS:
#   BOARD             Board used: {EVK1100}
DEFS = -D BOARD=EVK1100

# Include path
INC_PATH = \
  $(UTIL_PATH)/ \
  $(UTIL_PATH)/PREPROCESSOR/ \
  $(DRVR_PATH)/INTC/ \
  $(DRVR_PATH)/PM/ \
  $(DRVR_PATH)/GPIO/ \
  $(DRVR_PATH)/TC/ \
  ../../../../Source/portable/GCC/AVR32_UC3/ \
  ../../../../Source/include/ \
  ../../../Common/include/ \
  ../../

# C source files
CSRCS = \
  $(BRDS_PATH)/EVK1100/led.c \
  $(DRVR_PATH)/INTC/intc.c \
  $(DRVR_PATH)/PM/pm.c \
  $(DRVR_PATH)/GPIO/gpio.c \
  $(DRVR_PATH)/TC/tc.c \
  ../../../../Source/portable/GCC/AVR32_UC3/port.c \
  ../../../../Source/portable/MemMang/heap_3.c \
  ../../../../Source/list.c \
  ../../../../Source/queue.c \
  ../../../../Source/tasks.c \
  ../../../Common/Minimal/BlockQ.c \
  ../../../Common/Minimal/comtest.c \
  ../../../Common/Minimal/death.c \
  ../../../Common/Minimal/dynamic.c \
  ../../../Common/Minimal/flash.c \
  ../../../Common/Minimal/flop.c \
  ../../../Common/Minimal/integer.c \
  ../../../Common/Minimal/PollQ.c \
  ../../../Common/Minimal/semtest.c \
  ../../ParTest/ParTest.c \
  ../../serial/serial.c \
  ../../main.c

# Assembler source files
ASSRCS = \
  ../../../../Source/portable/GCC/AVR32_UC3/exception.S

# Library path
LIB_PATH =

# Libraries to link with the project
LIBS =

# Linker script file if any
LINKER_SCRIPT =

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
LD_EXTRA_FLAGS = -Wl,--gc-sections

# Documentation path
DOC_PATH = \
  ../../DOC/

# Documentation configuration file
DOC_CFG = \
  ../../doxyfile.doxygen
