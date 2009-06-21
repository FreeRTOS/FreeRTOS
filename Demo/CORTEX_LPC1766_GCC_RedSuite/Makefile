#/*
#	FreeRTOS.org V5.3.1 - Copyright (C) 2003-2009 Richard Barry.
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

RM := rm -rf

# Set the optimisation level - this should be set to 0, 1, 2, 3 or s (s for size).
OPTIM=1

# Set the debug level
DEBUG=-g3

###############################################################################
# List the directories that contain files to be built.
###############################################################################

# These two directories contain the FreeRTOS.org kernel source files.
FREERTOS_SOURCE_DIR=./../../Source
PORT_SOURCE_DIR=./../../Source/portable/GCC/ARM_CM3

# This directory contains the standard demo files that get included in every
# FreeRTOS.org demo.  They define tasks that demonstrate the API usage and 
# test the FreeRTOS.org port.
COMMON_DEMO_SOURCE_DIR=./../Common/Minimal

# The uIP stack source files.
uIP_ROOT_DIR=./../Common/ethernet/uIP/uip-1.0/uip

VPATH=		$(FREERTOS_SOURCE_DIR) : \
			$(PORT_SOURCE_DIR) : \
			$(COMMON_DEMO_SOURCE_DIR) : \
			$(FREERTOS_SOURCE_DIR)/portable/MemMang : \
			$(uIP_ROOT_DIR) : \
			. : \
			./webserver : \
			./LCD


###############################################################################
# Define a few constants to be used during the build.
###############################################################################

OUTPUT_DIR=./bin
OUTPUT_FILENAME=RTOSDemo.axf
CC=arm-none-eabi-gcc
OBJCOPY=arm-none-eabi-objcopy
LINKER_SCRIPT=rtosdemo_lpc1766.ld

###############################################################################
# List the files to include in the build.  These files will be located from the
# VPATH defined above.
###############################################################################

# The FreeRTOS.org source files.
FreeRTOS_OBJS=			$(OUTPUT_DIR)/port.o \
						$(OUTPUT_DIR)/list.o \
						$(OUTPUT_DIR)/tasks.o \
						$(OUTPUT_DIR)/queue.o \
						$(OUTPUT_DIR)/heap_2.o

# The demo app source files.
Demo_OBJS=				$(OUTPUT_DIR)/main.o \
						$(OUTPUT_DIR)/BlockQ.o \
						$(OUTPUT_DIR)/integer.o \
						$(OUTPUT_DIR)/PollQ.o \
						$(OUTPUT_DIR)/semtest.o \
						$(OUTPUT_DIR)/GenQTest.o \
						$(OUTPUT_DIR)/QPeek.o \
						$(OUTPUT_DIR)/recmutex.o \
						$(OUTPUT_DIR)/portlcd.o \
						$(OUTPUT_DIR)/blocktim.o \
						$(OUTPUT_DIR)/printf-stdarg.o \
						$(OUTPUT_DIR)/cr_startup_nxp_cm3.o \
						$(OUTPUT_DIR)/LED.o \
						$(OUTPUT_DIR)/syscalls.o # This is just a dummy.
						
# The TCP/IP and WEB server files.
WEB_OBJS=				$(OUTPUT_DIR)/uip_arp.o \
						$(OUTPUT_DIR)/psock.o \
						$(OUTPUT_DIR)/timer.o \
						$(OUTPUT_DIR)/uip.o \
						$(OUTPUT_DIR)/uIP_Task.o \
						$(OUTPUT_DIR)/emac.o \
						$(OUTPUT_DIR)/httpd.o \
						$(OUTPUT_DIR)/httpd-cgi.o \
						$(OUTPUT_DIR)/httpd-fs.o \
						$(OUTPUT_DIR)/http-strings.o



OBJS = $(FreeRTOS_OBJS) $(Demo_OBJS) $(WEB_OBJS)
			
C_DEPS = $(OBJS:.o=.d)

INCLUDE_PATHS=	-I"$(FREERTOS_SOURCE_DIR)/include" \
				-I"include" \
				-I"$(COMMON_DEMO_SOURCE_DIR)/../include" \
				-I"$(PORT_SOURCE_DIR)" \
				-I"$(uIP_ROOT_DIR)" \
				-I./LCD \
				-I./webserver \
				-I.

CFLAGS=		$(INCLUDE_PATHS) \
			-O$(OPTIM) \
			-mthumb \
			-mcpu=cortex-m3 \
			-fno-builtin \
			-D PACK_STRUCT_END=__attribute\(\(packed\)\) \
			-D ALIGN_STRUCT_END=__attribute\(\(aligned\(4\)\)\)	\
			-fno-strict-aliasing \
			$(DEBUG) \
			-Wall \
			-c \
			-ffunction-sections \
			-fdata-sections \
			-fmessage-length=0 \
			-funsigned-char \
			-Wextra \
			-MMD \
			-MP \
			-MF"$(@:%.o=%.d)" \
			-MT"$(@:%.o=%.d)"

ASFLAGS= 	

LIBS=

# Add inputs and outputs from these tool invocations to the build variables 

# All Target
all: $(OUTPUT_DIR)/$(OUTPUT_FILENAME)

# Tool invocations 
$(OUTPUT_DIR)/$(OUTPUT_FILENAME): $(OBJS)
	$(CC) -nostdlib -mthumb -nostartfiles --no-gc-sections -Xlinker -Map=$(OUTPUT_DIR)/output.map -mcpu=$(CPU) -T $(LINKER_SCRIPT) -o"$(OUTPUT_DIR)/$(OUTPUT_FILENAME)"  $(OBJS) $(USER_OBJS) $(LIBS)

$(OUTPUT_DIR)/%.o: %.c Makefile FreeRTOSConfig.h
	$(CC) $(CFLAGS)	-o"$@" "$<"

$(OUTPUT_DIR)/%.o: %.S
	$(AS) $(ASFLAGS) -o"$@" "$<"

# Other Targets
clean:
	-$(RM) $(OBJS) $(C_DEPS) $(EXECUTABLES) $(OUTPUT_DIR)/$(OUTPUT_FILENAME)
	-@echo ' '

#
# The rule to create the target directory
#
$(OUTPUT_DIR):
	@mkdir $(OUTPUT_DIR)


.PHONY: all clean dependents
.SECONDARY: post-build

-include $(wildcard $(OUTPUT_DIR)/*.d) __dummy__

