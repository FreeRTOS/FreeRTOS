RM := rm -rf

###############################################################################
# List the directories that contain files to be built.
###############################################################################

# These two directories contain the FreeRTOS.org kernel source files.
FREERTOS_SOURCE_DIR=./../../../Source
PORT_SOURCE_DIR=./../../../Source/portable/GCC/ColdFire_V2

# This directory contains the standard demo files that get included in every
# FreeRTOS.org demo.  They define tasks that demonstrate the API usage and 
# test the FreeRTOS.org port.
COMMON_DEMO_SOURCE_DIR=./../../Common/Minimal

# The lwIP stack source files.
LWIP_ROOT_DIR=./../../Common/ethernet/lwIP_130

VPATH=		$(FREERTOS_SOURCE_DIR) : \
			$(PORT_SOURCE_DIR) : \
			$(COMMON_DEMO_SOURCE_DIR) : \
			$(FREERTOS_SOURCE_DIR)/portable/MemMang : \
			. : \
			./ParTest : \
			./serial


###############################################################################
# Define a few constants to be used during the build.
###############################################################################

OUTPUT_DIR=./bin
CPU=528x
LINKER_SCRIPT=m5282evb-dram_code-rambar_data-hosted.ld
OUTPUT_FILENAME=RTOSDemo.elf
CC=m68k-elf-gcc
AS=m68K-elf-as


###############################################################################
# List the files to include in the build.  These files will be located from the
# VPATH defined above.
###############################################################################

# The FreeRTOS.org source files.
FreeRTOS_OBJS=			$(OUTPUT_DIR)/portasm.o \
						$(OUTPUT_DIR)/port.o \
						$(OUTPUT_DIR)/list.o \
						$(OUTPUT_DIR)/tasks.o \
						$(OUTPUT_DIR)/queue.o \
						$(OUTPUT_DIR)/heap_2.o

# The demo app source files.
Demo_OBJS=				$(OUTPUT_DIR)/main.o \
						$(OUTPUT_DIR)/serial.o \
						$(OUTPUT_DIR)/comtest.o \
						$(OUTPUT_DIR)/flash.o \
						$(OUTPUT_DIR)/ParTest.o \
						$(OUTPUT_DIR)/BlockQ.o \
						$(OUTPUT_DIR)/death.o \
						$(OUTPUT_DIR)/integer.o \
						$(OUTPUT_DIR)/PollQ.o \
						$(OUTPUT_DIR)/semtest.o \
						$(OUTPUT_DIR)/GenQTest.o \
						$(OUTPUT_DIR)/QPeek.o \
						$(OUTPUT_DIR)/recmutex.o \
						$(OUTPUT_DIR)/IntQueueTimer.o \
						$(OUTPUT_DIR)/IntQueue.o \
						$(OUTPUT_DIR)/FreeRTOS_Tick_Setup.o

OBJS = $(FreeRTOS_OBJS) $(Demo_OBJS)
			
C_DEPS = $(OBJS:.o=.d)

INCLUDE_PATHS=	-I"$(FREERTOS_SOURCE_DIR)/include" \
				-I"include" \
				-I"$(COMMON_DEMO_SOURCE_DIR)/../include" \
				-I"$(PORT_SOURCE_DIR)" \
				-I./MCF5282 \
				-I.

CFLAGS=		$(INCLUDE_PATHS) \
			-D COLDFIRE_V2_GCC \
			-Os \
			-fno-strict-aliasing \
			-g1 \
			-Wall \
			-Wextra \
			-c \
			-ffunction-sections \
			-fdata-sections \
			-fmessage-length=0 \
			-funsigned-char \
			-Wextra \
			-mcpu=$(CPU) \
			-MMD \
			-MP \
			-MF"$(@:%.o=%.d)" \
			-MT"$(@:%.o=%.d)"

ASFLAGS= 	-m528x \
			-g3 \
			--register-prefix-optional \
            --bitwise-or

LIBS=

# Add inputs and outputs from these tool invocations to the build variables 

# All Target
all: $(OUTPUT_DIR)/$(OUTPUT_FILENAME)

# Tool invocations 
$(OUTPUT_DIR)/$(OUTPUT_FILENAME): $(OBJS)
	$(CC) -nostartfiles --gc-sections -Xlinker -Map=$(OUTPUT_DIR)/output.map -mcpu=$(CPU) -T $(LINKER_SCRIPT) -o"$(OUTPUT_DIR)/$(OUTPUT_FILENAME)"  $(OBJS) $(USER_OBJS) $(LIBS)

$(OUTPUT_DIR)/%.o: %.c Makefile
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

