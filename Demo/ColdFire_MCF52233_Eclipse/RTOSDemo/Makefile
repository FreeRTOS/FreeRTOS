RM := rm -rf

# Set the optimisation level - this should be set to 0, 1, 2, 3 or s (s for size).
OPTIM=0

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

# This directory contains the modified uIP code
FREERTOS_uIP_DIR=./../../Common/ethernet/FreeRTOS-uIP

VPATH=		$(FREERTOS_SOURCE_DIR) : \
			$(PORT_SOURCE_DIR) : \
			$(COMMON_DEMO_SOURCE_DIR) : \
			$(FREERTOS_SOURCE_DIR)/portable/MemMang : \
			$(FREERTOS_uIP_DIR) : \
			. : \
			./webserver : \
			./ParTest : \
			./serial


###############################################################################
# Define a few constants to be used during the build.
###############################################################################

OUTPUT_DIR=./bin
CPU=52235
LINKER_SCRIPT=m52235evb-rom-hosted.ld
SREC_FILENAME=RTOSDemo.s19
ELF_FILENAME=RTOSDemo.elf
CC=m68k-elf-gcc
AS=m68K-elf-as
OBJCOPY=m68K-elf-objcopy


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
						$(OUTPUT_DIR)/heap_1.o

# The demo app source files, including the basic WEB server.
Demo_OBJS=				$(OUTPUT_DIR)/main.o \
						$(OUTPUT_DIR)/ParTest.o \
						$(OUTPUT_DIR)/flash.o \
						$(OUTPUT_DIR)/FreeRTOS_Tick_Setup.o \
						$(OUTPUT_DIR)/BlockQ.o \
						$(OUTPUT_DIR)/PollQ.o \
						$(OUTPUT_DIR)/semtest.o \
						$(OUTPUT_DIR)/GenQTest.o \
						$(OUTPUT_DIR)/QPeek.o \
						$(OUTPUT_DIR)/FEC.o \
						$(OUTPUT_DIR)/printf-stdarg.o

HTTP_OBJS=				$(OUTPUT_DIR)/uIP_Task.o \
						$(OUTPUT_DIR)/httpd.o \
						$(OUTPUT_DIR)/httpd-cgi.o \
						$(OUTPUT_DIR)/httpd-fs.o \
						$(OUTPUT_DIR)/http-strings.o

# uIP source files
uIP_OBJS=				$(OUTPUT_DIR)/timer.o \
						$(OUTPUT_DIR)/uip.o \
						$(OUTPUT_DIR)/uip_arp.o \
						$(OUTPUT_DIR)/uiplib.o \
						$(OUTPUT_DIR)/uip-split.o \
						$(OUTPUT_DIR)/psock.o

OBJS = $(FreeRTOS_OBJS) $(Demo_OBJS) $(uIP_OBJS) $(HTTP_OBJS)
			
C_DEPS = $(OBJS:.o=.d)

INCLUDE_PATHS=	-I./webserver \
				-I"$(FREERTOS_uIP_DIR)" \
				-I"$(FREERTOS_SOURCE_DIR)/include" \
				-I"include" \
				-I"$(COMMON_DEMO_SOURCE_DIR)/../include" \
				-I"$(PORT_SOURCE_DIR)" \
				-I./MCF5223x \
				-I.

CFLAGS=		$(INCLUDE_PATHS) \
			-D COLDFIRE_V2_GCC \
			-D PACK_STRUCT_END=__attribute\(\(packed\)\) \
			-D ALIGN_STRUCT_END=__attribute\(\(aligned\(4\)\)\) \
			-O$(OPTIM) \
			-fno-strict-aliasing \
			-g3 \
			-gdwarf-2 \
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

ASFLAGS= 	-m52235 \
			-g3 \
			--register-prefix-optional \
            --bitwise-or

LIBS=

# Add inputs and outputs from these tool invocations to the build variables 

# All Target
all: $(OUTPUT_DIR)/$(SREC_FILENAME)

# Tool invocations 
$(OUTPUT_DIR)/$(SREC_FILENAME): $(OUTPUT_DIR)/$(ELF_FILENAME)
	$(OBJCOPY) $(OUTPUT_DIR)/$(ELF_FILENAME) -O srec $(OUTPUT_DIR)/$(SREC_FILENAME)

$(OUTPUT_DIR)/$(ELF_FILENAME): $(OBJS)
	$(CC) -nostartfiles --gc-sections -Xlinker -Map=$(OUTPUT_DIR)/output.map -mcpu=$(CPU) -T $(LINKER_SCRIPT) -o"$(OUTPUT_DIR)/$(ELF_FILENAME)"  $(OBJS) $(USER_OBJS) $(LIBS)

$(OUTPUT_DIR)/%.o: %.c Makefile
	$(CC) $(CFLAGS)	-o"$@" "$<"

$(OUTPUT_DIR)/%.o: %.S
	$(AS) $(ASFLAGS) -o"$@" "$<"

# Other Targets
clean:
	-$(RM) $(OBJS) $(C_DEPS) $(EXECUTABLES) $(OUTPUT_DIR)/$(ELF_FILENAME) $(OUTPUT_DIR)/$(SREC_FILENAME)
	-@echo ' '

#
# The rule to create the target directory
#
$(OUTPUT_DIR):
	@mkdir $(OUTPUT_DIR)


.PHONY: all clean dependents
.SECONDARY: post-build

-include $(wildcard $(OUTPUT_DIR)/*.d) __dummy__

