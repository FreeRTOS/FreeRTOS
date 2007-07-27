# Hey Emacs, this is a -*- makefile -*-

# Goals available on make command line:
#
# [all]                   Default goal: build the project.
# clean                   Clean up the project.
# rebuild                 Rebuild the project.
# ccversion               Display CC version information.
# cppfiles  file.i        Generate preprocessed files from C source files.
# asfiles   file.x        Generate preprocessed assembler files from C and assembler source files.
# objfiles  file.o        Generate object files from C and assembler source files.
# a         file.a        Archive: create A output file from object files.
# elf       file.elf      Link: create ELF output file from object files.
# lss       file.lss      Create extended listing from target output file.
# sym       file.sym      Create symbol table from target output file.
# hex       file.hex      Create Intel HEX image from ELF output file.
# bin       file.bin      Create binary image from ELF output file.
# sizes                   Display target size information.
# isp                     Use ISP instead of JTAGICE mkII when programming.
# cpuinfo                 Get CPU information.
# halt                    Stop CPU execution.
# chiperase               Perform a JTAG Chip Erase command.
# erase                   Perform a flash chip erase.
# program                 Program MCU memory from ELF output file.
# secureflash             Protect chip by setting security bit.
# reset                   Reset MCU.
# debug                   Open a debug connection with the MCU.
# run                     Start CPU execution.
# readregs                Read CPU registers.
# doc                     Build the documentation.
# cleandoc                Clean up the documentation.
# rebuilddoc              Rebuild the documentation.
# verbose                 Display main executed commands.

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


# ** ** ** *** ** ** ** ** ** ** ** ** ** ** **
# ENVIRONMENT SETTINGS
# ** ** ** *** ** ** ** ** ** ** ** ** ** ** **

FirstWord = $(if $(1),$(word 1,$(1)))
LastWord  = $(if $(1),$(word $(words $(1)),$(1)))

MAKE      = make
MAKECFG   = config.mk
TGTTYPE   = $(suffix $(TARGET))
TGTFILE   = $(PART)-$(TARGET)

RM        = rm -Rf

AR        = avr32-ar
ARFLAGS   = rcs

CPP       = $(CC) -E
CPPFLAGS  = -march=$(ARCH) -mpart=$(PART) $(WARNINGS) $(DEFS) \
            $(PLATFORM_INC_PATH:%=-I%) $(INC_PATH:%=-I%) $(CPP_EXTRA_FLAGS)
DPNDFILES = $(CSRCS:.c=.d) $(ASSRCS:.S=.d)
CPPFILES  = $(CSRCS:.c=.i)

CC        = avr32-gcc
CFLAGS    = $(DEBUG) $(OPTIMIZATION) $(C_EXTRA_FLAGS) \
            $(PLATFORM_INC_PATH:%=-Wa,-I%) $(INC_PATH:%=-Wa,-I%) $(AS_EXTRA_FLAGS)
ASFILES   = $(CSRCS:.c=.x) $(ASSRCS:.S=.x)

AS        = avr32-as
ASFLAGS   = $(DEBUG) \
            $(PLATFORM_INC_PATH:%=-Wa,-I%) $(INC_PATH:%=-Wa,-I%) $(AS_EXTRA_FLAGS)
OBJFILES  = $(CSRCS:.c=.o) $(ASSRCS:.S=.o)

LD        = avr32-ld
LDFLAGS   = -march=$(ARCH) -mpart=$(PART) \
            $(LIB_PATH:%=-L%) $(LINKER_SCRIPT:%=-T%) $(LD_EXTRA_FLAGS)
LOADLIBES =
LDLIBS    = $(LIBS:%=-l%)

OBJDUMP   = avr32-objdump
LSS       = $(TGTFILE:$(TGTTYPE)=.lss)

NM        = avr32-nm
SYM       = $(TGTFILE:$(TGTTYPE)=.sym)

OBJCOPY   = avr32-objcopy
HEX       = $(TGTFILE:$(TGTTYPE)=.hex)
BIN       = $(TGTFILE:$(TGTTYPE)=.bin)

SIZE      = avr32-size

SLEEP     = sleep
SLEEPUSB  = 9

PROGRAM   = avr32program

ISP       = batchisp
ISPFLAGS  = -device at32$(PART) -hardware usb -operation

DBGPROXY  = avr32gdbproxy

DOCGEN    = doxygen


# ** ** ** *** ** ** ** ** ** ** ** ** ** ** **
# MESSAGES
# ** ** ** *** ** ** ** ** ** ** ** ** ** ** **

ERR_TARGET_TYPE       = Target type not supported: `$(TGTTYPE)'
MSG_CLEANING          = Cleaning project.
MSG_PREPROCESSING     = Preprocessing \`$<\' to \`$@\'.
MSG_COMPILING         = Compiling \`$<\' to \`$@\'.
MSG_ASSEMBLING        = Assembling \`$<\' to \`$@\'.
MSG_ARCHIVING         = Archiving to \`$@\'.
MSG_LINKING           = Linking to \`$@\'.
MSG_EXTENDED_LISTING  = Creating extended listing to \`$@\'.
MSG_SYMBOL_TABLE      = Creating symbol table to \`$@\'.
MSG_IHEX_IMAGE        = Creating Intel HEX image to \`$@\'.
MSG_BINARY_IMAGE      = Creating binary image to \`$@\'.
MSG_GETTING_CPU_INFO  = Getting CPU information.
MSG_HALTING           = Stopping CPU execution.
MSG_ERASING_CHIP      = Performing a JTAG Chip Erase command.
MSG_ERASING           = Performing a flash chip erase.
MSG_PROGRAMMING       = Programming MCU memory from \`$(TGTFILE)\'.
MSG_SECURING_FLASH    = Protecting chip by setting security bit.
MSG_RESETTING         = Resetting MCU.
MSG_DEBUGGING         = Opening debug connection with MCU.
MSG_RUNNING           = Starting CPU execution.
MSG_READING_CPU_REGS  = Reading CPU registers.
MSG_CLEANING_DOC      = Cleaning documentation.
MSG_GENERATING_DOC    = Generating documentation to \`$(DOC_PATH)\'.


# ** ** ** *** ** ** ** ** ** ** ** ** ** ** **
# MAKE RULES
# ** ** ** *** ** ** ** ** ** ** ** ** ** ** **

# Include the make configuration file.
include $(MAKECFG)

# ** ** TOP-LEVEL RULES ** **

# Default goal: build the project.
ifeq ($(TGTTYPE),.a)
.PHONY: all
all: ccversion a lss sym sizes
else
ifeq ($(TGTTYPE),.elf)
.PHONY: all
all: ccversion elf lss sym hex bin sizes
else
$(error $(ERR_TARGET_TYPE))
endif
endif

# Clean up the project.
.PHONY: clean
clean:
	@echo $(MSG_CLEANING)
	-$(VERBOSE_CMD)$(RM) $(BIN)
	-$(VERBOSE_CMD)$(RM) $(HEX)
	-$(VERBOSE_CMD)$(RM) $(SYM)
	-$(VERBOSE_CMD)$(RM) $(LSS)
	-$(VERBOSE_CMD)$(RM) $(TGTFILE)
	-$(VERBOSE_CMD)$(RM) $(OBJFILES)
	-$(VERBOSE_CMD)$(RM) $(ASFILES)
	-$(VERBOSE_CMD)$(RM) $(CPPFILES)
	-$(VERBOSE_CMD)$(RM) $(DPNDFILES)
	$(VERBOSE_NL)

# Rebuild the project.
.PHONY: rebuild
rebuild: clean all

# Display CC version information.
.PHONY: ccversion
ccversion:
	@echo
	@echo
	@$(CC) --version

# Generate preprocessed files from C source files.
.PHONY: cppfiles
cppfiles: $(CPPFILES)

# Generate preprocessed assembler files from C and assembler source files.
.PHONY: asfiles
asfiles: $(ASFILES)

# Generate object files from C and assembler source files.
.PHONY: objfiles
objfiles: $(OBJFILES)

ifeq ($(TGTTYPE),.a)
# Archive: create A output file from object files.
.PHONY: a
a: $(TGTFILE)
else
ifeq ($(TGTTYPE),.elf)
# Link: create ELF output file from object files.
.PHONY: elf
elf: $(TGTFILE)
endif
endif

# Create extended listing from target output file.
.PHONY: lss
lss: $(LSS)

# Create symbol table from target output file.
.PHONY: sym
sym: $(SYM)

ifeq ($(TGTTYPE),.elf)

# Create Intel HEX image from ELF output file.
.PHONY: hex
hex: $(HEX)

# Create binary image from ELF output file.
.PHONY: bin
bin: $(BIN)

endif

# Display target size information.
.PHONY: sizes
sizes: $(TGTFILE)
	@echo
	@echo
ifeq ($(TGTTYPE),.a)
	@$(SIZE) -Bxt $<
else
ifeq ($(TGTTYPE),.elf)
	@$(SIZE) -Ax $<
	@$(SIZE) -Bx $<
endif
endif
	@echo
	@echo

ifeq ($(TGTTYPE),.elf)

# Use ISP instead of JTAGICE mkII when programming.
.PHONY: isp
ifeq ($(filter-out isp verbose,$(MAKECMDGOALS)),)
isp: all
else
isp:
	@:
endif

ifeq ($(findstring isp,$(MAKECMDGOALS)),)

# Get CPU information.
.PHONY: cpuinfo
cpuinfo:
	@echo
	@echo $(MSG_GETTING_CPU_INFO)
	$(VERBOSE_CMD)$(PROGRAM) cpuinfo
ifneq ($(call LastWord,$(filter cpuinfo chiperase erase program secureflash reset debug run readregs,$(MAKECMDGOALS))),cpuinfo)
	@$(SLEEP) $(SLEEPUSB)
else
	@echo
endif

# Stop CPU execution.
.PHONY: halt
halt:
ifeq ($(filter cpuinfo chiperase erase program secureflash reset run readregs,$(MAKECMDGOALS)),)
	@echo
	@echo $(MSG_HALTING)
	$(VERBOSE_CMD)$(PROGRAM) halt
ifneq ($(call LastWord,$(filter halt debug,$(MAKECMDGOALS))),halt)
	@$(SLEEP) $(SLEEPUSB)
else
	@echo
endif
else
	@:
endif

# Perform a JTAG Chip Erase command.
.PHONY: chiperase
chiperase:
	@echo
	@echo $(MSG_ERASING_CHIP)
	$(VERBOSE_CMD)$(PROGRAM) chiperase
ifneq ($(call LastWord,$(filter cpuinfo chiperase program secureflash reset debug run readregs,$(MAKECMDGOALS))),chiperase)
	@$(SLEEP) $(SLEEPUSB)
else
	@echo
endif

# Perform a flash chip erase.
.PHONY: erase
erase:
ifeq ($(filter chiperase program,$(MAKECMDGOALS)),)
	@echo
	@echo $(MSG_ERASING)
	$(VERBOSE_CMD)$(PROGRAM) erase $(FLASH:%=-f%)
ifneq ($(call LastWord,$(filter cpuinfo erase secureflash reset debug run readregs,$(MAKECMDGOALS))),erase)
	@$(SLEEP) $(SLEEPUSB)
else
	@echo
endif
else
	@:
endif

# Program MCU memory from ELF output file.
.PHONY: program
program: all
	@echo
	@echo $(MSG_PROGRAMMING)
	$(VERBOSE_CMD)$(PROGRAM) program $(FLASH:%=-f%) $(PROG_CLOCK:%=-c%) -e -v -R $(if $(findstring run,$(MAKECMDGOALS)),-r) $(TGTFILE)
ifneq ($(call LastWord,$(filter cpuinfo chiperase program secureflash debug readregs,$(MAKECMDGOALS))),program)
	@$(SLEEP) $(SLEEPUSB)
else
	@echo
endif

# Protect chip by setting security bit.
.PHONY: secureflash
secureflash:
	@echo
	@echo $(MSG_SECURING_FLASH)
	$(VERBOSE_CMD)$(PROGRAM) secureflash
ifneq ($(call LastWord,$(filter cpuinfo chiperase erase program secureflash reset debug run readregs,$(MAKECMDGOALS))),secureflash)
	@$(SLEEP) $(SLEEPUSB)
else
	@echo
endif

# Reset MCU.
.PHONY: reset
reset:
ifeq ($(filter program run,$(MAKECMDGOALS)),)
	@echo
	@echo $(MSG_RESETTING)
	$(VERBOSE_CMD)$(PROGRAM) reset
ifneq ($(call LastWord,$(filter cpuinfo chiperase erase secureflash reset debug readregs,$(MAKECMDGOALS))),reset)
	@$(SLEEP) $(SLEEPUSB)
else
	@echo
endif
else
	@:
endif

# Open a debug connection with the MCU.
.PHONY: debug
debug:
	@echo
	@echo $(MSG_DEBUGGING)
	$(VERBOSE_CMD)$(DBGPROXY) $(FLASH:%=-f%)
ifneq ($(call LastWord,$(filter cpuinfo halt chiperase erase program secureflash reset debug run readregs,$(MAKECMDGOALS))),debug)
	@$(SLEEP) $(SLEEPUSB)
else
	@echo
endif

# Start CPU execution.
.PHONY: run
run:
ifeq ($(findstring program,$(MAKECMDGOALS)),)
	@echo
	@echo $(MSG_RUNNING)
	$(VERBOSE_CMD)$(PROGRAM) run $(if $(findstring reset,$(MAKECMDGOALS)),-R)
ifneq ($(call LastWord,$(filter cpuinfo chiperase erase secureflash debug run readregs,$(MAKECMDGOALS))),run)
	@$(SLEEP) $(SLEEPUSB)
else
	@echo
endif
else
	@:
endif

# Read CPU registers.
.PHONY: readregs
readregs:
	@echo
	@echo $(MSG_READING_CPU_REGS)
	$(VERBOSE_CMD)$(PROGRAM) readregs
ifneq ($(call LastWord,$(filter cpuinfo chiperase erase program secureflash reset debug run readregs,$(MAKECMDGOALS))),readregs)
	@$(SLEEP) $(SLEEPUSB)
else
	@echo
endif

else

# Perform a flash chip erase.
.PHONY: erase
erase:
ifeq ($(findstring program,$(MAKECMDGOALS)),)
	@echo
	@echo $(MSG_ERASING)
	$(VERBOSE_CMD)$(ISP) $(ISPFLAGS) erase f memory flash blankcheck
ifeq ($(call LastWord,$(filter erase secureflash debug run,$(MAKECMDGOALS))),erase)
	@echo
endif
else
	@:
endif

# Program MCU memory from ELF output file.
.PHONY: program
program: all
	@echo
	@echo $(MSG_PROGRAMMING)
	$(VERBOSE_CMD)$(ISP) $(ISPFLAGS) erase f memory flash blankcheck loadbuffer $(TGTFILE) program verify $(if $(findstring run,$(MAKECMDGOALS)),$(if $(findstring secureflash,$(MAKECMDGOALS)),,start $(if $(findstring reset,$(MAKECMDGOALS)),,no)reset 0))
ifeq ($(call LastWord,$(filter program secureflash debug,$(MAKECMDGOALS))),program)
	@echo
endif

# Protect chip by setting security bit.
.PHONY: secureflash
secureflash:
	@echo
	@echo $(MSG_SECURING_FLASH)
	$(VERBOSE_CMD)$(ISP) $(ISPFLAGS) memory security addrange 0x0 0x0 fillbuffer 0x01 program $(if $(findstring run,$(MAKECMDGOALS)),start $(if $(findstring reset,$(MAKECMDGOALS)),,no)reset 0)
ifeq ($(call LastWord,$(filter erase program secureflash debug,$(MAKECMDGOALS))),secureflash)
	@echo
endif

# Reset MCU.
.PHONY: reset
reset:
	@:

# Open a debug connection with the MCU.
.PHONY: debug
debug:
	@echo
	@echo $(MSG_DEBUGGING)
	$(VERBOSE_CMD)$(DBGPROXY) $(FLASH:%=-f%)
ifeq ($(call LastWord,$(filter erase program secureflash debug run,$(MAKECMDGOALS))),debug)
	@echo
endif

# Start CPU execution.
.PHONY: run
run:
ifeq ($(filter program secureflash,$(MAKECMDGOALS)),)
	@echo
	@echo $(MSG_RUNNING)
	$(VERBOSE_CMD)$(ISP) $(ISPFLAGS) start $(if $(findstring reset,$(MAKECMDGOALS)),,no)reset 0
ifeq ($(call LastWord,$(filter erase debug run,$(MAKECMDGOALS))),run)
	@echo
endif
else
	@:
endif

endif

endif

# Build the documentation.
.PHONY: doc
doc:
	@echo
	@echo $(MSG_GENERATING_DOC)
	$(VERBOSE_CMD)cd $(dir $(DOC_CFG)) && $(DOCGEN) $(notdir $(DOC_CFG))
	@echo

# Clean up the documentation.
.PHONY: cleandoc
cleandoc:
	@echo $(MSG_CLEANING_DOC)
	-$(VERBOSE_CMD)$(RM) $(DOC_PATH)
	$(VERBOSE_NL)

# Rebuild the documentation.
.PHONY: rebuilddoc
rebuilddoc: cleandoc doc

# Display main executed commands.
.PHONY: verbose
ifeq ($(filter-out isp verbose,$(MAKECMDGOALS)),)
verbose: all
else
verbose:
	@:
endif
ifneq ($(findstring verbose,$(MAKECMDGOALS)),)
# Prefix displaying the following command if and only if verbose is a goal.
VERBOSE_CMD =
# New line displayed if and only if verbose is a goal.
VERBOSE_NL  = @echo
else
VERBOSE_CMD = @
VERBOSE_NL  =
endif

# ** ** COMPILATION RULES ** **

# Include silently the dependency files.
-include $(DPNDFILES)

# The dependency files are not built alone but along with first generation files.
$(DPNDFILES):

# First generation files depend on make files.
$(CPPFILES) $(ASFILES) $(OBJFILES): Makefile $(MAKECFG)

ifeq ($(TGTTYPE),.elf)
# Files resulting from linking depend on linker script.
$(TGTFILE): $(LINKER_SCRIPT)
endif

# Preprocess: create preprocessed files from C source files.
%.i: %.c %.d
	@echo $(MSG_PREPROCESSING)
	$(VERBOSE_CMD)$(CPP) $(CPPFLAGS) -MD -MP -MT '$*.i $*.x $*.o' -o $@ $<
	@touch $*.d
	@touch $@
	$(VERBOSE_NL)

# Preprocess & compile: create assembler files from C source files.
%.x: %.c %.d
	@echo $(MSG_COMPILING)
	$(VERBOSE_CMD)$(CC) -S $(CPPFLAGS) -MD -MP -MT '$*.i $*.o' $(CFLAGS) -o $@ $<
	@touch $*.d
	@touch $@
	$(VERBOSE_NL)

# Preprocess: create preprocessed files from assembler source files.
%.x: %.S %.d
	@echo $(MSG_PREPROCESSING)
	$(VERBOSE_CMD)$(CPP) $(CPPFLAGS) -MD -MP -MT '$*.x $*.o' -o $@ $<
	@touch $*.d
	@touch $@
	$(VERBOSE_NL)

# Preprocess, compile & assemble: create object files from C source files.
%.o: %.c %.d
	@echo $(MSG_COMPILING)
	$(VERBOSE_CMD)$(CC) -c $(CPPFLAGS) -MD -MP -MT '$*.i $*.x' $(CFLAGS) -o $@ $<
	@touch $*.d
	@touch $@
	$(VERBOSE_NL)

# Preprocess & assemble: create object files from assembler source files.
%.o: %.S %.d
	@echo $(MSG_ASSEMBLING)
	$(VERBOSE_CMD)$(CC) -c $(CPPFLAGS) -MD -MP -MT '$*.x' $(ASFLAGS) -o $@ $<
	@touch $*.d
	@touch $@
	$(VERBOSE_NL)

.PRECIOUS: $(OBJFILES)
ifeq ($(TGTTYPE),.a)
# Archive: create A output file from object files.
.SECONDARY: $(TGTFILE)
$(TGTFILE): $(OBJFILES)
	@echo $(MSG_ARCHIVING)
	$(VERBOSE_CMD)$(AR) $(ARFLAGS) $@ $(filter %.o,$+)
	$(VERBOSE_NL)
else
ifeq ($(TGTTYPE),.elf)
# Link: create ELF output file from object files.
.SECONDARY: $(TGTFILE)
$(TGTFILE): $(OBJFILES)
	@echo $(MSG_LINKING)
	$(VERBOSE_CMD)$(CC) $(LDFLAGS) $(filter %.o,$+) $(LOADLIBES) $(LDLIBS) -o $@
	$(VERBOSE_NL)
endif
endif

# Create extended listing from target output file.
$(LSS): $(TGTFILE)
	@echo $(MSG_EXTENDED_LISTING)
	$(VERBOSE_CMD)$(OBJDUMP) -h -S $< > $@
	$(VERBOSE_NL)

# Create symbol table from target output file.
$(SYM): $(TGTFILE)
	@echo $(MSG_SYMBOL_TABLE)
	$(VERBOSE_CMD)$(NM) -n $< > $@
	$(VERBOSE_NL)

ifeq ($(TGTTYPE),.elf)

# Create Intel HEX image from ELF output file.
$(HEX): $(TGTFILE)
	@echo $(MSG_IHEX_IMAGE)
	$(VERBOSE_CMD)$(OBJCOPY) -O ihex $< $@
	$(VERBOSE_NL)

# Create binary image from ELF output file.
$(BIN): $(TGTFILE)
	@echo $(MSG_BINARY_IMAGE)
	$(VERBOSE_CMD)$(OBJCOPY) -O binary $< $@
	$(VERBOSE_NL)

endif
