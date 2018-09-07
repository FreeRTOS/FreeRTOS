# ----------------------------------------------------------------------------
#         SAM Software Package License
# ----------------------------------------------------------------------------
# Copyright (c) 2013, Atmel Corporation
#
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# - Redistributions of source code must retain the above copyright notice,
# this list of conditions and the disclaimer below.
#
# Atmel's name may not be used to endorse or promote products derived from
# this software without specific prior written permission.
#
# DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
# IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
# DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
# INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
# OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
# LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
# NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
# EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
# ----------------------------------------------------------------------------

ifeq ($(CONFIG_SOC_SAMA5D2),y)

CFLAGS_INC += -I$(TOP)/target/sama5d2

gnu-debug-lib-y ?= $(TOP)/target/sama5d2/toolchain/gnu/common.gdb
gnu-cstartup-y ?= target/sama5d2/toolchain/gnu/cstartup.S
iar-cstartup-y ?= target/sama5d2/toolchain/iar/cstartup.s

ifeq ($(VARIANT),sram)
gnu-linker-script-y ?= $(TOP)/target/sama5d2/toolchain/gnu/sram.ld
gnu-debug-script-y ?= $(TOP)/target/sama5d2/toolchain/gnu/sram.gdb
iar-linker-script-y ?= $(TOP)/target/sama5d2/toolchain/iar/sram.icf
iar-debug-script-y ?= $(TOP)/target/sama5d2/toolchain/iar/sram.mac
endif

ifeq ($(VARIANT),ddram)
gnu-linker-script-y ?= $(TOP)/target/sama5d2/toolchain/gnu/ddram.ld
gnu-debug-script-y ?= $(TOP)/target/sama5d2/toolchain/gnu/ddram.gdb
iar-linker-script-y ?= $(TOP)/target/sama5d2/toolchain/iar/ddram.icf
ifeq ($(CONFIG_BOARD_SAMA5D2_XPLAINED),y)
iar-debug-script-y ?= $(TOP)/target/sama5d2/toolchain/iar/ddram_sama5d2-xplained.mac
endif
ifeq ($(CONFIG_BOARD_SAMA5D2_XPLAINED_PROTO),y)
iar-debug-script-y ?= $(TOP)/target/sama5d2/toolchain/iar/ddram_sama5d2-xplained.mac
endif
bootstrap-y ?= target/sama5d2/bootstrap.o
bootstrap-linker-script-y ?= $(TOP)/target/sama5d2/toolchain/gnu/sram.ld
endif

chip-serie-name-y = sama5d2

target-y += target/sama5d2/chip.o
target-y += target/sama5d2/board_lowlevel.o
target-y += target/sama5d2/board_memories.o

endif
