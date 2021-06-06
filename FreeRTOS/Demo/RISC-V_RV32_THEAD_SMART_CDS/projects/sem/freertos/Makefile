#/*
# * Copyright (C) 2017-2019 Alibaba Group Holding Limited. All rights reserved.
# *
# * Licensed under the Apache License, Version 2.0 (the "License");
# * you may not use this file except in compliance with the License.
# * You may obtain a copy of the License at
# *
# *   http://www.apache.org/licenses/LICENSE-2.0
# *
# * Unless required by applicable law or agreed to in writing, software
# * distributed under the License is distributed on an "AS IS" BASIS,
# * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# * See the License for the specific language governing permissions and
# * limitations under the License.
# */



NAME   = smartl_e906_evb
CDIR   = .
BUILDDIR= $(CDIR)/out
OBJDIR = $(BUILDDIR)/obj
MAKEDIR = $(shell pwd)
ROOTDIR = $(MAKEDIR)/../../../

CFLAGS += -g2
CFLAGS += -Os

TARGET_CPU = e906fd
SOC	= smartl_rv32
BOARD = smartl_e906_evb
KERNEL = freertos
HAVE_VIC = n
HAVE_OS_TRACE = 
HELIX = n
SD = n
MMC = n
FATFS = n
TEST_KERNEL = n
TEST_DRIVER = n
TEST_CORE = n
EXAMPLE_DSP = n
EXAMPLE_VDSP = n
EXAMPLE_DSP_NN = n
EXAMPLE_VDSP_NN = n
HEX_BUILDDIR = $(ROOTDIR)/utilities/elf2hex/hex

export TARGET_CPU SOC BOARD KERNEL HAVE_VIC HAVE_OS_TRACE

LINKFILE = gcc_csky.ld
LINKDIR  = $(ROOTDIR)/board/$(BOARD)

CC      = riscv64-unknown-elf-gcc
LD      = riscv64-unknown-elf-ld
AR      = riscv64-unknown-elf-ar
AS      = riscv64-unknown-elf-as
OBJDUMP = riscv64-unknown-elf-objdump
OBJCOPY = riscv64-unknown-elf-objcopy
RM      = rm
MV      = mv

INCLUDEDIRS = \
              -I$(MAKEDIR)/                 \
              -I$(MAKEDIR)/ \
              -I$(MAKEDIR)/configs \
              -I$(ROOTDIR)/csi_core/include        \
              -I$(ROOTDIR)/csi_driver/include      \
              -I$(ROOTDIR)/csi_driver/$(SOC)/include \
              -I$(ROOTDIR)/libs/include                \
              -I$(ROOTDIR)/board/$(BOARD)/include \
              

CSRC = \
          $(ROOTDIR)/libs/mm/*.c          \
          $(ROOTDIR)/libs/libc/*.c          \
          $(ROOTDIR)/libs/syslog/*.c          \
          $(ROOTDIR)/libs/ringbuffer/*.c          \
          $(shell find $(ROOTDIR)/csi_driver/$(SOC)/ -name "*.c")      \
          $(ROOTDIR)/board/$(BOARD)/*.c   \

ifneq ($(KERNEL), none)
INCLUDEDIRS += -I$(ROOTDIR)/csi_kernel/include
endif

ifeq ($(TEST_KERNEL), y)
INCLUDEDIRS += -I$(ROOTDIR)/projects/tests/kernel/include
INCLUDEDIRS += -I$(ROOTDIR)/projects/tests/dtest/include
CSRC += $(ROOTDIR)/projects/tests/dtest/dtest.c
endif

ifeq ($(TEST_DRIVER), y)
INCLUDEDIRS += -I$(ROOTDIR)/projects/tests/driver/include
INCLUDEDIRS += -I$(ROOTDIR)/projects/tests/dtest/include
CSRC += $(ROOTDIR)/projects/tests/dtest/dtest.c
endif

ifeq ($(TEST_CORE), y)
INCLUDEDIRS += -I$(ROOTDIR)/projects/tests/core/include
INCLUDEDIRS += -I$(ROOTDIR)/projects/tests/dtest/include
CSRC += $(ROOTDIR)/projects/tests/dtest/dtest.c
endif

ifeq ($(EXAMPLE_DSP), y)
INCLUDEDIRS += -I$(ROOTDIR)/csi_dsp/include
DSP_LIB = $(ROOTDIR)/csi_dsp/lib/RP_DSP_LIB
endif

ifeq ($(KERNEL), rhino)
ifeq ($(HAVE_OS_TRACE), y)
INCLUDEDIRS += \
              -I$(ROOTDIR)/libs/trace/include \
              -I$(ROOTDIR)/libs/comm/include
CSRC += $(ROOTDIR)/libs/trace/trcBase.c \
        $(ROOTDIR)/libs/trace/trcHardwarePort.c   \
        $(ROOTDIR)/libs/trace/trcKernel.c   \
        $(ROOTDIR)/libs/trace/trcTrigger.c   \
        $(ROOTDIR)/libs/trace/trcKernelPort.c   \
        $(ROOTDIR)/libs/trace/trcUser.c   \
        $(ROOTDIR)/libs/comm/*.c
endif
endif

ifeq ($(EXAMPLE_VDSP), y)
INCLUDEDIRS += -I$(ROOTDIR)/csi_dsp/include
VDSP_LIB = $(ROOTDIR)/csi_dsp/lib/RP_VDSP_LIB
endif

ifeq ($(EXAMPLE_DSP_NN), y)
INCLUDEDIRS += -I$(ROOTDIR)/csi_dsp/include
INCLUDEDIRS += -I$(ROOTDIR)/csi_nn/include
DSP_NN_LIB = $(ROOTDIR)/csi_nn/lib/RP_NNDSPNN_LIB
endif

ifeq ($(EXAMPLE_VDSP_NN), y)
INCLUDEDIRS += -I$(ROOTDIR)/csi_dsp/include
INCLUDEDIRS += -I$(ROOTDIR)/csi_nn/include
VDSP_NN_LIB = $(ROOTDIR)/csi_nn/lib/RP_NNVDSPNN_LIB
endif

ifneq ($(KERNEL), none)
#CSRC += $(MAKEDIR)/../*.c
CSRC += $(shell find $(MAKEDIR)/../ -name "*.c")
SSRC += $(shell find $(MAKEDIR)/../ -name "*.S")
else
CSRC += $(shell find $(MAKEDIR)/ -name "*.c")
SSRC += $(shell find $(MAKEDIR)/ -name "*.S")
endif
SSRC += $(ROOTDIR)/csi_driver/$(SOC)/*.S

include sub.mk

CFLAGS += $(INCLUDEDIRS)
CFLAGS += -c -g -ffunction-sections -fdata-sections -Wall
ifeq ($(strip $(TARGET_CPU)),$(filter $(TARGET_CPU), rv32ec rv32emc))
CFLAGS += -march=$(TARGET_CPU)xthead -mabi=ilp32e
LDFLAGS += -march=$(TARGET_CPU)xthead -mabi=ilp32e
else
ifeq ($(TARGET_CPU), e902)
CFLAGS += -march=rv32ecxthead -mabi=ilp32e
LDFLAGS += -march=rv32ecxthead -mabi=ilp32e
else
ifeq ($(TARGET_CPU), e902m)
CFLAGS += -march=rv32emcxthead -mabi=ilp32e
LDFLAGS += -march=rv32emcxthead -mabi=ilp32e
else
ifeq ($(TARGET_CPU), rv32imac)
CFLAGS += -march=$(TARGET_CPU)xthead -mabi=ilp32
LDFLAGS += -march=$(TARGET_CPU)xthead -mabi=ilp32
else
ifeq ($(TARGET_CPU), e906)
CFLAGS += -march=rv32imacxthead -mabi=ilp32 -mcmodel=medlow
LDFLAGS += -march=rv32imac -mabi=ilp32
else
ifeq ($(TARGET_CPU), e906f)
CFLAGS += -march=rv32imafcxthead -mabi=ilp32f -mcmodel=medlow
LDFLAGS += -march=rv32imafcxthead -mabi=ilp32f
else
ifeq ($(TARGET_CPU), e906fd)
CFLAGS += -march=rv32imafdcxthead -mabi=ilp32d -mcmodel=medlow
LDFLAGS += -march=rv32imafdcxthead -mabi=ilp32d
else
CFLAGS += -mcpu=$(TARGET_CPU)
LDFLAGS += -mcpu=$(TARGET_CPU)
endif
endif
endif
endif
endif
endif
endif

LDFLAGS += 

NEWTHIRDPARTY_LIBS += 

export CC AS AR LD GS RM OBJDUMP CFLAGS AFLAGS MV

ifeq ($(V), 1)
Q =
else
Q = @
endif

ifeq ($(SOC), CH2201)
all: $(NAME).elf hexfile
else
all: $(NAME).elf
endif

SSRCFILE = $(wildcard $(SSRC))
CSRCFILE = $(wildcard $(CSRC))

OBJECTS = $(SSRCFILE:%.S=%.o) $(CSRCFILE:%.c=%.o)

%.o:%.c
	@echo CC ${shell echo $<|awk -F '/' '{print $$NF}'}
	$(Q)$(CC)  $(CFLAGS) -o $@  $<

%.o:%.S
	@echo AS ${shell echo $<|awk -F '/' '{print $$NF}'}
	$(Q)$(CC)  $(CFLAGS) -o $@  $<

build_dir:
	@mkdir -p $(BUILDDIR)
	@mkdir -p $(OBJDIR)

$(NAME).elf: build_dir $(OBJECTS) $(LINKDIR)/$(LINKFILE)
	@echo LINK $@
	$(Q)$(CC) $(LDFLAGS) \
	-nostartfiles -o $(BUILDDIR)/$(NAME).elf \
	-Wl,--whole-archive $(OBJECTS) $(DSP_LIB) $(VDSP_LIB) $(DSP_NN_LIB) $(VDSP_NN_LIB) $(NEWTHIRDPARTY_LIBS) -Wl,--no-whole-archive \
	-Wl,-T$(LINKDIR)/$(LINKFILE) \
	-lm -lc -lgcc -Wl,-gc-sections -Wl,-zmax-page-size=1024
	@-mv $(OBJECTS) $(OBJDIR)
	$(Q)$(OBJDUMP) -S $(BUILDDIR)/$(NAME).elf > $(BUILDDIR)/$(NAME).asm

hexfile:
	@mkdir -p out/generated
#	@mkdir -p $(HEX_BUILDDIR)/generated/hexs
#	@mkdir -p $(HEX_BUILDDIR)/generated/imgs
#	@$(OBJCOPY) -O binary $(BUILDDIR)/$(NAME).elf $(HEX_BUILDDIR)/generated/imgs/boot
#	@sh $(HEX_BUILDDIR)/mtbhex.sh $(ROOTDIR) $(LINKDIR) $(HEX_BUILDDIR)
#	@sh $(HEX_BUILDDIR)/img2hex.sh $(ROOTDIR) $(LINKDIR) $(OBJCOPY) $(HEX_BUILDDIR)
	@cp  -rf $(HEX_BUILDDIR)/generated/hexs $(HEX_BUILDDIR)/generated/imgs out/generated
#	@mv  out/generated/imgs/boot out/generated/imgs/$(NAME).bin
#	@mv  out/generated/hexs/boot.hex out/generated/hexs/$(NAME).hex
#	@rm  -rf $(HEX_BUILDDIR)/generated/hexs $(HEX_BUILDDIR)/generated/imgs

clean:
	@echo clean
	@$(RM) -rf $(BUILDDIR) $(OBJECTS)

