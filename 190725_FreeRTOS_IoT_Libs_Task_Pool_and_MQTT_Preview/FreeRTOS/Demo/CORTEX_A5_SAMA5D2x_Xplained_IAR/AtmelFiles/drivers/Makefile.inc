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

CFLAGS_INC += -I$(TOP)/drivers

lib-y += drivers/drivers.a

drivers-y :=

include $(TOP)/drivers/cortex-a/Makefile.inc
include $(TOP)/drivers/memories/Makefile.inc
include $(TOP)/drivers/misc/Makefile.inc
include $(TOP)/drivers/network/Makefile.inc
include $(TOP)/drivers/peripherals/Makefile.inc
include $(TOP)/drivers/power/Makefile.inc
include $(TOP)/drivers/video/Makefile.inc
include $(TOP)/drivers/usb/Makefile.inc

DRIVERS_OBJS := $(addprefix $(BUILDDIR)/,$(drivers-y))

-include $(DRIVERS_OBJS:.o=.d)

$(BUILDDIR)/drivers/drivers.a: $(DRIVERS_OBJS)
	@mkdir -p $(BUILDDIR)/drivers
	$(ECHO) AR $@
	$(Q)$(AR) -cr $@ $^
