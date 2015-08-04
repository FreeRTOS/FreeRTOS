#$Id: Makefile,v 1.1.2.1 2011/05/17 04:37:55 sadanan Exp $
###############################################################################
#
# Copyright (C) 2002 - 2014 Xilinx, Inc.  All rights reserved.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# Use of the Software is limited solely to applications:
# (a) running on a Xilinx device, or
# (b) that interact with a Xilinx device through a bus or interconnect.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
# XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
# WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
# OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.
#
# Except as contained in this notice, the name of the Xilinx shall not be used
# in advertising or otherwise to promote the sale, use or other dealings in
# this Software without prior written authorization from Xilinx.
#
###############################################################################
#
# Makefile for profiler
# 
#######################################################################

# PROFILE_ARCH_OBJS - Processor Architecture Dependent files defined here
include ../config.make

AS=mb-as
COMPILER = mb-gcc 
ARCHIVER = mb-ar
CP = cp
COMPILER_FLAGS=-O2 
EXTRA_COMPILER_FLAGS=
LIB = libxil.a
DUMMYLIB = libxilprofile.a

CC_FLAGS = $(subst -pg, , $(COMPILER_FLAGS))
ECC_FLAGS = $(subst -pg, , $(EXTRA_COMPILER_FLAGS))

RELEASEDIR = ../../../../lib
INCLUDEDIR = ../../../../include
INCLUDES = -I./. -I${INCLUDEDIR}

OBJS = _profile_init.o _profile_clean.o _profile_timer_hw.o profile_hist.o profile_cg.o 
DUMMYOBJ = dummy.o
INCLUDEFILES = profile.h mblaze_nt_types.h _profile_timer_hw.h

libs : reallibs dummylibs

reallibs : $(OBJS) $(PROFILE_ARCH_OBJS)
	$(ARCHIVER) -r $(RELEASEDIR)/$(LIB) $(OBJS) $(PROFILE_ARCH_OBJS)

dummylibs : $(DUMMYOBJ)
	$(ARCHIVER) -r $(RELEASEDIR)/$(DUMMYLIB) $(DUMMYOBJ)

%.o:%.c
	$(COMPILER) $(CC_FLAGS) $(ECC_FLAGS) -c $< -o $@ $(INCLUDES)

%.o:%.S
	$(COMPILER) $(CC_FLAGS) $(ECC_FLAGS) -c $< -o $@ $(INCLUDES)

include: 
	$(CP) -rf $(INCLUDEFILES) $(INCLUDEDIR)

clean:
	rm -f $(OBJS) $(PROFILE_ARCH_OBJS) $(LIB)
