#######################################################################
#
# Copyright (c) 2002 Xilinx, Inc.  All rights reserved. 
# Xilinx, Inc. 
#
# XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS" AS A 
# COURTESY TO YOU.  BY PROVIDING THIS DESIGN, CODE, OR INFORMATION AS 
# ONE POSSIBLE   IMPLEMENTATION OF THIS FEATURE, APPLICATION OR 
# STANDARD, XILINX IS MAKING NO REPRESENTATION THAT THIS IMPLEMENTATION 
# IS FREE FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE RESPONSIBLE 
# FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE FOR YOUR IMPLEMENTATION. 
# XILINX EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH RESPECT TO 
# THE ADEQUACY OF THE IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO 
# ANY WARRANTIES OR REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE 
# FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY 
# AND FITNESS FOR A PARTICULAR PURPOSE. 
#
# $Id: Makefile,v 1.1.2.1 2011/05/17 04:37:55 sadanan Exp $
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
