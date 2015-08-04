###############################################################################
#
# Copyright (C) 2012 - 2014 Xilinx, Inc.  All rights reserved.
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
######################################################################

# The following are defined in config.make
# LIBSOURCES - Based on if MicroBlaze support Exceptions
# LIBS - Do Build Profile Libraries 
include config.make

AS=mb-as
CC=mb-gcc
AR=mb-ar
CP=cp
COMPILER_FLAGS=-O2 -c
EXTRA_COMPILER_FLAGS=
LIB=libxil.a

CC_FLAGS = $(subst -pg, , $(COMPILER_FLAGS))
ECC_FLAGS = $(subst -pg, , $(EXTRA_COMPILER_FLAGS))

RELEASEDIR=../../../lib
INCLUDEDIR=../../../include
INCLUDES=-I./. -I${INCLUDEDIR}

OUTS = *.o 

INCLUDEFILES=*.h

libs: $(LIBS)

standalone_libs: $(LIBSOURCES)
	echo "Compiling standalone";
	$(CC) $(CC_FLAGS) $(ECC_FLAGS) $(INCLUDES) $^
	$(AR) -r ${RELEASEDIR}/${LIB} ${OUTS} 

profile_libs:
	$(MAKE) -C profile COMPILER_FLAGS="$(COMPILER_FLAGS)" EXTRA_COMPILER_FLAGS="$(EXTRA_COMPILER_FLAGS)" COMPILER="$(CC)" ARCHIVER="$(AR)" AS="$(AS)" libs

include: standalone_includes profile_includes

standalone_includes:
	${CP} ${INCLUDEFILES} ${INCLUDEDIR}

profile_includes:
	$(MAKE) -C profile COMPILER_FLAGS="$(COMPILER_FLAGS)" EXTRA_COMPILER_FLAGS="$(EXTRA_COMPILER_FLAGS)" COMPILER="$(CC)" ARCHIVER="$(AR)" AS="$(AS)" include

clean:
	rm -rf ${OUTS}
	$(MAKE) -C profile COMPILER_FLAGS="$(COMPILER_FLAGS)" EXTRA_COMPILER_FLAGS="$(EXTRA_COMPILER_FLAGS)" COMPILER="$(CC)" ARCHIVER="$(AR)" AS="$(AS)" clean
