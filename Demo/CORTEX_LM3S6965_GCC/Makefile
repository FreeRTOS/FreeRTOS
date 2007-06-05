#******************************************************************************
#
# Makefile - Rules for building the driver library and examples.
#
# Copyright (c) 2005,2006 Luminary Micro, Inc.  All rights reserved.
#
# Software License Agreement
#
# Luminary Micro, Inc. (LMI) is supplying this software for use solely and
# exclusively on LMI's Stellaris Family of microcontroller products.
#
# The software is owned by LMI and/or its suppliers, and is protected under
# applicable copyright laws.  All rights are reserved.  Any use in violation
# of the foregoing restrictions may subject the user to criminal sanctions
# under applicable laws, as well as to civil liability for the breach of the
# terms and conditions of this license.
#
# THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
# OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
# LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
# CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
#
#******************************************************************************

include makedefs

RTOS_SOURCE_DIR=../../Source
DEMO_SOURCE_DIR=../Common/Minimal
UIP_SOURCE_DIR=../Common/ethernet/uIP/uip-1.0/uip

CFLAGS+=-I LuminaryDrivers -I . -I ${RTOS_SOURCE_DIR}/include -I ${RTOS_SOURCE_DIR}/portable/GCC/ARM_CM3 -I ${UIP_SOURCE_DIR} -I webserver -I ../Common/include -D GCC_ARMCM3_LM3S102 -D inline= -D PACK_STRUCT_END=__attribute\(\(packed\)\) -D ALIGN_STRUCT_END=__attribute\(\(aligned\(4\)\)\) -D sprintf=usprintf -D snprintf=usnprintf -D printf=uipprintf

VPATH=${RTOS_SOURCE_DIR}:${RTOS_SOURCE_DIR}/portable/MemMang:${RTOS_SOURCE_DIR}/portable/GCC/ARM_CM3:${DEMO_SOURCE_DIR}:${UIP_SOURCE_DIR}:init:LuminaryDrivers:ParTest:webserver

OBJS=${COMPILER}/main.o	            \
	  ${COMPILER}/list.o            \
      ${COMPILER}/queue.o           \
      ${COMPILER}/tasks.o           \
      ${COMPILER}/port.o            \
      ${COMPILER}/heap_2.o          \
	  ${COMPILER}/BlockQ.o	        \
	  ${COMPILER}/PollQ.o	        \
	  ${COMPILER}/integer.o	        \
	  ${COMPILER}/semtest.o         \
	  ${COMPILER}/osram128x64x4.o   \
      ${COMPILER}/ustdlib.o         \
      ${COMPILER}/blocktim.o        \
      ${COMPILER}/death.o           \
      ${COMPILER}/ParTest.o         \
      ${COMPILER}/timertest.o       \
      ${COMPILER}/emac.o            \
      ${COMPILER}/http-strings.o    \
      ${COMPILER}/httpd-cgi.o       \
      ${COMPILER}/httpd-fs.o        \
      ${COMPILER}/httpd.o           \
      ${COMPILER}/psock.o           \
      ${COMPILER}/timer.o           \
      ${COMPILER}/uip.o             \
      ${COMPILER}/uip_arp.o         \
      ${COMPILER}/uIP_Task.o

INIT_OBJS= ${COMPILER}/startup.o

LIBS= LuminaryDrivers/libdriver.a


#
# The default rule, which causes init to be built.
#
all: ${COMPILER}           \
     ${COMPILER}/RTOSDemo.axf \
	 
#
# The rule to clean out all the build products
#

clean:
	@rm -rf ${COMPILER} ${wildcard *.bin} RTOSDemo.axf
	
#
# The rule to create the target directory
#
${COMPILER}:
	@mkdir ${COMPILER}

${COMPILER}/RTOSDemo.axf: ${INIT_OBJS} ${OBJS} ${LIBS}
SCATTER_RTOSDemo=standalone.ld
ENTRY_RTOSDemo=ResetISR

#
#
# Include the automatically generated dependency files.
#
-include ${wildcard ${COMPILER}/*.d} __dummy__


	 



