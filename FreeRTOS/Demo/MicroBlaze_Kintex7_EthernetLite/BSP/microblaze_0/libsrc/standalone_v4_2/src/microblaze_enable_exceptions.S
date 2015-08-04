/******************************************************************************
*
* Copyright (C) 2004 - 2014 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
# 
# Enable exceptions on microblaze.
#
#
####################################################################

#include "xparameters.h"

	.text
	.globl	microblaze_enable_exceptions
	.ent	microblaze_enable_exceptions
	.align 2
microblaze_enable_exceptions:
#if XPAR_MICROBLAZE_USE_MSR_INSTR == 1
	rtsd    r15, 8;
        msrset  r0, 0x100
#else /*XPAR_MICROBLAZE_USE_MSR_INSTR == 1*/
        mfs     r4, rmsr;
        ori     r4, r4, 0x100;                  /* Turn ON the EE bit */
        mts     rmsr, r4;
        rtsd    r15, 8;
        nop;       
#endif /*XPAR_MICROBLAZE_USE_MSR_INSTR == 1*/
.end microblaze_enable_exceptions

	
  
