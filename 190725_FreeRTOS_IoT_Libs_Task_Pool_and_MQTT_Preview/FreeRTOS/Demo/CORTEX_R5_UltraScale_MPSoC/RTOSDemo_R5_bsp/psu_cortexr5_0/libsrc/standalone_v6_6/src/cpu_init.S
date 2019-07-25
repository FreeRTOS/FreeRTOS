/******************************************************************************
*
* Copyright (C) 2014 - 2015 Xilinx, Inc. All rights reserved.
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
/*****************************************************************************/
/**
* @file cpu_init.s
*
* This file contains CPU specific initialization. Invoked from main CRT
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------- -------- ---------------------------------------------------
* 5.00  pkp	02/10/14 Initial version
*
* </pre>
*
* @note
*
* None.
*
******************************************************************************/

	.text
	.global __cpu_init
	.align 2
__cpu_init:

/* Clear cp15 regs with unknown reset values */
	mov	r0, #0x0
	mcr	p15, 0, r0, c5, c0, 0	/* DFSR */
	mcr	p15, 0, r0, c5, c0, 1	/* IFSR */
	mcr	p15, 0, r0, c6, c0, 0	/* DFAR */
	mcr	p15, 0, r0, c6, c0, 2	/* IFAR */
	mcr	p15, 0, r0, c9, c13, 2	/* PMXEVCNTR */
	mcr	p15, 0, r0, c13, c0, 2	/* TPIDRURW */
	mcr	p15, 0, r0, c13, c0, 3	/* TPIDRURO */


/* Reset and start Cycle Counter */
	mov	r2, #0x80000000		/* clear overflow */
	mcr	p15, 0, r2, c9, c12, 3
	mov	r2, #0xd		/* D, C, E */
	mcr	p15, 0, r2, c9, c12, 0
	mov	r2, #0x80000000		/* enable cycle counter */
	mcr	p15, 0, r2, c9, c12, 1

	bx	lr

.end
