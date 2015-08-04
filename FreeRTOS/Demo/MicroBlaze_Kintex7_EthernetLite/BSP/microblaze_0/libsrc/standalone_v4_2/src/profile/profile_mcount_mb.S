// $Id: profile_mcount_mb.S,v 1.1.2.1 2011/05/17 04:37:58 sadanan Exp $
/******************************************************************************
*
* Copyright (C) 2002 - 2014 Xilinx, Inc.  All rights reserved.
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

	.globl _mcount 
	.text 
	.align 2
	.ent _mcount

	#ifndef PROFILE_NO_GRAPH
	
_mcount:
	addi r1, r1, -48
	swi r11, r1, 44
	swi r12, r1, 40
	swi r5, r1, 36
	swi r6, r1, 32
	swi r7, r1, 28
	swi r8, r1, 24
	swi r9, r1, 20
	swi r10, r1, 16
	swi r15, r1, 12
	add r6, r0, r15
	brlid r15, mcount
	lwi r5, r1, 48

	lwi r11, r1, 44
	lwi r12, r1, 40	
	lwi r5, r1, 36
	lwi r6, r1, 32
	lwi r7, r1, 28
	lwi r8, r1, 24
	lwi r9, r1, 20
	lwi r10, r1, 16
	lwi r15, r1, 12
	rtsd r15, 4
	addi r1, r1, 48

	#endif	/* PROFILE_NO_GRAPH */
	
	.end _mcount 
