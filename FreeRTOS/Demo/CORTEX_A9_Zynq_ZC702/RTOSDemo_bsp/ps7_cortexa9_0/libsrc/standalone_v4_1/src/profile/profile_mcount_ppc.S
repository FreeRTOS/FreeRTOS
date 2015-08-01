// $Id: profile_mcount_ppc.S,v 1.1.2.1 2011/05/17 04:37:58 sadanan Exp $
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
	
	#define _MCOUNT_STACK_FRAME 48			
	.section .text 
	.align 2
	.type _mcount@function


_mcount:
	stwu 1,	-_MCOUNT_STACK_FRAME(1)
	stw 3, 8(1)
	stw 4, 12(1)
	stw 5, 16(1)
	stw 6, 20(1)
	stw 7, 24(1)
	stw 8, 28(1)
	stw 9, 32(1)
	stw 10, 36(1)
	stw 11, 40(1)
	stw 12, 44(1)
	mflr 4
	stw 4, (_MCOUNT_STACK_FRAME+4)(1)
	lwz 3, (_MCOUNT_STACK_FRAME)(1)
	lwz 3, 4(3)	
	bl mcount
	lwz 4, (_MCOUNT_STACK_FRAME+4)(1)
	mtlr 4
	lwz 12, 44(1)
	lwz 11, 40(1)
	lwz 10, 36(1)
	lwz 9, 32(1)
	lwz 8, 28(1)
	lwz 7, 24(1)
	lwz 6, 20(1)
	lwz 5, 16(1)
	lwz 4, 12(1)
	lwz 3, 8(1)	
	addi 1,1, _MCOUNT_STACK_FRAME
	blr
	
