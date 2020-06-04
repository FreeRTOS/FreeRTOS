/*
 * FreeRTOS Kernel V10.3.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#include "FreeRTOSConfig.h"
//#include "ISR_Support.h"

	.extern ulRegTest1Counter
	.extern ulRegTest2Counter
	.extern vPortYield
	
	.global vRegTest1
	.global vRegTest2

	.text
	.align 4


/*-----------------------------------------------------------*/

vRegTest1:

	/* Set initial values into the general purpose registers.
	 * a0 = return address, a1 = stack pointer. */
#ifdef __XTENSA_WINDOWED_ABI__
	entry	a1, 64
	s32i	a0, a1, 0		/* Save return address. */
#else
	addi	a1, a1, -64
	s32i	a0, a1, 0		/* Save return address. */
	s32i	a12, a1, 4		/* Save callee-saved regs if call0 ABI. */
	s32i	a13, a1, 8
	s32i	a14, a1, 12
	s32i	a15, a1, 16
#endif
	movi	a2, 0x11111111
	movi	a3, 0x22222222
	movi	a4, 0x33333333
	movi	a5, 0x44444444
	movi	a6, 0x55555555
	movi	a7, 0x66666666
	movi	a8, 0x77777777
	movi	a9, 0x88888888
	movi	a10, 0x99999999
	movi	a11, 0xaaaaaaaa
	movi	a12, 0xbbbbbbbb
	movi	a13, 0xcccccccc
	movi	a14, 0xdddddddd
	movi	a15, 0xeeeeeeee

_RegTest1Loop:

	/* Loop checking the values originally loaded into the general purpose
	 * registers remain through the life of the task. */
	movi	a0, 0x11111111
	bne		a0, a2, _RegTest1Error
	movi	a0, 0x22222222
	bne		a0, a3, _RegTest1Error
	movi	a0, 0x33333333
	bne		a0, a4, _RegTest1Error
	movi	a0, 0x44444444
	bne		a0, a5, _RegTest1Error
	movi	a0, 0x55555555
	bne		a0, a6, _RegTest1Error
	movi	a0, 0x66666666
	bne		a0, a7, _RegTest1Error
	movi	a0, 0x77777777
	bne		a0, a8, _RegTest1Error
	movi	a0, 0x88888888
	bne		a0, a9, _RegTest1Error
	movi	a0, 0x99999999
	bne		a0, a10, _RegTest1Error
	movi	a0, 0xaaaaaaaa
	bne		a0, a11, _RegTest1Error
	movi	a0, 0xbbbbbbbb
	bne		a0, a12, _RegTest1Error
	movi	a0, 0xcccccccc
	bne		a0, a13, _RegTest1Error
	movi	a0, 0xdddddddd
	bne		a0, a14, _RegTest1Error
	movi	a0, 0xeeeeeeee
	bne		a0, a15, _RegTest1Error

	/* Incrememnt the loop counter to prove this task has not gone into the
	 * error null loop. */
	s32i	a2, a1, 20
	movi	a2, ulRegTest1Counter
	l32i	a0, a2, 0
	addi	a0, a0, 1
	s32i	a0, a2, 0
	l32i	a2, a1, 20

	/* Loop again. */
	j		_RegTest1Loop

_RegTest1Error:
.L1:
	j		.L1


	.align 4

/*-----------------------------------------------------------*/

vRegTest2:

	/* Set initial values into the general purpose registers.
	 * a0 = return address, a1 = stack pointer. */
#ifdef __XTENSA_WINDOWED_ABI__
	entry	a1, 64
	s32i	a0, a1, 0		/* Save return address. */
#else
	addi	a1, a1, -64
	s32i	a0, a1, 0		/* Save return address. */
	s32i	a12, a1, 4		/* Save callee-saved regs if call0 ABI. */
	s32i	a13, a1, 8
	s32i	a14, a1, 12
	s32i	a15, a1, 16
#endif

_ReInit:

	movi	a2, 0x01010101
	movi	a3, 0x02020202
	movi	a4, 0x03030303
	movi	a5, 0x04040404
	movi	a6, 0x05050505
	movi	a7, 0x06060606
	movi	a8, 0x07070707
	movi	a9, 0x08080808
	movi	a10, 0x09090909
	movi	a11, 0x0a0a0a0a
	movi	a12, 0x0b0b0b0b
	movi	a13, 0x0c0c0c0c
	movi	a14, 0x0d0d0d0d
	movi	a15, 0x0e0e0e0e

_RegTest2Loop:

	/* Loop checking the values originally loaded into the general purpose
	 * registers remain through the life of the task. */
	movi	a0, 0x01010101
	bne		a0, a2, _RegTest1Error
	movi	a0, 0x02020202
	bne		a0, a3, _RegTest1Error
	movi	a0, 0x03030303
	bne		a0, a4, _RegTest1Error
	movi	a0, 0x04040404
	bne		a0, a5, _RegTest1Error
	movi	a0, 0x05050505
	bne		a0, a6, _RegTest1Error
	movi	a0, 0x06060606
	bne		a0, a7, _RegTest1Error
	movi	a0, 0x07070707
	bne		a0, a8, _RegTest1Error
	movi	a0, 0x08080808
	bne		a0, a9, _RegTest1Error
	movi	a0, 0x09090909
	bne		a0, a10, _RegTest1Error
	movi	a0, 0x0a0a0a0a
	bne		a0, a11, _RegTest1Error
	movi	a0, 0x0b0b0b0b
	bne		a0, a12, _RegTest1Error
	movi	a0, 0x0c0c0c0c
	bne		a0, a13, _RegTest1Error
	movi	a0, 0x0d0d0d0d
	bne		a0, a14, _RegTest1Error
	movi	a0, 0x0e0e0e0e
	bne		a0, a15, _RegTest1Error

	/* Force a yield from one of the reg test tasks to increase coverage.
	 * IMPORTANT: this call will trash some number of registers. Branch
	 * to _ReInit to set things up again. */
#ifdef __XTENSA_WINDOWED_ABI__
	call8	vPortYield
#else
	call0	vPortYield
#endif

	/* Increment the loop counter to prove this task has not gone into the
	 * error null loop. */
	s32i	a2, a1, 20
	movi	a2, ulRegTest2Counter
	l32i	a0, a2, 0
	addi	a0, a0, 1
	s32i	a0, a2, 0
	l32i	a2, a1, 20

	/* Loop again. */
	j		_ReInit			/* See comments above about not using  j _RegTest2Loop.  */

_RegTest2Error:
.L2:
	j		.L2
