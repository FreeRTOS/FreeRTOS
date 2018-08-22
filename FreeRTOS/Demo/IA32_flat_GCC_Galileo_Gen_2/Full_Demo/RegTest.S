/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

.file "RegTest.S"
#include "FreeRTOSConfig.h"
#include "ISR_Support.h"

	.extern ulRegTest1Counter
	.extern ulRegTest2Counter
	.extern dRegTest1_st7
	.extern dRegTest1_st6
	.extern dRegTest1_st5
	.extern dRegTest1_st4
	.extern dRegTest1_st3
	.extern dRegTest1_st2
	.extern dRegTest1_st1
	.extern dRegTest2_st7
	.extern dRegTest2_st6
	.extern dRegTest2_st5
	.extern dRegTest2_st4
	.extern dRegTest2_st3
	.extern dRegTest2_st2
	.extern dRegTest2_st1
	.extern vGenerateYieldInterrupt
	.extern vHPETIRQHandler1
	
	.global vRegTest1
	.global vRegTest2
	.global vApplicationHPETTimer1Wrapper

	.section .text.last /* Push up the memory to check executing from higher memory addresses. */
	.align 4

.func vRegTest1
vRegTest1:

	/* Set initial values into the general purpose registers. */
	movl 	$0x11111111, %eax
	movl 	$0x22222222, %ebx
	movl 	$0x33333333, %ecx
	movl 	$0x44444444, %edx
	movl 	$0x55555555, %esi
	movl 	$0x66666666, %edi

	/* Set initial values into the floating point registers. */
	.if configSUPPORT_FPU == 1
		fldl 	dRegTest1_st7
		fldl 	dRegTest1_st6
		fldl 	dRegTest1_st5
		fldl 	dRegTest1_st4
		fldl 	dRegTest1_st3
		fldl 	dRegTest1_st2
		fldl 	dRegTest1_st1
	.endif /* configSUPPORT_FPU */

_RegTest1Loop:

	/* Loop checking the values originally loaded into the general purpose
	registers remain through the life of the task. */
	cmp 	$0x11111111, %eax
	jne 	_RegTest1Error
	cmp 	$0x22222222, %ebx
	jne 	_RegTest1Error
	cmp 	$0x33333333, %ecx
	jne 	_RegTest1Error
	cmp 	$0x44444444, %edx
	jne 	_RegTest1Error
	cmp 	$0x55555555, %esi
	jne 	_RegTest1Error
	cmp 	$0x66666666, %edi
	jne 	_RegTest1Error


	.if configSUPPORT_FPU == 1
		/* Loop checking the values originally loaded into the floating point
		registers remain through the life of the task. */
		push 	%eax			/* push clobbered register. */
		fldl 	dRegTest1_st7 	/* st( 0 ) set to st( 7 ) value. */
		fucomp 	%st( 7 ) 		/* Compare st( 0 ) with st( 7 ) and pop. */
		fnstsw 	%ax				/* Copy status word to ax. */
		and 	$0x45, %ah		/* Mask bits. */
		xor 	$0x40, %ah		/* test bits. */
		jne 	_RegTest1Error
		fldl 	dRegTest1_st6
		fucomp 	%st( 6 )
		fnstsw 	%ax
		and 	$0x45, %ah
		xor 	$0x40, %ah
		jne 	_RegTest1Error
		fldl 	dRegTest1_st5
		fucomp 	%st( 5 )
		fnstsw 	%ax
		and 	$0x45, %ah
		xor 	$0x40, %ah
		jne 	_RegTest1Error
		fldl 	dRegTest1_st4
		fucomp 	%st( 4 )
		fnstsw 	%ax
		and 	$0x45, %ah
		xor 	$0x40, %ah
		jne 	_RegTest1Error
		fldl 	dRegTest1_st3
		fucomp 	%st( 3 )
		fnstsw 	%ax
		and 	$0x45, %ah
		xor 	$0x40, %ah
		jne 	_RegTest1Error
		fldl 	dRegTest1_st2
		fucomp 	%st( 2 )
		fnstsw 	%ax
		and 	$0x45, %ah
		xor 	$0x40, %ah
		jne 	_RegTest1Error
		fldl 	dRegTest1_st1
		fucomp 	%st( 1 )
		fnstsw 	%ax
		and 	$0x45, %ah
		xor 	$0x40, %ah
		jne 	_RegTest1Error

		/* Restore clobbered register. */
		pop 	%eax
	.endif /* configSUPPORT_FPU */

	/* Incrememnt the loop counter to prove this task has not gone into the
	error null loop. */
	add 	$1, ulRegTest1Counter

	/* Loop again. */
	jmp 	_RegTest1Loop

_RegTest1Error:
	jmp		.
.endfunc
/*-----------------------------------------------------------*/

.func vRegTest2
vRegTest2:

	/* Set initial values into the general purpose registers. */
	movl 	$0x10101010, %eax
	movl 	$0x20202020, %ebx
	movl 	$0x30303030, %ecx
	movl 	$0x40404040, %edx
	movl 	$0x50505050, %esi
	movl 	$0x60606060, %edi

	/* Set initial values into the floating point registers. */
	.if configSUPPORT_FPU == 1
		fldl 	dRegTest2_st7
		fldl 	dRegTest2_st6
		fldl 	dRegTest2_st5
		fldl 	dRegTest2_st4
		fldl 	dRegTest2_st3
		fldl 	dRegTest2_st2
		fldl 	dRegTest2_st1
	.endif

_RegTest2Loop:

	/* Loop checking the values originally loaded into the general purpose
	registers remain through the life of the task. */
	cmp 	$0x10101010, %eax
	jne 	_RegTest2Error
	cmp 	$0x20202020, %ebx
	jne 	_RegTest2Error
	cmp 	$0x30303030, %ecx
	jne 	_RegTest2Error
	cmp 	$0x40404040, %edx
	jne 	_RegTest2Error
	cmp 	$0x50505050, %esi
	jne 	_RegTest2Error
	cmp 	$0x60606060, %edi
	jne 	_RegTest1Error

	.if configSUPPORT_FPU == 1
		/* Loop checking the values originally loaded into the floating point
		registers remain through the life of the task. */
		/* Loop checking the values originally loaded into the floating point
		registers remain through the life of the task. */
		push 	%eax			/* push clobbered register. */
		fldl 	dRegTest2_st7 			/* st( 0 ) set to st( 7 ) value. */
		fucomp 	%st( 7 ) 		/* Compare st( 0 ) with st( 7 ) and pop. */
		fnstsw 	%ax				/* Copy status word to ax. */
		and 	$0x45, %ah		/* Mask bits. */
		xor 	$0x40, %ah		/* test bits. */
		jne 	_RegTest1Error
		fldl 	dRegTest2_st6
		fucomp 	%st( 6 )
		fnstsw 	%ax
		and 	$0x45, %ah
		xor 	$0x40, %ah
		jne 	_RegTest1Error
		fldl 	dRegTest2_st5
		fucomp 	%st( 5 )
		fnstsw 	%ax
		and 	$0x45, %ah
		xor 	$0x40, %ah
		jne 	_RegTest1Error
		fldl 	dRegTest2_st4
		fucomp 	%st( 4 )
		fnstsw 	%ax
		and 	$0x45, %ah
		xor 	$0x40, %ah
		jne 	_RegTest1Error
		fldl 	dRegTest2_st3
		fucomp 	%st( 3 )
		fnstsw 	%ax
		and 	$0x45, %ah
		xor 	$0x40, %ah
		jne 	_RegTest1Error
		fldl 	dRegTest2_st2
		fucomp 	%st( 2 )
		fnstsw 	%ax
		and 	$0x45, %ah
		xor 	$0x40, %ah
		jne 	_RegTest1Error
		fldl 	dRegTest2_st1
		fucomp 	%st( 1 )
		fnstsw 	%ax
		and 	$0x45, %ah
		xor 	$0x40, %ah
		jne 	_RegTest1Error

		/* Restore clobbered register. */
		pop 	%eax

	.endif /* configSUPPORT_FPU */

	/* Force a yield from one of the reg test tasks to increase coverage. */
	call vGenerateYieldInterrupt

	/* Increment the loop counter to prove this task has not entered the error
	null loop. */
	add 	$1, ulRegTest2Counter
	jmp 	_RegTest2Loop

_RegTest2Error:
	jmp 	.

.endfunc

/*-----------------------------------------------------------*/

/* Purely for demonstration purposes, two of the HPET timers used by the
IntQueue test use the central interrupt handler, and timer 1 uses its own
assembly wrapper - which is defined below.  See
http://www.freertos.org/RTOS_Intel_Quark_Galileo_GCC.html#interrupts for more
information. */
.func vApplicationHPETTimer1Wrapper
vApplicationHPETTimer1Wrapper:

	portFREERTOS_INTERRUPT_ENTRY
	call vHPETIRQHandler1
	portFREERTOS_INTERRUPT_EXIT

.endfunc

.end
