;
;/*
;    FreeRTOS V8.2.1 - Copyright (C) 2015 Real Time Engineers Ltd.
;	
;
;    ***************************************************************************
;     *                                                                       *
;     *    FreeRTOS tutorial books are available in pdf and paperback.        *
;     *    Complete, revised, and edited pdf reference manuals are also       *
;     *    available.                                                         *
;     *                                                                       *
;     *    Purchasing FreeRTOS documentation will not only help you, by       *
;     *    ensuring you get running as quickly as possible and with an        *
;     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
;     *    the FreeRTOS project to continue with its mission of providing     *
;     *    professional grade, cross platform, de facto standard solutions    *
;     *    for microcontrollers - completely free of charge!                  *
;     *                                                                       *
;     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
;     *                                                                       *
;     *    Thank you for using FreeRTOS, and thank you for your support!      *
;     *                                                                       *
;    ***************************************************************************
;
;
;    This file is part of the FreeRTOS distribution.
;
;    FreeRTOS is free software; you can redistribute it and/or modify it under
;    the terms of the GNU General Public License (version 2) as published by the
;    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
;    >>>NOTE<<< The modification to the GPL is included to allow you to
;    distribute a combined work that includes FreeRTOS without being obliged to
;    provide the source code for proprietary components outside of the FreeRTOS
;    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
;    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
;    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;    more details. You should have received a copy of the GNU General Public
;    License and the FreeRTOS license exception along with FreeRTOS; if not it
;    can be viewed here: http://www.freertos.org/a00114.html and also obtained
;    by writing to Richard Barry, contact details for whom are available on the
;    FreeRTOS WEB site.
;
;    1 tab == 4 spaces!
;
;    http://www.FreeRTOS.org - Documentation, latest information, license and
;    contact details.
;
;    http://www.SafeRTOS.com - A version that is certified for use in safety
;    critical systems.
;
;    http://www.OpenRTOS.com - Commercial support, development, porting,
;    licensing and training services.
;*/

; * The definition of the "register test" tasks, as described at the top of
; * main.c

	.include data_model.h

	.if $DEFINED( __LARGE_DATA_MODEL__ )
		.define "cmp.a", cmp_x
		.define "incx.w", inc_x
	.else
		.define "cmp.w", cmp_x
		.define "inc.w", inc_x
	.endif


	.global usRegTest1LoopCounter
	.global usRegTest2LoopCounter
	.global vPortYield
	
	.def vRegTest1Implementation
	.def vRegTest2Implementation

	.text
	
	.align 2
vRegTest1Implementation: .asmfunc

	; Fill each general purpose register with a known value.
	mov_x	#0x4444, r4
	mov_x	#0x5555, r5
	mov_x	#0x6666, r6
	mov_x	#0x7777, r7
	mov_x	#0x8888, r8
	mov_x	#0x9999, r9
	mov_x	#0xaaaa, r10
	mov_x	#0xbbbb, r11
	mov_x	#0xcccc, r12
	mov_x	#0xdddd, r13
	mov_x	#0xeeee, r14
	mov_x	#0xffff, r15
	
prvRegTest1Loop:

	; Test each general purpose register to check that it still contains the
	; expected known value, jumping to vRegTest1Error if any register contains
	; an unexpected value.
	cmp_x	#0x4444, r4
	jne		vRegTest1Error
	cmp_x	#0x5555, r5
	jne		vRegTest1Error
	cmp_x	#0x6666, r6
	jne		vRegTest1Error
	cmp_x	#0x7777, r7
	jne		vRegTest1Error
	cmp_x	#0x8888, r8
	jne		vRegTest1Error
	cmp_x	#0x9999, r9
	jne		vRegTest1Error
	cmp_x	#0xaaaa, r10
	jne		vRegTest1Error
	cmp_x	#0xbbbb, r11
	jne		vRegTest1Error
	cmp_x	#0xcccc, r12
	jne		vRegTest1Error
	cmp_x	#0xdddd, r13
	jne		vRegTest1Error
	cmp_x	#0xeeee, r14
	jne		vRegTest1Error
	cmp_x	#0xffff, r15
	jne		vRegTest1Error
	
	; This task is still running without jumping to vRegTest1Error, so increment
	; the loop counter so the check task knows the task is running error free.
	inc_x	&usRegTest1LoopCounter
	
	; Loop again, performing the same tests.
	jmp		prvRegTest1Loop
	nop
	
vRegTest1Error:
	jmp vRegTest1Error
	nop
	.endasmfunc	
; -----------------------------------------------------------

; See the comments in vRegTest1Implementation.  This task is the same, it just uses
; different values in its registers.
	.align 2
vRegTest2Implementation: .asmfunc

	mov_x	#0x4441, r4
	mov_x	#0x5551, r5
	mov_x	#0x6661, r6
	mov_x	#0x7771, r7
	mov_x	#0x8881, r8
	mov_x	#0x9991, r9
	mov_x	#0xaaa1, r10
	mov_x	#0xbbb1, r11
	mov_x	#0xccc1, r12
	mov_x	#0xddd1, r13
	mov_x	#0xeee1, r14
	mov_x	#0xfff1, r15
	
prvRegTest2Loop:

	cmp_x	#0x4441, r4
	jne		vRegTest2Error
	cmp_x	#0x5551, r5
	jne		vRegTest2Error
	cmp_x	#0x6661, r6
	jne		vRegTest2Error
	cmp_x	#0x7771, r7
	jne		vRegTest2Error
	cmp_x	#0x8881, r8
	jne		vRegTest2Error
	cmp_x	#0x9991, r9
	jne		vRegTest2Error
	cmp_x	#0xaaa1, r10
	jne		vRegTest2Error
	cmp_x	#0xbbb1, r11
	jne		vRegTest2Error
	cmp_x	#0xccc1, r12
	jne		vRegTest2Error
	cmp_x	#0xddd1, r13
	jne		vRegTest2Error
	cmp_x	#0xeee1, r14
	jne		vRegTest2Error
	cmp_x	#0xfff1, r15
	jne		vRegTest2Error
	
	; Also perform a manual yield, just to increase the scope of the test.
	call_x 	#vPortYield
	
	inc_x	&usRegTest2LoopCounter
	jmp		prvRegTest2Loop
	nop

	
vRegTest2Error:
	jmp vRegTest2Error
	nop
	.endasmfunc
; /*-----------------------------------------------------------

     		
	.end
		
