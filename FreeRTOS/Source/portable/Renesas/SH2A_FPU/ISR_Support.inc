;/*
;    FreeRTOS V7.5.3 - Copyright (C) 2013 Real Time Engineers Ltd.
;    All rights reserved
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
	.macro portSAVE_CONTEXT

	; Save r0 to r14 and pr.
	movml.l r15, @-r15
	
	; Save mac1, mach and gbr
	sts.l	macl, @-r15
	sts.l	mach, @-r15
	stc.l	gbr, @-r15
	
	; Get the address of pxCurrentTCB
	mov.l	#_pxCurrentTCB, r0
	
	; Get the address of pxTopOfStack from the TCB.
	mov.l	@r0, r0
	
	; Save the stack pointer in pxTopOfStack.
	mov.l	r15, @r0

	.endm

;-----------------------------------------------------------

	.macro portRESTORE_CONTEXT

	; Get the address of the pxCurrentTCB variable.
	mov.l	#_pxCurrentTCB, r0

	; Get the address of the task stack from pxCurrentTCB.
	mov.l	@r0, r0

	; Get the task stack itself into the stack pointer. 
	mov.l	@r0, r15		

	; Restore system registers.
	ldc.l	@r15+, gbr
	lds.l	@r15+, mach
	lds.l	@r15+, macl

	; Restore r0 to r14 and PR
	movml.l	@r15+, r15
	
	; Pop the SR and PC to jump to the start of the task.
	rte
	nop

	.endm
;-----------------------------------------------------------