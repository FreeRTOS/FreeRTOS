;
;/*
;    FreeRTOS V8.0.0 - Copyright (C) 2014 Real Time Engineers Ltd.
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

; * The definition of the "register test" tasks, as described at the top of
; * main.c

	.include data_model.h

	.global xTaskIncrementTick
	.global vTaskSwitchContext
	.global vPortSetupTimerInterrupt
	.global pxCurrentTCB
	.global usCriticalNesting

	.def vPortPreemptiveTickISR
	.def vPortCooperativeTickISR
	.def vPortYield
	.def xPortStartScheduler

;-----------------------------------------------------------

portSAVE_CONTEXT .macro

	;Save the remaining registers.
	pushm_x	#12, r15
	mov.w	&usCriticalNesting, r14
	push_x r14
	mov_x	&pxCurrentTCB, r12
	mov_x	sp, 0( r12 )
	.endm
;-----------------------------------------------------------

portRESTORE_CONTEXT .macro

	mov_x	&pxCurrentTCB, r12
	mov_x	@r12, sp
	pop_x	r15
	mov.w	r15, &usCriticalNesting
	popm_x	#12, r15
	pop.w	sr
	ret_x
	.endm
;-----------------------------------------------------------

;*
;* The RTOS tick ISR.
;*
;* If the cooperative scheduler is in use this simply increments the tick
;* count.
;*
;* If the preemptive scheduler is in use a context switch can also occur.
;*/

	.text
	.align 2

vPortPreemptiveTickISR: .asmfunc

	; The sr is not saved in portSAVE_CONTEXT() because vPortYield() needs
	;to save it manually before it gets modified (interrupts get disabled).
	push.w sr
	portSAVE_CONTEXT

	call_x	#xTaskIncrementTick
	call_x	#vTaskSwitchContext

	portRESTORE_CONTEXT
	.endasmfunc
;-----------------------------------------------------------

	.align 2

vPortCooperativeTickISR: .asmfunc

	; The sr is not saved in portSAVE_CONTEXT() because vPortYield() needs
	;to save it manually before it gets modified (interrupts get disabled).
	push.w sr
	portSAVE_CONTEXT

	call_x	#xTaskIncrementTick

	portRESTORE_CONTEXT

	.endasmfunc
;-----------------------------------------------------------

;
; Manual context switch called by the portYIELD() macro.
;

	.align 2

vPortYield: .asmfunc

	; The sr needs saving before it is modified.
	push.w	sr

	; Now the SR is stacked we can disable interrupts.
	dint
	nop

	; Save the context of the current task.
	portSAVE_CONTEXT

	; Select the next task to run.
	call_x	#vTaskSwitchContext

	; Restore the context of the new task.
	portRESTORE_CONTEXT
	.endasmfunc
;-----------------------------------------------------------


;
; Start off the scheduler by initialising the RTOS tick timer, then restoring
; the context of the first task.
;

	.align 2

xPortStartScheduler: .asmfunc

	; Setup the hardware to generate the tick.  Interrupts are disabled
	; when this function is called.
	call_x	#vPortSetupTimerInterrupt

	; Restore the context of the first task that is going to run.
	portRESTORE_CONTEXT
	.endasmfunc
;-----------------------------------------------------------

	.end

