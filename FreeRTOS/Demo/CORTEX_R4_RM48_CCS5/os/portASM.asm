;/*
;    FreeRTOS V7.2.0 - Copyright (C) 2012 Real Time Engineers Ltd.
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

; TCJ:  Using SSI interrupt todo portYIELD_WITHIN_API, means that we do not need
;       to save ulCriticalNesting in the task context

        .text
        .arm

;-------------------------------------------------------------------------------
;
; Save Task Context 
;
portSAVE_CONTEXT .macro
        stmfd   sp!, {r0}
        stmfd   sp,  {sp}^
        sub     sp,  sp, #4
        ldmfd   sp!, {r0}
        stmfd   r0!, {lr}
        mov	    lr,  r0
        ldmfd   sp!, {r0}
        stmfd   lr,  {r0-lr}^
        sub     lr,  lr, #0x3C
    .if (__TI_VFPV3D16_SUPPORT__)
        fstmdbd lr!, {d0-d15}
        mrs	    r0,  spsr
        fmrx    r1,  fpscr
        stmfd   lr!, {r0,r1}
    .else
        mrs	    r0,  spsr
        stmfd   lr!, {r0}
    .endif
        ldr		r0,  curTCB
        ldr	    r0,  [r0]
        str	    lr,  [r0]
        .endm

;-------------------------------------------------------------------------------

; Restore Task Context
;
portRESTORE_CONTEXT .macro
        ldr		r0,  curTCB
        ldr		r0,  [r0]
        ldr		lr,  [r0]
    .if (__TI_VFPV3D16_SUPPORT__)
        ldmfd   lr!, {r0,r1}
        fldmiad lr!, {d0-d15}
        fmxr    fpscr, r1
    .else
        ldmfd   lr!, {r0}
    .endif
        msr		spsr_csxf, r0
        ldmfd	lr, {r0-r14}^
        ldr		lr, [lr, #0x3C]
        subs	pc, lr, #4
        .endm

;-------------------------------------------------------------------------------
; Start First Task

        .def vPortStartFirstTask

vPortStartFirstTask
        portRESTORE_CONTEXT

;-------------------------------------------------------------------------------
; Yield Processor

        .def vPortYieldProcessor
        .ref vTaskSwitchContext

vPortYieldProcessor
        add     lr, lr, #4
        portSAVE_CONTEXT
        bl      vTaskSwitchContext
        portRESTORE_CONTEXT

;-------------------------------------------------------------------------------
; Yield Processor From Within FreeRTOS API

		.def vPortYeildWithinAPI

vPortYeildWithinAPI
        portSAVE_CONTEXT
		; clear SSI flag
		movw    r0, #0xFFF4
		movt 	r0, #0xFFFF
		ldr     r0, [r0];
		; switch task
        bl      vTaskSwitchContext
        portRESTORE_CONTEXT

;-------------------------------------------------------------------------------
; Preemptive Tick

        .def vPortPreemptiveTick
        .ref vTaskIncrementTick

vPortPreemptiveTick
        portSAVE_CONTEXT
        ; clear interrupt flag
        movw    r0, #0xFC88
        movt    r0, #0xFFFF
        mov     r1, #1
        str     r1, [r0]
        bl      vTaskIncrementTick
        bl      vTaskSwitchContext
        portRESTORE_CONTEXT

;-------------------------------------------------------------------------------

		.ref    pxCurrentTCB
curTCB	.word	pxCurrentTCB

;-------------------------------------------------------------------------------

