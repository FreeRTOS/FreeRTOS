;/*
;    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd.
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

        .text
        .arm
        .ref vTaskSwitchContext
        .ref xTaskIncrementTick
        .ref ulTaskHasFPUContext
		.ref pxCurrentTCB

;/*-----------------------------------------------------------*/
;
; Save Task Context 
;
portSAVE_CONTEXT .macro
		DSB

		; Push R0 as we are going to use it
		STMDB	SP!, {R0}

		; Set R0 to point to the task stack pointer.
		STMDB	SP,{SP}^
		SUB	SP, SP, #4
		LDMIA	SP!,{R0}

		; Push the return address onto the stack.
		STMDB	R0!, {LR}

		; Now LR has been saved, it can be used instead of R0.
		MOV	LR, R0

		; Pop R0 so it can be saved onto the task stack.
		LDMIA	SP!, {R0}

		; Push all the system mode registers onto the task stack.
		STMDB	LR,{R0-LR}^
		SUB	LR, LR, #60

		; Push the SPSR onto the task stack.
		MRS	R0, SPSR
		STMDB	LR!, {R0}

    .if (__TI_VFP_SUPPORT__)
		;Determine if the task maintains an FPU context.
		LDR	R0, ulFPUContextConst
		LDR	R0, [R0]

		; Test the flag
		CMP		R0, #0

		; If the task is not using a floating point context then skip the
		; saving of the FPU registers.
		BEQ		PC+3
		FSTMDBD	LR!, {D0-D15}
		FMRX    R1,  FPSCR
		STMFD   LR!, {R1}

		; Save the flag
		STMDB	LR!, {R0}
	.endif

		; Store the new top of stack for the task.
		LDR	R0, pxCurrentTCBConst
		LDR	R0, [R0]
		STR	LR, [R0]

        .endm

;/*-----------------------------------------------------------*/
;
; Restore Task Context
;
portRESTORE_CONTEXT .macro
		LDR		R0, pxCurrentTCBConst
		LDR		R0, [R0]
		LDR		LR, [R0]

	.if (__TI_VFP_SUPPORT__)
		; The floating point context flag is the first thing on the stack.
		LDR		R0, ulFPUContextConst
		LDMFD	LR!, {R1}
		STR		R1, [R0]

		; Test the flag
		CMP		R1, #0

		; If the task is not using a floating point context then skip the
		; VFP register loads.
		BEQ		PC+3

		; Restore the floating point context.
		LDMFD   LR!, {R0}
		FLDMIAD	LR!, {D0-D15}
		FMXR    FPSCR, R0
	.endif

		; Get the SPSR from the stack.
		LDMFD	LR!, {R0}
		MSR		SPSR_CSXF, R0

		; Restore all system mode registers for the task.
		LDMFD	LR, {R0-R14}^

		; Restore the return address.
		LDR		LR, [LR, #+60]

		; And return - correcting the offset in the LR to obtain the
		; correct address.
		SUBS	PC, LR, #4
        .endm

;/*-----------------------------------------------------------*/
; Start the first task by restoring its context.

        .def vPortStartFirstTask

vPortStartFirstTask:
        portRESTORE_CONTEXT

;/*-----------------------------------------------------------*/
; Yield to another task.

        .def vPortYieldProcessor

vPortYieldProcessor:
		; Within an IRQ ISR the link register has an offset from the true return
		; address.  SWI doesn't do this. Add the offset manually so the ISR
		; return code can be used.
        ADD     LR, LR, #4

        ; First save the context of the current task.
        portSAVE_CONTEXT

        ; Select the next task to execute. */
        BL      vTaskSwitchContext

        ; Restore the context of the task selected to execute.
        portRESTORE_CONTEXT

;/*-----------------------------------------------------------*/
; Yield to another task from within the FreeRTOS API

		.def vPortYeildWithinAPI

vPortYeildWithinAPI:
		; Save the context of the current task.

        portSAVE_CONTEXT
		; Clear SSI flag.
		MOVW    R0, #0xFFF4
		MOVT 	R0, #0xFFFF
		LDR     R0, [R0]

		; Select the next task to execute. */
        BL      vTaskSwitchContext

        ; Restore the context of the task selected to execute.
        portRESTORE_CONTEXT

;/*-----------------------------------------------------------*/
; Preemptive Tick

        .def vPortPreemptiveTick

vPortPreemptiveTick:

		; Save the context of the current task.
        portSAVE_CONTEXT

        ; Clear interrupt flag
        MOVW    R0, #0xFC88
        MOVT    R0, #0xFFFF
        MOV     R1, #1
        STR     R1, [R0]

        ; Increment the tick count, making any adjustments to the blocked lists
        ; that may be necessary.
        BL      xTaskIncrementTick

        ; Select the next task to execute.
        CMP	R0, #0
        BLNE    vTaskSwitchContext

        ; Restore the context of the task selected to execute.
        portRESTORE_CONTEXT

;-------------------------------------------------------------------------------

	.if (__TI_VFP_SUPPORT__)

		.def vPortInitialiseFPSCR

vPortInitialiseFPSCR:

		MOV		R0, #0
		FMXR    FPSCR, R0
		BX		LR

	.endif ;__TI_VFP_SUPPORT__


pxCurrentTCBConst	.word	pxCurrentTCB
ulFPUContextConst 	.word   ulTaskHasFPUContext
;-------------------------------------------------------------------------------

