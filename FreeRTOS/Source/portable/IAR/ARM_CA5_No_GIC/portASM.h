;/*
;    FreeRTOS V8.1.2 - Copyright (C) 2014 Real Time Engineers Ltd.
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

	EXTERN	vTaskSwitchContext
	EXTERN  ulCriticalNesting
	EXTERN	pxCurrentTCB
	EXTERN	ulPortTaskHasFPUContext
	EXTERN  ulAsmAPIPriorityMask

portSAVE_CONTEXT macro

	; Save the LR and SPSR onto the system mode stack before switching to
	; system mode to save the remaining system mode registers
	SRSDB	sp!, #SYS_MODE
	CPS		#SYS_MODE
	PUSH	{R0-R12, R14}

	; Push the critical nesting count
	LDR		R2, =ulCriticalNesting
	LDR		R1, [R2]
	PUSH	{R1}

	; Does the task have a floating point context that needs saving?  If
	; ulPortTaskHasFPUContext is 0 then no.
	LDR		R2, =ulPortTaskHasFPUContext
	LDR		R3, [R2]
	CMP		R3, #0

	; Save the floating point context, if any
	FMRXNE  R1,  FPSCR
	VPUSHNE {D0-D15}
#if configFPU_D32 == 1
	VPUSHNE	{D16-D31}
#endif ; configFPU_D32
	PUSHNE	{R1}

	; Save ulPortTaskHasFPUContext itself
	PUSH	{R3}

	; Save the stack pointer in the TCB
	LDR		R0, =pxCurrentTCB
	LDR		R1, [R0]
	STR		SP, [R1]

	endm

; /**********************************************************************/

portRESTORE_CONTEXT macro

	; Set the SP to point to the stack of the task being restored.
	LDR		R0, =pxCurrentTCB
	LDR		R1, [R0]
	LDR		SP, [R1]

	; Is there a floating point context to restore?  If the restored
	; ulPortTaskHasFPUContext is zero then no.
	LDR		R0, =ulPortTaskHasFPUContext
	POP		{R1}
	STR		R1, [R0]
	CMP		R1, #0

	; Restore the floating point context, if any
	POPNE 	{R0}
#if configFPU_D32 == 1
	VPOPNE	{D16-D31}
#endif ; configFPU_D32
	VPOPNE	{D0-D15}
	VMSRNE  FPSCR, R0

	; Restore the critical section nesting depth
	LDR		R0, =ulCriticalNesting
	POP		{R1}
	STR		R1, [R0]

	; Restore all system mode registers other than the SP (which is already
	; being used)
	POP		{R0-R12, R14}

	; Return to the task code, loading CPSR on the way.  CPSR has the interrupt
	; enable bit set appropriately for the task about to execute.
	RFEIA	sp!

	endm





