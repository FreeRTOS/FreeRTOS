/*
    FreeRTOS V7.2.0 - Copyright (C) 2012 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

	EXTERN pxCurrentTCB
	EXTERN ulCriticalNesting

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Context save and restore macro definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

portSAVE_CONTEXT MACRO

	; Push R0 as we are going to use the register. 					
	STMDB	SP!, {R0}

	; Set R0 to point to the task stack pointer. 					
	STMDB	SP, {SP}^
	NOP
	SUB		SP, SP, #4
	LDMIA	SP!, {R0}

	; Push the return address onto the stack. 						
	STMDB	R0!, {LR}

	; Now we have saved LR we can use it instead of R0. 				
	MOV		LR, R0

	; Pop R0 so we can save it onto the system mode stack. 			
	LDMIA	SP!, {R0}

	; Push all the system mode registers onto the task stack. 		
	STMDB	LR, {R0-LR}^
	NOP
	SUB		LR, LR, #60

	; Push the SPSR onto the task stack. 							
	MRS		R0, SPSR
	STMDB	LR!, {R0}

	LDR		R0, =ulCriticalNesting 
	LDR		R0, [R0]
	STMDB	LR!, {R0}

	; Store the new top of stack for the task. 						
	LDR		R1, =pxCurrentTCB
	LDR		R0, [R1]
	STR		LR, [R0]

	ENDM


portRESTORE_CONTEXT MACRO

	; Set the LR to the task stack. 									
	LDR		R1, =pxCurrentTCB
	LDR		R0, [R1]
	LDR		LR, [R0]

	; The critical nesting depth is the first item on the stack. 	
	; Load it into the ulCriticalNesting variable. 					
	LDR		R0, =ulCriticalNesting
	LDMFD	LR!, {R1}
	STR		R1, [R0]

	; Get the SPSR from the stack. 									
	LDMFD	LR!, {R0}
	MSR		SPSR_cxsf, R0

	; Restore all system mode registers for the task. 				
	LDMFD	LR, {R0-R14}^
	NOP

	; Restore the return address. 									
	LDR		LR, [LR, #+60]

	; And return - correcting the offset in the LR to obtain the 	
	; correct address. 												
	SUBS	PC, LR, #4

	ENDM

