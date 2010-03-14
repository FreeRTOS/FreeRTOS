;/*
;    FreeRTOS V6.0.4 - Copyright (C) 2010 Real Time Engineers Ltd.
;
;    ***************************************************************************
;    *                                                                         *
;    * If you are:                                                             *
;    *                                                                         *
;    *    + New to FreeRTOS,                                                   *
;    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
;    *    + Looking for basic training,                                        *
;    *    + Wanting to improve your FreeRTOS skills and productivity           *
;    *                                                                         *
;    * then take a look at the FreeRTOS eBook                                  *
;    *                                                                         *
;    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
;    *                  http://www.FreeRTOS.org/Documentation                  *
;    *                                                                         *
;    * A pdf reference manual is also available.  Both are usually delivered   *
;    * to your inbox within 20 minutes to two hours when purchased between 8am *
;    * and 8pm GMT (although please allow up to 24 hours in case of            *
;    * exceptional circumstances).  Thank you for your support!                *
;    *                                                                         *
;    ***************************************************************************
;
;    This file is part of the FreeRTOS distribution.
;
;    FreeRTOS is free software; you can redistribute it and/or modify it under
;    the terms of the GNU General Public License (version 2) as published by the
;    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
;    ***NOTE*** The exception to the GPL is included to allow you to distribute
;    a combined work that includes FreeRTOS without being obliged to provide the
;    source code for proprietary components outside of the FreeRTOS kernel.
;    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
;    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

#include "FreeRTOSConfig.h"

; Variables used by scheduler
;------------------------------------------------------------------------------
	EXTERN    pxCurrentTCB
	EXTERN    usCriticalNesting

;------------------------------------------------------------------------------
;   portSAVE_CONTEXT MACRO
;   Saves the context of the general purpose registers, CS and ES (only in far 
;	memory mode) registers the usCriticalNesting Value and the Stack Pointer
;   of the active Task onto the task stack
;------------------------------------------------------------------------------
portSAVE_CONTEXT MACRO

	PUSH      AX                    ; Save AX Register to stack.
	PUSH      HL
#if configMEMORY_MODE == 1
	MOV       A, CS                 ; Save CS register.
	XCH       A, X
	MOV       A, ES                 ; Save ES register.
	PUSH      AX
#else
	MOV       A, CS                 ; Save CS register.
	PUSH      AX
#endif
	PUSH      DE                    ; Save the remaining general purpose registers.
	PUSH      BC
	MOVW      AX, usCriticalNesting ; Save the usCriticalNesting value.
	PUSH      AX	
	MOVW      AX, pxCurrentTCB 	    ; Save the Stack pointer.
	MOVW      HL, AX					
	MOVW      AX, SP					
	MOVW      [HL], AX					
	ENDM
;------------------------------------------------------------------------------

;------------------------------------------------------------------------------
;   portRESTORE_CONTEXT MACRO
;   Restores the task Stack Pointer then use this to restore usCriticalNesting,
;   general purpose registers and the CS and ES (only in far memory mode)
;   of the selected task from the task stack
;------------------------------------------------------------------------------
portRESTORE_CONTEXT MACRO
	MOVW      AX, pxCurrentTCB	    ; Restore the Stack pointer.
	MOVW      HL, AX
	MOVW      AX, [HL]
	MOVW      SP, AX
	POP	      AX	                ; Restore usCriticalNesting value.
	MOVW      usCriticalNesting, AX
	POP	      BC                    ; Restore the necessary general purpose registers.
	POP	      DE
#if configMEMORY_MODE == 1
	POP       AX                    ; Restore the ES register.
	MOV       ES, A
	XCH       A, X                  ; Restore the CS register.
	MOV       CS, A
#else
	POP       AX
	MOV       CS, A                 ; Restore CS register.
#endif
	POP       HL                    ; Restore general purpose register HL.
	POP       AX                    ; Restore AX.
	ENDM
;------------------------------------------------------------------------------
