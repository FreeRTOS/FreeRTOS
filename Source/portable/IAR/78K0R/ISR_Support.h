;/*
;	FreeRTOS V5.4.0 - Copyright (C) 2003-2009 Richard Barry.
;
;	This file is part of the FreeRTOS distribution.
;
;	FreeRTOS is free software; you can redistribute it and/or modify it	under 
;	the terms of the GNU General Public License (version 2) as published by the 
;	Free Software Foundation and modified by the FreeRTOS exception.
;	**NOTE** The exception to the GPL is included to allow you to distribute a
;	combined work that includes FreeRTOS without being obliged to provide the 
;	source code for proprietary components outside of the FreeRTOS kernel.  
;	Alternative commercial license and support terms are also available upon 
;	request.  See the licensing section of http://www.FreeRTOS.org for full 
;	license details.
;
;	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
;	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;	more details.
;
;	You should have received a copy of the GNU General Public License along
;	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
;	Temple Place, Suite 330, Boston, MA  02111-1307  USA.
;
;
;	***************************************************************************
;	*                                                                         *
;	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
;	* See http://www.FreeRTOS.org/Documentation for details                   *
;	*                                                                         *
;	***************************************************************************
;
;	1 tab == 4 spaces!
;
;	Please ensure to read the configuration and relevant port sections of the
;	online documentation.
;
;	http://www.FreeRTOS.org - Documentation, latest information, license and
;	contact details.
;
;	http://www.SafeRTOS.com - A version that is certified for use in safety
;	critical systems.
;
;	http://www.OpenRTOS.com - Commercial support, development, porting,
;	licensing and training services.
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
