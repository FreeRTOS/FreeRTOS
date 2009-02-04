;	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2008 Richard Barry.
;
;	This file is part of the FreeRTOS.org distribution.
;
;	FreeRTOS.org is free software; you can redistribute it and/or modify
;	it under the terms of the GNU General Public License as published by
;	the Free Software Foundation; either version 2 of the License, or
;	(at your option) any later version.
;
;	FreeRTOS.org is distributed in the hope that it will be useful,
;	but WITHOUT ANY WARRANTY; without even the implied warranty of
;	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;	GNU General Public License for more details.
;
;	You should have received a copy of the GNU General Public License
;	along with FreeRTOS.org; if not, write to the Free Software
;	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
;
;	A special exception to the GPL can be applied should you wish to distribute
;	a combined work that includes FreeRTOS.org, without being obliged to provide
;	the source code for any proprietary components.  See the licensing section
;	of http://www.FreeRTOS.org for full details of how and when the exception
;	can be applied.
;
;	***************************************************************************
;	See http://www.FreeRTOS.org for documentation, latest information, license
;	and contact details.  Please ensure to read the configuration and relevant
;	port sections of the online documentation.
;	***************************************************************************
;
;------------------------------------------------------------------------------

#include "FreeRTOSConfig.h"

; Variables used by scheduler
;------------------------------------------------------------------------------
	EXTERN    pxCurrentTCB
	EXTERN    usCriticalNesting

;------------------------------------------------------------------------------
;   portSAVE_CONTEXT MACRO
;   Saves the context of the remaining general purpose registers, CS and ES
;   (only in far memory mode) registers
;   the usCriticalNesting Value and the Stack Pointer
;   of the active Task onto the task stack
;------------------------------------------------------------------------------
portSAVE_CONTEXT MACRO

	PUSH      AX                    ; save AX Register to stack
	PUSH      HL
#if configMEMORY_MODE == 1
	MOV       A, CS                 ; save CS register
	XCH       A, X
	MOV       A, ES                 ; save ES register
	PUSH      AX
#else
	MOV       A, CS                 ; save CS register
	PUSH      AX
#endif
	PUSH      DE                    ; save the  remaining general purpose registers
	PUSH      BC
	MOVW      AX, usCriticalNesting ; save the usCriticalNesting value	
	PUSH      AX	
	MOVW      AX, pxCurrentTCB 	    ; save the Stack pointer	
	MOVW      HL, AX					
	MOVW      AX, SP					
	MOVW      [HL], AX					
	ENDM
;------------------------------------------------------------------------------

;------------------------------------------------------------------------------
;   portRESTORE_CONTEXT MACRO
;   Restores the context of the Stack Pointer, usCriticalNesting
;   value, general purpose registers and the CS and ES (only in far memory mode)
;   of the selected task from the task stack
;------------------------------------------------------------------------------

portRESTORE_CONTEXT MACRO
	MOVW      AX, pxCurrentTCB	    ; restore the Stack pointer
	MOVW      HL, AX
	MOVW      AX, [HL]
	MOVW      SP, AX
	POP	      AX	            ; restore usCriticalNesting value
	MOVW      usCriticalNesting, AX
	POP	      BC                    ; restore the necessary general purpose registers
	POP	      DE
#if configMEMORY_MODE == 1
	POP       AX                    ; restore the ES register
	MOV       ES, A
	XCH       A, X                  ; restore the CS register
	MOV       CS, A
#else
	POP       AX
	MOV       CS, A                 ; restore CS register
#endif
	POP       HL                    ; restore general purpose register HL
	POP       AX                    ; restore AX	
	ENDM
;------------------------------------------------------------------------------
