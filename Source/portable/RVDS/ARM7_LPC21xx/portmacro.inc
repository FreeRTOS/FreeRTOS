;/*
;	FreeRTOS.org V5.1.2 - Copyright (C) 2003-2009 Richard Barry.
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
;   ***************************************************************************
;   ***************************************************************************
;   *                                                                         *
;   * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
;   * and even write all or part of your application on your behalf.          *
;   * See http://www.OpenRTOS.com for details of the services we provide to   *
;   * expedite your project.                                                  *
;   *                                                                         *
;   ***************************************************************************
;   ***************************************************************************
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

	IMPORT  ulCriticalNesting		;
	IMPORT	pxCurrentTCB			;


	MACRO
	portRESTORE_CONTEXT


	LDR		R0, =pxCurrentTCB		; Set the LR to the task stack.  The location was...
	LDR		R0, [R0]				; ... stored in pxCurrentTCB
	LDR		LR, [R0]

	LDR		R0, =ulCriticalNesting	; The critical nesting depth is the first item on... 
	LDMFD	LR!, {R1}				; ...the stack.  Load it into the ulCriticalNesting var.
	STR		R1, [R0]				;

	LDMFD	LR!, {R0}				; Get the SPSR from the stack.
	MSR		SPSR_cxsf, R0			;

	LDMFD	LR, {R0-R14}^			; Restore all system mode registers for the task.
	NOP								;

	LDR		LR, [LR, #+60]			; Restore the return address

									; And return - correcting the offset in the LR to obtain ...
	SUBS	PC, LR, #4				; ...the correct address.

	MEND

; /**********************************************************************/

	MACRO
	portSAVE_CONTEXT


	STMDB 	SP!, {R0}				; Store R0 first as we need to use it.

	STMDB	SP,{SP}^				; Set R0 to point to the task stack pointer.
	NOP								;
	SUB		SP, SP, #4				;
	LDMIA	SP!,{R0}				;

	STMDB	R0!, {LR}				; Push the return address onto the stack.
	MOV		LR, R0					; Now we have saved LR we can use it instead of R0.
	LDMIA	SP!, {R0}				; Pop R0 so we can save it onto the system mode stack.

	STMDB	LR,{R0-LR}^				; Push all the system mode registers onto the task stack.
	NOP								;
	SUB		LR, LR, #60				;

	MRS		R0, SPSR				; Push the SPSR onto the task stack.
	STMDB	LR!, {R0}				;

	LDR		R0, =ulCriticalNesting	;
	LDR		R0, [R0]				;
	STMDB	LR!, {R0}				;

	LDR		R0, =pxCurrentTCB		; Store the new top of stack for the task.
	LDR		R1, [R0]				; 		 
	STR		LR, [R1]				;
	
	MEND
	
	END
