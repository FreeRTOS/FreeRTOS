;/*
;	FreeRTOS V5.4.1 - Copyright (C) 2009 Real Time Engineers Ltd.
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
		
	INCLUDE portmacro.inc
	
	;The UART interrupt entry point is defined within an assembly wrapper
	;within this file.  This takes care of the task context saving before it
	;calls the main handler (vUART_ISRHandler()) which is written in C within
	;serial.c.  The execution of the handler can unblock tasks that were blocked
	;waiting for UART events.  Once the handler completes the asm wrapper 
	;finishes off by	restoring the context of whichever task is now selected to 
	;enter the RUNNING state (which might now be a different task to that which
	;was originally interrupted.
	IMPORT vUART_ISRHandler
	EXPORT vUART_ISREntry

	;/* Interrupt entry must always be in ARM mode. */
	ARM
	AREA	|.text|, CODE, READONLY


vUART_ISREntry

	PRESERVE8

	; Save the context of the interrupted task.
	portSAVE_CONTEXT			

	; Call the C handler function - defined within serial.c.
	LDR R0, =vUART_ISRHandler
	MOV LR, PC				
	BX R0

	; Finish off by restoring the context of the task that has been chosen to 
	; run next - which might be a different task to that which was originally
	; interrupted.
	portRESTORE_CONTEXT

	END
