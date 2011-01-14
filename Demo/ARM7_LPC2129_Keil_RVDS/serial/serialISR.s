;/*
;    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.
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
;    * then take a look at the FreeRTOS books - available as PDF or paperback  *
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
