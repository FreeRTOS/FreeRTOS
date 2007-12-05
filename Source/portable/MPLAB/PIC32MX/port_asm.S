/*
	FreeRTOS.org V4.7.0 - Copyright (C) 2003-2007 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.

	Also see http://www.SafeRTOS.com a version that has been certified for use
	in safety critical systems, plus commercial licensing, development and
	support options.
	***************************************************************************
*/
 
#include <p32xxxx.h>
#include <sys/asm.h>
#include "ISR_Support.h"
 
#define portEXC_CODE_MASK ( 0x1f << 2 )

	.set	nomips16
 	.set 	noreorder
 	
 	.extern pxCurrentTCB
 	.extern uxCriticalNesting
 	.extern vTaskSwitchContext
 	.extern vTaskIncrementTick
	.extern vApplicationGeneralExceptionHandler
	.extern xISRStackTop
 	
 	.global vPortStartFirstTask
	.global _general_exception_context
	.global vT1InterruptHandler


/******************************************************************/

 	.section 	.FreeRTOS, "ax", @progbits
 	.set		noreorder
	.set 		noat
 	.ent		vT1InterruptHandler
	
vT1InterruptHandler:

	portSAVE_CONTEXT

	jal 		vTaskIncrementTick
	nop

	/* If we are using the preemptive scheduler then we might want to select
	a different task to execute. */
	#if configUSE_PREEMPTION == 1
		jal 		vTaskSwitchContext
		nop
	#endif /* configUSE_PREEMPTION */

	/* Clear timer 0 interrupt. */
	la			s1, IFS0CLR
	addiu       s0,zero,_IFS0_T1IF_MASK
	sw			s0, 0(s1)

	portRESTORE_CONTEXT

	.end vT1InterruptHandler

/******************************************************************/

 	.section 	.FreeRTOS, "ax", @progbits
 	.set		noreorder
	.set 		noat
 	.ent		xPortStartScheduler

vPortStartFirstTask:

	/* Simply restore the context of the highest priority task that has been
	created so far. */
	portRESTORE_CONTEXT

	.end xPortStartScheduler

/*******************************************************************/

 	.section 	.FreeRTOS, "ax", @progbits
 	.set		noreorder
	.set 		noat
 	.ent		_general_exception_context

_general_exception_context:

	/* Save the context of the current task. */
	portSAVE_CONTEXT

	/* Was this handler caused by a syscall?  The original Cause
	value was saved to the stack as it could change as interrupts
	nest.  Use of k registers must be protected from use by nesting
	interrupts. */
	lw			s7, portCAUSE_STACK_LOCATION(s5)
	andi		s7, s7, portEXC_CODE_MASK
	addi		s7, s7, -( _EXCCODE_SYS << 2 )

	/* Yes - call the SYSCALL handler to select a new task to execute. */
	beq         s7, zero, SyscallHandler
	nop

	/* No - call the application handler to handle all other types of 
	exception.  Pass the status and cause to the application provided 
	handler.  Interrupts are disabled during the execution of the user
	defined handler. */
	di
	lw			a1, portSTATUS_STACK_LOCATION(s5)
	lw			a0, portCAUSE_STACK_LOCATION(s5)
	jal			vApplicationGeneralExceptionHandler
	nop
	ei
	beq 		zero, zero, FinishExceptionHandler
	nop

SyscallHandler:

	/* Adjust the return that was placed onto the stack to be the 
	address of the instruction following the syscall.  s6 already
	contains the EPC value. */
	addi		s6, 4
	sw			s6, portEPC_STACK_LOCATION(s5)

	jal			vTaskSwitchContext
	nop

FinishExceptionHandler:
	portRESTORE_CONTEXT

	.end		_general_exception_context



