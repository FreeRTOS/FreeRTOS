/*
	FreeRTOS.org V4.4.0 - Copyright (C) 2003-2007 Richard Barry.

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

	Also see http://www.SafeRTOS.com for an IEC 61508 compliant version along
	with commercial development and support options.
	***************************************************************************
*/

/*
	Change from V4.2.1:

	+ Introduced usage of configKERNEL_INTERRUPT_PRIORITY macro to set the
	  interrupt priority used by the kernel.
*/

#include <FreeRTOSConfig.h>

/* For backward compatibility, ensure configKERNEL_INTERRUPT_PRIORITY is 
defined.  The value zero should also ensure backward compatibility.  
FreeRTOS.org versions prior to V4.3.0 did not include this definition. */
#ifndef configKERNEL_INTERRUPT_PRIORITY
	#define configKERNEL_INTERRUPT_PRIORITY 0
#endif

	
	RSEG ICODE:CODE

	EXTERN vPortYieldFromISR
	EXTERN vPortSwitchContext
	EXTERN vPortIncrementTick
	EXTERN uxCriticalNesting
	EXTERN pxCurrentTCB

	PUBLIC vSetPSP
	PUBLIC vSetMSP
	PUBLIC xPortPendSVHandler
	PUBLIC xPortSysTickHandler
	PUBLIC vPortSetInterruptMask
	PUBLIC vPortClearInterruptMask


vSetPSP:
	msr psp, r0
	bx lr
	
/*-----------------------------------------------------------*/

vSetMSP
	msr msp, r0
	bx lr
	
/*-----------------------------------------------------------*/

xPortPendSVHandler:
	mrs r0, psp
	cbz r0, no_save
	/* Save the context into the TCB. */					
	sub r0, r0, #0x20
	stm r0, {r4-r11}
	nop
	sub r0, r0, #0x04
	ldr r1, =uxCriticalNesting
	ldr r1, [r1]
	str R1, [r0, #0x00]
	ldr r1, =pxCurrentTCB
	ldr r1, [r1]
	str r0, [r1]
no_save:
	ldr r0, =vPortSwitchContext
	push {r14}
	blx r0
	pop {r14}
	
	/* Restore the context. */	
	ldr r1, =pxCurrentTCB
	ldr r1, [r1]
	ldr r0, [r1]
	ldm r0, {r1, r4-r11}
	nop
	ldr r2, =uxCriticalNesting
	str r1, [r2]
	add r0, r0, #0x24
	msr psp, r0
	orr r14, r14, #0xd
	/* Exit with interrupts in the state required by the task. */	
	cbnz r1, sv_disable_interrupts
	bx r14
	
sv_disable_interrupts:
	mov	r1, #configKERNEL_INTERRUPT_PRIORITY
	msr	basepri, R1

	bx r14

/*-----------------------------------------------------------*/

xPortSysTickHandler:
	/* Call the scheduler tick function. */
	ldr r0, =vPortIncrementTick
	push {r14}
	blx r0
	pop {r14}
	
	/* If using preemption, also force a context switch. */
	#if configUSE_PREEMPTION == 1
		push {r14}
		ldr r0, =vPortYieldFromISR
		blx r0
		pop {r14}
	#endif

	/* Exit with interrupts in the correct state. */
    ldr r2, =uxCriticalNesting
	ldr r2, [r2]
	cbnz r2, tick_disable_interrupts
	bx r14

tick_disable_interrupts:
	mov	r1, #configKERNEL_INTERRUPT_PRIORITY
	msr	basepri, R1
	
	bx r14

/*-----------------------------------------------------------*/

vPortSetInterruptMask:
	push { r0 }
	mov R0, #configKERNEL_INTERRUPT_PRIORITY
	msr BASEPRI, R0
	pop { R0 }

	bx r14
	
/*-----------------------------------------------------------*/

vPortClearInterruptMask:
	PUSH { r0 }
	MOV R0, #0
	MSR BASEPRI, R0
	POP	 { R0 }

	bx r14

/*-----------------------------------------------------------*/

	END
	