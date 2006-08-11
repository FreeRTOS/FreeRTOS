/*
	FreeRTOS.org V4.0.5 - Copyright (C) 2003-2006 Richard Barry.

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
	***************************************************************************
*/
#include <FreeRTOSConfig.h>
	
	RSEG ICODE:CODE

	EXTERN vPortYieldFromISR
	EXTERN vTaskSwitchContext
	EXTERN vTaskIncrementTick
	EXTERN uxCriticalNesting
	EXTERN pxCurrentTCB

	PUBLIC vSetPSP
	PUBLIC vSetMSP
	PUBLIC xPortPendSVHandler
	PUBLIC xPortSysTickHandler


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
	ldr r0, =vTaskSwitchContext
	push {r14}
	cpsid i
	blx r0
	cpsie i
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
	cpsid i
	bx r14

/*-----------------------------------------------------------*/

xPortSysTickHandler:
	/* Call the scheduler tick function. */
	ldr r0, =vTaskIncrementTick
	push {r14}
	cpsid i
	blx r0
	cpsie i
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
	cpsid i
	bx r14

	END
/*-----------------------------------------------------------*/
