/*
    FreeRTOS V6.0.2 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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

	
	RSEG    CODE:CODE(2)
	thumb

	EXTERN vPortYieldFromISR
	EXTERN pxCurrentTCB
	EXTERN vTaskSwitchContext

	PUBLIC vSetMSP
	PUBLIC xPortPendSVHandler
	PUBLIC vPortSetInterruptMask
	PUBLIC vPortClearInterruptMask
	PUBLIC vPortSVCHandler
	PUBLIC vPortStartFirstTask


/*-----------------------------------------------------------*/

vSetMSP
	msr msp, r0
	bx lr
	
/*-----------------------------------------------------------*/

xPortPendSVHandler:
	mrs r0, psp						
	ldr	r3, =pxCurrentTCB			/* Get the location of the current TCB. */
	ldr	r2, [r3]						

	stmdb r0!, {r4-r11}				/* Save the remaining registers. */
	str r0, [r2]					/* Save the new top of stack into the first member of the TCB. */

	stmdb sp!, {r3, r14}
	mov r0, #configMAX_SYSCALL_INTERRUPT_PRIORITY
	msr basepri, r0
	bl vTaskSwitchContext			
	mov r0, #0
	msr basepri, r0
	ldmia sp!, {r3, r14}

	ldr r1, [r3]					
	ldr r0, [r1]					/* The first item in pxCurrentTCB is the task top of stack. */
	ldmia r0!, {r4-r11}				/* Pop the registers. */
	msr psp, r0						
	bx r14							


/*-----------------------------------------------------------*/

vPortSetInterruptMask:
	push { r0 }
	mov R0, #configMAX_SYSCALL_INTERRUPT_PRIORITY
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

vPortSVCHandler;
	ldr	r3, =pxCurrentTCB
	ldr r1, [r3]
	ldr r0, [r1]
	ldmia r0!, {r4-r11}
	msr psp, r0
	mov r0, #0
	msr	basepri, r0
	orr r14, r14, #13
	bx r14

/*-----------------------------------------------------------*/

vPortStartFirstTask
	/* Use the NVIC offset register to locate the stack. */
	ldr r0, =0xE000ED08
	ldr r0, [r0]
	ldr r0, [r0]
	/* Set the msp back to the start of the stack. */
	msr msp, r0
	/* Call SVC to start the first task. */
	svc 0

	END
	