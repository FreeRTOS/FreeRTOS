/*
    FreeRTOS V7.5.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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
	PUBLIC vPortSVCHandler
	PUBLIC vPortStartFirstTask


/*-----------------------------------------------------------*/

vSetMSP
	msr msp, r0
	bx lr
	
/*-----------------------------------------------------------*/

xPortPendSVHandler:
	mrs r0, psp							
											
	ldr	r3, =pxCurrentTCB	/* Get the location of the current TCB. */
	ldr	r2, [r3]						
											
	subs r0, r0, #32		/* Make space for the remaining low registers. */
	str r0, [r2]			/* Save the new top of stack. */
	stmia r0!, {r4-r7}		/* Store the low registers that are not saved automatically. */
	mov r4, r8				/* Store the high registers. */
	mov r5, r9							
	mov r6, r10							
	mov r7, r11							
	stmia r0!, {r4-r7}              	
											
	push {r3, r14}						
	cpsid i								
	bl vTaskSwitchContext				
	cpsie i								
	pop {r2, r3}			/* lr goes in r3. r2 now holds tcb pointer. */
											
	ldr r1, [r2]						
	ldr r0, [r1]			/* The first item in pxCurrentTCB is the task top of stack. */
	adds r0, r0, #16		/* Move to the high registers. */
	ldmia r0!, {r4-r7}		/* Pop the high registers. */
	mov r8, r4							
	mov r9, r5							
	mov r10, r6							
	mov r11, r7							
											
	msr psp, r0				/* Remember the new top of stack for the task. */
											
	subs r0, r0, #32		/* Go back for the low registers that are not automatically restored. */
	ldmia r0!, {r4-r7}		/* Pop low registers.  */
											
	bx r3								

/*-----------------------------------------------------------*/

vPortSVCHandler;
	ldr	r3, =pxCurrentTCB	/* Restore the context. */
	ldr r1, [r3]			/* Get the pxCurrentTCB address. */
	ldr r0, [r1]			/* The first item in pxCurrentTCB is the task top of stack. */
	adds r0, r0, #16		/* Move to the high registers. */
	ldmia r0!, {r4-r7}		/* Pop the high registers. */
	mov r8, r4						
	mov r9, r5						
	mov r10, r6						
	mov r11, r7						
										
	msr psp, r0				/* Remember the new top of stack for the task. */
										
	subs r0, r0, #32		/* Go back for the low registers that are not automatically restored. */
	ldmia r0!, {r4-r7}		/* Pop low registers.  */
	mov r1, r14				/* OR R14 with 0x0d. */
	movs r0, #0x0d					
	orrs r1, r0						
	bx r1							

/*-----------------------------------------------------------*/

vPortStartFirstTask
	movs r0, #0x00 	 		/* Locate the top of stack. */
	ldr r0, [r0] 		
	msr msp, r0		 		/* Set the msp back to the start of the stack. */
	cpsie i			 		/* Globally enable interrupts. */
	svc 0			 		/* System call to start first task. */
	nop				
	
	END
	