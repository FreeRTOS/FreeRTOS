/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

typedef void TCB_t;
extern volatile TCB_t * volatile pxCurrentTCB;
extern void vTaskSwitchContext( void );

/* 
 * Saves the stack pointer for one task into its TCB, calls 
 * vTaskSwitchContext() to update the TCB being used, then restores the stack 
 * from the new TCB read to run the task. 
 */
void portSWITCH_CONTEXT( void );

/*
 * Load the stack pointer from the TCB of the task which is going to be first
 * to execute.  Then force an IRET so the registers and IP are popped off the
 * stack.
 */
void portFIRST_CONTEXT( void );

/* There are slightly different versions depending on whether you are building
to include debugger information.  If debugger information is used then there
are a couple of extra bytes left of the ISR stack (presumably for use by the
debugger).  The true stack pointer is then stored in the bp register.  We add
2 to the stack pointer to remove the extra bytes before we restore our context. */

#ifdef DEBUG_BUILD

	#pragma aux portSWITCH_CONTEXT =	"mov	ax, seg pxCurrentTCB"														\
										"mov	ds, ax"																		\
										"les	bx, pxCurrentTCB"			/* Save the stack pointer into the TCB. */		\
										"mov	es:0x2[ bx ], ss"															\
										"mov	es:[ bx ], sp"																\
										"call	vTaskSwitchContext"			/* Perform the switch. */						\
										"mov	ax, seg pxCurrentTCB"		/* Restore the stack pointer from the TCB. */	\
										"mov	ds, ax"																		\
										"les	bx, dword ptr pxCurrentTCB"													\
										"mov	ss, es:[ bx + 2 ]"															\
										"mov	sp, es:[ bx ]"																\
										"mov	bp, sp"						/* Prepair the bp register for the restoration of the SP in the compiler generated portion of the ISR */	\
										"add	bp, 0x0002"

										

	#pragma aux portFIRST_CONTEXT =		"mov	ax, seg pxCurrentTCB"			\
										"mov	ds, ax"							\
										"les	bx, dword ptr pxCurrentTCB"		\
										"mov	ss, es:[ bx + 2 ]"				\
										"mov	sp, es:[ bx ]"					\
										"add	sp, 0x0002"						/* Remove the extra bytes that exist in debug builds before restoring the context. */ \
										"pop	ax"								\
										"pop	ax"								\
										"pop	es"								\
										"pop	ds"								\
										"popa"									\
										"iret"									
#else

	#pragma aux portSWITCH_CONTEXT =	"mov	ax, seg pxCurrentTCB"														\
										"mov	ds, ax"																		\
										"les	bx, pxCurrentTCB"			/* Save the stack pointer into the TCB. */		\
										"mov	es:0x2[ bx ], ss"															\
										"mov	es:[ bx ], sp"																\
										"call	vTaskSwitchContext"			/* Perform the switch. */						\
										"mov	ax, seg pxCurrentTCB"		/* Restore the stack pointer from the TCB. */	\
										"mov	ds, ax"																		\
										"les	bx, dword ptr pxCurrentTCB"													\
										"mov	ss, es:[ bx + 2 ]"															\
										"mov	sp, es:[ bx ]"
										

	#pragma aux portFIRST_CONTEXT =		"mov	ax, seg pxCurrentTCB"			\
										"mov	ds, ax"							\
										"les	bx, dword ptr pxCurrentTCB"		\
										"mov	ss, es:[ bx + 2 ]"				\
										"mov	sp, es:[ bx ]"					\
										"pop	ax"								\
										"pop	ax"								\
										"pop	es"								\
										"pop	ds"								\
										"popa"									\
										"iret"									
#endif


