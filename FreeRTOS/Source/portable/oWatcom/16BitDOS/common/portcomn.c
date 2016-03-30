/*
    FreeRTOS V9.0.0rc2 - Copyright (C) 2016 Real Time Engineers Ltd.
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

/*
Changes from V1.00:
	
	+ pxPortInitialiseStack() now initialises the stack of new tasks to the 
	  same format used by the compiler.  This allows the compiler generated
	  interrupt mechanism to be used for context switches.

Changes from V2.4.2:

	+ pvPortMalloc and vPortFree have been removed.  The projects now use
	  the definitions from the source/portable/MemMang directory.

Changes from V2.6.1:

	+ usPortCheckFreeStackSpace() has been moved to tasks.c.
*/

	

#include <stdlib.h>
#include "FreeRTOS.h"

/*-----------------------------------------------------------*/

/* See header file for description. */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
StackType_t DS_Reg = 0, *pxOriginalSP;

	/* Place a few bytes of known values on the bottom of the stack. 
	This is just useful for debugging. */

	*pxTopOfStack = 0x1111;
	pxTopOfStack--;
	*pxTopOfStack = 0x2222;
	pxTopOfStack--;
	*pxTopOfStack = 0x3333;
	pxTopOfStack--;
	*pxTopOfStack = 0x4444;
	pxTopOfStack--;
	*pxTopOfStack = 0x5555;
	pxTopOfStack--;


	/*lint -e950 -e611 -e923 Lint doesn't like this much - but nothing I can do about it. */

	/* We are going to start the scheduler using a return from interrupt
	instruction to load the program counter, so first there would be the
	status register and interrupt return address.  We make this the start 
	of the task. */
	*pxTopOfStack = portINITIAL_SW; 
	pxTopOfStack--;
	*pxTopOfStack = FP_SEG( pxCode );
	pxTopOfStack--;
	*pxTopOfStack = FP_OFF( pxCode );
	pxTopOfStack--;

	/* We are going to setup the stack for the new task to look like
	the stack frame was setup by a compiler generated ISR.  We need to know
	the address of the existing stack top to place in the SP register within
	the stack frame.  pxOriginalSP holds SP before (simulated) pusha was 
	called. */
	pxOriginalSP = pxTopOfStack;

	/* The remaining registers would be pushed on the stack by our context 
	switch function.  These are loaded with values simply to make debugging
	easier. */
	*pxTopOfStack = FP_OFF( pvParameters );		/* AX */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xCCCC;	/* CX */
	pxTopOfStack--;
	*pxTopOfStack = FP_SEG( pvParameters );		/* DX */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xBBBB;	/* BX */
	pxTopOfStack--;
	*pxTopOfStack = FP_OFF( pxOriginalSP );		/* SP */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xBBBB;	/* BP */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x0123;	/* SI */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xDDDD;	/* DI */

	/* We need the true data segment. */
	__asm{	MOV DS_Reg, DS };

	pxTopOfStack--;
	*pxTopOfStack = DS_Reg;	/* DS */

	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xEEEE;	/* ES */

	/* The AX register is pushed again twice - don't know why. */
	pxTopOfStack--;
	*pxTopOfStack = FP_OFF( pvParameters );		/* AX */
	pxTopOfStack--;
	*pxTopOfStack = FP_OFF( pvParameters );		/* AX */


	#ifdef DEBUG_BUILD
		/* The compiler adds space to each ISR stack if building to
		include debug information.  Presumably this is used by the
		debugger - we don't need to initialise it to anything just
		make sure it is there. */
		pxTopOfStack--;
	#endif

	/*lint +e950 +e611 +e923 */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/


