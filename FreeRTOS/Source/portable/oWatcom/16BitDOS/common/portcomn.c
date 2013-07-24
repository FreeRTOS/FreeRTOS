/*
    FreeRTOS V7.5.2 - Copyright (C) 2013 Real Time Engineers Ltd.

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
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
portSTACK_TYPE DS_Reg = 0, *pxOriginalSP;

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
	*pxTopOfStack = ( portSTACK_TYPE ) 0xCCCC;	/* CX */
	pxTopOfStack--;
	*pxTopOfStack = FP_SEG( pvParameters );		/* DX */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xBBBB;	/* BX */
	pxTopOfStack--;
	*pxTopOfStack = FP_OFF( pxOriginalSP );		/* SP */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xBBBB;	/* BP */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x0123;	/* SI */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xDDDD;	/* DI */

	/* We need the true data segment. */
	__asm{	MOV DS_Reg, DS };

	pxTopOfStack--;
	*pxTopOfStack = DS_Reg;	/* DS */

	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xEEEE;	/* ES */

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


