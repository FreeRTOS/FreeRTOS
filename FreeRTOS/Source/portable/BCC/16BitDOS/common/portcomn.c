/*
    FreeRTOS V7.3.0 - Copyright (C) 2012 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT 
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest versions, license 
    and contact details.  
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/*
Changes from V1.00:

	+ pxPortInitialiseStack() now initialises the stack of new tasks to the
	  same format used by the compiler.  This allows the compiler generated
	  interrupt mechanism to be used for context switches.

Changes from V2.6.1

	+ Move usPortCheckFreeStackSpace() to tasks.c.
*/


#include <dos.h>
#include <stdlib.h>
#include "FreeRTOS.h"

/*-----------------------------------------------------------*/

/* See header file for description. */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
portSTACK_TYPE DS_Reg = 0;

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
	function call with parameters preamble. */
	
	*pxTopOfStack = FP_SEG( pvParameters );
	pxTopOfStack--;
	*pxTopOfStack = FP_OFF( pvParameters );
	pxTopOfStack--;
	*pxTopOfStack = FP_SEG( pxCode );
	pxTopOfStack--;
	*pxTopOfStack = FP_OFF( pxCode );
	pxTopOfStack--;

	/* Next the status register and interrupt return address. */
	*pxTopOfStack = portINITIAL_SW; 
	pxTopOfStack--;
	*pxTopOfStack = FP_SEG( pxCode );
	pxTopOfStack--;
	*pxTopOfStack = FP_OFF( pxCode );
	pxTopOfStack--;

	/* The remaining registers would be pushed on the stack by our context
	switch function.  These are loaded with values simply to make debugging
	easier. */
	*pxTopOfStack = ( portSTACK_TYPE ) 0xAAAA;	/* AX */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xBBBB;	/* BX */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xCCCC;	/* CX */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xDDDD;	/* DX */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xEEEE;	/* ES */
	pxTopOfStack--;

	/* We need the true data segment. */
	__asm{	MOV DS_Reg, DS };

	*pxTopOfStack = DS_Reg;						/* DS */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x0123;	/* SI */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xDDDD;	/* DI */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xBBBB;	/* BP */

	/*lint +e950 +e611 +e923 */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

