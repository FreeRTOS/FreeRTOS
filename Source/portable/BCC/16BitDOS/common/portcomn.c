/*
	FreeRTOS.org V5.3.1 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
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

