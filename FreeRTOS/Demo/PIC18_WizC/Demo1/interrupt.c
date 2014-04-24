/*
    FreeRTOS V8.0.1 - Copyright (C) 2014 Real Time Engineers Ltd. 
    All rights reserved

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

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

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
Changes from V3.0.0
	+ Added functionality to only call vTaskSwitchContext() once
	  when handling multiple interruptsources in a single interruptcall.

	+ Included Filenames changed to a .c extension to allow stepping through
	  code using F7.

Changes from V3.0.1
*/

#include <pic.h>

/* Scheduler include files. */
#include <FreeRTOS.h>
#include <task.h>
#include <queue.h>

static bit uxSwitchRequested;

/*
 * Vector for the ISR.
 */
void pointed Interrupt()
{
	/*
	 * Save the context of the current task.
	 */
	portSAVE_CONTEXT( portINTERRUPTS_FORCED );

	/*
	 * No contextswitch requested yet
	 */
	uxSwitchRequested	= pdFALSE;
	
	/*
	 * Was the interrupt the FreeRTOS SystemTick?
	 */
	#include <libFreeRTOS/Drivers/Tick/isrTick.c>

/*******************************************************************************
** DO NOT MODIFY ANYTHING ABOVE THIS LINE
********************************************************************************
** Enter the includes for the ISR-code of the FreeRTOS drivers below.
**
** You cannot use local variables. Alternatives are:
** - Use static variables	(Global RAM usage increases)
** - Call a function		(Additional cycles are needed)
** - Use unused SFR's		(preferred, no additional overhead)
** See "../Serial/isrSerialTx.c" for an example of this last option
*******************************************************************************/







/*******************************************************************************
** DO NOT MODIFY ANYTHING BELOW THIS LINE
*******************************************************************************/
	/*
	 * Was a contextswitch requested by one of the
	 * interrupthandlers?
	 */
	 if ( uxSwitchRequested )
	 {
	 	vTaskSwitchContext();
	 }
	 
	/*
	 * Restore the context of the (possibly other) task.
	 */
	portRESTORE_CONTEXT();

	#pragma asmline retfie	0
}
