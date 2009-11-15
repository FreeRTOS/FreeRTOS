/*
    FreeRTOS V6.0.1 - Copyright (C) 2009 Real Time Engineers Ltd.

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



	/*
	 * Was the interrupt a byte being received?
	 */
	#include "../Serial/isrSerialRx.c"


	/*
	 * Was the interrupt the Tx register becoming empty?
	 */
	#include "../Serial/isrSerialTx.c"



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
