/*
    FreeRTOS V7.1.0 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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
