/*
    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd. 
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
 * Utility functions required to gather run time statistics.  See:
 * http://www.freertos.org/rtos-run-time-stats.html
 *
 * Note that this is a simulated port, where simulated time is a lot slower than
 * real time, therefore the run time counter values have no real meaningful
 * units.
 *
 * Also note that it is assumed this demo is going to be used for short periods
 * of time only, and therefore timer overflows are not handled.
*/

/* FreeRTOS includes. */
#include <FreeRTOS.h>

/* Variables used in the creation of the run time stats time base.  Run time 
stats record how much time each task spends in the Running state. */
static long long llInitialRunTimeCounterValue = 0LL, llTicksPerHundedthMillisecond = 0LL;

/*-----------------------------------------------------------*/

void vConfigureTimerForRunTimeStats( void )
{
LARGE_INTEGER liPerformanceCounterFrequency, liInitialRunTimeValue;

	/* Initialise the variables used to create the run time stats time base.
	Run time stats record how much time each task spends in the Running 
	state. */

	if( QueryPerformanceFrequency( &liPerformanceCounterFrequency ) == 0 )
	{
		llTicksPerHundedthMillisecond = 1;
	}
	else
	{
		/* How many times does the performance counter increment in 1/100th
		millisecond. */
		llTicksPerHundedthMillisecond = liPerformanceCounterFrequency.QuadPart / 100000LL;

		/* What is the performance counter value now, this will be subtracted
		from readings taken at run time. */
		QueryPerformanceCounter( &liInitialRunTimeValue );
		llInitialRunTimeCounterValue = liInitialRunTimeValue.QuadPart;
	}
}
/*-----------------------------------------------------------*/

unsigned long ulGetRunTimeCounterValue( void )
{
LARGE_INTEGER liCurrentCount;
unsigned long ulReturn;

	/* What is the performance counter value now? */
	QueryPerformanceCounter( &liCurrentCount );

	/* Subtract the performance counter value reading taken when the 
	application started to get a count from that reference point, then
	scale to (simulated) 1/100ths of a millisecond. */
	ulReturn = ( unsigned long ) ( ( liCurrentCount.QuadPart - llInitialRunTimeCounterValue ) / llTicksPerHundedthMillisecond );

	return ulReturn;
}
/*-----------------------------------------------------------*/
