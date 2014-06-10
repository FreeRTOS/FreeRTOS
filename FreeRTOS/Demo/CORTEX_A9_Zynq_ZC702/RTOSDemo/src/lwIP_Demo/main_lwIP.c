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

/******************************************************************************
 * NOTE 1:  This project provides three demo applications.  A simple blinky
 * style project, a more comprehensive test and demo application, and an
 * lwIP example.  The mainSELECTED_APPLICATION setting in main.c is used to
 * select between the three.  See the notes on using mainSELECTED_APPLICATION
 * in main.c.  This file implements the simply blinky style version.
 *
 * NOTE 2:  This file only contains the source code that is specific to the
 * basic demo.  Generic functions, such FreeRTOS hook functions, and functions
 * required to configure the hardware are defined in main.c.
 ******************************************************************************
 */
#warning Need to update the comment above.

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* Standard demo includes. */
#include "partest.h"

/* lwIP includes. */
#include "lwip/tcpip.h"

/* The rate at which data is sent to the queue.  The 200ms value is converted
to ticks using the portTICK_PERIOD_MS constant. */
#define mainTIMER_PERIOD_MS			( 200 / portTICK_PERIOD_MS )

/* The LED toggled by the Rx task. */
#define mainTIMER_LED				( 0 )

/* A block time of zero just means "don't block". */
#define mainDONT_BLOCK				( 0 )

/*-----------------------------------------------------------*/

/*
 * The callback for the timer that just toggles an LED to show the system is
 * running.
 */
static void prvLEDToggleTimer( TimerHandle_t pxTimer );

/*
 * Defined in lwIPApps.c.
 */
extern void lwIPAppsInit( void *pvArguments );

/*-----------------------------------------------------------*/

void main_lwIP( void )
{
TimerHandle_t xTimer;

	/* Init lwIP and start lwIP tasks. */
	tcpip_init( lwIPAppsInit, NULL );

	/* A timer is used to toggle an LED just to show the application is
	executing. */
	xTimer = xTimerCreate( 	"LED", 					/* Text name to make debugging easier. */
							mainTIMER_PERIOD_MS, 	/* The timer's period. */
							pdTRUE,					/* This is an auto reload timer. */
							NULL,					/* ID is not used. */
							prvLEDToggleTimer );	/* The callback function. */

	/* Start the timer. */
	configASSERT( xTimer );
	xTimerStart( xTimer, mainDONT_BLOCK );

	/* Start the tasks and timer running. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then
	there was either insufficient FreeRTOS heap memory available for the idle
	and/or timer tasks to be created, or vTaskStartScheduler() was called from
	User mode.  See the memory management section on the FreeRTOS web site for
	more details on the FreeRTOS heap http://www.freertos.org/a00111.html.  The
	mode from which main() is called is set in the C start up code and must be
	a privileged mode (not user mode). */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvLEDToggleTimer( TimerHandle_t pxTimer )
{
	/* Prevent compiler warnings. */
	( void ) pxTimer;

	/* Just toggle an LED to show the application is running. */
	vParTestToggleLED( mainTIMER_LED );
}

/*-----------------------------------------------------------*/
