/*
    FreeRTOS V7.5.3 - Copyright (C) 2013 Real Time Engineers Ltd. 
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

/**
 * Repeatedly toggles one or more LEDs using software timers - one timer per
 * LED.
 */
 
/* Scheduler include files. */
#include "FreeRTOS.h"
#include "timers.h"

/* Demo program include files. */
#include "partest.h"
#include "flash_timer.h"

/* The toggle rates are all a multple of ledFLASH_RATE_BASE. */
#define ledFLASH_RATE_BASE	( ( ( portTickType ) 333 ) / portTICK_RATE_MS )

/* A block time of zero simple means "don't block". */
#define ledDONT_BLOCK		( ( portTickType ) 0 )

/*-----------------------------------------------------------*/

/*
 * The callback function used by each LED flashing timer.  All the timers use
 * this function, and the timer ID is used within the function to determine
 * which timer has actually expired.
 */
static void prvLEDTimerCallback( xTimerHandle xTimer );

/*-----------------------------------------------------------*/

void vStartLEDFlashTimers( unsigned portBASE_TYPE uxNumberOfLEDs )
{
unsigned portBASE_TYPE uxLEDTimer;
xTimerHandle xTimer;

	/* Create and start the requested number of timers. */
	for( uxLEDTimer = 0; uxLEDTimer < uxNumberOfLEDs; ++uxLEDTimer )
	{
		/* Create the timer. */
		xTimer = xTimerCreate( 	( const signed char * const ) "Flasher",/* A text name, purely to help debugging. */
								ledFLASH_RATE_BASE * ( uxLEDTimer + 1 ),	/* The timer period, which is a multiple of ledFLASH_RATE_BASE. */
								pdTRUE,									/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) uxLEDTimer,					/* The ID is used to identify the timer within the timer callback function, as each timer uses the same callback. */
								prvLEDTimerCallback						/* Each timer uses the same callback. */
							  );
				
		/* If the timer was created successfully, attempt to start it.  If the
		scheduler has not yet been started then the timer command queue must
		be long enough to hold each command sent to it until such time that the
		scheduler is started.  The timer command queue length is set by
		configTIMER_QUEUE_LENGTH in FreeRTOSConfig.h. */
		if( xTimer != NULL )
		{
			xTimerStart( xTimer, ledDONT_BLOCK );
		}							  
	}
}
/*-----------------------------------------------------------*/

static void prvLEDTimerCallback( xTimerHandle xTimer )
{
portBASE_TYPE xTimerID;

	/* The timer ID is used to identify the timer that has actually expired as
	each timer uses the same callback.  The ID is then also used as the number
	of the LED that is to be toggled. */
	xTimerID = ( portBASE_TYPE ) pvTimerGetTimerID( xTimer );
	vParTestToggleLED( xTimerID );
}


