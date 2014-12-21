/*
    FreeRTOS V8.2.0rc1 - Copyright (C) 2014 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

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
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?".  Have you defined configASSERT()?  *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

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

    ***************************************************************************
     *                                                                       *
     *   Investing in training allows your team to be as productive as       *
     *   possible as early as possible, lowering your overall development    *
     *   cost, and enabling you to bring a more robust product to market     *
     *   earlier than would otherwise be possible.  Richard Barry is both    *
     *   the architect and key author of FreeRTOS, and so also the world's   *
     *   leading authority on what is the world's most popular real time     *
     *   kernel for deeply embedded MCU designs.  Obtaining your training    *
     *   from Richard ensures your team will gain directly from his in-depth *
     *   product knowledge and years of usage experience.  Contact Real Time *
     *   Engineers Ltd to enquire about the FreeRTOS Masterclass, presented  *
     *   by Richard Barry:  http://www.FreeRTOS.org/contact
     *                                                                       *
    ***************************************************************************

    ***************************************************************************
     *                                                                       *
     *    You are receiving this top quality software for free.  Please play *
     *    fair and reciprocate by reporting any suspected issues and         *
     *    participating in the community forum:                              *
     *    http://www.FreeRTOS.org/support                                    *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

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
#define ledFLASH_RATE_BASE	( ( ( TickType_t ) 333 ) / portTICK_PERIOD_MS )

/* A block time of zero simple means "don't block". */
#define ledDONT_BLOCK		( ( TickType_t ) 0 )

/*-----------------------------------------------------------*/

/*
 * The callback function used by each LED flashing timer.  All the timers use
 * this function, and the timer ID is used within the function to determine
 * which timer has actually expired.
 */
static void prvLEDTimerCallback( TimerHandle_t xTimer );

/*-----------------------------------------------------------*/

void vStartLEDFlashTimers( UBaseType_t uxNumberOfLEDs )
{
UBaseType_t uxLEDTimer;
TimerHandle_t xTimer;

	/* Create and start the requested number of timers. */
	for( uxLEDTimer = 0; uxLEDTimer < uxNumberOfLEDs; ++uxLEDTimer )
	{
		/* Create the timer. */
		xTimer = xTimerCreate( 	"Flasher",								/* A text name, purely to help debugging. */
								ledFLASH_RATE_BASE * ( uxLEDTimer + 1 ),/* The timer period, which is a multiple of ledFLASH_RATE_BASE. */
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

static void prvLEDTimerCallback( TimerHandle_t xTimer )
{
BaseType_t xTimerID;

	/* The timer ID is used to identify the timer that has actually expired as
	each timer uses the same callback.  The ID is then also used as the number
	of the LED that is to be toggled. */
	xTimerID = ( BaseType_t ) pvTimerGetTimerID( xTimer );
	vParTestToggleLED( xTimerID );
}


