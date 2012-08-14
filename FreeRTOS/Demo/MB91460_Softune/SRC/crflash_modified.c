/*
    FreeRTOS V7.2.0 - Copyright (C) 2012 Real Time Engineers Ltd.
	

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
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/*
 * This demo application file demonstrates the use of queues to pass data
 * between co-routines.
 *
 * N represents the number of 'fixed delay' co-routines that are created and
 * is set during initialisation.
 *
 * N 'fixed delay' co-routines are created that just block for a fixed
 * period then post the number of an LED onto a queue.  Each such co-routine
 * uses a different block period.  A single 'flash' co-routine is also created
 * that blocks on the same queue, waiting for the number of the next LED it
 * should flash.  Upon receiving a number it simply toggle the instructed LED
 * then blocks on the queue once more.  In this manner each LED from LED 0 to
 * LED N-1 is caused to flash at a different rate.
 *
 * The 'fixed delay' co-routines are created with co-routine priority 0.  The
 * flash co-routine is created with co-routine priority 1.  This means that
 * the queue should never contain more than a single item.  This is because
 * posting to the queue will unblock the 'flash' co-routine, and as this has
 * a priority greater than the tasks posting to the queue it is guaranteed to
 * have emptied the queue and blocked once again before the queue can contain
 * any more date.  An error is indicated if an attempt to post data to the
 * queue fails - indicating that the queue is already full.
 *
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "croutine.h"
#include "queue.h"

/* Demo application includes. */
#include "partest.h"
#include "crflash.h"

/* The queue should only need to be of length 1.  See the description at the
top of the file. */
#define crfQUEUE_LENGTH		1

#define crfFIXED_DELAY_PRIORITY		0
#define crfFLASH_PRIORITY			1

/* Only one flash co-routine is created so the index is not significant. */
#define crfFLASH_INDEX				0

/* Don't allow more than crfMAX_FLASH_TASKS 'fixed delay' co-routines to be
created. */
#define crfMAX_FLASH_TASKS			8

/* We don't want to block when posting to the queue. */
#define crfPOSTING_BLOCK_TIME		0

/* Added by MPi, this define is added in order to make the vParTestToggleLED()
work. This basically differentiates the PDR09 from PDR00. 7-seg display LEDs connected 
to PDR09 (SEG1) are used by the prvFlashCoRoutine() and PDR00 (SEG2) are used by tasks. */ 
#define PDR00_Offset	8

/*
 * The 'fixed delay' co-routine as described at the top of the file.
 */
static void prvFixedDelayCoRoutine( xCoRoutineHandle xHandle, unsigned portBASE_TYPE uxIndex );

/*
 * The 'flash' co-routine as described at the top of the file.
 */
static void prvFlashCoRoutine( xCoRoutineHandle xHandle, unsigned portBASE_TYPE uxIndex );

/* The queue used to pass data between the 'fixed delay' co-routines and the
'flash' co-routine. */
static xQueueHandle xFlashQueue;

/* This will be set to pdFALSE if we detect an error. */
static unsigned portBASE_TYPE uxCoRoutineFlashStatus = pdPASS;

/*-----------------------------------------------------------*/

/*
 * See the header file for details.
 */
void vStartFlashCoRoutines( unsigned portBASE_TYPE uxNumberToCreate )
{
unsigned portBASE_TYPE uxIndex;

	if( uxNumberToCreate > crfMAX_FLASH_TASKS )
	{
		uxNumberToCreate = crfMAX_FLASH_TASKS;
	}

	/* Create the queue used to pass data between the co-routines. */
	xFlashQueue = xQueueCreate( crfQUEUE_LENGTH, sizeof( unsigned portBASE_TYPE ) );

	if( xFlashQueue )
	{
		/* Create uxNumberToCreate 'fixed delay' co-routines. */
		for( uxIndex = 0; uxIndex < uxNumberToCreate; uxIndex++ )
		{
			xCoRoutineCreate( prvFixedDelayCoRoutine, crfFIXED_DELAY_PRIORITY, uxIndex );
		}

		/* Create the 'flash' co-routine. */
		xCoRoutineCreate( prvFlashCoRoutine, crfFLASH_PRIORITY, crfFLASH_INDEX );
	}
}
/*-----------------------------------------------------------*/

static void prvFixedDelayCoRoutine( xCoRoutineHandle xHandle, unsigned portBASE_TYPE uxIndex )
{
/* Even though this is a co-routine the xResult variable does not need to be
static as we do not need it to maintain its state between blocks. */
signed portBASE_TYPE xResult;
/* The uxIndex parameter of the co-routine function is used as an index into
the xFlashRates array to obtain the delay period to use. */
static const portTickType xFlashRates[ crfMAX_FLASH_TASKS ] = { 150 / portTICK_RATE_MS,
																200 / portTICK_RATE_MS,
																250 / portTICK_RATE_MS,
																300 / portTICK_RATE_MS,
																350 / portTICK_RATE_MS,
																400 / portTICK_RATE_MS,
																450 / portTICK_RATE_MS,
																500  / portTICK_RATE_MS };

	/* Co-routines MUST start with a call to crSTART. */
	crSTART( xHandle );

	for( ;; )
	{
		/* Post our uxIndex value onto the queue.  This is used as the LED to
		flash. */
		crQUEUE_SEND( xHandle, xFlashQueue, ( void * ) &uxIndex, crfPOSTING_BLOCK_TIME, &xResult );

		if( xResult != pdPASS )
		{
			/* For the reasons stated at the top of the file we should always
			find that we can post to the queue.  If we could not then an error
			has occurred. */
			uxCoRoutineFlashStatus = pdFAIL;
		}

		crDELAY( xHandle, xFlashRates[ uxIndex ] );
	}

	/* Co-routines MUST end with a call to crEND. */
	crEND();
}
/*-----------------------------------------------------------*/

static void prvFlashCoRoutine( xCoRoutineHandle xHandle, unsigned portBASE_TYPE uxIndex )
{
/* Even though this is a co-routine the variable do not need to be
static as we do not need it to maintain their state between blocks. */
signed portBASE_TYPE xResult;
unsigned portBASE_TYPE uxLEDToFlash;

	/* Co-routines MUST start with a call to crSTART. */
	crSTART( xHandle );
	( void ) uxIndex;
	
	for( ;; )
	{
		/* Block to wait for the number of the LED to flash. */
		crQUEUE_RECEIVE( xHandle, xFlashQueue, &uxLEDToFlash, portMAX_DELAY, &xResult );		

		if( xResult != pdPASS )
		{
			/* We would not expect to wake unless we received something. */
			uxCoRoutineFlashStatus = pdFAIL;
		}
		else
		{
			/* We received the number of an LED to flash - flash it! */
			/* Added by MPi, PDR00_Offset is added in order to make the 
			vParTestToggleLED() work. */ 
			vParTestToggleLED( uxLEDToFlash +  PDR00_Offset );
		}
	}

	/* Co-routines MUST end with a call to crEND. */
	crEND();
}
/*-----------------------------------------------------------*/

portBASE_TYPE xAreFlashCoRoutinesStillRunning( void )
{
	/* Return pdPASS or pdFAIL depending on whether an error has been detected
	or not. */
	return uxCoRoutineFlashStatus;
}

