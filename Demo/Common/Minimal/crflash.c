/*
	FreeRTOS.org V4.2.1 - Copyright (C) 2003-2007 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license
	and contact details.  Please ensure to read the configuration and relevant
	port sections of the online documentation.

	Also see http://www.SafeRTOS.com for an IEC 61508 compliant version along
	with commercial development and support options.
	***************************************************************************
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
			vParTestToggleLED( uxLEDToFlash );
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

