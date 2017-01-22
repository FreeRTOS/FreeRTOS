/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

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

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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
static void prvFixedDelayCoRoutine( CoRoutineHandle_t xHandle, UBaseType_t uxIndex );

/*
 * The 'flash' co-routine as described at the top of the file.
 */
static void prvFlashCoRoutine( CoRoutineHandle_t xHandle, UBaseType_t uxIndex );

/* The queue used to pass data between the 'fixed delay' co-routines and the
'flash' co-routine. */
static QueueHandle_t xFlashQueue;

/* This will be set to pdFALSE if we detect an error. */
static BaseType_t xCoRoutineFlashStatus = pdPASS;

/*-----------------------------------------------------------*/

/*
 * See the header file for details.
 */
void vStartFlashCoRoutines( UBaseType_t uxNumberToCreate )
{
UBaseType_t uxIndex;

	if( uxNumberToCreate > crfMAX_FLASH_TASKS )
	{
		uxNumberToCreate = crfMAX_FLASH_TASKS;
	}

	/* Create the queue used to pass data between the co-routines. */
	xFlashQueue = xQueueCreate( crfQUEUE_LENGTH, sizeof( UBaseType_t ) );

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

static void prvFixedDelayCoRoutine( CoRoutineHandle_t xHandle, UBaseType_t uxIndex )
{
/* Even though this is a co-routine the xResult variable does not need to be
static as we do not need it to maintain its state between blocks. */
BaseType_t xResult;
/* The uxIndex parameter of the co-routine function is used as an index into
the xFlashRates array to obtain the delay period to use. */
static const TickType_t xFlashRates[ crfMAX_FLASH_TASKS ] = { 150 / portTICK_PERIOD_MS,
																200 / portTICK_PERIOD_MS,
																250 / portTICK_PERIOD_MS,
																300 / portTICK_PERIOD_MS,
																350 / portTICK_PERIOD_MS,
																400 / portTICK_PERIOD_MS,
																450 / portTICK_PERIOD_MS,
																500  / portTICK_PERIOD_MS };

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
			xCoRoutineFlashStatus = pdFAIL;
		}

		crDELAY( xHandle, xFlashRates[ uxIndex ] );
	}

	/* Co-routines MUST end with a call to crEND. */
	crEND();
}
/*-----------------------------------------------------------*/

static void prvFlashCoRoutine( CoRoutineHandle_t xHandle, UBaseType_t uxIndex )
{
/* Even though this is a co-routine the variable do not need to be
static as we do not need it to maintain their state between blocks. */
BaseType_t xResult;
UBaseType_t uxLEDToFlash;

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
			xCoRoutineFlashStatus = pdFAIL;
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

BaseType_t xAreFlashCoRoutinesStillRunning( void )
{
	/* Return pdPASS or pdFAIL depending on whether an error has been detected
	or not. */
	return xCoRoutineFlashStatus;
}

