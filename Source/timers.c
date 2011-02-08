/* Need a method of switching to an overflow list. _RB_*/

/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
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

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
all the API functions to use the MPU wrappers.  That should only be done when
task.h is included from an application file. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/* IDs for commands that can be sent/received on the timer queue. */
#define tmrSTART		0

/* Misc definitions. */
#define timerNO_DELAY	( portTickType ) 0U

/* The definition of the timers themselves. */
typedef struct tmrTimerControl
{
	const signed char		*pcTimerName;		/*<< Text name.  This is not used by the kernel, it is included simply to make debugging easier. */
	xListItem				xTimerListItem;		/*<< Standard linked list item as used by all kernel features for event management. */
	portTickType			xTimerPeriodInTicks;/*<< How quickly and often the timer expires. */
	unsigned portBASE_TYPE	uxAutoReload;		/*<< Set to pdTRUE if the timer should be automatically restarted once expired.  Set to pdFALSE if the timer is, in effect, a one shot timer. */
	void 					*pvTimerID;			/*<< An ID to identify the timer.  This allows the timer to be identified when the same callback is used for multiple timers. */
	tmrTIMER_CALLBACK		pxCallbackFunction;	/*<< The function that will be called when the timer expires. */
} xTIMER;

/* The definition of messages that can be sent and received on the timer 
queue. */
typedef struct tmrTimerQueueMessage
{
	portBASE_TYPE			xMessageID;
	portTickType			xMessageValue;
	xTIMER *				pxTimer;
} xTIMER_MESSAGE;


/* The list in which active timers are stored.  Timers are referenced in expire
time order, with the nearest expiry time at the front of the list.  Only the
timer service task is allowed to access xActiveTimerList. */
PRIVILEGED_DATA static xList xActiveTimerList;

/* A queue that is used to send commands to the timer service task. */
PRIVILEGED_DATA static xQueueHandle xTimerQueue = NULL;

/*-----------------------------------------------------------*/

/*
 * Called when a timer is about to be modified.  If the timer is already in the
 * list of active timers then it is removed prior to the modification.
 */
static void prvRemoveTimerFromActiveList( xTIMER *pxTimer ) PRIVILEGED_FUNCTION;

static void prvCheckForValidListAndQueue( void ) PRIVILEGED_FUNCTION;

/*
 * The timer service task (daemon).
 */
static void prvTimerTask( void *pvParameters ) PRIVILEGED_FUNCTION;


/* Handlers for commands received on the timer queue. */
static void prvTimerStart( xTIMER *pxTimer );

/*-----------------------------------------------------------*/

portBASE_TYPE xTimerCreateTimerTask( void )
{
portBASE_TYPE xReturn = pdFAIL;

	/* This function is called when the scheduler is started if 
	configUSE_TIMERS is set to 1. */
	prvCheckForValidListAndQueue();

	if( xTimerQueue != NULL )
	{
		xReturn = xTaskCreate( prvTimerTask, ( const signed char * ) "Timers", configMINIMAL_STACK_SIZE, NULL, configTIMER_TASK_PRIORITY, NULL );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

xTimerHandle xTimerCreate( const signed char *pcTimerName, portTickType xTimerPeriodInTicks, unsigned portBASE_TYPE uxAutoReload, void *pvTimerID, tmrTIMER_CALLBACK pxCallbackFunction )
{
xTIMER *pxNewTimer;

	/* Allocate the timer structure. */
	pxNewTimer = ( xTIMER * ) pvPortMalloc( sizeof( xTIMER ) );
	if( pxNewTimer != NULL )
	{
		prvCheckForValidListAndQueue();

		/* Initialise the timer structure members. */
		pxNewTimer->pcTimerName = pcTimerName;
		pxNewTimer->xTimerPeriodInTicks = xTimerPeriodInTicks;
		pxNewTimer->uxAutoReload = uxAutoReload;
		pxNewTimer->pvTimerID = pvTimerID;
		pxNewTimer->pxCallbackFunction = pxCallbackFunction;
		vListInitialiseItem( &( pxNewTimer->xTimerListItem ) );
	}

	return ( xTimerHandle ) pxNewTimer;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xTimerStart( xTimerHandle xTimer, portTickType xBlockTime )
{
portBASE_TYPE xReturn = pdFAIL;
xTIMER_MESSAGE xMessage;

	if( xTimerQueue != NULL )
	{
		xMessage.xMessageID = tmrSTART;
		xMessage.pxTimer = ( xTIMER * ) xTimer;

		xReturn = xQueueSendToBack( xTimerQueue, &xMessage, xBlockTime );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void *pvTimerGetTimerID( xTimerHandle xTimer )
{
xTIMER *pxTimer = ( xTIMER * ) xTimer;

	return pxTimer->pvTimerID;
}
/*-----------------------------------------------------------*/

static void prvRemoveTimerFromActiveList( xTIMER *pxTimer )
{
	/* Is the timer already in the list of active timers? */
	if( listIS_CONTAINED_WITHIN( NULL, &( pxTimer->xTimerListItem ) ) == pdFALSE )
	{
		/* The timer is in the list, remove it. */
		vListRemove( &( pxTimer->xTimerListItem ) );
	}
}
/*-----------------------------------------------------------*/

static void prvTimerTask( void *pvParameters )
{
portTickType xNextWakeTime, xTimeNow;
xTIMER *pxTimer;
xTIMER_MESSAGE xMessage;

	/* Just to avoid compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		if( listLIST_IS_EMPTY( &xActiveTimerList ) == pdFALSE )
		{
			xNextWakeTime = listGET_ITEM_VALUE_OF_HEAD_ENTRY( &xActiveTimerList );
		}
		else
		{
			xNextWakeTime = portMAX_DELAY;
		}

		if( xNextWakeTime <= xTaskGetTickCount() )
		{
			/* Remove the timer from the list.  This functionality relies on
			the list of active timers not being accessed from outside of this
			task. */
			pxTimer = listGET_OWNER_OF_HEAD_ENTRY( &xActiveTimerList );
			vListRemove( &( pxTimer->xTimerListItem ) );

			if( pxTimer->uxAutoReload == pdTRUE )
			{
				listSET_LIST_ITEM_VALUE( &( pxTimer->xTimerListItem ), ( xNextWakeTime + pxTimer->xTimerPeriodInTicks ) );
				vListInsert( &xActiveTimerList, &( pxTimer->xTimerListItem ) );
			}

			/* Call the timer callback. */
			pxTimer->pxCallbackFunction( ( xTimerHandle ) pxTimer );
		}
		else
		{
			/* Calculate the block time. */
			taskENTER_CRITICAL();
			{
				xTimeNow = xTaskGetTickCount();
				if( xTimeNow < xNextWakeTime )
				{
					vQueueWaitForMessageRestricted( xTimerQueue, ( xNextWakeTime - xTimeNow ) );
				}
			}
			taskEXIT_CRITICAL();
			portYIELD_WITHIN_API();

			while( xQueueReceive( xTimerQueue, &xMessage, timerNO_DELAY ) != pdFAIL )
			{
				switch( xMessage.xMessageID )
				{
					case tmrSTART	:	prvTimerStart( xMessage.pxTimer );
										break;
					default			:	/* Don't expect to get here. */
										break;
				}
			}
		}
	}
}
/*-----------------------------------------------------------*/

static void prvCheckForValidListAndQueue( void )
{
	/* Check that the list from which active timers are referenced, and the
	queue used to communicate with the timer service, have been 
	initialised. */
	taskENTER_CRITICAL();
	{
		if( xTimerQueue == NULL )
		{
			vListInitialise( &xActiveTimerList );
			xTimerQueue = xQueueCreate( configTIMER_QUEUE_LENGTH, sizeof( xTIMER_MESSAGE ) );
		}
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

static void prvTimerStart( xTIMER *pxTimer )
{
portTickType xTimeToWake;

	if( pxTimer != NULL )
	{
		/* Is the timer already in the list of active timers? */
		prvRemoveTimerFromActiveList( pxTimer );

		xTimeToWake = xTaskGetTickCount() + pxTimer->xTimerPeriodInTicks;
		listSET_LIST_ITEM_VALUE( &( pxTimer->xTimerListItem ), xTimeToWake );
		listSET_LIST_ITEM_OWNER( &( pxTimer->xTimerListItem ), pxTimer );
		vListInsert( &xActiveTimerList, &( pxTimer->xTimerListItem ) );
	}
}










portBASE_TYPE xTimerIsTimerActive( xTimerHandle xTimer )
{
	return pdFALSE;
}

void vTimerStop( xTimerHandle xTimer )
{
}


void vTimerChangePeriod( xTimerHandle xTimer )
{
}

void vTimerDelete( xTimerHandle xTimer )
{
}
/*-----------------------------------------------------------*/
