/* Need to consider the switching of timer lists, and the placement of tasks into
the current and overflow timer lists very carefully.  For example, should the
assessment as to which list a timer should be inserted into be relative the the
tick count at the timer, or the tick count when the timer task unblocked, etc. */

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

/* Misc definitions. */
#define tmrNO_DELAY		( portTickType ) 0U

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
	portBASE_TYPE			xMessageID;			/*<< The command being sent to the timer service task. */
	portTickType			xMessageValue;		/*<< An optional value used by a subset of commands, for example, when chaning the period of a timer. */
	xTIMER *				pxTimer;			/*<< The timer to which the command will be applied. */
} xTIMER_MESSAGE;


/* The list in which active timers are stored.  Timers are referenced in expire
time order, with the nearest expiry time at the front of the list.  Only the
timer service task is allowed to access xActiveTimerList. */
PRIVILEGED_DATA static xList xActiveTimerList1;
PRIVILEGED_DATA static xList xActiveTimerList2;
PRIVILEGED_DATA static xList *pxCurrentTimerList;
PRIVILEGED_DATA static xList *pxOverflowTimerList;

/* A queue that is used to send commands to the timer service task. */
PRIVILEGED_DATA static xQueueHandle xTimerQueue = NULL;

/*-----------------------------------------------------------*/

/*
 * Initialise the infrustructure used by the timer service task if it has not
 * been initialised already.
 */
static void prvCheckForValidListAndQueue( void ) PRIVILEGED_FUNCTION;

/*
 * The timer service task (daemon).  Timer functionality is controlled by this
 * task.  Other tasks communicate with the timer service task using the
 * xTimerQueue queue.
 */
static void prvTimerTask( void *pvParameters ) PRIVILEGED_FUNCTION;

/*
 * Called by the timer service task to interpret and process a command it
 * received on the timer queue.
 */
static void	prvProcessReceivedCommands( void ) PRIVILEGED_FUNCTION;

/*
 * Insert the timer into either xActiveTimerList1, or xActiveTimerList2, 
 * depending on if the expire time causes a timer counter overflow. 
 */
static void prvInsertTimerInActiveList( xTIMER *pxTimer, portTickType xNextExpiryTime );

/*-----------------------------------------------------------*/

portBASE_TYPE xTimerCreateTimerTask( void )
{
portBASE_TYPE xReturn = pdFAIL;

	/* This function is called when the scheduler is started if
	configUSE_TIMERS is set to 1.  Check that the infrustructure used by the
	timer service task has been created/initialised.  If timers have already
	been created then the initialisation will already have been performed. */
	prvCheckForValidListAndQueue();

	if( xTimerQueue != NULL )
	{
		xReturn = xTaskCreate( prvTimerTask, ( const signed char * ) "Timer Service", configTIMER_TASK_STACK_DEPTH, NULL, configTIMER_TASK_PRIORITY, NULL );
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
		/* Ensure the infrustructure used by the timer service task has been
		created/initialised. */
		prvCheckForValidListAndQueue();

		/* Initialise the timer structure members using the function parameters. */
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

portBASE_TYPE xTimerGenericCommand( xTimerHandle xTimer, portBASE_TYPE xCommandID, portTickType xOptionalValue, portTickType xBlockTime )
{
portBASE_TYPE xReturn = pdFAIL;
xTIMER_MESSAGE xMessage;

	/* Send a message to the timer service task to perform a particular action
	on a particular timer definition. */
	if( xTimerQueue != NULL )
	{
		/* Send a command to the timer service task to start the xTimer timer. */
		xMessage.xMessageID = xCommandID;
		xMessage.xMessageValue = xOptionalValue;
		xMessage.pxTimer = ( xTIMER * ) xTimer;

		if( xTaskGetSchedulerState() == taskSCHEDULER_RUNNING )
		{
			xReturn = xQueueSendToBack( xTimerQueue, &xMessage, xBlockTime );
		}
		else
		{
			xReturn = xQueueSendToBack( xTimerQueue, &xMessage, tmrNO_DELAY );
		}
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static void prvTimerTask( void *pvParameters )
{
portTickType xNextExpireTime, xTimeNow;
xTIMER *pxTimer;

	/* Just to avoid compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Timers are listed in expiry time order, with the head of the list
		referencing the task that will expire first.  Obtain the time at which
		the timer with the nearest expiry time will expire.  If there are no
		active timers then just set the next expire time to the maximum possible
		time to ensure this task does not run unnecessarily. */
		if( listLIST_IS_EMPTY( pxCurrentTimerList ) == pdFALSE )
		{
			xNextExpireTime = listGET_ITEM_VALUE_OF_HEAD_ENTRY( pxCurrentTimerList );
		}
		else
		{
			xNextExpireTime = portMAX_DELAY;
		}

		/* Has the timer expired? */
		if( xNextExpireTime <= xTaskGetTickCount() )
		{
			/* Remove the timer from the list of active timers. */
			pxTimer = listGET_OWNER_OF_HEAD_ENTRY( pxCurrentTimerList );
			vListRemove( &( pxTimer->xTimerListItem ) );

			/* If the timer is an autoreload timer then calculate the next
			expiry time and re-insert the timer in the list of active timers. */
			if( pxTimer->uxAutoReload == pdTRUE )
			{
				prvInsertTimerInActiveList( pxTimer, ( xNextExpireTime + pxTimer->xTimerPeriodInTicks ) );				
			}

			/* Call the timer callback. */
			pxTimer->pxCallbackFunction( ( xTimerHandle ) pxTimer );
		}
		else
		{
			/* Block this task until the next timer expires, or a command is
			received. */
			taskENTER_CRITICAL();
			{
				xTimeNow = xTaskGetTickCount();
				if( xTimeNow < xNextExpireTime )
				{
					/* This is a simple fast function - a yield will not be
					performed until	after this critical section exits. */
					vQueueWaitForMessageRestricted( xTimerQueue, ( xNextExpireTime - xTimeNow ) );
				}
			}
			taskEXIT_CRITICAL();

			/* Yield to wait for either a command to arrive, or the block time
			to expire.  If a command arrived between the critical section being
			exited and this yeild then the yield will just return to the same
			task. */
			portYIELD_WITHIN_API();

			/* Empty the command queue, if it contains any commands. */
			prvProcessReceivedCommands();
		}
	}
}
/*-----------------------------------------------------------*/

static void prvInsertTimerInActiveList( xTIMER *pxTimer, portTickType xNextExpiryTime )
{
	listSET_LIST_ITEM_VALUE( &( pxTimer->xTimerListItem ), xNextExpiryTime );
	listSET_LIST_ITEM_OWNER( &( pxTimer->xTimerListItem ), pxTimer );
	
	if( xNextExpiryTime < xTaskGetTickCount() )
	{
		vListInsert( pxOverflowTimerList, &( pxTimer->xTimerListItem ) );
	}
	else
	{
		vListInsert( pxCurrentTimerList, &( pxTimer->xTimerListItem ) );
	}
}
/*-----------------------------------------------------------*/

static void	prvProcessReceivedCommands( void )
{
xTIMER_MESSAGE xMessage;
xTIMER *pxTimer;
xList *pxTemp;

	while( xQueueReceive( xTimerQueue, &xMessage, tmrNO_DELAY ) != pdFAIL )
	{
		pxTimer = xMessage.pxTimer;

		/* Is the timer already in the list of active timers?  When the command
		is trmCOMMAND_PROCESS_TIMER_OVERFLOW, the timer will be NULL as the
		command is to the task rather than to an individual timer. */
		if( pxTimer != NULL )
		{
			if( listIS_CONTAINED_WITHIN( NULL, &( pxTimer->xTimerListItem ) ) == pdFALSE )
			{
				/* The timer is in the list, remove it. */
				vListRemove( &( pxTimer->xTimerListItem ) );
			}
		}

		switch( xMessage.xMessageID )
		{
			case tmrCOMMAND_START :	
				/* Start or restart a timer. */
				prvInsertTimerInActiveList( pxTimer,  xTaskGetTickCount() + pxTimer->xTimerPeriodInTicks );
				break;

			case tmrCOMMAND_STOP :	
				/* The timer has already been removed from the active list.
				There is nothing to do here. */
				break;

			case tmrCOMMAND_CHANGE_PERIOD :
				pxTimer->xTimerPeriodInTicks = xMessage.xMessageValue;
				prvInsertTimerInActiveList( pxTimer, ( xTaskGetTickCount() + pxTimer->xTimerPeriodInTicks ) );
				break;

			case tmrCOMMAND_DELETE :
				/* The timer has already been removed from the active list,
				just free up the memory. */
				vPortFree( pxTimer );
				break;
				
			case trmCOMMAND_PROCESS_TIMER_OVERFLOW :
				/* The tick count has overflowed.  The timer lists must be
				switched. */
				pxTemp = pxCurrentTimerList;
				pxCurrentTimerList = pxOverflowTimerList;
				pxOverflowTimerList = pxTemp;
				break;

			default	:			
				/* Don't expect to get here. */
				break;
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
			vListInitialise( &xActiveTimerList1 );
			vListInitialise( &xActiveTimerList2 );
			pxCurrentTimerList = &xActiveTimerList1;
			pxOverflowTimerList = &xActiveTimerList2;
			xTimerQueue = xQueueCreate( configTIMER_QUEUE_LENGTH, sizeof( xTIMER_MESSAGE ) );
		}
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

portBASE_TYPE xTimerIsTimerActive( xTimerHandle xTimer )
{
portBASE_TYPE xTimerIsInActiveList;
xTIMER *pxTimer = ( xTIMER * ) xTimer;

	/* Is the timer in the list of active timers? */
	taskENTER_CRITICAL();
	{
		/* Checking to see if it is in the NULL list in effect checks to see if
		it is referenced from either the current or the overflow timer lists in
		one go, but the logic has to be reversed, hence the '!'. */
		xTimerIsInActiveList = !( listIS_CONTAINED_WITHIN( NULL, &( pxTimer->xTimerListItem ) ) );
	}
	taskEXIT_CRITICAL();

	return xTimerIsInActiveList;
}
/*-----------------------------------------------------------*/

void *pvTimerGetTimerID( xTimerHandle xTimer )
{
xTIMER *pxTimer = ( xTIMER * ) xTimer;

	return pxTimer->pvTimerID;
}
/*-----------------------------------------------------------*/

