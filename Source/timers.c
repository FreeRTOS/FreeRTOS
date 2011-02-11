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
	portTickType			xMessageValue;		/*<< An optional value used by a subset of commands, for example, when changing the period of a timer. */
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
 * Initialise the infrastructure used by the timer service task if it has not
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
static void	prvProcessReceivedCommands( portTickType xAssumedTimeNow ) PRIVILEGED_FUNCTION;

/*
 * Insert the timer into either xActiveTimerList1, or xActiveTimerList2, 
 * depending on if the expire time causes a timer counter overflow. 
 */
static void prvInsertTimerInActiveList( xTIMER *pxTimer, portTickType xNextExpiryTime, portTickType xAssumedTimeNow ) PRIVILEGED_FUNCTION;

/*
 * An active timer has reached its expire time.  Reload the timer if it is an
 * auto reload timer, then call its callback.
 */
static void prvProcessExpiredTimer( portTickType xNextExpireTime, portTickType xAssumedTimeNow ) PRIVILEGED_FUNCTION;

/*
 * The tick count has overflowed.  Switch the timer lists after ensuring the
 * current timer list does not still reference some timers.
 */
static void prvSwitchTimerLists( portTickType xAssumedTimeNow ) PRIVILEGED_FUNCTION;

/*-----------------------------------------------------------*/

portBASE_TYPE xTimerCreateTimerTask( void )
{
portBASE_TYPE xReturn = pdFAIL;

	/* This function is called when the scheduler is started if
	configUSE_TIMERS is set to 1.  Check that the infrastructure used by the
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
		/* Ensure the infrastructure used by the timer service task has been
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

static void prvProcessExpiredTimer( portTickType xNextExpireTime, portTickType xAssumedTimeNow )
{
xTIMER *pxTimer;

	if( listLIST_IS_EMPTY( pxCurrentTimerList ) == pdFALSE )
	{
		/* Remove the timer from the list of active timers. */
		pxTimer = ( xTIMER * ) listGET_OWNER_OF_HEAD_ENTRY( pxCurrentTimerList );
		vListRemove( &( pxTimer->xTimerListItem ) );

		/* If the timer is an auto reload timer then calculate the next
		expiry time and re-insert the timer in the list of active timers. */
		if( pxTimer->uxAutoReload == pdTRUE )
		{
			/* This is the only time a timer is inserted into a list using
			a time relative to anything other than the current time.  It
			will therefore be inserted into the correct list relative to
			the time this task thinks it is now, even if a command to
			switch lists due to a tick count overflow is already waiting in
			the timer queue. */
			prvInsertTimerInActiveList( pxTimer, ( xNextExpireTime + pxTimer->xTimerPeriodInTicks ), xAssumedTimeNow );
		}

		/* Call the timer callback. */
		pxTimer->pxCallbackFunction( ( xTimerHandle ) pxTimer );
	}
}
/*-----------------------------------------------------------*/

static void prvTimerTask( void *pvParameters )
{
portTickType xNextExpireTime, xTimeNow, xFrozenTimeNow;

	/* Just to avoid compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Take a snapshot of the time to use while assessing expiry and auto
		reload times. */
		xFrozenTimeNow = xTaskGetTickCount();

		/* Timers are listed in expiry time order, with the head of the list
		referencing the task that will expire first.  Obtain the time at which
		the timer with the nearest expiry time will expire.  If there are no
		active timers then just set the next expire time to the maximum possible
		time to ensure this task does not run unnecessarily.  */
		if( listLIST_IS_EMPTY( pxCurrentTimerList ) == pdFALSE )
		{
			xNextExpireTime = listGET_ITEM_VALUE_OF_HEAD_ENTRY( pxCurrentTimerList );
		}
		else
		{
			xNextExpireTime = portMAX_DELAY;
		}

		/* Has the timer expired?  This expiry time is relative to the snapshot
		of the time taken to be used in this loop iteration - so it doesn't 
		matter at this point if a tick count overflows here. */
		if( xNextExpireTime <= xFrozenTimeNow )
		{
			prvProcessExpiredTimer( xNextExpireTime, xFrozenTimeNow );
		}
		else
		{
			/* Block this task until the next timer expires, or a command is
			received. */
			vTaskSuspendAll();
			{
				/* Has the tick overflowed since a time snapshot was taken? */
				xTimeNow = xTaskGetTickCount();
				if( xTimeNow >= xFrozenTimeNow )
				{
					/* Has the expire not still not been met?  The tick count
					may be greater now than when the time snapshot was taken. */
					if( xNextExpireTime <= xTimeNow )
					{
						prvProcessExpiredTimer( xNextExpireTime, xFrozenTimeNow );
					}
					else
					{
						/* The tick count has not overflowed since the time 
						snapshot, and the next expire time has not been reached
						since the last snapshot was taken.  This task should
						therefore block to wait for the next expire time. */
						vQueueWaitForMessageRestricted( xTimerQueue, ( xNextExpireTime - xTimeNow ) );
					}
				}
				else
				{
					/* The tick count has overflowed since the time snapshot
					was taken, therefore, the task should not block but continue
					with another loop.  The command queue should contain a
					command to switch lists. */
				}
			}
			if( xTaskResumeAll() == pdFALSE )
			{
				/* Yield to wait for either a command to arrive, or the block time
				to expire.  If a command arrived between the critical section being
				exited and this yield then the yield will just return to the same
				task. */
				portYIELD_WITHIN_API();
			}

			/* Take a snapshot of the time now for use in this iteration of the
			task loop. */
			xFrozenTimeNow = xTaskGetTickCount();

			/* Empty the command queue, if it contains any commands. */
			prvProcessReceivedCommands( xFrozenTimeNow );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvInsertTimerInActiveList( xTIMER *pxTimer, portTickType xNextExpiryTime, portTickType xAssumedTimeNow )
{
	listSET_LIST_ITEM_VALUE( &( pxTimer->xTimerListItem ), xNextExpiryTime );
	listSET_LIST_ITEM_OWNER( &( pxTimer->xTimerListItem ), pxTimer );
	
	if( xNextExpiryTime < xAssumedTimeNow )
	{
		vListInsert( pxOverflowTimerList, &( pxTimer->xTimerListItem ) );
	}
	else
	{
		vListInsert( pxCurrentTimerList, &( pxTimer->xTimerListItem ) );
	}
}
/*-----------------------------------------------------------*/

static void	prvProcessReceivedCommands( portTickType xAssumedTimeNow )
{
xTIMER_MESSAGE xMessage;
xTIMER *pxTimer;
portBASE_TYPE xSwitchListsOnExit = pdFALSE;

	while( xQueueReceive( xTimerQueue, &xMessage, tmrNO_DELAY ) != pdFAIL )
	{
		pxTimer = xMessage.pxTimer;

		/* Is the timer already in a list of active timers?  When the command
		is trmCOMMAND_PROCESS_TIMER_OVERFLOW, the timer will be NULL as the
		command is to the task rather than to an individual timer. */
		if( pxTimer != NULL )
		{
			if( listIS_CONTAINED_WITHIN( NULL, &( pxTimer->xTimerListItem ) ) == pdFALSE )
			{
				/* The timer is in a list, remove it. */
				vListRemove( &( pxTimer->xTimerListItem ) );
			}
		}

		switch( xMessage.xMessageID )
		{
			case tmrCOMMAND_START :	
				/* Start or restart a timer. */
				prvInsertTimerInActiveList( pxTimer,  xAssumedTimeNow + pxTimer->xTimerPeriodInTicks, xAssumedTimeNow );
				break;

			case tmrCOMMAND_STOP :	
				/* The timer has already been removed from the active list.
				There is nothing to do here. */
				break;

			case tmrCOMMAND_CHANGE_PERIOD :
				pxTimer->xTimerPeriodInTicks = xMessage.xMessageValue;
				prvInsertTimerInActiveList( pxTimer, ( xAssumedTimeNow + pxTimer->xTimerPeriodInTicks ), xAssumedTimeNow );
				break;

			case tmrCOMMAND_DELETE :
				/* The timer has already been removed from the active list,
				just free up the memory. */
				vPortFree( pxTimer );
				break;
				
			case trmCOMMAND_PROCESS_TIMER_OVERFLOW :
				/* Hold this pending until all the other messages have been 
				processed. */
				xSwitchListsOnExit = pdTRUE;
				break;

			default	:			
				/* Don't expect to get here. */
				break;
		}
	}

	if( xSwitchListsOnExit == pdTRUE )
	{
		prvSwitchTimerLists( xAssumedTimeNow );
	}
}
/*-----------------------------------------------------------*/

static void prvSwitchTimerLists( portTickType xAssumedTimeNow )
{
portTickType xNextExpireTime;
xList *pxTemp;

	/* The tick count has overflowed.  The timer lists must be switched.  
	If there are any timers still referenced from the current timer list 
	then they must have expired and should be processed before the lists 
	are switched. */
	while( listLIST_IS_EMPTY( pxCurrentTimerList ) == pdFALSE )
	{
		xNextExpireTime = listGET_ITEM_VALUE_OF_HEAD_ENTRY( pxCurrentTimerList );
		prvProcessExpiredTimer( xNextExpireTime, xAssumedTimeNow );
	}

	pxTemp = pxCurrentTimerList;
	pxCurrentTimerList = pxOverflowTimerList;
	pxOverflowTimerList = pxTemp;
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




