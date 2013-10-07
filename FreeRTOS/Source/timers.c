/*
    FreeRTOS V7.5.2 - Copyright (C) 2013 Real Time Engineers Ltd.

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

/* Standard includes. */
#include <stdlib.h>

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
all the API functions to use the MPU wrappers.  That should only be done when
task.h is included from an application file. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* Lint e961 and e750 are suppressed as a MISRA exception justified because the
MPU ports require MPU_WRAPPERS_INCLUDED_FROM_API_FILE to be defined for the
header files above, but not in this file, in order to generate the correct
privileged Vs unprivileged linkage and placement. */
#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE /*lint !e961 !e750. */


/* This entire source file will be skipped if the application is not configured
to include software timer functionality.  This #if is closed at the very bottom
of this file.  If you want to include software timer functionality then ensure
configUSE_TIMERS is set to 1 in FreeRTOSConfig.h. */
#if ( configUSE_TIMERS == 1 )

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

/*lint -e956 A manual analysis and inspection has been used to determine which
static variables must be declared volatile. */

/* The list in which active timers are stored.  Timers are referenced in expire
time order, with the nearest expiry time at the front of the list.  Only the
timer service task is allowed to access xActiveTimerList. */
PRIVILEGED_DATA static xList xActiveTimerList1;
PRIVILEGED_DATA static xList xActiveTimerList2;
PRIVILEGED_DATA static xList *pxCurrentTimerList;
PRIVILEGED_DATA static xList *pxOverflowTimerList;

/* A queue that is used to send commands to the timer service task. */
PRIVILEGED_DATA static xQueueHandle xTimerQueue = NULL;

#if ( INCLUDE_xTimerGetTimerDaemonTaskHandle == 1 )

	PRIVILEGED_DATA static xTaskHandle xTimerTaskHandle = NULL;

#endif

/*lint +e956 */

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
static void	prvProcessReceivedCommands( void ) PRIVILEGED_FUNCTION;

/*
 * Insert the timer into either xActiveTimerList1, or xActiveTimerList2,
 * depending on if the expire time causes a timer counter overflow.
 */
static portBASE_TYPE prvInsertTimerInActiveList( xTIMER *pxTimer, portTickType xNextExpiryTime, portTickType xTimeNow, portTickType xCommandTime ) PRIVILEGED_FUNCTION;

/*
 * An active timer has reached its expire time.  Reload the timer if it is an
 * auto reload timer, then call its callback.
 */
static void prvProcessExpiredTimer( portTickType xNextExpireTime, portTickType xTimeNow ) PRIVILEGED_FUNCTION;

/*
 * The tick count has overflowed.  Switch the timer lists after ensuring the
 * current timer list does not still reference some timers.
 */
static void prvSwitchTimerLists( portTickType xLastTime ) PRIVILEGED_FUNCTION;

/*
 * Obtain the current tick count, setting *pxTimerListsWereSwitched to pdTRUE
 * if a tick count overflow occurred since prvSampleTimeNow() was last called.
 */
static portTickType prvSampleTimeNow( portBASE_TYPE *pxTimerListsWereSwitched ) PRIVILEGED_FUNCTION;

/*
 * If the timer list contains any active timers then return the expire time of
 * the timer that will expire first and set *pxListWasEmpty to false.  If the
 * timer list does not contain any timers then return 0 and set *pxListWasEmpty
 * to pdTRUE.
 */
static portTickType prvGetNextExpireTime( portBASE_TYPE *pxListWasEmpty ) PRIVILEGED_FUNCTION;

/*
 * If a timer has expired, process it.  Otherwise, block the timer service task
 * until either a timer does expire or a command is received.
 */
static void prvProcessTimerOrBlockTask( portTickType xNextExpireTime, portBASE_TYPE xListWasEmpty ) PRIVILEGED_FUNCTION;

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
		#if ( INCLUDE_xTimerGetTimerDaemonTaskHandle == 1 )
		{
			/* Create the timer task, storing its handle in xTimerTaskHandle so
			it can be returned by the xTimerGetTimerDaemonTaskHandle() function. */
			xReturn = xTaskCreate( prvTimerTask, ( const signed char * ) "Tmr Svc", ( unsigned short ) configTIMER_TASK_STACK_DEPTH, NULL, ( ( unsigned portBASE_TYPE ) configTIMER_TASK_PRIORITY ) | portPRIVILEGE_BIT, &xTimerTaskHandle );
		}
		#else
		{
			/* Create the timer task without storing its handle. */
			xReturn = xTaskCreate( prvTimerTask, ( const signed char * ) "Tmr Svc", ( unsigned short ) configTIMER_TASK_STACK_DEPTH, NULL, ( ( unsigned portBASE_TYPE ) configTIMER_TASK_PRIORITY ) | portPRIVILEGE_BIT, NULL);
		}
		#endif
	}

	configASSERT( xReturn );
	return xReturn;
}
/*-----------------------------------------------------------*/

xTimerHandle xTimerCreate( const signed char * const pcTimerName, portTickType xTimerPeriodInTicks, unsigned portBASE_TYPE uxAutoReload, void *pvTimerID, tmrTIMER_CALLBACK pxCallbackFunction )
{
xTIMER *pxNewTimer;

	/* Allocate the timer structure. */
	if( xTimerPeriodInTicks == ( portTickType ) 0U )
	{
		pxNewTimer = NULL;
	}
	else
	{
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

			traceTIMER_CREATE( pxNewTimer );
		}
		else
		{
			traceTIMER_CREATE_FAILED();
		}
	}

	/* 0 is not a valid value for xTimerPeriodInTicks. */
	configASSERT( ( xTimerPeriodInTicks > 0 ) );

	return ( xTimerHandle ) pxNewTimer;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xTimerGenericCommand( xTimerHandle xTimer, portBASE_TYPE xCommandID, portTickType xOptionalValue, signed portBASE_TYPE *pxHigherPriorityTaskWoken, portTickType xBlockTime )
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

		if( pxHigherPriorityTaskWoken == NULL )
		{
			if( xTaskGetSchedulerState() == taskSCHEDULER_RUNNING )
			{
				xReturn = xQueueSendToBack( xTimerQueue, &xMessage, xBlockTime );
			}
			else
			{
				xReturn = xQueueSendToBack( xTimerQueue, &xMessage, tmrNO_DELAY );
			}
		}
		else
		{
			xReturn = xQueueSendToBackFromISR( xTimerQueue, &xMessage, pxHigherPriorityTaskWoken );
		}

		traceTIMER_COMMAND_SEND( xTimer, xCommandID, xOptionalValue, xReturn );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

#if ( INCLUDE_xTimerGetTimerDaemonTaskHandle == 1 )

	xTaskHandle xTimerGetTimerDaemonTaskHandle( void )
	{
		/* If xTimerGetTimerDaemonTaskHandle() is called before the scheduler has been
		started, then xTimerTaskHandle will be NULL. */
		configASSERT( ( xTimerTaskHandle != NULL ) );
		return xTimerTaskHandle;
	}

#endif
/*-----------------------------------------------------------*/

static void prvProcessExpiredTimer( portTickType xNextExpireTime, portTickType xTimeNow )
{
xTIMER *pxTimer;
portBASE_TYPE xResult;

	/* Remove the timer from the list of active timers.  A check has already
	been performed to ensure the list is not empty. */
	pxTimer = ( xTIMER * ) listGET_OWNER_OF_HEAD_ENTRY( pxCurrentTimerList );
	( void ) uxListRemove( &( pxTimer->xTimerListItem ) );
	traceTIMER_EXPIRED( pxTimer );

	/* If the timer is an auto reload timer then calculate the next
	expiry time and re-insert the timer in the list of active timers. */
	if( pxTimer->uxAutoReload == ( unsigned portBASE_TYPE ) pdTRUE )
	{
		/* This is the only time a timer is inserted into a list using
		a time relative to anything other than the current time.  It
		will therefore be inserted into the correct list relative to
		the time this task thinks it is now, even if a command to
		switch lists due to a tick count overflow is already waiting in
		the timer queue. */
		if( prvInsertTimerInActiveList( pxTimer, ( xNextExpireTime + pxTimer->xTimerPeriodInTicks ), xTimeNow, xNextExpireTime ) == pdTRUE )
		{
			/* The timer expired before it was added to the active timer
			list.  Reload it now.  */
			xResult = xTimerGenericCommand( pxTimer, tmrCOMMAND_START, xNextExpireTime, NULL, tmrNO_DELAY );
			configASSERT( xResult );
			( void ) xResult;
		}
	}

	/* Call the timer callback. */
	pxTimer->pxCallbackFunction( ( xTimerHandle ) pxTimer );
}
/*-----------------------------------------------------------*/

static void prvTimerTask( void *pvParameters )
{
portTickType xNextExpireTime;
portBASE_TYPE xListWasEmpty;

	/* Just to avoid compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Query the timers list to see if it contains any timers, and if so,
		obtain the time at which the next timer will expire. */
		xNextExpireTime = prvGetNextExpireTime( &xListWasEmpty );

		/* If a timer has expired, process it.  Otherwise, block this task
		until either a timer does expire, or a command is received. */
		prvProcessTimerOrBlockTask( xNextExpireTime, xListWasEmpty );

		/* Empty the command queue. */
		prvProcessReceivedCommands();
	}
}
/*-----------------------------------------------------------*/

static void prvProcessTimerOrBlockTask( portTickType xNextExpireTime, portBASE_TYPE xListWasEmpty )
{
portTickType xTimeNow;
portBASE_TYPE xTimerListsWereSwitched;

	vTaskSuspendAll();
	{
		/* Obtain the time now to make an assessment as to whether the timer
		has expired or not.  If obtaining the time causes the lists to switch
		then don't process this timer as any timers that remained in the list
		when the lists were switched will have been processed within the
		prvSampelTimeNow() function. */
		xTimeNow = prvSampleTimeNow( &xTimerListsWereSwitched );
		if( xTimerListsWereSwitched == pdFALSE )
		{
			/* The tick count has not overflowed, has the timer expired? */
			if( ( xListWasEmpty == pdFALSE ) && ( xNextExpireTime <= xTimeNow ) )
			{
				( void ) xTaskResumeAll();
				prvProcessExpiredTimer( xNextExpireTime, xTimeNow );
			}
			else
			{
				/* The tick count has not overflowed, and the next expire
				time has not been reached yet.  This task should therefore
				block to wait for the next expire time or a command to be
				received - whichever comes first.  The following line cannot
				be reached unless xNextExpireTime > xTimeNow, except in the
				case when the current timer list is empty. */
				vQueueWaitForMessageRestricted( xTimerQueue, ( xNextExpireTime - xTimeNow ) );

				if( xTaskResumeAll() == pdFALSE )
				{
					/* Yield to wait for either a command to arrive, or the block time
					to expire.  If a command arrived between the critical section being
					exited and this yield then the yield will not cause the task
					to block. */
					portYIELD_WITHIN_API();
				}
			}
		}
		else
		{
			( void ) xTaskResumeAll();
		}
	}
}
/*-----------------------------------------------------------*/

static portTickType prvGetNextExpireTime( portBASE_TYPE *pxListWasEmpty )
{
portTickType xNextExpireTime;

	/* Timers are listed in expiry time order, with the head of the list
	referencing the task that will expire first.  Obtain the time at which
	the timer with the nearest expiry time will expire.  If there are no
	active timers then just set the next expire time to 0.  That will cause
	this task to unblock when the tick count overflows, at which point the
	timer lists will be switched and the next expiry time can be
	re-assessed.  */
	*pxListWasEmpty = listLIST_IS_EMPTY( pxCurrentTimerList );
	if( *pxListWasEmpty == pdFALSE )
	{
		xNextExpireTime = listGET_ITEM_VALUE_OF_HEAD_ENTRY( pxCurrentTimerList );
	}
	else
	{
		/* Ensure the task unblocks when the tick count rolls over. */
		xNextExpireTime = ( portTickType ) 0U;
	}

	return xNextExpireTime;
}
/*-----------------------------------------------------------*/

static portTickType prvSampleTimeNow( portBASE_TYPE *pxTimerListsWereSwitched )
{
portTickType xTimeNow;
PRIVILEGED_DATA static portTickType xLastTime = ( portTickType ) 0U; /*lint !e956 Variable is only accessible to one task. */

	xTimeNow = xTaskGetTickCount();

	if( xTimeNow < xLastTime )
	{
		prvSwitchTimerLists( xLastTime );
		*pxTimerListsWereSwitched = pdTRUE;
	}
	else
	{
		*pxTimerListsWereSwitched = pdFALSE;
	}

	xLastTime = xTimeNow;

	return xTimeNow;
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvInsertTimerInActiveList( xTIMER *pxTimer, portTickType xNextExpiryTime, portTickType xTimeNow, portTickType xCommandTime )
{
portBASE_TYPE xProcessTimerNow = pdFALSE;

	listSET_LIST_ITEM_VALUE( &( pxTimer->xTimerListItem ), xNextExpiryTime );
	listSET_LIST_ITEM_OWNER( &( pxTimer->xTimerListItem ), pxTimer );

	if( xNextExpiryTime <= xTimeNow )
	{
		/* Has the expiry time elapsed between the command to start/reset a
		timer was issued, and the time the command was processed? */
		if( ( xTimeNow - xCommandTime ) >= pxTimer->xTimerPeriodInTicks )
		{
			/* The time between a command being issued and the command being
			processed actually exceeds the timers period.  */
			xProcessTimerNow = pdTRUE;
		}
		else
		{
			vListInsert( pxOverflowTimerList, &( pxTimer->xTimerListItem ) );
		}
	}
	else
	{
		if( ( xTimeNow < xCommandTime ) && ( xNextExpiryTime >= xCommandTime ) )
		{
			/* If, since the command was issued, the tick count has overflowed
			but the expiry time has not, then the timer must have already passed
			its expiry time and should be processed immediately. */
			xProcessTimerNow = pdTRUE;
		}
		else
		{
			vListInsert( pxCurrentTimerList, &( pxTimer->xTimerListItem ) );
		}
	}

	return xProcessTimerNow;
}
/*-----------------------------------------------------------*/

static void	prvProcessReceivedCommands( void )
{
xTIMER_MESSAGE xMessage;
xTIMER *pxTimer;
portBASE_TYPE xTimerListsWereSwitched, xResult;
portTickType xTimeNow;

	while( xQueueReceive( xTimerQueue, &xMessage, tmrNO_DELAY ) != pdFAIL ) /*lint !e603 xMessage does not have to be initialised as it is passed out, not in, and it is not used unless xQueueReceive() returns pdTRUE. */
	{
		pxTimer = xMessage.pxTimer;

		if( listIS_CONTAINED_WITHIN( NULL, &( pxTimer->xTimerListItem ) ) == pdFALSE )
		{
			/* The timer is in a list, remove it. */
			( void ) uxListRemove( &( pxTimer->xTimerListItem ) );
		}

		traceTIMER_COMMAND_RECEIVED( pxTimer, xMessage.xMessageID, xMessage.xMessageValue );

		/* In this case the xTimerListsWereSwitched parameter is not used, but 
		it must be present in the function call.  prvSampleTimeNow() must be 
		called after the message is received from xTimerQueue so there is no 
		possibility of a higher priority task adding a message to the message
		queue with a time that is ahead of the timer daemon task (because it
		pre-empted the timer daemon task after the xTimeNow value was set). */
		xTimeNow = prvSampleTimeNow( &xTimerListsWereSwitched );

		switch( xMessage.xMessageID )
		{
			case tmrCOMMAND_START :
				/* Start or restart a timer. */
				if( prvInsertTimerInActiveList( pxTimer,  xMessage.xMessageValue + pxTimer->xTimerPeriodInTicks, xTimeNow, xMessage.xMessageValue ) == pdTRUE )
				{
					/* The timer expired before it was added to the active timer
					list.  Process it now. */
					pxTimer->pxCallbackFunction( ( xTimerHandle ) pxTimer );

					if( pxTimer->uxAutoReload == ( unsigned portBASE_TYPE ) pdTRUE )
					{
						xResult = xTimerGenericCommand( pxTimer, tmrCOMMAND_START, xMessage.xMessageValue + pxTimer->xTimerPeriodInTicks, NULL, tmrNO_DELAY );
						configASSERT( xResult );
						( void ) xResult;
					}
				}
				break;

			case tmrCOMMAND_STOP :
				/* The timer has already been removed from the active list.
				There is nothing to do here. */
				break;

			case tmrCOMMAND_CHANGE_PERIOD :
				pxTimer->xTimerPeriodInTicks = xMessage.xMessageValue;
				configASSERT( ( pxTimer->xTimerPeriodInTicks > 0 ) );

				/* The new period does not really have a reference, and can be
				longer or shorter than the old one.  The command time is 
				therefore set to the current time, and as the period cannot be
				zero the next expiry time can only be in the future, meaning
				(unlike for the xTimerStart() case above) there is no fail case
				that needs to be handled here. */
				( void ) prvInsertTimerInActiveList( pxTimer, ( xTimeNow + pxTimer->xTimerPeriodInTicks ), xTimeNow, xTimeNow );
				break;

			case tmrCOMMAND_DELETE :
				/* The timer has already been removed from the active list,
				just free up the memory. */
				vPortFree( pxTimer );
				break;

			default	:
				/* Don't expect to get here. */
				break;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSwitchTimerLists( portTickType xLastTime )
{
portTickType xNextExpireTime, xReloadTime;
xList *pxTemp;
xTIMER *pxTimer;
portBASE_TYPE xResult;

	/* Remove compiler warnings if configASSERT() is not defined. */
	( void ) xLastTime;

	/* The tick count has overflowed.  The timer lists must be switched.
	If there are any timers still referenced from the current timer list
	then they must have expired and should be processed before the lists
	are switched. */
	while( listLIST_IS_EMPTY( pxCurrentTimerList ) == pdFALSE )
	{
		xNextExpireTime = listGET_ITEM_VALUE_OF_HEAD_ENTRY( pxCurrentTimerList );

		/* Remove the timer from the list. */
		pxTimer = ( xTIMER * ) listGET_OWNER_OF_HEAD_ENTRY( pxCurrentTimerList );
		( void ) uxListRemove( &( pxTimer->xTimerListItem ) );

		/* Execute its callback, then send a command to restart the timer if
		it is an auto-reload timer.  It cannot be restarted here as the lists
		have not yet been switched. */
		pxTimer->pxCallbackFunction( ( xTimerHandle ) pxTimer );

		if( pxTimer->uxAutoReload == ( unsigned portBASE_TYPE ) pdTRUE )
		{
			/* Calculate the reload value, and if the reload value results in
			the timer going into the same timer list then it has already expired
			and the timer should be re-inserted into the current list so it is
			processed again within this loop.  Otherwise a command should be sent
			to restart the timer to ensure it is only inserted into a list after
			the lists have been swapped. */
			xReloadTime = ( xNextExpireTime + pxTimer->xTimerPeriodInTicks );
			if( xReloadTime > xNextExpireTime )
			{
				listSET_LIST_ITEM_VALUE( &( pxTimer->xTimerListItem ), xReloadTime );
				listSET_LIST_ITEM_OWNER( &( pxTimer->xTimerListItem ), pxTimer );
				vListInsert( pxCurrentTimerList, &( pxTimer->xTimerListItem ) );
			}
			else
			{
				xResult = xTimerGenericCommand( pxTimer, tmrCOMMAND_START, xNextExpireTime, NULL, tmrNO_DELAY );
				configASSERT( xResult );
				( void ) xResult;
			}
		}
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
			xTimerQueue = xQueueCreate( ( unsigned portBASE_TYPE ) configTIMER_QUEUE_LENGTH, sizeof( xTIMER_MESSAGE ) );
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

/* This entire source file will be skipped if the application is not configured
to include software timer functionality.  If you want to include software timer
functionality then ensure configUSE_TIMERS is set to 1 in FreeRTOSConfig.h. */
#endif /* configUSE_TIMERS == 1 */



