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


#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
all the API functions to use the MPU wrappers.  That should only be done when
task.h is included from an application file. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "StackMacros.h"

#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/*
 * Macro to define the amount of stack available to the idle task.
 */
#define tskIDLE_STACK_SIZE	configMINIMAL_STACK_SIZE

/*
 * Task control block.  A task control block (TCB) is allocated to each task,
 * and stores the context of the task.
 */
typedef struct tskTaskControlBlock
{
	volatile portSTACK_TYPE	*pxTopOfStack;		/*< Points to the location of the last item placed on the tasks stack.  THIS MUST BE THE FIRST MEMBER OF THE STRUCT. */

	#if ( portUSING_MPU_WRAPPERS == 1 )
		xMPU_SETTINGS xMPUSettings;				/*< The MPU settings are defined as part of the port layer.  THIS MUST BE THE SECOND MEMBER OF THE STRUCT. */
	#endif	
	
	xListItem				xGenericListItem;	/*< List item used to place the TCB in ready and blocked queues. */
	xListItem				xEventListItem;		/*< List item used to place the TCB in event lists. */
	unsigned portBASE_TYPE	uxPriority;			/*< The priority of the task where 0 is the lowest priority. */
	portSTACK_TYPE			*pxStack;			/*< Points to the start of the stack. */
	signed char				pcTaskName[ configMAX_TASK_NAME_LEN ];/*< Descriptive name given to the task when created.  Facilitates debugging only. */

	#if ( portSTACK_GROWTH > 0 )
		portSTACK_TYPE *pxEndOfStack;			/*< Used for stack overflow checking on architectures where the stack grows up from low memory. */
	#endif

	#if ( portCRITICAL_NESTING_IN_TCB == 1 )
		unsigned portBASE_TYPE uxCriticalNesting;
	#endif

	#if ( configUSE_TRACE_FACILITY == 1 )
		unsigned portBASE_TYPE	uxTCBNumber;	/*< This is used for tracing the scheduler and making debugging easier only. */
	#endif

	#if ( configUSE_MUTEXES == 1 )
		unsigned portBASE_TYPE uxBasePriority;	/*< The priority last assigned to the task - used by the priority inheritance mechanism. */
	#endif

	#if ( configUSE_APPLICATION_TASK_TAG == 1 )
		pdTASK_HOOK_CODE pxTaskTag;
	#endif

	#if ( configGENERATE_RUN_TIME_STATS == 1 )
		unsigned long ulRunTimeCounter;		/*< Used for calculating how much CPU time each task is utilising. */
	#endif

} tskTCB;


/*
 * Some kernel aware debuggers require data to be viewed to be global, rather
 * than file scope.
 */
#ifdef portREMOVE_STATIC_QUALIFIER
	#define static
#endif

/*lint -e956 */
PRIVILEGED_DATA tskTCB * volatile pxCurrentTCB = NULL;

/* Lists for ready and blocked tasks. --------------------*/

PRIVILEGED_DATA static xList pxReadyTasksLists[ configMAX_PRIORITIES ];	/*< Prioritised ready tasks. */
PRIVILEGED_DATA static xList xDelayedTaskList1;							/*< Delayed tasks. */
PRIVILEGED_DATA static xList xDelayedTaskList2;							/*< Delayed tasks (two lists are used - one for delays that have overflowed the current tick count. */
PRIVILEGED_DATA static xList * volatile pxDelayedTaskList ;				/*< Points to the delayed task list currently being used. */
PRIVILEGED_DATA static xList * volatile pxOverflowDelayedTaskList;		/*< Points to the delayed task list currently being used to hold tasks that have overflowed the current tick count. */
PRIVILEGED_DATA static xList xPendingReadyList;							/*< Tasks that have been readied while the scheduler was suspended.  They will be moved to the ready queue when the scheduler is resumed. */

#if ( INCLUDE_vTaskDelete == 1 )

	PRIVILEGED_DATA static volatile xList xTasksWaitingTermination;		/*< Tasks that have been deleted - but the their memory not yet freed. */
	PRIVILEGED_DATA static volatile unsigned portBASE_TYPE uxTasksDeleted = ( unsigned portBASE_TYPE ) 0;

#endif

#if ( INCLUDE_vTaskSuspend == 1 )

	PRIVILEGED_DATA static xList xSuspendedTaskList;					/*< Tasks that are currently suspended. */

#endif

/* File private variables. --------------------------------*/
PRIVILEGED_DATA static volatile unsigned portBASE_TYPE uxCurrentNumberOfTasks 	= ( unsigned portBASE_TYPE ) 0;
PRIVILEGED_DATA static volatile portTickType xTickCount 						= ( portTickType ) 0;
PRIVILEGED_DATA static unsigned portBASE_TYPE uxTopUsedPriority	 				= tskIDLE_PRIORITY;
PRIVILEGED_DATA static volatile unsigned portBASE_TYPE uxTopReadyPriority 		= tskIDLE_PRIORITY;
PRIVILEGED_DATA static volatile signed portBASE_TYPE xSchedulerRunning 			= pdFALSE;
PRIVILEGED_DATA static volatile unsigned portBASE_TYPE uxSchedulerSuspended	 	= ( unsigned portBASE_TYPE ) pdFALSE;
PRIVILEGED_DATA static volatile unsigned portBASE_TYPE uxMissedTicks 			= ( unsigned portBASE_TYPE ) 0;
PRIVILEGED_DATA static volatile portBASE_TYPE xMissedYield 						= ( portBASE_TYPE ) pdFALSE;
PRIVILEGED_DATA static volatile portBASE_TYPE xNumOfOverflows 					= ( portBASE_TYPE ) 0;
PRIVILEGED_DATA static unsigned portBASE_TYPE uxTaskNumber 						= ( unsigned portBASE_TYPE ) 0;
PRIVILEGED_DATA static portTickType xNextTaskUnblockTime						= ( portTickType ) portMAX_DELAY;

#if ( configGENERATE_RUN_TIME_STATS == 1 )

	PRIVILEGED_DATA static char pcStatsString[ 50 ] ;
	PRIVILEGED_DATA static unsigned long ulTaskSwitchedInTime = 0UL;	/*< Holds the value of a timer/counter the last time a task was switched in. */
	static void prvGenerateRunTimeStatsForTasksInList( const signed char *pcWriteBuffer, xList *pxList, unsigned long ulTotalRunTime ) PRIVILEGED_FUNCTION;

#endif

/* Debugging and trace facilities private variables and macros. ------------*/

/*
 * The value used to fill the stack of a task when the task is created.  This
 * is used purely for checking the high water mark for tasks.
 */
#define tskSTACK_FILL_BYTE	( 0xa5U )

/*
 * Macros used by vListTask to indicate which state a task is in.
 */
#define tskBLOCKED_CHAR		( ( signed char ) 'B' )
#define tskREADY_CHAR		( ( signed char ) 'R' )
#define tskDELETED_CHAR		( ( signed char ) 'D' )
#define tskSUSPENDED_CHAR	( ( signed char ) 'S' )

/*
 * Macros and private variables used by the trace facility.
 */
#if ( configUSE_TRACE_FACILITY == 1 )

	#define tskSIZE_OF_EACH_TRACE_LINE			( ( unsigned long ) ( sizeof( unsigned long ) + sizeof( unsigned long ) ) )
	PRIVILEGED_DATA static volatile signed char * volatile pcTraceBuffer;
	PRIVILEGED_DATA static signed char *pcTraceBufferStart;
	PRIVILEGED_DATA static signed char *pcTraceBufferEnd;
	PRIVILEGED_DATA static signed portBASE_TYPE xTracing = pdFALSE;
	static unsigned portBASE_TYPE uxPreviousTask = 255U;
	PRIVILEGED_DATA static char pcStatusString[ 50 ];

#endif

/*-----------------------------------------------------------*/

/*
 * Macro that writes a trace of scheduler activity to a buffer.  This trace
 * shows which task is running when and is very useful as a debugging tool.
 * As this macro is called each context switch it is a good idea to undefine
 * it if not using the facility.
 */
#if ( configUSE_TRACE_FACILITY == 1 )

	#define vWriteTraceToBuffer()																	\
	{																								\
		if( xTracing )																				\
		{																							\
			if( uxPreviousTask != pxCurrentTCB->uxTCBNumber )										\
			{																						\
				if( ( pcTraceBuffer + tskSIZE_OF_EACH_TRACE_LINE ) < pcTraceBufferEnd )				\
				{																					\
					uxPreviousTask = pxCurrentTCB->uxTCBNumber;										\
					*( unsigned long * ) pcTraceBuffer = ( unsigned long ) xTickCount;				\
					pcTraceBuffer += sizeof( unsigned long );										\
					*( unsigned long * ) pcTraceBuffer = ( unsigned long ) uxPreviousTask;			\
					pcTraceBuffer += sizeof( unsigned long );										\
				}																					\
				else																				\
				{																					\
					xTracing = pdFALSE;																\
				}																					\
			}																						\
		}																							\
	}

#else

	#define vWriteTraceToBuffer()

#endif
/*-----------------------------------------------------------*/

/*
 * Place the task represented by pxTCB into the appropriate ready queue for
 * the task.  It is inserted at the end of the list.  One quirk of this is
 * that if the task being inserted is at the same priority as the currently
 * executing task, then it will only be rescheduled after the currently
 * executing task has been rescheduled.
 */
#define prvAddTaskToReadyQueue( pxTCB )																					\
	if( ( pxTCB )->uxPriority > uxTopReadyPriority )																	\
	{																													\
		uxTopReadyPriority = ( pxTCB )->uxPriority;																		\
	}																													\
	vListInsertEnd( ( xList * ) &( pxReadyTasksLists[ ( pxTCB )->uxPriority ] ), &( ( pxTCB )->xGenericListItem ) )
/*-----------------------------------------------------------*/

/*
 * Macro that looks at the list of tasks that are currently delayed to see if
 * any require waking.
 *
 * Tasks are stored in the queue in the order of their wake time - meaning
 * once one tasks has been found whose timer has not expired we need not look
 * any further down the list.
 */
#define prvCheckDelayedTasks()															\
{																						\
register tskTCB *pxTCB;																	\
portTickType xItemValue;																\
																						\
	/* Is the tick count greater than or equal to the wake time of the first			\
	task referenced from the delayed tasks list? */										\
	if( xTickCount >= xNextTaskUnblockTime )											\
	{																					\
		for( ;; )																		\
		{																				\
			if( listLIST_IS_EMPTY( pxDelayedTaskList ) != pdFALSE )						\
			{																			\
				/* The delayed list is empty.  Set xNextTaskUnblockTime to the			\
				maximum possible value so it is extremely unlikely that the				\
				if( xTickCount >= xNextTaskUnblockTime ) test will pass next			\
				time through. */														\
				xNextTaskUnblockTime = portMAX_DELAY;									\
				break;																	\
			}																			\
			else																		\
			{																			\
				/* The delayed list is not empty, get the value of the item at			\
				the head of the delayed list.  This is the time at which the			\
				task at the head of the delayed list should be removed from				\
				the Blocked state. */													\
				pxTCB = ( tskTCB * ) listGET_OWNER_OF_HEAD_ENTRY( pxDelayedTaskList );	\
				xItemValue = listGET_LIST_ITEM_VALUE( &( pxTCB->xGenericListItem ) );	\
																						\
				if( xTickCount < xItemValue )											\
				{																		\
					/* It is not time to unblock this item yet, but the item			\
					value is the time at which the task at the head of the				\
					blocked list should be removed from the Blocked state -				\
					so record the item value in xNextTaskUnblockTime. */				\
					xNextTaskUnblockTime = xItemValue;									\
					break;																\
				}																		\
																						\
				/* It is time to remove the item from the Blocked state. */				\
				vListRemove( &( pxTCB->xGenericListItem ) );							\
																						\
				/* Is the task waiting on an event also? */								\
				if( pxTCB->xEventListItem.pvContainer )									\
				{																		\
					vListRemove( &( pxTCB->xEventListItem ) );							\
				}																		\
				prvAddTaskToReadyQueue( pxTCB );										\
			}																			\
		}																				\
	}																					\
}
/*-----------------------------------------------------------*/

/*
 * Several functions take an xTaskHandle parameter that can optionally be NULL,
 * where NULL is used to indicate that the handle of the currently executing
 * task should be used in place of the parameter.  This macro simply checks to
 * see if the parameter is NULL and returns a pointer to the appropriate TCB.
 */
#define prvGetTCBFromHandle( pxHandle ) ( ( ( pxHandle ) == NULL ) ? ( tskTCB * ) pxCurrentTCB : ( tskTCB * ) ( pxHandle ) )

/* Callback function prototypes. --------------------------*/
extern void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName );
		
/* File private functions. --------------------------------*/

/*
 * Utility to ready a TCB for a given task.  Mainly just copies the parameters
 * into the TCB structure.
 */
static void prvInitialiseTCBVariables( tskTCB *pxTCB, const signed char * const pcName, unsigned portBASE_TYPE uxPriority, const xMemoryRegion * const xRegions, unsigned short usStackDepth ) PRIVILEGED_FUNCTION;

/*
 * Utility to ready all the lists used by the scheduler.  This is called
 * automatically upon the creation of the first task.
 */
static void prvInitialiseTaskLists( void ) PRIVILEGED_FUNCTION;

/*
 * The idle task, which as all tasks is implemented as a never ending loop.
 * The idle task is automatically created and added to the ready lists upon
 * creation of the first user task.
 *
 * The portTASK_FUNCTION_PROTO() macro is used to allow port/compiler specific
 * language extensions.  The equivalent prototype for this function is:
 *
 * void prvIdleTask( void *pvParameters );
 *
 */
static portTASK_FUNCTION_PROTO( prvIdleTask, pvParameters );

/*
 * Utility to free all memory allocated by the scheduler to hold a TCB,
 * including the stack pointed to by the TCB.
 *
 * This does not free memory allocated by the task itself (i.e. memory
 * allocated by calls to pvPortMalloc from within the tasks application code).
 */
#if ( ( INCLUDE_vTaskDelete == 1 ) || ( INCLUDE_vTaskCleanUpResources == 1 ) )

	static void prvDeleteTCB( tskTCB *pxTCB ) PRIVILEGED_FUNCTION;

#endif

/*
 * Used only by the idle task.  This checks to see if anything has been placed
 * in the list of tasks waiting to be deleted.  If so the task is cleaned up
 * and its TCB deleted.
 */
static void prvCheckTasksWaitingTermination( void ) PRIVILEGED_FUNCTION;

/*
 * The currently executing task is entering the Blocked state.  Add the task to
 * either the current or the overflow delayed task list.
 */
static void prvAddCurrentTaskToDelayedList( portTickType xTimeToWake ) PRIVILEGED_FUNCTION;

/*
 * Allocates memory from the heap for a TCB and associated stack.  Checks the
 * allocation was successful.
 */
static tskTCB *prvAllocateTCBAndStack( unsigned short usStackDepth, portSTACK_TYPE *puxStackBuffer ) PRIVILEGED_FUNCTION;

/*
 * Called from vTaskList.  vListTasks details all the tasks currently under
 * control of the scheduler.  The tasks may be in one of a number of lists.
 * prvListTaskWithinSingleList accepts a list and details the tasks from
 * within just that list.
 *
 * THIS FUNCTION IS INTENDED FOR DEBUGGING ONLY, AND SHOULD NOT BE CALLED FROM
 * NORMAL APPLICATION CODE.
 */
#if ( configUSE_TRACE_FACILITY == 1 )

	static void prvListTaskWithinSingleList( const signed char *pcWriteBuffer, xList *pxList, signed char cStatus ) PRIVILEGED_FUNCTION;

#endif

/*
 * When a task is created, the stack of the task is filled with a known value.
 * This function determines the 'high water mark' of the task stack by
 * determining how much of the stack remains at the original preset value.
 */
#if ( ( configUSE_TRACE_FACILITY == 1 ) || ( INCLUDE_uxTaskGetStackHighWaterMark == 1 ) )

	static unsigned short usTaskCheckFreeStackSpace( const unsigned char * pucStackByte ) PRIVILEGED_FUNCTION;

#endif


/*lint +e956 */



/*-----------------------------------------------------------
 * TASK CREATION API documented in task.h
 *----------------------------------------------------------*/

signed portBASE_TYPE xTaskGenericCreate( pdTASK_CODE pxTaskCode, const signed char * const pcName, unsigned short usStackDepth, void *pvParameters, unsigned portBASE_TYPE uxPriority, xTaskHandle *pxCreatedTask, portSTACK_TYPE *puxStackBuffer, const xMemoryRegion * const xRegions )
{
signed portBASE_TYPE xReturn;
tskTCB * pxNewTCB;

	/* Allocate the memory required by the TCB and stack for the new task,
	checking that the allocation was successful. */
	pxNewTCB = prvAllocateTCBAndStack( usStackDepth, puxStackBuffer );

	if( pxNewTCB != NULL )
	{
		portSTACK_TYPE *pxTopOfStack;

		#if( portUSING_MPU_WRAPPERS == 1 )
			/* Should the task be created in privileged mode? */
			portBASE_TYPE xRunPrivileged;
			if( ( uxPriority & portPRIVILEGE_BIT ) != 0x00 )
			{
				xRunPrivileged = pdTRUE;
			}
			else
			{
				xRunPrivileged = pdFALSE;
			}
			uxPriority &= ~portPRIVILEGE_BIT;
		#endif /* portUSING_MPU_WRAPPERS == 1 */

		/* Calculate the top of stack address.  This depends on whether the
		stack grows from high memory to low (as per the 80x86) or visa versa.
		portSTACK_GROWTH is used to make the result positive or negative as
		required by the port. */
		#if( portSTACK_GROWTH < 0 )
		{
			pxTopOfStack = pxNewTCB->pxStack + ( usStackDepth - ( unsigned short ) 1 );
			pxTopOfStack = ( portSTACK_TYPE * ) ( ( ( unsigned long ) pxTopOfStack ) & ( ( unsigned long ) ~portBYTE_ALIGNMENT_MASK  ) );
		}
		#else
		{
			pxTopOfStack = pxNewTCB->pxStack;

			/* If we want to use stack checking on architectures that use
			a positive stack growth direction then we also need to store the
			other extreme of the stack space. */
			pxNewTCB->pxEndOfStack = pxNewTCB->pxStack + ( usStackDepth - 1 );
		}
		#endif

		/* Setup the newly allocated TCB with the initial state of the task. */
		prvInitialiseTCBVariables( pxNewTCB, pcName, uxPriority, xRegions, usStackDepth );

		/* Initialize the TCB stack to look as if the task was already running,
		but had been interrupted by the scheduler.  The return address is set
		to the start of the task function. Once the stack has been initialised
		the	top of stack variable is updated. */
		#if( portUSING_MPU_WRAPPERS == 1 )
		{
			pxNewTCB->pxTopOfStack = pxPortInitialiseStack( pxTopOfStack, pxTaskCode, pvParameters, xRunPrivileged );
		}
		#else
		{
			pxNewTCB->pxTopOfStack = pxPortInitialiseStack( pxTopOfStack, pxTaskCode, pvParameters );
		}
		#endif

		if( ( void * ) pxCreatedTask != NULL )
		{
			/* Pass the TCB out - in an anonymous way.  The calling function/
			task can use this as a handle to delete the task later if
			required.*/
			*pxCreatedTask = ( xTaskHandle ) pxNewTCB;
		}
		
		/* We are going to manipulate the task queues to add this task to a
		ready list, so must make sure no interrupts occur. */
		taskENTER_CRITICAL();
		{
			uxCurrentNumberOfTasks++;
			if( pxCurrentTCB == NULL )
			{
				/* There are no other tasks, or all the other tasks are in
				the suspended state - make this the current task. */
				pxCurrentTCB =  pxNewTCB;

				if( uxCurrentNumberOfTasks == ( unsigned portBASE_TYPE ) 1 )
				{
					/* This is the first task to be created so do the preliminary
					initialisation required.  We will not recover if this call
					fails, but we will report the failure. */
					prvInitialiseTaskLists();
				}
			}
			else
			{
				/* If the scheduler is not already running, make this task the
				current task if it is the highest priority task to be created
				so far. */
				if( xSchedulerRunning == pdFALSE )
				{
					if( pxCurrentTCB->uxPriority <= uxPriority )
					{
						pxCurrentTCB = pxNewTCB;
					}
				}
			}

			/* Remember the top priority to make context switching faster.  Use
			the priority in pxNewTCB as this has been capped to a valid value. */
			if( pxNewTCB->uxPriority > uxTopUsedPriority )
			{
				uxTopUsedPriority = pxNewTCB->uxPriority;
			}

			#if ( configUSE_TRACE_FACILITY == 1 )
			{
				/* Add a counter into the TCB for tracing only. */
				pxNewTCB->uxTCBNumber = uxTaskNumber;
			}
			#endif
			uxTaskNumber++;

			prvAddTaskToReadyQueue( pxNewTCB );

			xReturn = pdPASS;
			traceTASK_CREATE( pxNewTCB );
		}
		taskEXIT_CRITICAL();
	}
	else
	{
		xReturn = errCOULD_NOT_ALLOCATE_REQUIRED_MEMORY;
		traceTASK_CREATE_FAILED();
	}

	if( xReturn == pdPASS )
	{
		if( xSchedulerRunning != pdFALSE )
		{
			/* If the created task is of a higher priority than the current task
			then it should run now. */
			if( pxCurrentTCB->uxPriority < uxPriority )
			{
				portYIELD_WITHIN_API();
			}
		}
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskDelete == 1 )

	void vTaskDelete( xTaskHandle pxTaskToDelete )
	{
	tskTCB *pxTCB;

		taskENTER_CRITICAL();
		{
			/* Ensure a yield is performed if the current task is being
			deleted. */
			if( pxTaskToDelete == pxCurrentTCB )
			{
				pxTaskToDelete = NULL;
			}

			/* If null is passed in here then we are deleting ourselves. */
			pxTCB = prvGetTCBFromHandle( pxTaskToDelete );

			/* Remove task from the ready list and place in the	termination list.
			This will stop the task from be scheduled.  The idle task will check
			the termination list and free up any memory allocated by the
			scheduler for the TCB and stack. */
			vListRemove( &( pxTCB->xGenericListItem ) );

			/* Is the task waiting on an event also? */
			if( pxTCB->xEventListItem.pvContainer )
			{
				vListRemove( &( pxTCB->xEventListItem ) );
			}

			vListInsertEnd( ( xList * ) &xTasksWaitingTermination, &( pxTCB->xGenericListItem ) );

			/* Increment the ucTasksDeleted variable so the idle task knows
			there is a task that has been deleted and that it should therefore
			check the xTasksWaitingTermination list. */
			++uxTasksDeleted;

			/* Increment the uxTaskNumberVariable also so kernel aware debuggers
			can detect that the task lists need re-generating. */
			uxTaskNumber++;

			traceTASK_DELETE( pxTCB );
		}
		taskEXIT_CRITICAL();

		/* Force a reschedule if we have just deleted the current task. */
		if( xSchedulerRunning != pdFALSE )
		{
			if( ( void * ) pxTaskToDelete == NULL )
			{
				portYIELD_WITHIN_API();
			}
		}
	}

#endif






/*-----------------------------------------------------------
 * TASK CONTROL API documented in task.h
 *----------------------------------------------------------*/

#if ( INCLUDE_vTaskDelayUntil == 1 )

	void vTaskDelayUntil( portTickType * const pxPreviousWakeTime, portTickType xTimeIncrement )
	{
	portTickType xTimeToWake;
	portBASE_TYPE xAlreadyYielded, xShouldDelay = pdFALSE;

		vTaskSuspendAll();
		{
			/* Generate the tick time at which the task wants to wake. */
			xTimeToWake = *pxPreviousWakeTime + xTimeIncrement;

			if( xTickCount < *pxPreviousWakeTime )
			{
				/* The tick count has overflowed since this function was
				lasted called.  In this case the only time we should ever
				actually delay is if the wake time has also	overflowed,
				and the wake time is greater than the tick time.  When this
				is the case it is as if neither time had overflowed. */
				if( ( xTimeToWake < *pxPreviousWakeTime ) && ( xTimeToWake > xTickCount ) )
				{
					xShouldDelay = pdTRUE;
				}
			}
			else
			{
				/* The tick time has not overflowed.  In this case we will
				delay if either the wake time has overflowed, and/or the
				tick time is less than the wake time. */
				if( ( xTimeToWake < *pxPreviousWakeTime ) || ( xTimeToWake > xTickCount ) )
				{
					xShouldDelay = pdTRUE;
				}
			}

			/* Update the wake time ready for the next call. */
			*pxPreviousWakeTime = xTimeToWake;

			if( xShouldDelay != pdFALSE )
			{
				traceTASK_DELAY_UNTIL();

				/* We must remove ourselves from the ready list before adding
				ourselves to the blocked list as the same list item is used for
				both lists. */
				vListRemove( ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );
				prvAddCurrentTaskToDelayedList( xTimeToWake );
			}
		}
		xAlreadyYielded = xTaskResumeAll();

		/* Force a reschedule if xTaskResumeAll has not already done so, we may
		have put ourselves to sleep. */
		if( !xAlreadyYielded )
		{
			portYIELD_WITHIN_API();
		}
	}

#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskDelay == 1 )

	void vTaskDelay( portTickType xTicksToDelay )
	{
	portTickType xTimeToWake;
	signed portBASE_TYPE xAlreadyYielded = pdFALSE;

		/* A delay time of zero just forces a reschedule. */
		if( xTicksToDelay > ( portTickType ) 0 )
		{
			vTaskSuspendAll();
			{
				traceTASK_DELAY();

				/* A task that is removed from the event list while the
				scheduler is suspended will not get placed in the ready
				list or removed from the blocked list until the scheduler
				is resumed.

				This task cannot be in an event list as it is the currently
				executing task. */

				/* Calculate the time to wake - this may overflow but this is
				not a problem. */
				xTimeToWake = xTickCount + xTicksToDelay;

				/* We must remove ourselves from the ready list before adding
				ourselves to the blocked list as the same list item is used for
				both lists. */
				vListRemove( ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );
				prvAddCurrentTaskToDelayedList( xTimeToWake );
			}
			xAlreadyYielded = xTaskResumeAll();
		}

		/* Force a reschedule if xTaskResumeAll has not already done so, we may
		have put ourselves to sleep. */
		if( !xAlreadyYielded )
		{
			portYIELD_WITHIN_API();
		}
	}

#endif
/*-----------------------------------------------------------*/

void vTaskUnblockTask( xTaskHandle pxTask )
{
tskTCB *pxTCB = ( tskTCB * ) pxTask;

	/* This function is not intended to be a public API function and definitely
	is not for generic use as it assumes pxTask is not the running task and not
	suspended, does not remove the task from any event lists it might be
	blocked on, and does not take care of mutual exclusion. */
	vListRemove( &( pxTCB->xGenericListItem ) );
	prvAddTaskToReadyQueue( pxTCB );
}
/*-----------------------------------------------------------*/

#if ( INCLUDE_uxTaskPriorityGet == 1 )

	unsigned portBASE_TYPE uxTaskPriorityGet( xTaskHandle pxTask )
	{
	tskTCB *pxTCB;
	unsigned portBASE_TYPE uxReturn;

		taskENTER_CRITICAL();
		{
			/* If null is passed in here then we are changing the
			priority of the calling function. */
			pxTCB = prvGetTCBFromHandle( pxTask );
			uxReturn = pxTCB->uxPriority;
		}
		taskEXIT_CRITICAL();

		return uxReturn;
	}

#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskPrioritySet == 1 )

	void vTaskPrioritySet( xTaskHandle pxTask, unsigned portBASE_TYPE uxNewPriority )
	{
	tskTCB *pxTCB;
	unsigned portBASE_TYPE uxCurrentPriority;
	portBASE_TYPE xYieldRequired = pdFALSE;

		/* Ensure the new priority is valid. */
		if( uxNewPriority >= configMAX_PRIORITIES )
		{
			uxNewPriority = configMAX_PRIORITIES - ( unsigned portBASE_TYPE ) 1U;
		}

		taskENTER_CRITICAL();
		{
			if( pxTask == pxCurrentTCB )
			{
				pxTask = NULL;
			}

			/* If null is passed in here then we are changing the
			priority of the calling function. */
			pxTCB = prvGetTCBFromHandle( pxTask );

			traceTASK_PRIORITY_SET( pxTask, uxNewPriority );

			#if ( configUSE_MUTEXES == 1 )
			{
				uxCurrentPriority = pxTCB->uxBasePriority;
			}
			#else
			{
				uxCurrentPriority = pxTCB->uxPriority;
			}
			#endif

			if( uxCurrentPriority != uxNewPriority )
			{
				/* The priority change may have readied a task of higher
				priority than the calling task. */
				if( uxNewPriority > uxCurrentPriority )
				{
					if( pxTask != NULL )
					{
						/* The priority of another task is being raised.  If we
						were raising the priority of the currently running task
						there would be no need to switch as it must have already
						been the highest priority task. */
						xYieldRequired = pdTRUE;
					}
				}
				else if( pxTask == NULL )
				{
					/* Setting our own priority down means there may now be another
					task of higher priority that is ready to execute. */
					xYieldRequired = pdTRUE;
				}



				#if ( configUSE_MUTEXES == 1 )
				{
					/* Only change the priority being used if the task is not
					currently using an inherited priority. */
					if( pxTCB->uxBasePriority == pxTCB->uxPriority )
					{
						pxTCB->uxPriority = uxNewPriority;
					}

					/* The base priority gets set whatever. */
					pxTCB->uxBasePriority = uxNewPriority;
				}
				#else
				{
					pxTCB->uxPriority = uxNewPriority;
				}
				#endif

				listSET_LIST_ITEM_VALUE( &( pxTCB->xEventListItem ), ( configMAX_PRIORITIES - ( portTickType ) uxNewPriority ) );

				/* If the task is in the blocked or suspended list we need do
				nothing more than change it's priority variable. However, if
				the task is in a ready list it needs to be removed and placed
				in the queue appropriate to its new priority. */
				if( listIS_CONTAINED_WITHIN( &( pxReadyTasksLists[ uxCurrentPriority ] ), &( pxTCB->xGenericListItem ) ) )
				{
					/* The task is currently in its ready list - remove before adding
					it to it's new ready list.  As we are in a critical section we
					can do this even if the scheduler is suspended. */
					vListRemove( &( pxTCB->xGenericListItem ) );
					prvAddTaskToReadyQueue( pxTCB );
				}

				if( xYieldRequired == pdTRUE )
				{
					portYIELD_WITHIN_API();
				}
			}
		}
		taskEXIT_CRITICAL();
	}

#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskSuspend == 1 )

	void vTaskSuspend( xTaskHandle pxTaskToSuspend )
	{
	tskTCB *pxTCB;

		taskENTER_CRITICAL();
		{
			/* Ensure a yield is performed if the current task is being
			suspended. */
			if( pxTaskToSuspend == pxCurrentTCB )
			{
				pxTaskToSuspend = NULL;
			}

			/* If null is passed in here then we are suspending ourselves. */
			pxTCB = prvGetTCBFromHandle( pxTaskToSuspend );

			traceTASK_SUSPEND( pxTCB );

			/* Remove task from the ready/delayed list and place in the	suspended list. */
			vListRemove( &( pxTCB->xGenericListItem ) );

			/* Is the task waiting on an event also? */
			if( pxTCB->xEventListItem.pvContainer )
			{
				vListRemove( &( pxTCB->xEventListItem ) );
			}

			vListInsertEnd( ( xList * ) &xSuspendedTaskList, &( pxTCB->xGenericListItem ) );
		}
		taskEXIT_CRITICAL();

		if( ( void * ) pxTaskToSuspend == NULL )
		{
			if( xSchedulerRunning != pdFALSE )
			{
				/* We have just suspended the current task. */
				portYIELD_WITHIN_API();
			}
			else
			{
				/* The scheduler is not running, but the task that was pointed
				to by pxCurrentTCB has just been suspended and pxCurrentTCB
				must be adjusted to point to a different task. */
				if( uxCurrentNumberOfTasks == ( unsigned portBASE_TYPE ) 1U )
				{
					/* No other tasks are defined, so set pxCurrentTCB back to
					NULL so when the next task is created pxCurrentTCB will
					be set to point to it no matter what its relative priority
					is. */
					pxCurrentTCB = NULL;
				}
				else
				{
					vTaskSwitchContext();
				}
			}
		}
	}

#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskSuspend == 1 )

	signed portBASE_TYPE xTaskIsTaskSuspended( xTaskHandle xTask )
	{
	portBASE_TYPE xReturn = pdFALSE;
	const tskTCB * const pxTCB = ( tskTCB * ) xTask;

		/* Is the task we are attempting to resume actually in the
		suspended list? */
		if( listIS_CONTAINED_WITHIN( &xSuspendedTaskList, &( pxTCB->xGenericListItem ) ) != pdFALSE )
		{
			/* Has the task already been resumed from within an ISR? */
			if( listIS_CONTAINED_WITHIN( &xPendingReadyList, &( pxTCB->xEventListItem ) ) != pdTRUE )
			{
				/* Is it in the suspended list because it is in the
				Suspended state?  It is possible to be in the suspended
				list because it is blocked on a task with no timeout
				specified. */
				if( listIS_CONTAINED_WITHIN( NULL, &( pxTCB->xEventListItem ) ) == pdTRUE )
				{
					xReturn = pdTRUE;
				}
			}
		}

		return xReturn;
	}

#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskSuspend == 1 )

	void vTaskResume( xTaskHandle pxTaskToResume )
	{
	tskTCB *pxTCB;

		/* Remove the task from whichever list it is currently in, and place
		it in the ready list. */
		pxTCB = ( tskTCB * ) pxTaskToResume;

		/* The parameter cannot be NULL as it is impossible to resume the
		currently executing task. */
		if( ( pxTCB != NULL ) && ( pxTCB != pxCurrentTCB ) )
		{
			taskENTER_CRITICAL();
			{
				if( xTaskIsTaskSuspended( pxTCB ) == pdTRUE )
				{
					traceTASK_RESUME( pxTCB );

					/* As we are in a critical section we can access the ready
					lists even if the scheduler is suspended. */
					vListRemove(  &( pxTCB->xGenericListItem ) );
					prvAddTaskToReadyQueue( pxTCB );

					/* We may have just resumed a higher priority task. */
					if( pxTCB->uxPriority >= pxCurrentTCB->uxPriority )
					{
						/* This yield may not cause the task just resumed to run, but
						will leave the lists in the correct state for the next yield. */
						portYIELD_WITHIN_API();
					}
				}
			}
			taskEXIT_CRITICAL();
		}
	}

#endif

/*-----------------------------------------------------------*/

#if ( ( INCLUDE_xTaskResumeFromISR == 1 ) && ( INCLUDE_vTaskSuspend == 1 ) )

	portBASE_TYPE xTaskResumeFromISR( xTaskHandle pxTaskToResume )
	{
	portBASE_TYPE xYieldRequired = pdFALSE;
	tskTCB *pxTCB;

		pxTCB = ( tskTCB * ) pxTaskToResume;

		if( xTaskIsTaskSuspended( pxTCB ) == pdTRUE )
		{
			traceTASK_RESUME_FROM_ISR( pxTCB );

			if( uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE )
			{
				xYieldRequired = ( pxTCB->uxPriority >= pxCurrentTCB->uxPriority );
				vListRemove(  &( pxTCB->xGenericListItem ) );
				prvAddTaskToReadyQueue( pxTCB );
			}
			else
			{
				/* We cannot access the delayed or ready lists, so will hold this
				task pending until the scheduler is resumed, at which point a
				yield will be performed if necessary. */
				vListInsertEnd( ( xList * ) &( xPendingReadyList ), &( pxTCB->xEventListItem ) );
			}
		}

		return xYieldRequired;
	}

#endif




/*-----------------------------------------------------------
 * PUBLIC SCHEDULER CONTROL documented in task.h
 *----------------------------------------------------------*/


void vTaskStartScheduler( void )
{
portBASE_TYPE xReturn;

	/* Add the idle task at the lowest priority. */
	xReturn = xTaskCreate( prvIdleTask, ( signed char * ) "IDLE", tskIDLE_STACK_SIZE, ( void * ) NULL, ( tskIDLE_PRIORITY | portPRIVILEGE_BIT ), ( xTaskHandle * ) NULL );

	#if ( configUSE_TIMERS == 1 )
	{
		if( xReturn == pdPASS )
		{
			xReturn = xTimerCreateTimerTask();
		}
	}
	#endif

	if( xReturn == pdPASS )
	{
		/* Interrupts are turned off here, to ensure a tick does not occur
		before or during the call to xPortStartScheduler().  The stacks of
		the created tasks contain a status word with interrupts switched on
		so interrupts will automatically get re-enabled when the first task
		starts to run.

		STEPPING THROUGH HERE USING A DEBUGGER CAN CAUSE BIG PROBLEMS IF THE
		DEBUGGER ALLOWS INTERRUPTS TO BE PROCESSED. */
		portDISABLE_INTERRUPTS();

		xSchedulerRunning = pdTRUE;
		xTickCount = ( portTickType ) 0;

		/* If configGENERATE_RUN_TIME_STATS is defined then the following
		macro must be defined to configure the timer/counter used to generate
		the run time counter time base. */
		portCONFIGURE_TIMER_FOR_RUN_TIME_STATS();
		
		/* Setting up the timer tick is hardware specific and thus in the
		portable interface. */
		if( xPortStartScheduler() )
		{
			/* Should not reach here as if the scheduler is running the
			function will not return. */
		}
		else
		{
			/* Should only reach here if a task calls xTaskEndScheduler(). */
		}
	}
}
/*-----------------------------------------------------------*/

void vTaskEndScheduler( void )
{
	/* Stop the scheduler interrupts and call the portable scheduler end
	routine so the original ISRs can be restored if necessary.  The port
	layer must ensure interrupts enable	bit is left in the correct state. */
	portDISABLE_INTERRUPTS();
	xSchedulerRunning = pdFALSE;
	vPortEndScheduler();
}
/*----------------------------------------------------------*/

void vTaskSuspendAll( void )
{
	/* A critical section is not required as the variable is of type
	portBASE_TYPE. */
	++uxSchedulerSuspended;
}
/*----------------------------------------------------------*/

signed portBASE_TYPE xTaskResumeAll( void )
{
register tskTCB *pxTCB;
signed portBASE_TYPE xAlreadyYielded = pdFALSE;

	/* It is possible that an ISR caused a task to be removed from an event
	list while the scheduler was suspended.  If this was the case then the
	removed task will have been added to the xPendingReadyList.  Once the
	scheduler has been resumed it is safe to move all the pending ready
	tasks from this list into their appropriate ready list. */
	taskENTER_CRITICAL();
	{
		--uxSchedulerSuspended;

		if( uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE )
		{
			if( uxCurrentNumberOfTasks > ( unsigned portBASE_TYPE ) 0 )
			{
				portBASE_TYPE xYieldRequired = pdFALSE;

				/* Move any readied tasks from the pending list into the
				appropriate ready list. */
				while( listLIST_IS_EMPTY( ( xList * ) &xPendingReadyList ) == pdFALSE )
				{
					pxTCB = ( tskTCB * ) listGET_OWNER_OF_HEAD_ENTRY(  ( ( xList * ) &xPendingReadyList ) );
					vListRemove( &( pxTCB->xEventListItem ) );
					vListRemove( &( pxTCB->xGenericListItem ) );
					prvAddTaskToReadyQueue( pxTCB );

					/* If we have moved a task that has a priority higher than
					the current task then we should yield. */
					if( pxTCB->uxPriority >= pxCurrentTCB->uxPriority )
					{
						xYieldRequired = pdTRUE;
					}
				}

				/* If any ticks occurred while the scheduler was suspended then
				they should be processed now.  This ensures the tick count does not
				slip, and that any delayed tasks are resumed at the correct time. */
				if( uxMissedTicks > ( unsigned portBASE_TYPE ) 0 )
				{
					while( uxMissedTicks > ( unsigned portBASE_TYPE ) 0 )
					{
						vTaskIncrementTick();
						--uxMissedTicks;
					}

					/* As we have processed some ticks it is appropriate to yield
					to ensure the highest priority task that is ready to run is
					the task actually running. */
					#if configUSE_PREEMPTION == 1
					{
						xYieldRequired = pdTRUE;
					}
					#endif
				}

				if( ( xYieldRequired == pdTRUE ) || ( xMissedYield == pdTRUE ) )
				{
					xAlreadyYielded = pdTRUE;
					xMissedYield = pdFALSE;
					portYIELD_WITHIN_API();
				}
			}
		}
	}
	taskEXIT_CRITICAL();

	return xAlreadyYielded;
}






/*-----------------------------------------------------------
 * PUBLIC TASK UTILITIES documented in task.h
 *----------------------------------------------------------*/



portTickType xTaskGetTickCount( void )
{
portTickType xTicks;

	/* Critical section required if running on a 16 bit processor. */
	taskENTER_CRITICAL();
	{
		xTicks = xTickCount;
	}
	taskEXIT_CRITICAL();

	return xTicks;
}
/*-----------------------------------------------------------*/

portTickType xTaskGetTickCountFromISR( void )
{
	return xTickCount;
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE uxTaskGetNumberOfTasks( void )
{
	/* A critical section is not required because the variables are of type
	portBASE_TYPE. */
	return uxCurrentNumberOfTasks;
}
/*-----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )

	void vTaskList( signed char *pcWriteBuffer )
	{
	unsigned portBASE_TYPE uxQueue;

		/* This is a VERY costly function that should be used for debug only.
		It leaves interrupts disabled for a LONG time. */

		vTaskSuspendAll();
		{
			/* Run through all the lists that could potentially contain a TCB and
			report the task name, state and stack high water mark. */

			*pcWriteBuffer = ( signed char ) 0x00;
			strcat( ( char * ) pcWriteBuffer, ( const char * ) "\r\n" );

			uxQueue = uxTopUsedPriority + ( unsigned portBASE_TYPE ) 1U;

			do
			{
				uxQueue--;

				if( !listLIST_IS_EMPTY( &( pxReadyTasksLists[ uxQueue ] ) ) )
				{
					prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) &( pxReadyTasksLists[ uxQueue ] ), tskREADY_CHAR );
				}
			}while( uxQueue > ( unsigned short ) tskIDLE_PRIORITY );

			if( !listLIST_IS_EMPTY( pxDelayedTaskList ) )
			{
				prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) pxDelayedTaskList, tskBLOCKED_CHAR );
			}

			if( !listLIST_IS_EMPTY( pxOverflowDelayedTaskList ) )
			{
				prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) pxOverflowDelayedTaskList, tskBLOCKED_CHAR );
			}

			#if( INCLUDE_vTaskDelete == 1 )
			{
				if( !listLIST_IS_EMPTY( &xTasksWaitingTermination ) )
				{
					prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) &xTasksWaitingTermination, tskDELETED_CHAR );
				}
			}
			#endif

			#if ( INCLUDE_vTaskSuspend == 1 )
			{
				if( !listLIST_IS_EMPTY( &xSuspendedTaskList ) )
				{
					prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) &xSuspendedTaskList, tskSUSPENDED_CHAR );
				}
			}
			#endif
		}
		xTaskResumeAll();
	}

#endif
/*----------------------------------------------------------*/

#if ( configGENERATE_RUN_TIME_STATS == 1 )

	void vTaskGetRunTimeStats( signed char *pcWriteBuffer )
	{
	unsigned portBASE_TYPE uxQueue;
	unsigned long ulTotalRunTime;

		/* This is a VERY costly function that should be used for debug only.
		It leaves interrupts disabled for a LONG time. */

		vTaskSuspendAll();
		{
			#ifdef portALT_GET_RUN_TIME_COUNTER_VALUE
				portALT_GET_RUN_TIME_COUNTER_VALUE( ulTotalRunTime );
			#else
				ulTotalRunTime = portGET_RUN_TIME_COUNTER_VALUE();
			#endif

			/* Divide ulTotalRunTime by 100 to make the percentage caluclations
			simpler in the prvGenerateRunTimeStatsForTasksInList() function. */
			ulTotalRunTime /= 100UL;
			
			/* Run through all the lists that could potentially contain a TCB,
			generating a table of run timer percentages in the provided
			buffer. */

			*pcWriteBuffer = ( signed char ) 0x00;
			strcat( ( char * ) pcWriteBuffer, ( const char * ) "\r\n" );

			uxQueue = uxTopUsedPriority + ( unsigned portBASE_TYPE ) 1U;

			do
			{
				uxQueue--;

				if( !listLIST_IS_EMPTY( &( pxReadyTasksLists[ uxQueue ] ) ) )
				{
					prvGenerateRunTimeStatsForTasksInList( pcWriteBuffer, ( xList * ) &( pxReadyTasksLists[ uxQueue ] ), ulTotalRunTime );
				}
			}while( uxQueue > ( unsigned short ) tskIDLE_PRIORITY );

			if( !listLIST_IS_EMPTY( pxDelayedTaskList ) )
			{
				prvGenerateRunTimeStatsForTasksInList( pcWriteBuffer, ( xList * ) pxDelayedTaskList, ulTotalRunTime );
			}

			if( !listLIST_IS_EMPTY( pxOverflowDelayedTaskList ) )
			{
				prvGenerateRunTimeStatsForTasksInList( pcWriteBuffer, ( xList * ) pxOverflowDelayedTaskList, ulTotalRunTime );
			}

			#if ( INCLUDE_vTaskDelete == 1 )
			{
				if( !listLIST_IS_EMPTY( &xTasksWaitingTermination ) )
				{
					prvGenerateRunTimeStatsForTasksInList( pcWriteBuffer, ( xList * ) &xTasksWaitingTermination, ulTotalRunTime );
				}
			}
			#endif

			#if ( INCLUDE_vTaskSuspend == 1 )
			{
				if( !listLIST_IS_EMPTY( &xSuspendedTaskList ) )
				{
					prvGenerateRunTimeStatsForTasksInList( pcWriteBuffer, ( xList * ) &xSuspendedTaskList, ulTotalRunTime );
				}
			}
			#endif
		}
		xTaskResumeAll();
	}

#endif
/*----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )

	void vTaskStartTrace( signed char * pcBuffer, unsigned long ulBufferSize )
	{
		taskENTER_CRITICAL();
		{
			pcTraceBuffer = ( signed char * )pcBuffer;
			pcTraceBufferStart = pcBuffer;
			pcTraceBufferEnd = pcBuffer + ( ulBufferSize - tskSIZE_OF_EACH_TRACE_LINE );
			xTracing = pdTRUE;
		}
		taskEXIT_CRITICAL();
	}

#endif
/*----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )

	unsigned long ulTaskEndTrace( void )
	{
	unsigned long ulBufferLength;

		taskENTER_CRITICAL();
			xTracing = pdFALSE;
		taskEXIT_CRITICAL();

		ulBufferLength = ( unsigned long ) ( pcTraceBuffer - pcTraceBufferStart );

		return ulBufferLength;
	}

#endif



/*-----------------------------------------------------------
 * SCHEDULER INTERNALS AVAILABLE FOR PORTING PURPOSES
 * documented in task.h
 *----------------------------------------------------------*/


void vTaskIncrementTick( void )
{
	/* Called by the portable layer each time a tick interrupt occurs.
	Increments the tick then checks to see if the new tick value will cause any
	tasks to be unblocked. */
	if( uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE )
	{
		++xTickCount;
		if( xTickCount == ( portTickType ) 0 )
		{
			xList *pxTemp;

			/* Tick count has overflowed so we need to swap the delay lists.
			If there are any items in pxDelayedTaskList here then there is
			an error! */
			configASSERT( ( listLIST_IS_EMPTY( pxDelayedTaskList ) ) );
			
			pxTemp = pxDelayedTaskList;
			pxDelayedTaskList = pxOverflowDelayedTaskList;
			pxOverflowDelayedTaskList = pxTemp;
			xNumOfOverflows++;
	
			if( listLIST_IS_EMPTY( pxDelayedTaskList ) != pdFALSE )
			{
				/* The delayed list is empty.  Set xNextTaskUnblockTime to the
				maximum possible value so it is extremely unlikely that the
				if( xTickCount >= xNextTaskUnblockTime ) test will pass
				until there is an item in the delayed list. */
				xNextTaskUnblockTime = portMAX_DELAY;
			}
			else
			{
				tskTCB * pxTCB;

				/* The delayed list is not empty, get the value of the item at
				the head of the delayed list.  This is the time at which the
				task at the head of the delayed list should be removed from
				the Blocked state. */
				pxTCB = ( tskTCB * ) listGET_OWNER_OF_HEAD_ENTRY( pxDelayedTaskList );
				xNextTaskUnblockTime = listGET_LIST_ITEM_VALUE( &( pxTCB->xGenericListItem ) );
			}
		}

		/* See if this tick has made a timeout expire. */
		prvCheckDelayedTasks();
	}
	else
	{
		++uxMissedTicks;

		/* The tick hook gets called at regular intervals, even if the
		scheduler is locked. */
		#if ( configUSE_TICK_HOOK == 1 )
		{
			extern void vApplicationTickHook( void );

			vApplicationTickHook();
		}
		#endif
	}

	#if ( configUSE_TICK_HOOK == 1 )
	{
		extern void vApplicationTickHook( void );

		/* Guard against the tick hook being called when the missed tick
		count is being unwound (when the scheduler is being unlocked. */
		if( uxMissedTicks == 0 )
		{
			vApplicationTickHook();
		}
	}
	#endif

	traceTASK_INCREMENT_TICK( xTickCount );
}
/*-----------------------------------------------------------*/

#if ( ( INCLUDE_vTaskCleanUpResources == 1 ) && ( INCLUDE_vTaskSuspend == 1 ) )

	void vTaskCleanUpResources( void )
	{
	unsigned short usQueue;
	volatile tskTCB *pxTCB;

		usQueue = ( unsigned short ) uxTopUsedPriority + ( unsigned short ) 1;

		/* Remove any TCB's from the ready queues. */
		do
		{
			usQueue--;

			while( !listLIST_IS_EMPTY( &( pxReadyTasksLists[ usQueue ] ) ) )
			{
				listGET_OWNER_OF_NEXT_ENTRY( pxTCB, &( pxReadyTasksLists[ usQueue ] ) );
				vListRemove( ( xListItem * ) &( pxTCB->xGenericListItem ) );

				prvDeleteTCB( ( tskTCB * ) pxTCB );
			}
		}while( usQueue > ( unsigned short ) tskIDLE_PRIORITY );

		/* Remove any TCB's from the delayed queue. */
		while( !listLIST_IS_EMPTY( &xDelayedTaskList1 ) )
		{
			listGET_OWNER_OF_NEXT_ENTRY( pxTCB, &xDelayedTaskList1 );
			vListRemove( ( xListItem * ) &( pxTCB->xGenericListItem ) );

			prvDeleteTCB( ( tskTCB * ) pxTCB );
		}

		/* Remove any TCB's from the overflow delayed queue. */
		while( !listLIST_IS_EMPTY( &xDelayedTaskList2 ) )
		{
			listGET_OWNER_OF_NEXT_ENTRY( pxTCB, &xDelayedTaskList2 );
			vListRemove( ( xListItem * ) &( pxTCB->xGenericListItem ) );

			prvDeleteTCB( ( tskTCB * ) pxTCB );
		}

		while( !listLIST_IS_EMPTY( &xSuspendedTaskList ) )
		{
			listGET_OWNER_OF_NEXT_ENTRY( pxTCB, &xSuspendedTaskList );
			vListRemove( ( xListItem * ) &( pxTCB->xGenericListItem ) );

			prvDeleteTCB( ( tskTCB * ) pxTCB );
		}
	}

#endif
/*-----------------------------------------------------------*/

#if ( configUSE_APPLICATION_TASK_TAG == 1 )

	void vTaskSetApplicationTaskTag( xTaskHandle xTask, pdTASK_HOOK_CODE pxTagValue )
	{
	tskTCB *xTCB;

		/* If xTask is NULL then we are setting our own task hook. */
		if( xTask == NULL )
		{
			xTCB = ( tskTCB * ) pxCurrentTCB;
		}
		else
		{
			xTCB = ( tskTCB * ) xTask;
		}

		/* Save the hook function in the TCB.  A critical section is required as
		the value can be accessed from an interrupt. */
		taskENTER_CRITICAL();
			xTCB->pxTaskTag = pxTagValue;
		taskEXIT_CRITICAL();
	}

#endif
/*-----------------------------------------------------------*/

#if ( configUSE_APPLICATION_TASK_TAG == 1 )

	pdTASK_HOOK_CODE xTaskGetApplicationTaskTag( xTaskHandle xTask )
	{
	tskTCB *xTCB;
	pdTASK_HOOK_CODE xReturn;

		/* If xTask is NULL then we are setting our own task hook. */
		if( xTask == NULL )
		{
			xTCB = ( tskTCB * ) pxCurrentTCB;
		}
		else
		{
			xTCB = ( tskTCB * ) xTask;
		}

		/* Save the hook function in the TCB.  A critical section is required as
		the value can be accessed from an interrupt. */
		taskENTER_CRITICAL();
			xReturn = xTCB->pxTaskTag;
		taskEXIT_CRITICAL();

		return xReturn;
	}

#endif
/*-----------------------------------------------------------*/

#if ( configUSE_APPLICATION_TASK_TAG == 1 )

	portBASE_TYPE xTaskCallApplicationTaskHook( xTaskHandle xTask, void *pvParameter )
	{
	tskTCB *xTCB;
	portBASE_TYPE xReturn;

		/* If xTask is NULL then we are calling our own task hook. */
		if( xTask == NULL )
		{
			xTCB = ( tskTCB * ) pxCurrentTCB;
		}
		else
		{
			xTCB = ( tskTCB * ) xTask;
		}

		if( xTCB->pxTaskTag != NULL )
		{
			xReturn = xTCB->pxTaskTag( pvParameter );
		}
		else
		{
			xReturn = pdFAIL;
		}

		return xReturn;
	}

#endif
/*-----------------------------------------------------------*/

void vTaskSwitchContext( void )
{
	if( uxSchedulerSuspended != ( unsigned portBASE_TYPE ) pdFALSE )
	{
		/* The scheduler is currently suspended - do not allow a context
		switch. */
		xMissedYield = pdTRUE;
	}
	else
	{
		traceTASK_SWITCHED_OUT();
	
		#if ( configGENERATE_RUN_TIME_STATS == 1 )
		{
			unsigned long ulTempCounter;
			
				#ifdef portALT_GET_RUN_TIME_COUNTER_VALUE
					portALT_GET_RUN_TIME_COUNTER_VALUE( ulTempCounter );
				#else
					ulTempCounter = portGET_RUN_TIME_COUNTER_VALUE();
				#endif
	
				/* Add the amount of time the task has been running to the accumulated
				time so far.  The time the task started running was stored in
				ulTaskSwitchedInTime.  Note that there is no overflow protection here
				so count values are only valid until the timer overflows.  Generally
				this will be about 1 hour assuming a 1uS timer increment. */
				pxCurrentTCB->ulRunTimeCounter += ( ulTempCounter - ulTaskSwitchedInTime );
				ulTaskSwitchedInTime = ulTempCounter;
		}
		#endif
	
		taskFIRST_CHECK_FOR_STACK_OVERFLOW();
		taskSECOND_CHECK_FOR_STACK_OVERFLOW();
	
		/* Find the highest priority queue that contains ready tasks. */
		while( listLIST_IS_EMPTY( &( pxReadyTasksLists[ uxTopReadyPriority ] ) ) )
		{
			--uxTopReadyPriority;
		}
	
		/* listGET_OWNER_OF_NEXT_ENTRY walks through the list, so the tasks of the
		same priority get an equal share of the processor time. */
		listGET_OWNER_OF_NEXT_ENTRY( pxCurrentTCB, &( pxReadyTasksLists[ uxTopReadyPriority ] ) );
	
		traceTASK_SWITCHED_IN();
		vWriteTraceToBuffer();
	}
}
/*-----------------------------------------------------------*/

void vTaskPlaceOnEventList( const xList * const pxEventList, portTickType xTicksToWait )
{
portTickType xTimeToWake;

	/* THIS FUNCTION MUST BE CALLED WITH INTERRUPTS DISABLED OR THE
	SCHEDULER SUSPENDED. */

	/* Place the event list item of the TCB in the appropriate event list.
	This is placed in the list in priority order so the highest priority task
	is the first to be woken by the event. */
	vListInsert( ( xList * ) pxEventList, ( xListItem * ) &( pxCurrentTCB->xEventListItem ) );

	/* We must remove ourselves from the ready list before adding ourselves
	to the blocked list as the same list item is used for both lists.  We have
	exclusive access to the ready lists as the scheduler is locked. */
	vListRemove( ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );


	#if ( INCLUDE_vTaskSuspend == 1 )
	{
		if( xTicksToWait == portMAX_DELAY )
		{
			/* Add ourselves to the suspended task list instead of a delayed task
			list to ensure we are not woken by a timing event.  We will block
			indefinitely. */
			vListInsertEnd( ( xList * ) &xSuspendedTaskList, ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );
		}
		else
		{
			/* Calculate the time at which the task should be woken if the event does
			not occur.  This may overflow but this doesn't matter. */
			xTimeToWake = xTickCount + xTicksToWait;
			prvAddCurrentTaskToDelayedList( xTimeToWake );
		}
	}
	#else
	{
			/* Calculate the time at which the task should be woken if the event does
			not occur.  This may overflow but this doesn't matter. */
			xTimeToWake = xTickCount + xTicksToWait;
			prvAddCurrentTaskToDelayedList( xTimeToWake );
	}
	#endif
}
/*-----------------------------------------------------------*/

#if configUSE_TIMERS == 1

	void vTaskPlaceOnEventListRestricted( const xList * const pxEventList, portTickType xTicksToWait )
	{
	portTickType xTimeToWake;

		/* This function should not be called by application code hence the
		'Restricted' in its name.  It is not part of the public API.  It is
		designed for use by kernel code, and has special calling requirements -
		it should be called from a critical section. */

	
		/* Place the event list item of the TCB in the appropriate event list.
		In this case it is assume that this is the only task that is going to
		be waiting on this event list, so the faster vListInsertEnd() function
		can be used in place of vListInsert. */
		vListInsertEnd( ( xList * ) pxEventList, ( xListItem * ) &( pxCurrentTCB->xEventListItem ) );

		/* We must remove this task from the ready list before adding it to the
		blocked list as the same list item is used for both lists.  This
		function is called form a critical section. */
		vListRemove( ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );

		/* Calculate the time at which the task should be woken if the event does
		not occur.  This may overflow but this doesn't matter. */
		xTimeToWake = xTickCount + xTicksToWait;
		prvAddCurrentTaskToDelayedList( xTimeToWake );
	}
	
#endif /* configUSE_TIMERS */
/*-----------------------------------------------------------*/

signed portBASE_TYPE xTaskRemoveFromEventList( const xList * const pxEventList )
{
tskTCB *pxUnblockedTCB;
portBASE_TYPE xReturn;

	/* THIS FUNCTION MUST BE CALLED WITH INTERRUPTS DISABLED OR THE
	SCHEDULER SUSPENDED.  It can also be called from within an ISR. */

	/* The event list is sorted in priority order, so we can remove the
	first in the list, remove the TCB from the delayed list, and add
	it to the ready list.

	If an event is for a queue that is locked then this function will never
	get called - the lock count on the queue will get modified instead.  This
	means we can always expect exclusive access to the event list here.
	
	This function assumes that a check has already been made to ensure that
	pxEventList is not empty. */
	pxUnblockedTCB = ( tskTCB * ) listGET_OWNER_OF_HEAD_ENTRY( pxEventList );
	vListRemove( &( pxUnblockedTCB->xEventListItem ) );

	if( uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE )
	{
		vListRemove( &( pxUnblockedTCB->xGenericListItem ) );
		prvAddTaskToReadyQueue( pxUnblockedTCB );
	}
	else
	{
		/* We cannot access the delayed or ready lists, so will hold this
		task pending until the scheduler is resumed. */
		vListInsertEnd( ( xList * ) &( xPendingReadyList ), &( pxUnblockedTCB->xEventListItem ) );
	}

	if( pxUnblockedTCB->uxPriority >= pxCurrentTCB->uxPriority )
	{
		/* Return true if the task removed from the event list has
		a higher priority than the calling task.  This allows
		the calling task to know if it should force a context
		switch now. */
		xReturn = pdTRUE;
	}
	else
	{
		xReturn = pdFALSE;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void vTaskSetTimeOutState( xTimeOutType * const pxTimeOut )
{
	pxTimeOut->xOverflowCount = xNumOfOverflows;
	pxTimeOut->xTimeOnEntering = xTickCount;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xTaskCheckForTimeOut( xTimeOutType * const pxTimeOut, portTickType * const pxTicksToWait )
{
portBASE_TYPE xReturn;

	taskENTER_CRITICAL();
	{
		#if ( INCLUDE_vTaskSuspend == 1 )
			/* If INCLUDE_vTaskSuspend is set to 1 and the block time specified is
			the maximum block time then the task should block indefinitely, and
			therefore never time out. */
			if( *pxTicksToWait == portMAX_DELAY )
			{
				xReturn = pdFALSE;
			}
			else /* We are not blocking indefinitely, perform the checks below. */
		#endif

		if( ( xNumOfOverflows != pxTimeOut->xOverflowCount ) && ( ( portTickType ) xTickCount >= ( portTickType ) pxTimeOut->xTimeOnEntering ) )
		{
			/* The tick count is greater than the time at which vTaskSetTimeout()
			was called, but has also overflowed since vTaskSetTimeOut() was called.
			It must have wrapped all the way around and gone past us again. This
			passed since vTaskSetTimeout() was called. */
			xReturn = pdTRUE;
		}
		else if( ( ( portTickType ) ( ( portTickType ) xTickCount - ( portTickType ) pxTimeOut->xTimeOnEntering ) ) < ( portTickType ) *pxTicksToWait )
		{
			/* Not a genuine timeout. Adjust parameters for time remaining. */
			*pxTicksToWait -= ( ( portTickType ) xTickCount - ( portTickType ) pxTimeOut->xTimeOnEntering );
			vTaskSetTimeOutState( pxTimeOut );
			xReturn = pdFALSE;
		}
		else
		{
			xReturn = pdTRUE;
		}
	}
	taskEXIT_CRITICAL();

	return xReturn;
}
/*-----------------------------------------------------------*/

void vTaskMissedYield( void )
{
	xMissedYield = pdTRUE;
}

/*
 * -----------------------------------------------------------
 * The Idle task.
 * ----------------------------------------------------------
 *
 * The portTASK_FUNCTION() macro is used to allow port/compiler specific
 * language extensions.  The equivalent prototype for this function is:
 *
 * void prvIdleTask( void *pvParameters );
 *
 */
static portTASK_FUNCTION( prvIdleTask, pvParameters )
{
	/* Stop warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* See if any tasks have been deleted. */
		prvCheckTasksWaitingTermination();

		#if ( configUSE_PREEMPTION == 0 )
		{
			/* If we are not using preemption we keep forcing a task switch to
			see if any other task has become available.  If we are using
			preemption we don't need to do this as any task becoming available
			will automatically get the processor anyway. */
			taskYIELD();
		}
		#endif

		#if ( ( configUSE_PREEMPTION == 1 ) && ( configIDLE_SHOULD_YIELD == 1 ) )
		{
			/* When using preemption tasks of equal priority will be
			timesliced.  If a task that is sharing the idle priority is ready
			to run then the idle task should yield before the end of the
			timeslice.

			A critical region is not required here as we are just reading from
			the list, and an occasional incorrect value will not matter.  If
			the ready list at the idle priority contains more than one task
			then a task other than the idle task is ready to execute. */
			if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > ( unsigned portBASE_TYPE ) 1 )
			{
				taskYIELD();
			}
		}
		#endif

		#if ( configUSE_IDLE_HOOK == 1 )
		{
			extern void vApplicationIdleHook( void );

			/* Call the user defined function from within the idle task.  This
			allows the application designer to add background functionality
			without the overhead of a separate task.
			NOTE: vApplicationIdleHook() MUST NOT, UNDER ANY CIRCUMSTANCES,
			CALL A FUNCTION THAT MIGHT BLOCK. */
			vApplicationIdleHook();
		}
		#endif
	}
} /*lint !e715 pvParameters is not accessed but all task functions require the same prototype. */







/*-----------------------------------------------------------
 * File private functions documented at the top of the file.
 *----------------------------------------------------------*/



static void prvInitialiseTCBVariables( tskTCB *pxTCB, const signed char * const pcName, unsigned portBASE_TYPE uxPriority, const xMemoryRegion * const xRegions, unsigned short usStackDepth )
{
	/* Store the function name in the TCB. */
	#if configMAX_TASK_NAME_LEN > 1
	{
		/* Don't bring strncpy into the build unnecessarily. */
		strncpy( ( char * ) pxTCB->pcTaskName, ( const char * ) pcName, ( unsigned short ) configMAX_TASK_NAME_LEN );
	}
	#endif
	pxTCB->pcTaskName[ ( unsigned short ) configMAX_TASK_NAME_LEN - ( unsigned short ) 1 ] = ( signed char ) '\0';

	/* This is used as an array index so must ensure it's not too large.  First
	remove the privilege bit if one is present. */
	if( uxPriority >= configMAX_PRIORITIES )
	{
		uxPriority = configMAX_PRIORITIES - ( unsigned portBASE_TYPE ) 1U;
	}

	pxTCB->uxPriority = uxPriority;
	#if ( configUSE_MUTEXES == 1 )
	{
		pxTCB->uxBasePriority = uxPriority;
	}
	#endif

	vListInitialiseItem( &( pxTCB->xGenericListItem ) );
	vListInitialiseItem( &( pxTCB->xEventListItem ) );

	/* Set the pxTCB as a link back from the xListItem.  This is so we can get
	back to	the containing TCB from a generic item in a list. */
	listSET_LIST_ITEM_OWNER( &( pxTCB->xGenericListItem ), pxTCB );

	/* Event lists are always in priority order. */
	listSET_LIST_ITEM_VALUE( &( pxTCB->xEventListItem ), configMAX_PRIORITIES - ( portTickType ) uxPriority );
	listSET_LIST_ITEM_OWNER( &( pxTCB->xEventListItem ), pxTCB );

	#if ( portCRITICAL_NESTING_IN_TCB == 1 )
	{
		pxTCB->uxCriticalNesting = ( unsigned portBASE_TYPE ) 0;
	}
	#endif

	#if ( configUSE_APPLICATION_TASK_TAG == 1 )
	{
		pxTCB->pxTaskTag = NULL;
	}
	#endif

	#if ( configGENERATE_RUN_TIME_STATS == 1 )
	{
		pxTCB->ulRunTimeCounter = 0UL;
	}
	#endif

	#if ( portUSING_MPU_WRAPPERS == 1 )
	{
		vPortStoreTaskMPUSettings( &( pxTCB->xMPUSettings ), xRegions, pxTCB->pxStack, usStackDepth );
	}
	#else
	{
		( void ) xRegions;
		( void ) usStackDepth;
	}
	#endif
}
/*-----------------------------------------------------------*/

#if ( portUSING_MPU_WRAPPERS == 1 )

	void vTaskAllocateMPURegions( xTaskHandle xTaskToModify, const xMemoryRegion * const xRegions )
	{
	tskTCB *pxTCB;
	
		if( xTaskToModify == pxCurrentTCB )
		{
			xTaskToModify = NULL;
		}

		/* If null is passed in here then we are deleting ourselves. */
		pxTCB = prvGetTCBFromHandle( xTaskToModify );

        vPortStoreTaskMPUSettings( &( pxTCB->xMPUSettings ), xRegions, NULL, 0 );
	}
	/*-----------------------------------------------------------*/
#endif

static void prvInitialiseTaskLists( void )
{
unsigned portBASE_TYPE uxPriority;

	for( uxPriority = ( unsigned portBASE_TYPE ) 0U; uxPriority < configMAX_PRIORITIES; uxPriority++ )
	{
		vListInitialise( ( xList * ) &( pxReadyTasksLists[ uxPriority ] ) );
	}

	vListInitialise( ( xList * ) &xDelayedTaskList1 );
	vListInitialise( ( xList * ) &xDelayedTaskList2 );
	vListInitialise( ( xList * ) &xPendingReadyList );

	#if ( INCLUDE_vTaskDelete == 1 )
	{
		vListInitialise( ( xList * ) &xTasksWaitingTermination );
	}
	#endif

	#if ( INCLUDE_vTaskSuspend == 1 )
	{
		vListInitialise( ( xList * ) &xSuspendedTaskList );
	}
	#endif

	/* Start with pxDelayedTaskList using list1 and the pxOverflowDelayedTaskList
	using list2. */
	pxDelayedTaskList = &xDelayedTaskList1;
	pxOverflowDelayedTaskList = &xDelayedTaskList2;
}
/*-----------------------------------------------------------*/

static void prvCheckTasksWaitingTermination( void )
{
	#if ( INCLUDE_vTaskDelete == 1 )
	{
		portBASE_TYPE xListIsEmpty;

		/* ucTasksDeleted is used to prevent vTaskSuspendAll() being called
		too often in the idle task. */
		if( uxTasksDeleted > ( unsigned portBASE_TYPE ) 0 )
		{
			vTaskSuspendAll();
				xListIsEmpty = listLIST_IS_EMPTY( &xTasksWaitingTermination );
			xTaskResumeAll();

			if( xListIsEmpty == pdFALSE )
			{
				tskTCB *pxTCB;

				taskENTER_CRITICAL();
				{
					pxTCB = ( tskTCB * ) listGET_OWNER_OF_HEAD_ENTRY( ( ( xList * ) &xTasksWaitingTermination ) );
					vListRemove( &( pxTCB->xGenericListItem ) );
					--uxCurrentNumberOfTasks;
					--uxTasksDeleted;
				}
				taskEXIT_CRITICAL();

				prvDeleteTCB( pxTCB );
			}
		}
	}
	#endif
}
/*-----------------------------------------------------------*/

static void prvAddCurrentTaskToDelayedList( portTickType xTimeToWake )
{
	/* The list item will be inserted in wake time order. */
	listSET_LIST_ITEM_VALUE( &( pxCurrentTCB->xGenericListItem ), xTimeToWake );

	if( xTimeToWake < xTickCount )
	{
		/* Wake time has overflowed.  Place this item in the overflow list. */
		vListInsert( ( xList * ) pxOverflowDelayedTaskList, ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );
	}
	else
	{
		/* The wake time has not overflowed, so we can use the current block list. */
		vListInsert( ( xList * ) pxDelayedTaskList, ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );

		/* If the task entering the blocked state was placed at the head of the
		list of blocked tasks then xNextTaskUnmblockTime needs to be updated
		too. */
		if( xTimeToWake < xNextTaskUnblockTime )
		{
			xNextTaskUnblockTime = xTimeToWake;
		}
	}
}
/*-----------------------------------------------------------*/

static tskTCB *prvAllocateTCBAndStack( unsigned short usStackDepth, portSTACK_TYPE *puxStackBuffer )
{
tskTCB *pxNewTCB;

	/* Allocate space for the TCB.  Where the memory comes from depends on
	the implementation of the port malloc function. */
	pxNewTCB = ( tskTCB * ) pvPortMalloc( sizeof( tskTCB ) );

	if( pxNewTCB != NULL )
	{
		/* Allocate space for the stack used by the task being created.
		The base of the stack memory stored in the TCB so the task can
		be deleted later if required. */
		pxNewTCB->pxStack = ( portSTACK_TYPE * ) pvPortMallocAligned( ( ( ( size_t )usStackDepth ) * sizeof( portSTACK_TYPE ) ), puxStackBuffer );

		if( pxNewTCB->pxStack == NULL )
		{
			/* Could not allocate the stack.  Delete the allocated TCB. */
			vPortFree( pxNewTCB );
			pxNewTCB = NULL;
		}
		else
		{
			/* Just to help debugging. */
			memset( pxNewTCB->pxStack, tskSTACK_FILL_BYTE, usStackDepth * sizeof( portSTACK_TYPE ) );
		}
	}

	return pxNewTCB;
}
/*-----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )

	static void prvListTaskWithinSingleList( const signed char *pcWriteBuffer, xList *pxList, signed char cStatus )
	{
	volatile tskTCB *pxNextTCB, *pxFirstTCB;
	unsigned short usStackRemaining;

		/* Write the details of all the TCB's in pxList into the buffer. */
		listGET_OWNER_OF_NEXT_ENTRY( pxFirstTCB, pxList );
		do
		{
			listGET_OWNER_OF_NEXT_ENTRY( pxNextTCB, pxList );
			#if ( portSTACK_GROWTH > 0 )
			{
				usStackRemaining = usTaskCheckFreeStackSpace( ( unsigned char * ) pxNextTCB->pxEndOfStack );
			}
			#else
			{
				usStackRemaining = usTaskCheckFreeStackSpace( ( unsigned char * ) pxNextTCB->pxStack );
			}
			#endif			
			
			sprintf( pcStatusString, ( char * ) "%s\t\t%c\t%u\t%u\t%u\r\n", pxNextTCB->pcTaskName, cStatus, ( unsigned int ) pxNextTCB->uxPriority, usStackRemaining, ( unsigned int ) pxNextTCB->uxTCBNumber );
			strcat( ( char * ) pcWriteBuffer, ( char * ) pcStatusString );

		} while( pxNextTCB != pxFirstTCB );
	}

#endif
/*-----------------------------------------------------------*/

#if ( configGENERATE_RUN_TIME_STATS == 1 )

	static void prvGenerateRunTimeStatsForTasksInList( const signed char *pcWriteBuffer, xList *pxList, unsigned long ulTotalRunTime )
	{
	volatile tskTCB *pxNextTCB, *pxFirstTCB;
	unsigned long ulStatsAsPercentage;

		/* Write the run time stats of all the TCB's in pxList into the buffer. */
		listGET_OWNER_OF_NEXT_ENTRY( pxFirstTCB, pxList );
		do
		{
			/* Get next TCB in from the list. */
			listGET_OWNER_OF_NEXT_ENTRY( pxNextTCB, pxList );

			/* Divide by zero check. */
			if( ulTotalRunTime > 0UL )
			{
				/* Has the task run at all? */
				if( pxNextTCB->ulRunTimeCounter == 0 )
				{
					/* The task has used no CPU time at all. */
					sprintf( pcStatsString, ( char * ) "%s\t\t0\t\t0%%\r\n", pxNextTCB->pcTaskName );
				}
				else
				{
					/* What percentage of the total run time has the task used?
					This will always be rounded down to the nearest integer.
					ulTotalRunTime has already been divided by 100. */
					ulStatsAsPercentage = pxNextTCB->ulRunTimeCounter / ulTotalRunTime;

					if( ulStatsAsPercentage > 0UL )
					{
						#ifdef portLU_PRINTF_SPECIFIER_REQUIRED
						{
							sprintf( pcStatsString, ( char * ) "%s\t\t%lu\t\t%lu%%\r\n", pxNextTCB->pcTaskName, pxNextTCB->ulRunTimeCounter, ulStatsAsPercentage );							
						}
						#else
						{
							/* sizeof( int ) == sizeof( long ) so a smaller
							printf() library can be used. */
							sprintf( pcStatsString, ( char * ) "%s\t\t%u\t\t%u%%\r\n", pxNextTCB->pcTaskName, ( unsigned int ) pxNextTCB->ulRunTimeCounter, ( unsigned int ) ulStatsAsPercentage );
						}
						#endif
					}
					else
					{
						/* If the percentage is zero here then the task has
						consumed less than 1% of the total run time. */
						#ifdef portLU_PRINTF_SPECIFIER_REQUIRED
						{
							sprintf( pcStatsString, ( char * ) "%s\t\t%lu\t\t<1%%\r\n", pxNextTCB->pcTaskName, pxNextTCB->ulRunTimeCounter );							
						}
						#else
						{
							/* sizeof( int ) == sizeof( long ) so a smaller
							printf() library can be used. */
							sprintf( pcStatsString, ( char * ) "%s\t\t%u\t\t<1%%\r\n", pxNextTCB->pcTaskName, ( unsigned int ) pxNextTCB->ulRunTimeCounter );
						}
						#endif
					}
				}

				strcat( ( char * ) pcWriteBuffer, ( char * ) pcStatsString );
			}

		} while( pxNextTCB != pxFirstTCB );
	}

#endif
/*-----------------------------------------------------------*/

#if ( ( configUSE_TRACE_FACILITY == 1 ) || ( INCLUDE_uxTaskGetStackHighWaterMark == 1 ) )

	static unsigned short usTaskCheckFreeStackSpace( const unsigned char * pucStackByte )
	{
	register unsigned short usCount = 0;

		while( *pucStackByte == tskSTACK_FILL_BYTE )
		{
			pucStackByte -= portSTACK_GROWTH;
			usCount++;
		}

		usCount /= sizeof( portSTACK_TYPE );

		return usCount;
	}

#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_uxTaskGetStackHighWaterMark == 1 )

	unsigned portBASE_TYPE uxTaskGetStackHighWaterMark( xTaskHandle xTask )
	{
	tskTCB *pxTCB;
	unsigned char *pcEndOfStack;
	unsigned portBASE_TYPE uxReturn;

		pxTCB = prvGetTCBFromHandle( xTask );

		#if portSTACK_GROWTH < 0
		{
			pcEndOfStack = ( unsigned char * ) pxTCB->pxStack;
		}
		#else
		{
			pcEndOfStack = ( unsigned char * ) pxTCB->pxEndOfStack;
		}
		#endif

		uxReturn = ( unsigned portBASE_TYPE ) usTaskCheckFreeStackSpace( pcEndOfStack );

		return uxReturn;
	}

#endif
/*-----------------------------------------------------------*/

#if ( ( INCLUDE_vTaskDelete == 1 ) || ( INCLUDE_vTaskCleanUpResources == 1 ) )

	static void prvDeleteTCB( tskTCB *pxTCB )
	{
		/* Free up the memory allocated by the scheduler for the task.  It is up to
		the task to free any memory allocated at the application level. */
		vPortFreeAligned( pxTCB->pxStack );
		vPortFree( pxTCB );
	}

#endif


/*-----------------------------------------------------------*/

#if ( INCLUDE_xTaskGetCurrentTaskHandle == 1 )

	xTaskHandle xTaskGetCurrentTaskHandle( void )
	{
	xTaskHandle xReturn;

		/* A critical section is not required as this is not called from
		an interrupt and the current TCB will always be the same for any
		individual execution thread. */
		xReturn = pxCurrentTCB;

		return xReturn;
	}

#endif

/*-----------------------------------------------------------*/

#if ( INCLUDE_xTaskGetSchedulerState == 1 )

	portBASE_TYPE xTaskGetSchedulerState( void )
	{
	portBASE_TYPE xReturn;

		if( xSchedulerRunning == pdFALSE )
		{
			xReturn = taskSCHEDULER_NOT_STARTED;
		}
		else
		{
			if( uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE )
			{
				xReturn = taskSCHEDULER_RUNNING;
			}
			else
			{
				xReturn = taskSCHEDULER_SUSPENDED;
			}
		}

		return xReturn;
	}

#endif
/*-----------------------------------------------------------*/

#if ( configUSE_MUTEXES == 1 )

	void vTaskPriorityInherit( xTaskHandle * const pxMutexHolder )
	{
	tskTCB * const pxTCB = ( tskTCB * ) pxMutexHolder;

		if( pxTCB->uxPriority < pxCurrentTCB->uxPriority )
		{
			/* Adjust the mutex holder state to account for its new priority. */
			listSET_LIST_ITEM_VALUE( &( pxTCB->xEventListItem ), configMAX_PRIORITIES - ( portTickType ) pxCurrentTCB->uxPriority );

			/* If the task being modified is in the ready state it will need to
			be moved in to a new list. */
			if( listIS_CONTAINED_WITHIN( &( pxReadyTasksLists[ pxTCB->uxPriority ] ), &( pxTCB->xGenericListItem ) ) )
			{
				vListRemove( &( pxTCB->xGenericListItem ) );

				/* Inherit the priority before being moved into the new list. */
				pxTCB->uxPriority = pxCurrentTCB->uxPriority;
				prvAddTaskToReadyQueue( pxTCB );
			}
			else
			{
				/* Just inherit the priority. */
				pxTCB->uxPriority = pxCurrentTCB->uxPriority;
			}
		}
	}

#endif
/*-----------------------------------------------------------*/

#if ( configUSE_MUTEXES == 1 )

	void vTaskPriorityDisinherit( xTaskHandle * const pxMutexHolder )
	{
	tskTCB * const pxTCB = ( tskTCB * ) pxMutexHolder;

		if( pxMutexHolder != NULL )
		{
			if( pxTCB->uxPriority != pxTCB->uxBasePriority )
			{
				/* We must be the running task to be able to give the mutex back.
				Remove ourselves from the ready list we currently appear in. */
				vListRemove( &( pxTCB->xGenericListItem ) );

				/* Disinherit the priority before adding ourselves into the new
				ready list. */
				pxTCB->uxPriority = pxTCB->uxBasePriority;
				listSET_LIST_ITEM_VALUE( &( pxTCB->xEventListItem ), configMAX_PRIORITIES - ( portTickType ) pxTCB->uxPriority );
				prvAddTaskToReadyQueue( pxTCB );
			}
		}
	}

#endif
/*-----------------------------------------------------------*/

#if ( portCRITICAL_NESTING_IN_TCB == 1 )

	void vTaskEnterCritical( void )
	{
		portDISABLE_INTERRUPTS();

		if( xSchedulerRunning != pdFALSE )
		{
			( pxCurrentTCB->uxCriticalNesting )++;
		}
	}

#endif
/*-----------------------------------------------------------*/

#if ( portCRITICAL_NESTING_IN_TCB == 1 )

void vTaskExitCritical( void )
{
	if( xSchedulerRunning != pdFALSE )
	{
		if( pxCurrentTCB->uxCriticalNesting > 0 )
		{
			( pxCurrentTCB->uxCriticalNesting )--;

			if( pxCurrentTCB->uxCriticalNesting == 0 )
			{
				portENABLE_INTERRUPTS();
			}
		}
	}
}

#endif
/*-----------------------------------------------------------*/




