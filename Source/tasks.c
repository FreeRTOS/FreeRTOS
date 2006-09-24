/*
	FreeRTOS.org V4.1.1 - Copyright (C) 2003-2006 Richard Barry.

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
	***************************************************************************
*/

/*
Changes from V1.00:
	
	+ Call to portRESTORE_CONTEXT has been removed.  The first context
	  switch is now performed within sPortStartScheduler().

Changes from V1.01:

	+ More use of 8bit data types.
	+ Function name prefixes changed where the data type returned has changed.
	+ configUSE_TRACE_FACILITY is no longer defined by default.

Changes from V1.2.0

	+ Introduced ucTopReadyPriority.  This tracks the highest priority ready
	  queue that contains a valid TCB and thus makes the context switch
	  slightly faster.

	+ prvAddTaskToReadyQueue() has been made a macro.

Changes from V1.2.6

	+ Added conditional compilation directives.
	+ Extended API.
	+ Rearranged function order.
	+ Creating a task now causes a context switch if the task being created
	  has a higher priority than the calling task - assuming the kernel is
	  running.
	+ vTaskDelete() now only causes a context switch if the calling task is
	  the task being deleted.

Changes from V2.0.0

	+ Allow the type of the tick count to be 16 or 32 bits.
	+ Introduce xPendingReadyList feature to allow the time interrupts have to
	  be disabled to be minimised.
	+ Remove the #if( INCLUDE_vTaskSuspendAll ) statements.  vTaskSuspendAll()
	  is now always included as it is used by the scheduler itself.

Changes from V2.1.0

	+ Bug fix - pxCurrentTCB is now initialised before the call to
	  prvInitializeTaskLists().  Previously pxCurrentTCB could be accessed
	  while null.

Changed from V2.1.1

	+ Change to where lStackSize is declared within sTaskCreate() to prevent
	  compiler warnings with 8051 port.

Changes from V2.2.0

	+ Explicit use of 'signed' qualifier on portCHAR types added.
	+ Changed odd calculation of initial pxTopOfStack value when
	  portSTACK_GROWTH < 0.
	+ Removed pcVersionNumber definition.

Changes from V2.5.3

	+ cTaskResumeAll() modified to ensure it can be called prior to the task
	  lists being initialised.

Changes from V2.5.5

	+ Added API function vTaskDelayUntil().
	+ Added INCLUDE_vTaskDelay conditional compilation.

Changes from V2.6.0

 	+ Updated the vWriteTraceToBuffer macro to always be 4 byte aligned so it
	  can be used on ARM architectures.
	+ tskMAX_TASK_NAME_LEN definition replaced with the port specific
	  configMAX_TASK_NAME_LEN definition.
	+ Removed the call to strcpy when copying across the task name into the
	  TCB.
	+ Added ucTasksDeleted variable to prevent vTaskSuspendAll() being called
	  too often in the idle task.

Changes between V3.0.0 and V2.6.1

	+ When resuming the scheduler a yield is performed if either a tick has
	  been missed, or a task is moved from the pending ready list into a ready
	  list.  Previously a yield was not performed on this second condition.
	+ Introduced the type portBASE_TYPE.  This necessitates several API
	  changes.
	+ Removed the sUsingPreemption variable.  The constant defined in
	  portmacro.h is now used directly.
	+ The idle task can now include an optional hook function - and no longer
	  completes its time slice if other tasks with equal priority to it are
	  ready to run.
	+ See the FreeRTOS.org documentation for more information on V2.x.x to
	  V3.x.x modifications.

Changes from V3.1.1

	+ Modified vTaskPrioritySet() and vTaskResume() to allow these functions to
	  be called while the scheduler is suspended.
	+ Corrected the task ordering within event lists.

Changes from V3.2.0

	+ Added function xTaskGetCurrentTaskHandle().

Changes from V3.2.4

	+ Changed the volatile declarations on some variables to reflect the 
	  changes to the list definitions.
	+ Changed the order of the TCB definition so there is commonality between
	  the task control block and a co-routine control block.
	+ Allow the scheduler to be started even if no tasks other than the idle
	  task has been created.  This allows co-routines to run even when no tasks
	  have been created.
	+ The need for a context switch is now signalled if a task woken by an 
	  event has a priority greater or equal to the currently running task.
	  Previously this was only greater than.

Changes from V4.0.0

	+ Added the xMissedYield handling.

Changes from V4.0.1

	+ The function vTaskList() now suspends the scheduler rather than disabling
	  interrupts during the creation of the task list.  
	+ Allow a task to delete itself by passing in its own handle.  Previously 
	  this could only be done by passing in NULL.
	+ The tick hook function is now called only within a tick isr.  Previously
	  it was also called when the tick function was called during the scheduler
	  unlocking process.

Changes from V4.0.3

	+ Extra checks have been placed in vTaskPrioritySet() to avoid unnecessary
	  yields.

Changed from V4.0.4

	+ Bug fix:  The 'value' of the event list item is updated when the priority
	  of a task is changed.  Previously only the priority of the TCB itself was
	  changed.
	+ When resuming a task a check is first made to see if the task is actually
	  suspended.
	+ vTaskPrioritySet() and vTaskResume() no longer use the event list item.
	  This has not been necessary since V4.0.1 when the xMissedYield handling
	  was added.
	+ Implement xTaskResumeFromISR().

Changes from V4.0.5

	+ Added utility functions and xOverflowCount variable to facilitate the
	  queue.c changes.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "FreeRTOS.h"
#include "task.h"

/*
 * Macro to define the amount of stack available to the idle task.
 */
#define tskIDLE_STACK_SIZE	configMINIMAL_STACK_SIZE


/*
 * Default a definitions for backwards compatibility with old
 * portmacro.h files.
 */
#ifndef configMAX_TASK_NAME_LEN
	#define configMAX_TASK_NAME_LEN 16
#endif

#ifndef INCLUDE_xTaskGetCurrentTaskHandle
	#define INCLUDE_xTaskGetCurrentTaskHandle 0
#endif

#ifndef configIDLE_SHOULD_YIELD
	#define configIDLE_SHOULD_YIELD		1
#endif

#if configMAX_TASK_NAME_LEN < 1
	#undef configMAX_TASK_NAME_LEN
	#define configMAX_TASK_NAME_LEN 1
#endif

#ifndef INCLUDE_xTaskResumeFromISR
	#define INCLUDE_xTaskResumeFromISR 1
#endif 

/*
 * Task control block.  A task control block (TCB) is allocated to each task,
 * and stores the context of the task.
 */
typedef struct tskTaskControlBlock
{
	volatile portSTACK_TYPE	*pxTopOfStack;		/*< Points to the location of the last item placed on the tasks stack.  THIS MUST BE THE FIRST MEMBER OF THE STRUCT. */
	xListItem				xGenericListItem;	/*< List item used to place the TCB in ready and blocked queues. */
	xListItem				xEventListItem;		/*< List item used to place the TCB in event lists. */
	unsigned portBASE_TYPE	uxPriority;			/*< The priority of the task where 0 is the lowest priority. */
	portSTACK_TYPE			*pxStack;			/*< Points to the start of the stack. */
	unsigned portBASE_TYPE	uxTCBNumber;		/*< This is used for tracing the scheduler and making debugging easier only. */
	signed portCHAR			pcTaskName[ configMAX_TASK_NAME_LEN ];/*< Descriptive name given to the task when created.  Facilitates debugging only. */
	unsigned portSHORT		usStackDepth;		/*< Total depth of the stack (when empty).  This is defined as the number of variables the stack can hold, not the number of bytes. */
} tskTCB;

/*lint -e956 */

tskTCB * volatile pxCurrentTCB = NULL;					

/* Lists for ready and blocked tasks. --------------------*/

static xList pxReadyTasksLists[ configMAX_PRIORITIES ];	/*< Prioritised ready tasks. */
static xList xDelayedTaskList1;							/*< Delayed tasks. */
static xList xDelayedTaskList2;							/*< Delayed tasks (two lists are used - one for delays that have overflowed the current tick count. */
static xList * volatile pxDelayedTaskList;				/*< Points to the delayed task list currently being used. */
static xList * volatile pxOverflowDelayedTaskList;		/*< Points to the delayed task list currently being used to hold tasks that have overflowed the current tick count. */
static xList xPendingReadyList;							/*< Tasks that have been readied while the scheduler was suspended.  They will be moved to the ready queue when the scheduler is resumed. */

#if ( INCLUDE_vTaskDelete == 1 )

	static volatile xList xTasksWaitingTermination;		/*< Tasks that have been deleted - but the their memory not yet freed. */
	static volatile unsigned portBASE_TYPE uxTasksDeleted = ( unsigned portBASE_TYPE ) 0;

#endif

#if ( INCLUDE_vTaskSuspend == 1 )

	static xList xSuspendedTaskList;					/*< Tasks that are currently suspended. */

#endif

/* File private variables. --------------------------------*/
static volatile unsigned portBASE_TYPE uxCurrentNumberOfTasks	= ( unsigned portBASE_TYPE ) 0;
static volatile portTickType xTickCount							= ( portTickType ) 0;
static unsigned portBASE_TYPE uxTopUsedPriority					= tskIDLE_PRIORITY;
static volatile unsigned portBASE_TYPE uxTopReadyPriority		= tskIDLE_PRIORITY;
static volatile signed portBASE_TYPE xSchedulerRunning			= pdFALSE;
static volatile unsigned portBASE_TYPE uxSchedulerSuspended		= ( unsigned portBASE_TYPE ) pdFALSE;
static volatile unsigned portBASE_TYPE uxMissedTicks			= ( unsigned portBASE_TYPE ) 0;
static volatile portBASE_TYPE xMissedYield						= ( portBASE_TYPE ) pdFALSE;
static volatile portBASE_TYPE xNumOfOverflows					= ( portBASE_TYPE ) 0;
/* Debugging and trace facilities private variables and macros. ------------*/

/*
 * The value used to fill the stack of a task when the task is created.  This
 * is used purely for checking the high water mark for tasks.
 */
#define tskSTACK_FILL_BYTE	( 0xa5 )

/*
 * Macros used by vListTask to indicate which state a task is in.
 */
#define tskBLOCKED_CHAR		( ( signed portCHAR ) 'B' )
#define tskREADY_CHAR		( ( signed portCHAR ) 'R' )
#define tskDELETED_CHAR		( ( signed portCHAR ) 'D' )
#define tskSUSPENDED_CHAR	( ( signed portCHAR ) 'S' )

/*
 * Macros and private variables used by the trace facility.
 */
#if ( configUSE_TRACE_FACILITY == 1 )

	#define tskSIZE_OF_EACH_TRACE_LINE			( ( unsigned portLONG ) ( sizeof( unsigned portLONG ) + sizeof( unsigned portLONG ) ) )
	static volatile signed portCHAR * volatile pcTraceBuffer;
	static signed portCHAR *pcTraceBufferStart;
	static signed portCHAR *pcTraceBufferEnd;
	static signed portBASE_TYPE xTracing = pdFALSE;

#endif

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
			static unsigned portBASE_TYPE uxPreviousTask = 255;										\
																									\
			if( uxPreviousTask != pxCurrentTCB->uxTCBNumber )										\
			{																						\
				if( ( pcTraceBuffer + tskSIZE_OF_EACH_TRACE_LINE ) < pcTraceBufferEnd )				\
				{																					\
					uxPreviousTask = pxCurrentTCB->uxTCBNumber;										\
					*( unsigned portLONG * ) pcTraceBuffer = ( unsigned portLONG ) xTickCount;		\
					pcTraceBuffer += sizeof( unsigned portLONG );									\
					*( unsigned portLONG * ) pcTraceBuffer = ( unsigned portLONG ) uxPreviousTask;	\
					pcTraceBuffer += sizeof( unsigned portLONG );									\
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


/*
 * Place the task represented by pxTCB into the appropriate ready queue for
 * the task.  It is inserted at the end of the list.  One quirk of this is
 * that if the task being inserted is at the same priority as the currently
 * executing task, then it will only be rescheduled after the currently
 * executing task has been rescheduled.
 */
#define prvAddTaskToReadyQueue( pxTCB )																			\
{																												\
	if( pxTCB->uxPriority > uxTopReadyPriority )																\
	{																											\
		uxTopReadyPriority = pxTCB->uxPriority;																	\
	}																											\
	vListInsertEnd( ( xList * ) &( pxReadyTasksLists[ pxTCB->uxPriority ] ), &( pxTCB->xGenericListItem ) );	\
}		

/*
 * Macro that looks at the list of tasks that are currently delayed to see if
 * any require waking.
 *
 * Tasks are stored in the queue in the order of their wake time - meaning
 * once one tasks has been found whose timer has not expired we need not look
 * any further down the list.
 */
#define prvCheckDelayedTasks()																						\
{																													\
register tskTCB *pxTCB;																								\
																													\
	while( ( pxTCB = ( tskTCB * ) listGET_OWNER_OF_HEAD_ENTRY( pxDelayedTaskList ) ) != NULL )						\
	{																												\
		if( xTickCount < listGET_LIST_ITEM_VALUE( &( pxTCB->xGenericListItem ) ) )									\
		{																											\
			break;																									\
		}																											\
		vListRemove( &( pxTCB->xGenericListItem ) );																\
		/* Is the task waiting on an event also? */																	\
		if( pxTCB->xEventListItem.pvContainer )																		\
		{																											\
			vListRemove( &( pxTCB->xEventListItem ) );																\
		}																											\
		prvAddTaskToReadyQueue( pxTCB );														\
	}																												\
}																							

/*
 * Several functions take an xTaskHandle parameter that can optionally be NULL,
 * where NULL is used to indicate that the handle of the currently executing
 * task should be used in place of the parameter.  This macro simply checks to
 * see if the parameter is NULL and returns a pointer to the appropriate TCB.
 */
#define prvGetTCBFromHandle( pxHandle ) ( ( pxHandle == NULL ) ? ( tskTCB * ) pxCurrentTCB : ( tskTCB * ) pxHandle )


/* File private functions. --------------------------------*/

/*
 * Utility to ready a TCB for a given task.  Mainly just copies the parameters
 * into the TCB structure.
 */
static void prvInitialiseTCBVariables( tskTCB *pxTCB, unsigned portSHORT usStackDepth, const signed portCHAR * const pcName, unsigned portBASE_TYPE uxPriority );

/*
 * Utility to ready all the lists used by the scheduler.  This is called
 * automatically upon the creation of the first task.
 */
static void prvInitialiseTaskLists( void );

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
	static void prvDeleteTCB( tskTCB *pxTCB );
#endif

/*
 * Used only by the idle task.  This checks to see if anything has been placed
 * in the list of tasks waiting to be deleted.  If so the task is cleaned up
 * and its TCB deleted.
 */
static void prvCheckTasksWaitingTermination( void );

/*
 * Allocates memory from the heap for a TCB and associated stack.  Checks the
 * allocation was successful.
 */
static tskTCB *prvAllocateTCBAndStack( unsigned portSHORT usStackDepth );

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

	static void prvListTaskWithinSingleList( signed portCHAR *pcWriteBuffer, xList *pxList, signed portCHAR cStatus );

#endif

/*
 * When a task is created, the stack of the task is filled with a known value.
 * This function determines the 'high water mark' of the task stack by
 * determining how much of the stack remains at the original preset value.
 */
#if ( configUSE_TRACE_FACILITY == 1 )

	unsigned portSHORT usTaskCheckFreeStackSpace( const unsigned portCHAR *pucStackByte );

#endif

/*lint +e956 */





/*-----------------------------------------------------------
 * TASK CREATION API documented in task.h
 *----------------------------------------------------------*/

signed portBASE_TYPE xTaskCreate( pdTASK_CODE pvTaskCode, const signed portCHAR * const pcName, unsigned portSHORT usStackDepth, void *pvParameters, unsigned portBASE_TYPE uxPriority, xTaskHandle *pxCreatedTask )
{
signed portBASE_TYPE xReturn;
tskTCB * pxNewTCB;
static unsigned portBASE_TYPE uxTaskNumber = 0; /*lint !e956 Static is deliberate - this is guarded before use. */

	/* Allocate the memory required by the TCB and stack for the new task.
	checking that the allocation was successful. */
	pxNewTCB = prvAllocateTCBAndStack( usStackDepth );

	if( pxNewTCB != NULL )
	{		
		portSTACK_TYPE *pxTopOfStack;

		/* Setup the newly allocated TCB with the initial state of the task. */
		prvInitialiseTCBVariables( pxNewTCB, usStackDepth, pcName, uxPriority );

		/* Calculate the top of stack address.  This depends on whether the
		stack grows from high memory to low (as per the 80x86) or visa versa.
		portSTACK_GROWTH is used to make the result positive or negative as
		required by the port. */
		#if portSTACK_GROWTH < 0
		{
			pxTopOfStack = pxNewTCB->pxStack + ( pxNewTCB->usStackDepth - 1 );
		}
		#else
		{
			pxTopOfStack = pxNewTCB->pxStack;	
		}
		#endif

		/* Initialize the TCB stack to look as if the task was already running,
		but had been interrupted by the scheduler.  The return address is set
		to the start of the task function. Once the stack has been initialised
		the	top of stack variable is updated. */
		pxNewTCB->pxTopOfStack = pxPortInitialiseStack( pxTopOfStack, pvTaskCode, pvParameters );

		/* We are going to manipulate the task queues to add this task to a
		ready list, so must make sure no interrupts occur. */
		portENTER_CRITICAL();
		{
			uxCurrentNumberOfTasks++;
			if( uxCurrentNumberOfTasks == ( unsigned portBASE_TYPE ) 1 )
			{
				/* As this is the first task it must also be the current task. */
				pxCurrentTCB =  pxNewTCB;

				/* This is the first task to be created so do the preliminary
				initialisation required.  We will not recover if this call
				fails, but we will report the failure. */
				prvInitialiseTaskLists();
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

			/* Add a counter into the TCB for tracing only. */
			pxNewTCB->uxTCBNumber = uxTaskNumber;
			uxTaskNumber++;

			prvAddTaskToReadyQueue( pxNewTCB );

			xReturn = pdPASS;
		}
		portEXIT_CRITICAL();
	}
	else
	{
		xReturn = errCOULD_NOT_ALLOCATE_REQUIRED_MEMORY;
	}

	if( xReturn == pdPASS )
	{
		if( ( void * ) pxCreatedTask != NULL )
		{
			/* Pass the TCB out - in an anonymous way.  The calling function/
			task can use this as a handle to delete the task later if
			required.*/
			*pxCreatedTask = ( xTaskHandle ) pxNewTCB;
		}

		if( xSchedulerRunning != pdFALSE )
		{
			/* If the created task is of a higher priority than the current task
			then it should run now. */
			if( pxCurrentTCB->uxPriority < uxPriority )
			{
				taskYIELD();
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
		}
		taskEXIT_CRITICAL();

		/* Force a reschedule if we have just deleted the current task. */
		if( xSchedulerRunning != pdFALSE ) 
		{
			if( ( void * ) pxTaskToDelete == NULL )
			{
				taskYIELD();
			}
		}
	}

#endif






/*-----------------------------------------------------------
 * TASK CONTROL API documented in task.h
 *----------------------------------------------------------*/

#if ( INCLUDE_vTaskDelayUntil == 1 )

	void vTaskDelayUntil( portTickType *pxPreviousWakeTime, portTickType xTimeIncrement )
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

			if( xShouldDelay )
			{
				/* We must remove ourselves from the ready list before adding
				ourselves to the blocked list as the same list item is used for
				both lists. */
				vListRemove( ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );

				/* The list item will be inserted in wake time order. */
				listSET_LIST_ITEM_VALUE( &( pxCurrentTCB->xGenericListItem ), xTimeToWake );

				if( xTimeToWake < xTickCount )
				{
					/* Wake time has overflowed.  Place this item in the
					overflow list. */
					vListInsert( ( xList * ) pxOverflowDelayedTaskList, ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );
				}
				else
				{
					/* The wake time has not overflowed, so we can use the
					current block list. */
					vListInsert( ( xList * ) pxDelayedTaskList, ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );
				}
			}
		}
		xAlreadyYielded = xTaskResumeAll();

		/* Force a reschedule if xTaskResumeAll has not already done so, we may
		have put ourselves to sleep. */
		if( !xAlreadyYielded )
		{
			taskYIELD();
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

				/* The list item will be inserted in wake time order. */
				listSET_LIST_ITEM_VALUE( &( pxCurrentTCB->xGenericListItem ), xTimeToWake );

				if( xTimeToWake < xTickCount )
				{
					/* Wake time has overflowed.  Place this item in the
					overflow list. */
					vListInsert( ( xList * ) pxOverflowDelayedTaskList, ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );
				}
				else
				{
					/* The wake time has not overflowed, so we can use the
					current block list. */
					vListInsert( ( xList * ) pxDelayedTaskList, ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );
				}
			}
			xAlreadyYielded = xTaskResumeAll();
		}
		
		/* Force a reschedule if xTaskResumeAll has not already done so, we may
		have put ourselves to sleep. */
		if( !xAlreadyYielded )
		{
			taskYIELD();
		}
	}
	
#endif
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
	unsigned portBASE_TYPE uxCurrentPriority, xYieldRequired = pdFALSE;

		/* Ensure the new priority is valid. */
		if( uxNewPriority >= configMAX_PRIORITIES )
		{
			uxNewPriority = configMAX_PRIORITIES - 1;
		}

		taskENTER_CRITICAL();
		{
			/* If null is passed in here then we are changing the
			priority of the calling function. */
			pxTCB = prvGetTCBFromHandle( pxTask );
			uxCurrentPriority = pxTCB->uxPriority;

			if( uxCurrentPriority != uxNewPriority )
			{
				/* The priority change may have readied a task of higher
				priority than the calling task. */
				if( uxNewPriority > pxCurrentTCB->uxPriority ) 
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
			
				pxTCB->uxPriority = uxNewPriority;
				listSET_LIST_ITEM_VALUE( &( pxTCB->xEventListItem ), configMAX_PRIORITIES - ( portTickType ) uxNewPriority );

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
					taskYIELD();
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

		/* We may have just suspended the current task. */
		if( ( void * ) pxTaskToSuspend == NULL )
		{
			taskYIELD();
		}
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
		if( pxTCB != NULL )
		{
			taskENTER_CRITICAL();
			{
				/* Is the task we are attempting to resume actually suspended? */
				if( listIS_CONTAINED_WITHIN( &xSuspendedTaskList, &( pxTCB->xGenericListItem ) ) != pdFALSE )
				{
					/* Has the task already been resumed from within an ISR? */
					if( listIS_CONTAINED_WITHIN( &xPendingReadyList, &( pxTCB->xEventListItem ) ) != pdTRUE )
					{			
						/* As we are in a critical section we can access the ready 
						lists even if the scheduler is suspended. */
						vListRemove(  &( pxTCB->xGenericListItem ) );
						prvAddTaskToReadyQueue( pxTCB );

						/* We may have just resumed a higher priority task. */
						if( pxTCB->uxPriority >= pxCurrentTCB->uxPriority )
						{
							/* This yield may not cause the task just resumed to run, but
							will leave the lists in the correct state for the next yield. */
							taskYIELD();
						}
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

		/* Is the task we are attempting to resume actually suspended? */
		if( listIS_CONTAINED_WITHIN( &xSuspendedTaskList, &( pxTCB->xGenericListItem ) ) != pdFALSE )
		{
			/* Has the task already been resumed from within an ISR? */
			if( listIS_CONTAINED_WITHIN( &xPendingReadyList, &( pxTCB->xEventListItem ) ) != pdTRUE )
			{
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
					yield will be preformed if necessary. */
					vListInsertEnd( ( xList * ) &( xPendingReadyList ), &( pxTCB->xEventListItem ) );
				}
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
	xReturn = xTaskCreate( prvIdleTask, ( signed portCHAR * ) "IDLE", tskIDLE_STACK_SIZE, ( void * ) NULL, tskIDLE_PRIORITY, ( xTaskHandle * ) NULL );

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
	portENTER_CRITICAL();
		++uxSchedulerSuspended;
	portEXIT_CRITICAL();
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
	portENTER_CRITICAL();
	{
		--uxSchedulerSuspended;

		if( uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE )
		{			
			if( uxCurrentNumberOfTasks > ( unsigned portBASE_TYPE ) 0 )
			{
				portBASE_TYPE xYieldRequired = pdFALSE;
				
				/* Move any readied tasks from the pending list into the
				appropriate ready list. */
				while( ( pxTCB = ( tskTCB * ) listGET_OWNER_OF_HEAD_ENTRY(  ( ( xList * ) &xPendingReadyList ) ) ) != NULL )
				{
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
					xYieldRequired = pdTRUE;
				}
				
				if( ( xYieldRequired == pdTRUE ) || ( xMissedYield == pdTRUE ) )
				{
					xAlreadyYielded = pdTRUE;
					xMissedYield = pdFALSE;
					taskYIELD();
				}
			}
		}
	}
	portEXIT_CRITICAL();

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

unsigned portBASE_TYPE uxTaskGetNumberOfTasks( void )
{
unsigned portBASE_TYPE uxNumberOfTasks;

	taskENTER_CRITICAL();
		uxNumberOfTasks = uxCurrentNumberOfTasks;
	taskEXIT_CRITICAL();

	return uxNumberOfTasks;
}
/*-----------------------------------------------------------*/

#if ( ( configUSE_TRACE_FACILITY == 1 ) && ( INCLUDE_vTaskDelete == 1 ) && ( INCLUDE_vTaskSuspend == 1 ) )

	void vTaskList( signed portCHAR *pcWriteBuffer )
	{
	unsigned portBASE_TYPE uxQueue;

		/* This is a VERY costly function that should be used for debug only.
		It leaves interrupts disabled for a LONG time. */

        vTaskSuspendAll();
		{
			/* Run through all the lists that could potentially contain a TCB and
			report the task name, state and stack high water mark. */

			pcWriteBuffer[ 0 ] = ( signed portCHAR ) 0x00;
			strcat( ( portCHAR * ) pcWriteBuffer, ( const portCHAR * ) "\r\n" );

			uxQueue = uxTopUsedPriority + 1;

			do
			{
				uxQueue--;

				if( !listLIST_IS_EMPTY( &( pxReadyTasksLists[ uxQueue ] ) ) )
				{
					prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) &( pxReadyTasksLists[ uxQueue ] ), tskREADY_CHAR );			
				}
			}while( uxQueue > ( unsigned portSHORT ) tskIDLE_PRIORITY );

			if( !listLIST_IS_EMPTY( pxDelayedTaskList ) )
			{
				prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) pxDelayedTaskList, tskBLOCKED_CHAR );
			}

			if( !listLIST_IS_EMPTY( pxOverflowDelayedTaskList ) )
			{
				prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) pxOverflowDelayedTaskList, tskBLOCKED_CHAR );
			}

			if( !listLIST_IS_EMPTY( &xTasksWaitingTermination ) )
			{
				prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) &xTasksWaitingTermination, tskDELETED_CHAR );
			}

			if( !listLIST_IS_EMPTY( &xSuspendedTaskList ) )
			{
				prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) &xSuspendedTaskList, tskSUSPENDED_CHAR );
			}
		}
        xTaskResumeAll();
	}

#endif
/*----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )

	void vTaskStartTrace( signed portCHAR * pcBuffer, unsigned portLONG ulBufferSize )
	{
		portENTER_CRITICAL();
		{
			pcTraceBuffer = ( volatile signed portCHAR * volatile )pcBuffer;
			pcTraceBufferStart = pcBuffer;
			pcTraceBufferEnd = pcBuffer + ( ulBufferSize - tskSIZE_OF_EACH_TRACE_LINE );
			xTracing = pdTRUE;
		}
		portEXIT_CRITICAL();
	}

#endif
/*----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )

	unsigned portLONG ulTaskEndTrace( void )
	{
	unsigned portLONG ulBufferLength;

		portENTER_CRITICAL();
			xTracing = pdFALSE;
		portEXIT_CRITICAL();

		ulBufferLength = ( unsigned portLONG ) ( pcTraceBuffer - pcTraceBufferStart );

		return ulBufferLength;
	}

#endif



/*-----------------------------------------------------------
 * SCHEDULER INTERNALS AVAILABLE FOR PORTING PURPOSES
 * documented in task.h
 *----------------------------------------------------------*/


inline void vTaskIncrementTick( void )
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
			pxTemp = pxDelayedTaskList;
			pxDelayedTaskList = pxOverflowDelayedTaskList;
			pxOverflowDelayedTaskList = pxTemp;
            xNumOfOverflows++;
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
}
/*-----------------------------------------------------------*/

#if ( ( INCLUDE_vTaskCleanUpResources == 1 ) && ( INCLUDE_vTaskSuspend == 1 ) )

	void vTaskCleanUpResources( void )
	{
	unsigned portSHORT usQueue;
	volatile tskTCB *pxTCB;

		usQueue = ( unsigned portSHORT ) uxTopUsedPriority + ( unsigned portSHORT ) 1;

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
		}while( usQueue > ( unsigned portSHORT ) tskIDLE_PRIORITY );

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

		while( !listLIST_IS_EMPTY( &xPendingReadyList ) )
		{
			listGET_OWNER_OF_NEXT_ENTRY( pxTCB, &xPendingReadyList );
			vListRemove( ( xListItem * ) &( pxTCB->xGenericListItem ) );

			prvDeleteTCB( ( tskTCB * ) pxTCB );
		}		
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
		return;
	}

	/* Find the highest priority queue that contains ready tasks. */
	while( listLIST_IS_EMPTY( &( pxReadyTasksLists[ uxTopReadyPriority ] ) ) )
	{
		--uxTopReadyPriority;
	}

	/* listGET_OWNER_OF_NEXT_ENTRY walks through the list, so the tasks of the
	same priority get an equal share of the processor time. */
	listGET_OWNER_OF_NEXT_ENTRY( pxCurrentTCB, &( pxReadyTasksLists[ uxTopReadyPriority ] ) );
	vWriteTraceToBuffer();
}
/*-----------------------------------------------------------*/

void vTaskPlaceOnEventList( xList *pxEventList, portTickType xTicksToWait )
{
portTickType xTimeToWake;

	/* THIS FUNCTION MUST BE CALLED WITH INTERRUPTS DISABLED OR THE
	SCHEDULER SUSPENDED. */

	/* Place the event list item of the TCB in the appropriate event list.
	This is placed in the list in priority order so the highest priority task
	is the first to be woken by the event. */
	vListInsert( ( xList * ) pxEventList, ( xListItem * ) &( pxCurrentTCB->xEventListItem ) );

	/* Calculate the time at which the task should be woken if the event does
	not occur.  This may overflow but this doesn't matter. */
	xTimeToWake = xTickCount + xTicksToWait;

	/* We must remove ourselves from the ready list before adding ourselves
	to the blocked list as the same list item is used for both lists.  We have
	exclusive access to the ready lists as the scheduler is locked. */
	vListRemove( ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) );

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
	}
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xTaskRemoveFromEventList( const xList *pxEventList )
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
	means we can always expect exclusive access to the event list here. */
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

void vTaskSetTimeOutState( xTimeOutType *pxTimeOut )
{
    pxTimeOut->xOverflowCount = xNumOfOverflows;
    pxTimeOut->xTimeOnEntering = xTickCount;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xTaskCheckForTimeOut( xTimeOutType *pxTimeOut, portTickType *pxTicksToWait )
{
portBASE_TYPE xReturn;

    if( ( xNumOfOverflows != pxTimeOut->xOverflowCount ) && ( xTickCount > pxTimeOut->xTimeOnEntering ) )
    {
        /* The tick count is greater than the time at which vTaskSetTimeout() 
		was called, but has also overflowed since vTaskSetTimeOut() was called.
        It must have wrapped all the way around and gone past us again. This
        passed since vTaskSetTimeout() was called. */
        xReturn = pdTRUE;
    }
    else if( ( xTickCount - pxTimeOut->xTimeOnEntering ) < *pxTicksToWait )
    {
        /* Not a genuine timeout. Adjust parameters for time remaining. */
        *pxTicksToWait -= ( xTickCount - pxTimeOut->xTimeOnEntering );
        vTaskSetTimeOutState( pxTimeOut );
        xReturn = pdFALSE;
    }
    else
    {
        xReturn = pdTRUE;
    }

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



static void prvInitialiseTCBVariables( tskTCB *pxTCB, unsigned portSHORT usStackDepth, const signed portCHAR * const pcName, unsigned portBASE_TYPE uxPriority )
{
	pxTCB->usStackDepth = usStackDepth;

	/* Store the function name in the TCB. */
	strncpy( ( char * ) pxTCB->pcTaskName, ( const char * ) pcName, ( unsigned portSHORT ) configMAX_TASK_NAME_LEN );
	pxTCB->pcTaskName[ ( unsigned portSHORT ) configMAX_TASK_NAME_LEN - ( unsigned portSHORT ) 1 ] = '\0';

	/* This is used as an array index so must ensure it's not too large. */
	if( uxPriority >= configMAX_PRIORITIES )
	{
		uxPriority = configMAX_PRIORITIES - 1;
	}

	pxTCB->uxPriority = uxPriority;

	vListInitialiseItem( &( pxTCB->xGenericListItem ) );
	vListInitialiseItem( &( pxTCB->xEventListItem ) );

	/* Set the pxTCB as a link back from the xListItem.  This is so we can get
	back to	the containing TCB from a generic item in a list. */
	listSET_LIST_ITEM_OWNER( &( pxTCB->xGenericListItem ), pxTCB );

	/* Event lists are always in priority order. */
	listSET_LIST_ITEM_VALUE( &( pxTCB->xEventListItem ), configMAX_PRIORITIES - ( portTickType ) uxPriority );
	listSET_LIST_ITEM_OWNER( &( pxTCB->xEventListItem ), pxTCB );
}
/*-----------------------------------------------------------*/

static void prvInitialiseTaskLists( void )
{
unsigned portBASE_TYPE uxPriority;

	for( uxPriority = 0; uxPriority < configMAX_PRIORITIES; uxPriority++ )
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

			if( !xListIsEmpty )
			{
				tskTCB *pxTCB;

				portENTER_CRITICAL();
				{			
					pxTCB = ( tskTCB * ) listGET_OWNER_OF_HEAD_ENTRY( ( ( xList * ) &xTasksWaitingTermination ) );
					vListRemove( &( pxTCB->xGenericListItem ) );
					--uxCurrentNumberOfTasks;
					--uxTasksDeleted;
				}
				portEXIT_CRITICAL();

				prvDeleteTCB( pxTCB );
			}
		}
	}
	#endif
}
/*-----------------------------------------------------------*/

static tskTCB *prvAllocateTCBAndStack( unsigned portSHORT usStackDepth )
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
		pxNewTCB->pxStack = ( portSTACK_TYPE * ) pvPortMalloc( ( ( size_t )usStackDepth ) * sizeof( portSTACK_TYPE ) );

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

	static void prvListTaskWithinSingleList( signed portCHAR *pcWriteBuffer, xList *pxList, signed portCHAR cStatus )
	{
	volatile tskTCB *pxNextTCB, *pxFirstTCB;
	static portCHAR pcStatusString[ 50 ];
	unsigned portSHORT usStackRemaining;

		/* Write the details of all the TCB's in pxList into the buffer. */
		listGET_OWNER_OF_NEXT_ENTRY( pxFirstTCB, pxList );
		do
		{
			listGET_OWNER_OF_NEXT_ENTRY( pxNextTCB, pxList );
			usStackRemaining = usTaskCheckFreeStackSpace( ( unsigned portCHAR * ) pxNextTCB->pxStack );
			sprintf( pcStatusString, ( portCHAR * ) "%s\t\t%c\t%u\t%u\t%u\r\n", pxNextTCB->pcTaskName, cStatus, ( unsigned int ) pxNextTCB->uxPriority, usStackRemaining, ( unsigned int ) pxNextTCB->uxTCBNumber );
			strcat( ( portCHAR * ) pcWriteBuffer, ( portCHAR * ) pcStatusString );

		} while( pxNextTCB != pxFirstTCB );
	}

#endif
/*-----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )
	unsigned portSHORT usTaskCheckFreeStackSpace( const unsigned portCHAR *pucStackByte )
	{
	register unsigned portSHORT usCount = 0;

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



#if ( ( INCLUDE_vTaskDelete == 1 ) || ( INCLUDE_vTaskCleanUpResources == 1 ) )

	static void prvDeleteTCB( tskTCB *pxTCB )
	{
		/* Free up the memory allocated by the scheduler for the task.  It is up to
		the task to free any memory allocated at the application level. */
		vPortFree( pxTCB->pxStack );
		vPortFree( pxTCB );
	}

#endif


/*-----------------------------------------------------------*/

#if ( INCLUDE_xTaskGetCurrentTaskHandle == 1 )

	xTaskHandle xTaskGetCurrentTaskHandle( void )
	{
	xTaskHandle xReturn;

		portENTER_CRITICAL();
		{
			xReturn = ( xTaskHandle ) pxCurrentTCB;
		}
		portEXIT_CRITICAL();

		return xReturn;
	}

#endif





