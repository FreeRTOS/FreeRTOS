/*
    FreeRTOS V7.3.0 - Copyright (C) 2012 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

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
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************


    http://www.FreeRTOS.org - Documentation, training, latest versions, license
    and contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell
    the code with commercial support, indemnification, and middleware, under
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
all the API functions to use the MPU wrappers.  That should only be done when
task.h is included from an application file. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "StackMacros.h"

#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/*
 * Defines the size, in words, of the stack allocated to the idle task.
 */
#define tskIDLE_STACK_SIZE	configMINIMAL_STACK_SIZE

/*
 * Task control block.  A task control block (TCB) is allocated for each task,
 * and stores task state information, including a pointer to the task's context
 * (the task's run time environment, including register values)
 */
typedef struct tskTaskControlBlock
{
	volatile portSTACK_TYPE	*pxTopOfStack;		/*< Points to the location of the last item placed on the tasks stack.  THIS MUST BE THE FIRST MEMBER OF THE TCB STRUCT. */

	#if ( portUSING_MPU_WRAPPERS == 1 )
		xMPU_SETTINGS xMPUSettings;				/*< The MPU settings are defined as part of the port layer.  THIS MUST BE THE SECOND MEMBER OF THE TCB STRUCT. */
	#endif

	xListItem				xGenericListItem;		/*< The list that the state list item of a task is reference from denotes the state of that task (Ready, Blocked, Suspended ). */
	xListItem				xEventListItem;		/*< Used to reference a task from an event list. */
	unsigned portBASE_TYPE	uxPriority;			/*< The priority of the task.  0 is the lowest priority. */
	portSTACK_TYPE			*pxStack;			/*< Points to the start of the stack. */
	signed char				pcTaskName[ configMAX_TASK_NAME_LEN ];/*< Descriptive name given to the task when created.  Facilitates debugging only. */

	#if ( portSTACK_GROWTH > 0 )
		portSTACK_TYPE *pxEndOfStack;			/*< Points to the end of the stack on architectures where the stack grows up from low memory. */
	#endif

	#if ( portCRITICAL_NESTING_IN_TCB == 1 )
		unsigned portBASE_TYPE uxCriticalNesting; /*< Holds the critical section nesting depth for ports that do not maintain their own count in the port layer. */
	#endif

	#if ( configUSE_TRACE_FACILITY == 1 )
		unsigned portBASE_TYPE	uxTCBNumber;	/*< Stores a number that increments each time a TCB is created.  It allows debuggers to determine when a task has been deleted and then recreated. */
		unsigned portBASE_TYPE  uxTaskNumber;	/*< Stores a number specifically for use by third party trace code. */
	#endif

	#if ( configUSE_MUTEXES == 1 )
		unsigned portBASE_TYPE uxBasePriority;	/*< The priority last assigned to the task - used by the priority inheritance mechanism. */
	#endif

	#if ( configUSE_APPLICATION_TASK_TAG == 1 )
		pdTASK_HOOK_CODE pxTaskTag;
	#endif

	#if ( configGENERATE_RUN_TIME_STATS == 1 )
		unsigned long ulRunTimeCounter;			/*< Stores the amount of time the task has spent in the Running state. */
	#endif

} tskTCB;


/*
 * Some kernel aware debuggers require the data the debugger needs access to to
 * be global, rather than file scope.
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

	PRIVILEGED_DATA static xList xTasksWaitingTermination;				/*< Tasks that have been deleted - but the their memory not yet freed. */
	PRIVILEGED_DATA static volatile unsigned portBASE_TYPE uxTasksDeleted = ( unsigned portBASE_TYPE ) 0U;

#endif

#if ( INCLUDE_vTaskSuspend == 1 )

	PRIVILEGED_DATA static xList xSuspendedTaskList;					/*< Tasks that are currently suspended. */

#endif

#if ( INCLUDE_xTaskGetIdleTaskHandle == 1 )

	PRIVILEGED_DATA static xTaskHandle xIdleTaskHandle = NULL;			/*< Holds the handle of the idle task.  The idle task is created automatically when the scheduler is started. */

#endif

/* File private variables. --------------------------------*/
PRIVILEGED_DATA static volatile unsigned portBASE_TYPE uxCurrentNumberOfTasks 	= ( unsigned portBASE_TYPE ) 0U;
PRIVILEGED_DATA static volatile portTickType xTickCount 						= ( portTickType ) 0U;
PRIVILEGED_DATA static unsigned portBASE_TYPE uxTopUsedPriority	 				= tskIDLE_PRIORITY;
PRIVILEGED_DATA static volatile unsigned portBASE_TYPE uxTopReadyPriority 		= tskIDLE_PRIORITY;
PRIVILEGED_DATA static volatile signed portBASE_TYPE xSchedulerRunning 			= pdFALSE;
PRIVILEGED_DATA static volatile unsigned portBASE_TYPE uxSchedulerSuspended	 	= ( unsigned portBASE_TYPE ) pdFALSE;
PRIVILEGED_DATA static volatile unsigned portBASE_TYPE uxMissedTicks 			= ( unsigned portBASE_TYPE ) 0U;
PRIVILEGED_DATA static volatile portBASE_TYPE xMissedYield 						= ( portBASE_TYPE ) pdFALSE;
PRIVILEGED_DATA static volatile portBASE_TYPE xNumOfOverflows 					= ( portBASE_TYPE ) 0;
PRIVILEGED_DATA static unsigned portBASE_TYPE uxTaskNumber 						= ( unsigned portBASE_TYPE ) 0U;
PRIVILEGED_DATA static volatile portTickType xNextTaskUnblockTime				= ( portTickType ) portMAX_DELAY;

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

/*-----------------------------------------------------------*/

#if configUSE_PORT_OPTIMISED_TASK_SELECTION == 0

	/* If configUSE_PORT_OPTIMISED_TASK_SELECTION is 0 then task selection is
	performed in a generic way that is not optimised to any particular
	microcontroller architecture. */

	/* uxTopReadyPriority holds the priority of the highest priority ready
	state task. */
	#define taskRECORD_READY_PRIORITY( uxPriority )																		\
	{																													\
		if( ( uxPriority ) > uxTopReadyPriority )																		\
		{																												\
			uxTopReadyPriority = ( uxPriority );																		\
		}																												\
	} /* taskRECORD_READY_PRIORITY */

	/*-----------------------------------------------------------*/

	#define taskSELECT_HIGHEST_PRIORITY_TASK()																			\
	{																													\
		/* Find the highest priority queue that contains ready tasks. */												\
		while( listLIST_IS_EMPTY( &( pxReadyTasksLists[ uxTopReadyPriority ] ) ) )										\
		{																												\
			configASSERT( uxTopReadyPriority );																			\
			--uxTopReadyPriority;																						\
		}																												\
																														\
		/* listGET_OWNER_OF_NEXT_ENTRY indexes through the list, so the tasks of										\
		the	same priority get an equal share of the processor time. */													\
		listGET_OWNER_OF_NEXT_ENTRY( pxCurrentTCB, &( pxReadyTasksLists[ uxTopReadyPriority ] ) );						\
	} /* taskSELECT_HIGHEST_PRIORITY_TASK */

	/*-----------------------------------------------------------*/

	/* Define away taskRESET_READY_PRIORITY() and portRESET_READY_PRIORITY() as
	they are only required when a port optimised method of task selection is
	being used. */
	#define taskRESET_READY_PRIORITY( uxPriority )
	#define portRESET_READY_PRIORITY( uxPriority, uxTopReadyPriority )

#else /* configUSE_PORT_OPTIMISED_TASK_SELECTION */

	/* If configUSE_PORT_OPTIMISED_TASK_SELECTION is 1 then task selection is
	performed in a way that is tailored to the particular microcontroller
	architecture being used. */

	/* A port optimised version is provided.  Call the port defined macros. */
	#define taskRECORD_READY_PRIORITY( uxPriority )	portRECORD_READY_PRIORITY( uxPriority, uxTopReadyPriority )

	/*-----------------------------------------------------------*/

	#define taskSELECT_HIGHEST_PRIORITY_TASK()														\
	{																								\
	unsigned portBASE_TYPE uxTopPriority;															\
																									\
		/* Find the highest priority queue that contains ready tasks. */							\
		portGET_HIGHEST_PRIORITY( uxTopPriority, uxTopReadyPriority );								\
		configASSERT( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ uxTopPriority ] ) ) > 0 );		\
		listGET_OWNER_OF_NEXT_ENTRY( pxCurrentTCB, &( pxReadyTasksLists[ uxTopPriority ] ) );		\
	} /* taskSELECT_HIGHEST_PRIORITY_TASK() */

	/*-----------------------------------------------------------*/

	/* A port optimised version is provided, call it only if the TCB being reset
	is being referenced from a ready list.  If it is referenced from a delayed
	or suspended list then it won't be in a ready list. */
	#define taskRESET_READY_PRIORITY( uxPriority )													\
	{																								\
		if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ ( uxPriority ) ] ) ) == 0 )				\
		{																							\
			portRESET_READY_PRIORITY( ( uxPriority ), ( uxTopReadyPriority ) );						\
		}																							\
	}

#endif /* configUSE_PORT_OPTIMISED_TASK_SELECTION */

/*
 * Place the task represented by pxTCB into the appropriate ready queue for
 * the task.  It is inserted at the end of the list.  One quirk of this is
 * that if the task being inserted is at the same priority as the currently
 * executing task, then it will only be rescheduled after the currently
 * executing task has been rescheduled.
 */
#define prvAddTaskToReadyQueue( pxTCB )																				\
	traceMOVED_TASK_TO_READY_STATE( pxTCB )																			\
	taskRECORD_READY_PRIORITY( ( pxTCB )->uxPriority );																\
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
				uxListRemove( &( pxTCB->xGenericListItem ) );							\
																						\
				/* Is the task waiting on an event also? */								\
				if( pxTCB->xEventListItem.pvContainer != NULL )							\
				{																		\
					uxListRemove( &( pxTCB->xEventListItem ) );							\
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
extern void vApplicationStackOverflowHook( xTaskHandle pxTask, signed char *pcTaskName );
extern void vApplicationTickHook( void );

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
#if ( INCLUDE_vTaskDelete == 1 )

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

/*
 * Return the amount of time, in ticks, that will pass before the kernel will
 * next move a task from the Blocked state to the Running state.
 *
 * This conditional compilation should use inequality to 0, not equality to 1.
 * This is to ensure portSUPPRESS_TICKS_AND_SLEEP() can be called when user
 * defined low power mode implementations require configUSE_TICKLESS_IDLE to be
 * set to a value other than 1.
 */
#if ( configUSE_TICKLESS_IDLE != 0 )

	static portTickType prvGetExpectedIdleTime( void ) PRIVILEGED_FUNCTION;

#endif

/*lint +e956 */



/*-----------------------------------------------------------
 * TASK CREATION API documented in task.h
 *----------------------------------------------------------*/

signed portBASE_TYPE xTaskGenericCreate( pdTASK_CODE pxTaskCode, const signed char * const pcName, unsigned short usStackDepth, void *pvParameters, unsigned portBASE_TYPE uxPriority, xTaskHandle *pxCreatedTask, portSTACK_TYPE *puxStackBuffer, const xMemoryRegion * const xRegions )
{
signed portBASE_TYPE xReturn;
tskTCB * pxNewTCB;

	configASSERT( pxTaskCode );
	configASSERT( ( ( uxPriority & ( ~portPRIVILEGE_BIT ) ) < configMAX_PRIORITIES ) );

	/* Allocate the memory required by the TCB and stack for the new task,
	checking that the allocation was successful. */
	pxNewTCB = prvAllocateTCBAndStack( usStackDepth, puxStackBuffer );

	if( pxNewTCB != NULL )
	{
		portSTACK_TYPE *pxTopOfStack;

		#if( portUSING_MPU_WRAPPERS == 1 )
			/* Should the task be created in privileged mode? */
			portBASE_TYPE xRunPrivileged;
			if( ( uxPriority & portPRIVILEGE_BIT ) != 0U )
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
			pxTopOfStack = ( portSTACK_TYPE * ) ( ( ( portPOINTER_SIZE_TYPE ) pxTopOfStack ) & ( ( portPOINTER_SIZE_TYPE ) ~portBYTE_ALIGNMENT_MASK  ) );

			/* Check the alignment of the calculated top of stack is correct. */
			configASSERT( ( ( ( unsigned long ) pxTopOfStack & ( unsigned long ) portBYTE_ALIGNMENT_MASK ) == 0UL ) );
		}
		#else
		{
			pxTopOfStack = pxNewTCB->pxStack;

			/* Check the alignment of the stack buffer is correct. */
			configASSERT( ( ( ( unsigned long ) pxNewTCB->pxStack & ( unsigned long ) portBYTE_ALIGNMENT_MASK ) == 0UL ) );

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

		/* Check the alignment of the initialised stack. */
		portALIGNMENT_ASSERT_pxCurrentTCB( ( ( ( unsigned long ) pxNewTCB->pxTopOfStack & ( unsigned long ) portBYTE_ALIGNMENT_MASK ) == 0UL ) );

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
			portSETUP_TCB( pxNewTCB );
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
			if( uxListRemove( ( xListItem * ) &( pxTCB->xGenericListItem ) ) == 0 )
			{
				taskRESET_READY_PRIORITY( pxTCB->uxPriority );
			}

			/* Is the task waiting on an event also? */
			if( pxTCB->xEventListItem.pvContainer != NULL )
			{
				uxListRemove( &( pxTCB->xEventListItem ) );
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

		configASSERT( pxPreviousWakeTime );
		configASSERT( ( xTimeIncrement > 0U ) );

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
				if( uxListRemove( ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) ) == 0 )
				{
					/* The current task must be in a ready list, so there is
					no need to check, and the port reset macro can be called
					directly. */
					portRESET_READY_PRIORITY( pxCurrentTCB->uxPriority, uxTopReadyPriority );
				}

				prvAddCurrentTaskToDelayedList( xTimeToWake );
			}
		}
		xAlreadyYielded = xTaskResumeAll();

		/* Force a reschedule if xTaskResumeAll has not already done so, we may
		have put ourselves to sleep. */
		if( xAlreadyYielded == pdFALSE )
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
		if( xTicksToDelay > ( portTickType ) 0U )
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
				if( uxListRemove( ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) ) == 0 )
				{
					/* The current task must be in a ready list, so there is
					no need to check, and the port reset macro can be called
					directly. */
					portRESET_READY_PRIORITY( pxCurrentTCB->uxPriority, uxTopReadyPriority );
				}
				prvAddCurrentTaskToDelayedList( xTimeToWake );
			}
			xAlreadyYielded = xTaskResumeAll();
		}

		/* Force a reschedule if xTaskResumeAll has not already done so, we may
		have put ourselves to sleep. */
		if( xAlreadyYielded == pdFALSE )
		{
			portYIELD_WITHIN_API();
		}
	}

#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_eTaskStateGet == 1 )

	eTaskState eTaskStateGet( xTaskHandle pxTask )
	{
	eTaskState eReturn;
	xList *pxStateList;
	tskTCB *pxTCB;

		pxTCB = ( tskTCB * ) pxTask;

		if( pxTCB == pxCurrentTCB )
		{
			/* The task calling this function is querying its own state. */
			eReturn = eRunning;
		}
		else
		{
			taskENTER_CRITICAL();
			{
				pxStateList = ( xList * ) listLIST_ITEM_CONTAINER( &( pxTCB->xGenericListItem ) );
			}
			taskEXIT_CRITICAL();

			if( ( pxStateList == pxDelayedTaskList ) || ( pxStateList == pxOverflowDelayedTaskList ) )
			{
				/* The task being queried is referenced from one of the Blocked
				lists. */
				eReturn = eBlocked;
			}

			#if ( INCLUDE_vTaskSuspend == 1 )
				else if( pxStateList == &xSuspendedTaskList )
				{
					/* The task being queried is referenced from the suspended
					list. */
					eReturn = eSuspended;
				}
			#endif

			#if ( INCLUDE_vTaskDelete == 1 )
				else if( pxStateList == &xTasksWaitingTermination )
				{
					/* The task being queried is referenced from the deleted
					tasks list. */
					eReturn = eDeleted;
				}
			#endif

			else
			{
				/* If the task is not in any other state, it must be in the
				Ready (including pending ready) state. */
				eReturn = eReady;
			}
		}

		return eReturn;
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
	unsigned portBASE_TYPE uxCurrentPriority, uxPriorityUsedOnEntry;
	portBASE_TYPE xYieldRequired = pdFALSE;

		configASSERT( ( uxNewPriority < configMAX_PRIORITIES ) );

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

			traceTASK_PRIORITY_SET( pxTCB, uxNewPriority );

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

				/* Remember the ready list the task might be referenced from
				before its uxPriority member is changed so the
				taskRESET_READY_PRIORITY() macro can function correctly. */
				uxPriorityUsedOnEntry = pxTCB->uxPriority;

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
					if( uxListRemove( ( xListItem * ) &( pxTCB->xGenericListItem ) ) == 0 )
					{
						taskRESET_READY_PRIORITY( uxPriorityUsedOnEntry );
					}
					prvAddTaskToReadyQueue( pxTCB );
				}

				if( xYieldRequired == pdTRUE )
				{
					portYIELD_WITHIN_API();
				}
			}
		}
		taskEXIT_CRITICAL();

		/* Remove compiler warning about unused parameter when the port
		optimised task selection is not being used. */
		( void ) uxPriorityUsedOnEntry;
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
			if( uxListRemove( ( xListItem * ) &( pxTCB->xGenericListItem ) ) == 0 )
			{
				taskRESET_READY_PRIORITY( pxTCB->uxPriority );
			}

			/* Is the task waiting on an event also? */
			if( pxTCB->xEventListItem.pvContainer != NULL )
			{
				uxListRemove( &( pxTCB->xEventListItem ) );
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
				if( listCURRENT_LIST_LENGTH( &xSuspendedTaskList ) == uxCurrentNumberOfTasks )
				{
					/* No other tasks are ready, so set pxCurrentTCB back to
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

		/* It does not make sense to check if the calling task is suspended. */
		configASSERT( xTask );

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

		/* It does not make sense to resume the calling task. */
		configASSERT( pxTaskToResume );

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
					uxListRemove(  &( pxTCB->xGenericListItem ) );
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
	unsigned portBASE_TYPE uxSavedInterruptStatus;

		configASSERT( pxTaskToResume );

		pxTCB = ( tskTCB * ) pxTaskToResume;

		uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR();
		{
			if( xTaskIsTaskSuspended( pxTCB ) == pdTRUE )
			{
				traceTASK_RESUME_FROM_ISR( pxTCB );

				if( uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE )
				{
					xYieldRequired = ( pxTCB->uxPriority >= pxCurrentTCB->uxPriority );
					uxListRemove(  &( pxTCB->xGenericListItem ) );
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
		}
		portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedInterruptStatus );

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
	#if ( INCLUDE_xTaskGetIdleTaskHandle == 1 )
	{
		/* Create the idle task, storing its handle in xIdleTaskHandle so it can
		be returned by the xTaskGetIdleTaskHandle() function. */
		xReturn = xTaskCreate( prvIdleTask, ( signed char * ) "IDLE", tskIDLE_STACK_SIZE, ( void * ) NULL, ( tskIDLE_PRIORITY | portPRIVILEGE_BIT ), &xIdleTaskHandle );
	}
	#else
	{
		/* Create the idle task without storing its handle. */
		xReturn = xTaskCreate( prvIdleTask, ( signed char * ) "IDLE", tskIDLE_STACK_SIZE, ( void * ) NULL, ( tskIDLE_PRIORITY | portPRIVILEGE_BIT ), NULL );
	}
	#endif

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
		xTickCount = ( portTickType ) 0U;

		/* If configGENERATE_RUN_TIME_STATS is defined then the following
		macro must be defined to configure the timer/counter used to generate
		the run time counter time base. */
		portCONFIGURE_TIMER_FOR_RUN_TIME_STATS();

		/* Setting up the timer tick is hardware specific and thus in the
		portable interface. */
		if( xPortStartScheduler() != pdFALSE )
		{
			/* Should not reach here as if the scheduler is running the
			function will not return. */
		}
		else
		{
			/* Should only reach here if a task calls xTaskEndScheduler(). */
		}
	}

	/* This line will only be reached if the kernel could not be started. */
	configASSERT( xReturn );
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

#if ( configUSE_TICKLESS_IDLE != 0 )

	portTickType prvGetExpectedIdleTime( void )
	{
	portTickType xReturn;
	
		if( pxCurrentTCB->uxPriority > tskIDLE_PRIORITY )
		{
			xReturn = 0;
		}
		else if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > 1 )
		{
			/* There are other idle priority tasks in the ready state.  If
			time slicing is used then the very next tick interrupt must be
			processed. */
			xReturn = 0;
		}
		else
		{
			xReturn = xNextTaskUnblockTime - xTickCount;
		}
	
		return xReturn;
	}

#endif /* configUSE_TICKLESS_IDLE != 0  */
/*----------------------------------------------------------*/

signed portBASE_TYPE xTaskResumeAll( void )
{
register tskTCB *pxTCB;
signed portBASE_TYPE xAlreadyYielded = pdFALSE;

	/* If uxSchedulerSuspended is zero then this function does not match a
	previous call to vTaskSuspendAll(). */
	configASSERT( uxSchedulerSuspended );

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
			if( uxCurrentNumberOfTasks > ( unsigned portBASE_TYPE ) 0U )
			{
				portBASE_TYPE xYieldRequired = pdFALSE;

				/* Move any readied tasks from the pending list into the
				appropriate ready list. */
				while( listLIST_IS_EMPTY( ( xList * ) &xPendingReadyList ) == pdFALSE )
				{
					pxTCB = ( tskTCB * ) listGET_OWNER_OF_HEAD_ENTRY(  ( ( xList * ) &xPendingReadyList ) );
					uxListRemove( &( pxTCB->xEventListItem ) );
					uxListRemove( &( pxTCB->xGenericListItem ) );
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
				if( uxMissedTicks > ( unsigned portBASE_TYPE ) 0U )
				{
					while( uxMissedTicks > ( unsigned portBASE_TYPE ) 0U )
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
portTickType xReturn;
unsigned portBASE_TYPE uxSavedInterruptStatus;

	uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR();
	xReturn = xTickCount;
	portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedInterruptStatus );

	return xReturn;
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE uxTaskGetNumberOfTasks( void )
{
	/* A critical section is not required because the variables are of type
	portBASE_TYPE. */
	return uxCurrentNumberOfTasks;
}
/*-----------------------------------------------------------*/

#if ( INCLUDE_pcTaskGetTaskName == 1 )

	signed char *pcTaskGetTaskName( xTaskHandle xTaskToQuery )
	{
	tskTCB *pxTCB;

		/* If null is passed in here then the name of the calling task is being queried. */
		pxTCB = prvGetTCBFromHandle( xTaskToQuery );
		configASSERT( pxTCB );
		return &( pxTCB->pcTaskName[ 0 ] );
	}

#endif
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

				if( listLIST_IS_EMPTY( &( pxReadyTasksLists[ uxQueue ] ) ) == pdFALSE )
				{
					prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) &( pxReadyTasksLists[ uxQueue ] ), tskREADY_CHAR );
				}
			}while( uxQueue > ( unsigned short ) tskIDLE_PRIORITY );

			if( listLIST_IS_EMPTY( pxDelayedTaskList ) == pdFALSE )
			{
				prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) pxDelayedTaskList, tskBLOCKED_CHAR );
			}

			if( listLIST_IS_EMPTY( pxOverflowDelayedTaskList ) == pdFALSE )
			{
				prvListTaskWithinSingleList( pcWriteBuffer, ( xList * ) pxOverflowDelayedTaskList, tskBLOCKED_CHAR );
			}

			#if( INCLUDE_vTaskDelete == 1 )
			{
				if( listLIST_IS_EMPTY( &xTasksWaitingTermination ) == pdFALSE )
				{
					prvListTaskWithinSingleList( pcWriteBuffer, &xTasksWaitingTermination, tskDELETED_CHAR );
				}
			}
			#endif

			#if ( INCLUDE_vTaskSuspend == 1 )
			{
				if( listLIST_IS_EMPTY( &xSuspendedTaskList ) == pdFALSE )
				{
					prvListTaskWithinSingleList( pcWriteBuffer, &xSuspendedTaskList, tskSUSPENDED_CHAR );
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

				if( listLIST_IS_EMPTY( &( pxReadyTasksLists[ uxQueue ] ) ) == pdFALSE )
				{
					prvGenerateRunTimeStatsForTasksInList( pcWriteBuffer, ( xList * ) &( pxReadyTasksLists[ uxQueue ] ), ulTotalRunTime );
				}
			}while( uxQueue > ( unsigned short ) tskIDLE_PRIORITY );

			if( listLIST_IS_EMPTY( pxDelayedTaskList ) == pdFALSE )
			{
				prvGenerateRunTimeStatsForTasksInList( pcWriteBuffer, ( xList * ) pxDelayedTaskList, ulTotalRunTime );
			}

			if( listLIST_IS_EMPTY( pxOverflowDelayedTaskList ) == pdFALSE )
			{
				prvGenerateRunTimeStatsForTasksInList( pcWriteBuffer, ( xList * ) pxOverflowDelayedTaskList, ulTotalRunTime );
			}

			#if ( INCLUDE_vTaskDelete == 1 )
			{
				if( listLIST_IS_EMPTY( &xTasksWaitingTermination ) == pdFALSE )
				{
					prvGenerateRunTimeStatsForTasksInList( pcWriteBuffer, &xTasksWaitingTermination, ulTotalRunTime );
				}
			}
			#endif

			#if ( INCLUDE_vTaskSuspend == 1 )
			{
				if( listLIST_IS_EMPTY( &xSuspendedTaskList ) == pdFALSE )
				{
					prvGenerateRunTimeStatsForTasksInList( pcWriteBuffer, &xSuspendedTaskList, ulTotalRunTime );
				}
			}
			#endif
		}
		xTaskResumeAll();
	}

#endif
/*----------------------------------------------------------*/

#if ( INCLUDE_xTaskGetIdleTaskHandle == 1 )

	xTaskHandle xTaskGetIdleTaskHandle( void )
	{
		/* If xTaskGetIdleTaskHandle() is called before the scheduler has been
		started, then xIdleTaskHandle will be NULL. */
		configASSERT( ( xIdleTaskHandle != NULL ) );
		return xIdleTaskHandle;
	}

#endif
/*----------------------------------------------------------*/

/* This conditional compilation should use inequality to 0, not equality to 1.
This is to ensure vTaskStepTick() is available when user defined low power mode	
implementations require configUSE_TICKLESS_IDLE to be set to a value other than
1. */
#if ( configUSE_TICKLESS_IDLE != 0 )

	void vTaskStepTick( portTickType xTicksToJump )
	{
		configASSERT( xTicksToJump <= xNextTaskUnblockTime );
		xTickCount += xTicksToJump;
	}

#endif

/*-----------------------------------------------------------
 * SCHEDULER INTERNALS AVAILABLE FOR PORTING PURPOSES
 * documented in task.h
 *----------------------------------------------------------*/

void vTaskIncrementTick( void )
{
tskTCB * pxTCB;

	/* Called by the portable layer each time a tick interrupt occurs.
	Increments the tick then checks to see if the new tick value will cause any
	tasks to be unblocked. */
	traceTASK_INCREMENT_TICK( xTickCount );
	if( uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE )
	{
		++xTickCount;
		if( xTickCount == ( portTickType ) 0U )
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
				/* The new current delayed list is empty.  Set
				xNextTaskUnblockTime to the maximum possible value so it is
				extremely unlikely that the
				if( xTickCount >= xNextTaskUnblockTime ) test will pass until
				there is an item in the delayed list. */
				xNextTaskUnblockTime = portMAX_DELAY;
			}
			else
			{
				/* The new current delayed list is not empty, get the value of
				the item at the head of the delayed list.  This is the time at
				which the task at the head of the delayed list should be removed
				from the Blocked state. */
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
			vApplicationTickHook();
		}
		#endif
	}

	#if ( configUSE_TICK_HOOK == 1 )
	{
		/* Guard against the tick hook being called when the missed tick
		count is being unwound (when the scheduler is being unlocked. */
		if( uxMissedTicks == ( unsigned portBASE_TYPE ) 0U )
		{
			vApplicationTickHook();
		}
	}
	#endif
}
/*-----------------------------------------------------------*/

#if ( configUSE_APPLICATION_TASK_TAG == 1 )

	void vTaskSetApplicationTaskTag( xTaskHandle xTask, pdTASK_HOOK_CODE pxHookFunction )
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
			xTCB->pxTaskTag = pxHookFunction;
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

		taskSELECT_HIGHEST_PRIORITY_TASK();

		traceTASK_SWITCHED_IN();
	}
}
/*-----------------------------------------------------------*/

void vTaskPlaceOnEventList( const xList * const pxEventList, portTickType xTicksToWait )
{
portTickType xTimeToWake;

	configASSERT( pxEventList );

	/* THIS FUNCTION MUST BE CALLED WITH INTERRUPTS DISABLED OR THE
	SCHEDULER SUSPENDED. */

	/* Place the event list item of the TCB in the appropriate event list.
	This is placed in the list in priority order so the highest priority task
	is the first to be woken by the event. */
	vListInsert( ( xList * ) pxEventList, ( xListItem * ) &( pxCurrentTCB->xEventListItem ) );

	/* We must remove ourselves from the ready list before adding ourselves
	to the blocked list as the same list item is used for both lists.  We have
	exclusive access to the ready lists as the scheduler is locked. */
	if( uxListRemove( ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) ) == 0 )
	{
		/* The current task must be in a ready list, so there is no need to
		check, and the port reset macro can be called directly. */
		portRESET_READY_PRIORITY( pxCurrentTCB->uxPriority, uxTopReadyPriority );
	}

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

		configASSERT( pxEventList );

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
		if( uxListRemove( ( xListItem * ) &( pxCurrentTCB->xGenericListItem ) ) == 0 )
		{
			/* The current task must be in a ready list, so there is no need to
			check, and the port reset macro can be called directly. */
			portRESET_READY_PRIORITY( pxCurrentTCB->uxPriority, uxTopReadyPriority );
		}

		/* Calculate the time at which the task should be woken if the event does
		not occur.  This may overflow but this doesn't matter. */
		xTimeToWake = xTickCount + xTicksToWait;
		
		traceTASK_DELAY_UNTIL();
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
	configASSERT( pxUnblockedTCB );
	uxListRemove( &( pxUnblockedTCB->xEventListItem ) );

	if( uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE )
	{
		uxListRemove( &( pxUnblockedTCB->xGenericListItem ) );
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
	configASSERT( pxTimeOut );
	pxTimeOut->xOverflowCount = xNumOfOverflows;
	pxTimeOut->xTimeOnEntering = xTickCount;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xTaskCheckForTimeOut( xTimeOutType * const pxTimeOut, portTickType * const pxTicksToWait )
{
portBASE_TYPE xReturn;

	configASSERT( pxTimeOut );
	configASSERT( pxTicksToWait );

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
/*-----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )
	unsigned portBASE_TYPE uxTaskGetTaskNumber( xTaskHandle xTask )
	{
	unsigned portBASE_TYPE uxReturn;
	tskTCB *pxTCB;

		if( xTask != NULL )
		{
			pxTCB = ( tskTCB * ) xTask;
			uxReturn = pxTCB->uxTaskNumber;
		}
		else
		{
			uxReturn = 0U;
		}

		return uxReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )
	void vTaskSetTaskNumber( xTaskHandle xTask, unsigned portBASE_TYPE uxHandle )
	{
	tskTCB *pxTCB;

		if( xTask != NULL )
		{
			pxTCB = ( tskTCB * ) xTask;
			pxTCB->uxTaskNumber = uxHandle;
		}
	}
#endif


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

		/* This conditional compilation should use inequality to 0, not equality
		to 1.  This is to ensure portSUPPRESS_TICKS_AND_SLEEP() is called when
		user defined low power mode	implementations require
		configUSE_TICKLESS_IDLE to be set to a value other than 1. */
		#if ( configUSE_TICKLESS_IDLE != 0 )
		{
		portTickType xExpectedIdleTime;
		/* If the expected idle time is 1 then the idle time would end at
		the end of the current time slice.  The idle time must be at least
		2 to ensure any pended ticks between this point and the tick being
		stopped can be legitimately stepped over when the tick suppression
		routines returns. */
		const portTickType xMinimumExpectedIdleTime = ( portTickType ) 2;

			/* It is not desirable to suspend then resume the scheduler on
			each iteration of the idle task.  Therefore, a preliminary
			test of the expected idle time is performed without the
			scheduler suspended.  The result here is not necessarily
			valid. */
			xExpectedIdleTime = prvGetExpectedIdleTime();

			if( xExpectedIdleTime >= xMinimumExpectedIdleTime )
			{
				vTaskSuspendAll();
				{
					/* Now the scheduler is suspended, the expected idle
					time can be sampled again, and this time its value can
					be used. */
					configASSERT( xNextTaskUnblockTime >= xTickCount );
					xExpectedIdleTime = prvGetExpectedIdleTime();

					if( xExpectedIdleTime >= xMinimumExpectedIdleTime )
					{
						portSUPPRESS_TICKS_AND_SLEEP( xExpectedIdleTime );
					}
				}
				xTaskResumeAll();
			}
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
		pxTCB->uxCriticalNesting = ( unsigned portBASE_TYPE ) 0U;
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
		while( uxTasksDeleted > ( unsigned portBASE_TYPE ) 0U )
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
					uxListRemove( &( pxTCB->xGenericListItem ) );
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
		list of blocked tasks then xNextTaskUnblockTime needs to be updated
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
			memset( pxNewTCB->pxStack, ( int ) tskSTACK_FILL_BYTE, ( size_t ) usStackDepth * sizeof( portSTACK_TYPE ) );
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
	PRIVILEGED_DATA static char pcStatusString[ configMAX_TASK_NAME_LEN + 30 ];

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

			sprintf( pcStatusString, ( char * ) "%s\t\t%c\t%u\t%u\t%u\r\n", pxNextTCB->pcTaskName, cStatus, ( unsigned int ) pxNextTCB->uxPriority, ( unsigned int ) usStackRemaining, ( unsigned int ) pxNextTCB->uxTCBNumber );
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
				if( pxNextTCB->ulRunTimeCounter == 0UL )
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
	register unsigned short usCount = 0U;

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

#if ( INCLUDE_vTaskDelete == 1 )

	static void prvDeleteTCB( tskTCB *pxTCB )
	{
		/* This call is required specifically for the TriCore port.  It must be
		above the vPortFree() calls.  The call is also used by ports/demos that
		want to allocate and clean RAM statically. */
		portCLEAN_UP_TCB( pxTCB );

		/* Free up the memory allocated by the scheduler for the task.  It is up to
		the task to free any memory allocated at the application level. */
		vPortFreeAligned( pxTCB->pxStack );
		vPortFree( pxTCB );
	}

#endif


/*-----------------------------------------------------------*/

#if ( ( INCLUDE_xTaskGetCurrentTaskHandle == 1 ) || ( configUSE_MUTEXES == 1 ) )

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

#if ( ( INCLUDE_xTaskGetSchedulerState == 1 ) || ( configUSE_TIMERS == 1 ) )

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

		/* If the mutex was given back by an interrupt while the queue was
		locked then the mutex holder might now be NULL. */
		if( pxMutexHolder != NULL )
		{
			if( pxTCB->uxPriority < pxCurrentTCB->uxPriority )
			{
				/* Adjust the mutex holder state to account for its new priority. */
				listSET_LIST_ITEM_VALUE( &( pxTCB->xEventListItem ), configMAX_PRIORITIES - ( portTickType ) pxCurrentTCB->uxPriority );

				/* If the task being modified is in the ready state it will need to
				be moved into a new list. */
				if( listIS_CONTAINED_WITHIN( &( pxReadyTasksLists[ pxTCB->uxPriority ] ), &( pxTCB->xGenericListItem ) ) != pdFALSE )
				{
					if( uxListRemove( ( xListItem * ) &( pxTCB->xGenericListItem ) ) == 0 )
					{
						taskRESET_READY_PRIORITY( pxTCB->uxPriority );
					}

					/* Inherit the priority before being moved into the new list. */
					pxTCB->uxPriority = pxCurrentTCB->uxPriority;
					prvAddTaskToReadyQueue( pxTCB );
				}
				else
				{
					/* Just inherit the priority. */
					pxTCB->uxPriority = pxCurrentTCB->uxPriority;
				}

				traceTASK_PRIORITY_INHERIT( pxTCB, pxCurrentTCB->uxPriority );
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
				if( uxListRemove( ( xListItem * ) &( pxTCB->xGenericListItem ) ) == 0 )
				{
					taskRESET_READY_PRIORITY( pxTCB->uxPriority );
				}

				/* Disinherit the priority before adding the task into the new
				ready list. */
				traceTASK_PRIORITY_DISINHERIT( pxTCB, pxTCB->uxBasePriority );
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
			if( pxCurrentTCB->uxCriticalNesting > 0U )
			{
				( pxCurrentTCB->uxCriticalNesting )--;

				if( pxCurrentTCB->uxCriticalNesting == 0U )
				{
					portENABLE_INTERRUPTS();
				}
			}
		}
	}

#endif
/*-----------------------------------------------------------*/




