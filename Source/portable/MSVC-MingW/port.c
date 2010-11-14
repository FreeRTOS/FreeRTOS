/*
    FreeRTOS V6.1.0 - Copyright (C) 2010 Real Time Engineers Ltd.

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

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include <stdio.h>





typedef struct xTaskControlBlock
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

} xTCB;









FILE *pfTraceFile = NULL;
//#define vPortTrace( x ) if( pfTraceFile == NULL ) pfTraceFile = fopen( "c:/temp/trace.txt", "w" ); if( pfTraceFile != NULL ) fprintf( pfTraceFile, x )
#define vPortTrace( x ) ( void ) x

#define portMAX_INTERRUPTS				( ( unsigned long ) sizeof( unsigned long ) * 8UL ) /* The number of bits in an unsigned long. */
#define portNO_CRITICAL_NESTING 		( ( unsigned long ) 0 )

/*
 * Created as a high priority thread, this function uses a timer to simulate
 * a tick interrupt being generated on an embedded target.  In this Windows
 * environment the timer does not achieve real time performance though.
 */
static DWORD WINAPI prvSimulatedPeripheralTimer( LPVOID lpParameter );

/* 
 * Process all the simulated interrupts - each represented by a bit in 
 * ulPendingInterrupts variable.
 */
static void prvProcessEvents( void );

/*-----------------------------------------------------------*/

/* The WIN32 simulator runs each task in a thread.  The context switching is
managed by the threads, so the task stack does not have to be managed directly,
although the task stack is still used to hold an xThreadState structure this is
the only thing it will ever hold.  The structure indirectly maps the task handle 
to a thread handle. */
typedef struct
{
	portSTACK_TYPE ulCriticalNesting;	/* Critical nesting count of the task. */
	void * pvThread;					/* Handle of the thread that executes the task. */
} xThreadState;

/* The parameters passed to a thread when it is created. */
typedef struct XPARAMS
{
	pdTASK_CODE pxCode;		/* The entry point of the task (rather than thread) code. */
	void *pvParameters;		/* The parameters that are passed to the task (rather than thread. */
} xParams;

/* Pseudo interrupts waiting to be processed.  This is a bit mask where each
bit represents one interrupt, so a maximum of 32 interrupts can be simulated. */
static volatile unsigned long ulPendingInterrupts = 0UL;

/* An event used to inform the interrupt dispatch thread (a high priority thread
that simulated interrupt processing) that an IRQ or SWI type interrupt is
pending. */
static void *pvInterruptEvent = NULL;

/* Mutex used to protect all the pseudo interrupt variables that are accessed by
multiple threads. */
static void *pvInterruptEventMutex = NULL;

/* The main thread, which also acts as the pseudo interrupt handler. */
static void *pvMainThreadAndInterrupHandler;

/* Events used to manage sequencing. */
static void *pvTickAcknowledgeEvent = NULL, *pvInterruptAcknowledgeEvent = NULL;

/* The critical nesting count for the currently executing task.  This is 
initialised to a non-zero value so interrupts do not become enabled during 
the initialisation phase.  As each task has its own critical nesting value 
ulCriticalNesting will get set to zero when the first task runs.  This 
initialisation is probably not critical in this simulated environment as the
pseudo interrupt handlers/dispatchers do not get created until the FreeRTOS
scheduler is started. */
static unsigned portLONG ulCriticalNesting = 9999UL;

/* Handlers for all the simulated software interrupts.  The first two positions
are used for the Yield and Tick interrupts so are handled slightly differently,
all the other interrupts can be user defined. */
static void (*vIsrHandler[ portMAX_INTERRUPTS ])( void ) = { 0 };

/* Pointer to the TCB of the currently executing task. */
extern void *pxCurrentTCB;

/*-----------------------------------------------------------*/

static DWORD WINAPI prvSimulatedPeripheralTimer( LPVOID lpParameter )
{
void *pvTimer;
LARGE_INTEGER liDueTime;
void *pvObjectList[ 2 ];
const long long ll_ms_In_100ns_units = ( long long ) -1000;
extern volatile unsigned long ulTicks;

	/* Just to prevent compiler warnings. */
	( void ) lpParameter;

	/* The timer is created as a one shot timer even though we want it to repeat
	at a given frequency.  This is because Windows is not a real time environment,
	and attempting to set a high frequency periodic timer will result in event
	overruns.  Therefore the timer is just reset after each time the pseudo 
	interrupt handler has processed each tick event. */
	pvTimer = CreateWaitableTimer( NULL, TRUE, NULL );
	
	liDueTime.QuadPart = ( long long ) portTICK_RATE_MS * ll_ms_In_100ns_units;

	/* Block on the timer itself and the event mutex that grants access to the 
	interrupt variables. */
	pvObjectList[ 0 ] = pvInterruptEventMutex;
	pvObjectList[ 1 ] = pvTimer;

	for(;;)
	{
		ulTicks++;

		/* The timer is reset on each itteration of this loop rather than being set
		to function periodicallys - this is for the reasons stated in the comments
		where the timer is created. */
		vPortTrace( "prvSimulatedPeripheralTimer: Tick acked, setting new tick timer\r\n" );
		SetWaitableTimer( pvTimer, &liDueTime, 0, NULL, NULL, TRUE );

		/* Wait until the timer expires and we can access the pseudo interrupt 
		variables. */
		//WaitForMultipleObjects( ( sizeof( pvObjectList ) / sizeof( void * ) ), pvObjectList, TRUE, INFINITE );
		WaitForSingleObject( pvTimer, INFINITE );
		vPortTrace( "prvSimulatedPeripheralTimer: Timer signalled, waiting interrupt event mutex\r\n" );
		WaitForSingleObject( pvInterruptEventMutex, INFINITE );
		vPortTrace( "prvSimulatedPeripheralTimer: Got interrupt event mutex\r\n" );
		
		/* The timer has expired, generate the simulated tick event. */
		ulPendingInterrupts |= ( 1 << portINTERRUPT_TICK );
		if( pvInterruptEvent != NULL )
		{
			vPortTrace( "prvSimulatedPeripheralTimer: Setting interrupt event to signal tick\r\n" );
			SetEvent( pvInterruptEvent );
		}

		/* Give back the mutex so the pseudo interrupt handler unblocks and can
		access the interrupt handler variables.  This high priority task will then
		loop back round to wait for the lower priority psuedo interrupt handler 
		thread to acknowledge the tick. */
		if( pvInterruptEventMutex != NULL )
		{
			vPortTrace( "prvSimulatedPeripheralTimer: Releasing interrupt event mutex so tick can be processed\r\n" );
			ReleaseMutex( pvInterruptEventMutex );
		}

		/* Wait for the previous tick to be acknowledged before resetting the timer.
		As mentioned above this is done to prevent timer overruns in the non real-
		time environment.  THIS IS NOT HOW A REAL PORT SHOULD USE TIMERS! */
		WaitForSingleObject( pvTickAcknowledgeEvent, INFINITE );
	}
}
/*-----------------------------------------------------------*/

portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
xThreadState *pxThreadState = NULL;
xParams *pxThreadParams = ( void * ) pvPortMalloc( sizeof( xParams ) );

	if( pxThreadParams != NULL )
	{
		/* In this simulated case a stack is not initialised, but instead a thread
		is created that will execute the task being created.  The thread handles
		the context switching itself.  The xThreadState object is placed onto
		the stack that was created for the task - so the stack buffer is still
		used, just not in the conventional way.  It will not be used for anything
		other than holding this structure. */
		pxThreadState = ( xThreadState * ) ( pxTopOfStack - sizeof( xThreadState ) );

		/* The parameters that are passed into the thread so it knows how to
		start the task executing. */
		pxThreadParams->pxCode = pxCode;
		pxThreadParams->pvParameters = pvParameters;

		/* Create the thread itself. */
		//pxThreadState->pvThread = ( void * ) CreateThread( NULL, 0, ( LPTHREAD_START_ROUTINE ) prvThreadEntryPoint, pxThreadParams, CREATE_SUSPENDED, NULL );
		pxThreadState->pvThread = ( void * ) CreateThread( NULL, 0, ( LPTHREAD_START_ROUTINE ) pxCode, pvParameters, CREATE_SUSPENDED, NULL );
		pxThreadState->ulCriticalNesting = portNO_CRITICAL_NESTING;
		SetThreadPriority( pxThreadState->pvThread, THREAD_PRIORITY_IDLE );
	}
	
	return ( portSTACK_TYPE * ) pxThreadState;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
void *pvHandle;
long lSuccess = pdPASS;
xThreadState *pxThreadState;

	/* Set the priority of this thread such that it is above the priority of the
	threads that run tasks, but below the priority of the thread that generates
	the pseudo tick interrupts.  This priority is chosen because this is the
	thread that actually handles the psuedo interrupts. */
	pvHandle = GetCurrentThread();
	if( pvHandle == NULL )
	{
		lSuccess = pdFAIL;
	}
	
	if( lSuccess == pdPASS )
	{
		if( SetThreadPriority( pvHandle, THREAD_PRIORITY_BELOW_NORMAL ) == 0 )
		{
			lSuccess = pdFAIL;
		}
	}

	if( lSuccess == pdPASS )
	{
		/* Create the events and mutexes that are used to synchronise all the
		threads. */
		pvInterruptEventMutex = CreateMutex( NULL, FALSE, NULL );
		pvInterruptEvent = CreateEvent( NULL, FALSE, FALSE, NULL );
		pvTickAcknowledgeEvent = CreateEvent( NULL, FALSE, FALSE, NULL );
		pvInterruptAcknowledgeEvent = CreateEvent( NULL, FALSE, FALSE, NULL );

		/* Start the thread that simulates the timer peripheral to generate
		tick interrupts. */
		pvHandle = CreateThread( NULL, 0, prvSimulatedPeripheralTimer, NULL, 0, NULL );
		if( pvHandle != NULL )
		{
			SetThreadPriority( pvHandle, THREAD_PRIORITY_ABOVE_NORMAL );
		}
		
		/* Start the highest priority task by obtaining its associated thread state
		structure, in which is stored the thread handle. */
		pxThreadState = ( xThreadState * ) *( ( unsigned long * ) pxCurrentTCB );
		ulCriticalNesting = portNO_CRITICAL_NESTING;

		vPortTrace( "Created system threads, starting task" );

		ResumeThread( pxThreadState->pvThread );
	}	
	
	/* Handle all pseudo interrupts - including yield requests and simulated ticks. */
	prvProcessEvents();

	/* Would not expect to return from prvProcessEvents(), so should not get here. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvProcessEvents( void )
{
long lSwitchRequired, lAcknowledgeTick, lAcknowledgeInterrupt;
xThreadState *pxThreadState;
void *pvObjectList[ 2 ];
unsigned long i;
char cTraceBuffer[ 256 ];

	vPortTrace( "Entering prvProcessEvents\r\n" );

	/* Going to block on the mutex that ensured exclusive access to the pdeudo 
	interrupt objects, and the event that signals that an interrupt is waiting
	to be processed. */
	pvObjectList[ 0 ] = pvInterruptEventMutex;
	pvObjectList[ 1 ] = pvInterruptEvent;

	for(;;)
	{
		vPortTrace( "prvProcessEvents: Waiting for next interrupt event\r\n" );
		WaitForMultipleObjects( sizeof( pvObjectList ) / sizeof( void * ), pvObjectList, TRUE, INFINITE );
		vPortTrace( "prvProcessEvents: Got interrupt event and mutex\r\n" );
		//vPortTrace( "prvProcessEvents: Waiting for next interrupt event\r\n" );
		//WaitForSingleObject( pvInterruptEvent, INFINITE );
		//vPortTrace( "prvProcessEvents: Waiting interrupt event mutex to access interrupt data\r\n" );
		//WaitForSingleObject( pvInterruptEventMutex, INFINITE );

		lSwitchRequired = pdFALSE;
		lAcknowledgeTick = pdFALSE;
		lAcknowledgeInterrupt = pdFALSE;

		/* For each interrupt we are interested in processing, each of which is 
		represented by a bit in the 32bit ulPendingInterrupts variable. */
		for( i = 0; i < portMAX_INTERRUPTS; i++ )
		{
			/* Is the pseudo interrupt pending? */
			if( ulPendingInterrupts & ( 1UL << i ) )
			{
				switch( i )
				{
					case portINTERRUPT_YIELD:

						vPortTrace( "prvProcessEvents: Processing Yield\r\n" );
						/* Yield interrupts occur no matter what the critical nesting count. */
						lSwitchRequired = pdTRUE;

						/* Clear the interrupt pending bit. */
						ulPendingInterrupts &= ~( 1UL << portINTERRUPT_YIELD );

						lAcknowledgeInterrupt = pdTRUE;
						break;

					case portINTERRUPT_TICK:
					
						/* Tick interrupts should only be processed if the critical nesting count
						is zero.  The critical nesting count represents the interrupt mask on 
						real target hardware. */
						vPortTrace( "prvProcessEvents: Processing tick event\r\n" );
						if( ulCriticalNesting == 0 )
						{
							/* Process the tick itself. */
							vPortTrace( "prvProcessEvents: Incrementing tick\r\n" );
							vTaskIncrementTick();
							#if( configUSE_PREEMPTION != 0 )
							{
								/* A context switch is only automatically performed from the tick
								interrupt if the pre-emptive scheduler is being used. */
								lSwitchRequired = pdTRUE;
							}
							#endif
							
							lAcknowledgeTick = pdTRUE;

							/* Clear the interrupt pending bit. */
							ulPendingInterrupts &= ~( 1UL << portINTERRUPT_TICK );
						}
						break;

					default:

						/* Is a handler installed? */
						if( vIsrHandler[ i ] != NULL )
						{
							lSwitchRequired = pdTRUE;

							/* Run the actual handler. */
							vIsrHandler[ i ]();

							/* Clear the interrupt pending bit. */
							ulPendingInterrupts &= ~( 1UL << i );

							lAcknowledgeInterrupt = pdTRUE;
						}
						break;
				}
			}
		}

		if( lSwitchRequired != pdFALSE )
		{
			void *pvOldCurrentTCB;

			pvOldCurrentTCB = pxCurrentTCB;

			/* Save the state of the current thread before suspending it. */
			pxThreadState = ( xThreadState *) *( ( unsigned long * ) pxCurrentTCB );
			pxThreadState->ulCriticalNesting = ulCriticalNesting ;
			
			/* Select the next task to run. */
			vTaskSwitchContext();
			
			/* If the task selected to enter the running state is not the task
			that is already in the running state. */
			if( pvOldCurrentTCB != pxCurrentTCB )
			{
				/* Suspend the old thread. */
				SuspendThread( pxThreadState->pvThread );
				sprintf( cTraceBuffer, "Event processor: suspending %s, resuming %s\r\n", ((xTCB*)pvOldCurrentTCB)->pcTaskName, ((xTCB*)pxCurrentTCB)->pcTaskName );
				vPortTrace( cTraceBuffer );

				/* Obtain the state of the task now selected to enter the Running state. */
				pxThreadState = ( xThreadState * ) ( *( unsigned long *) pxCurrentTCB );
				ulCriticalNesting = pxThreadState->ulCriticalNesting;
				ResumeThread( pxThreadState->pvThread );
			}
		}

		/* Was a tick processed? */
		if( lAcknowledgeTick != pdFALSE )
		{
			vPortTrace( "prvProcessEvents: Acking tick\r\n" );
			SetEvent( pvTickAcknowledgeEvent );
		}

		if( lAcknowledgeInterrupt != pdFALSE )
		{
			vPortTrace( "prvProcessEvents: Acking interrupt\r\n" );
			SetEvent( pvInterruptAcknowledgeEvent );
		}

		ReleaseMutex( pvInterruptEventMutex );
	}
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
}
/*-----------------------------------------------------------*/

void vPortGeneratePseudoInterrupt( unsigned long ulInterruptNumber )
{
	if( ( ulInterruptNumber < portMAX_INTERRUPTS ) && ( pvInterruptEventMutex != NULL ) )
	{
		/* Yield interrupts are processed even when critical nesting is non-zero. */
		if( ( ulCriticalNesting == 0 ) || ( ulInterruptNumber == portINTERRUPT_YIELD ) )
		{
			/* In case this task has just started running, reset the interrupt
			acknowledge event as it might have been set due to the activities
			of a thread that has already been executed and suspended. */
			ResetEvent( pvInterruptAcknowledgeEvent );

			WaitForSingleObject( pvInterruptEventMutex, INFINITE );
			ulPendingInterrupts |= ( 1 << ulInterruptNumber );
			vPortTrace( "vPortGeneratePseudoInterrupt: Got interrupt mutex, about to signal interrupt event\r\n" );
			SetEvent( pvInterruptEvent );
			vPortTrace( "vPortGeneratePseudoInterrupt: About to release interrupt event mutex\r\n" );
			ReleaseMutex( pvInterruptEventMutex );
			vPortTrace( "vPortGeneratePseudoInterrupt: Interrupt event mutex released, going to wait for next interrupt input\r\n" );

			WaitForSingleObject( pvInterruptAcknowledgeEvent, INFINITE );
			vPortTrace( "vPortGeneratePseudoInterrupt: Interrupt acknowledged, leaving vPortGeneratePseudoInterrupt()\r\n" );
		}
	}
}
/*-----------------------------------------------------------*/

void vPortSetInterruptHandler( unsigned long ulInterruptNumber, void (*pvHandler)( void ) )
{
	if( ulInterruptNumber < portMAX_INTERRUPTS )
	{
		if( pvInterruptEventMutex != NULL )
		{
			WaitForSingleObject( pvInterruptEventMutex, INFINITE );
			vIsrHandler[ ulInterruptNumber ] = pvHandler;
			ReleaseMutex( pvInterruptEventMutex );
		}
		else
		{
			vIsrHandler[ ulInterruptNumber ] = pvHandler;
		}
	}
}
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
	ulCriticalNesting++;
}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
	if( ulCriticalNesting > portNO_CRITICAL_NESTING )
	{
		ulCriticalNesting--;

		if( ulCriticalNesting == 0 )
		{
			/* Were any interrupts set to pending while interrupts were 
			(pseudo) disabled? */
			if( ulPendingInterrupts != 0UL )
			{
				WaitForSingleObject( pvInterruptEventMutex, INFINITE );
				vPortTrace( "vPortExitCritical:  Setting interrupt event\r\n" );
				SetEvent( pvInterruptEvent );
				ReleaseMutex( pvInterruptEventMutex );

				vPortTrace( "vPortExitCritical:  Waiting interrupt ack\r\n" );
				WaitForSingleObject( pvInterruptAcknowledgeEvent, INFINITE );
				vPortTrace( "vPortExitCritical: Interrupt acknowledged, leaving critical section code\r\n" );

				/* Just in case the Yield does not happen immediately.  This
				line could be dangerious if not all interrupts are being
				processed. */
//				while( ulPendingInterrupts != 0UL );
			}
		}
	}
}
