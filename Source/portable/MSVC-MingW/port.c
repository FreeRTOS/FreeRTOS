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

#define portMAX_INTERRUPTS				( ( unsigned long ) sizeof( unsigned long ) * 8UL ) /* The number of bits in an unsigned long. */
#define portNO_CRITICAL_NESTING 		( ( unsigned long ) 0 )

/*
 * Created as a high priority thread, this function uses a timer to simulate
 * a tick interrupt being generated on an embedded target.  In this Windows
 * environment the timer does not achieve anything approaching real time 
 * performance though.
 */
static DWORD WINAPI prvSimulatedPeripheralTimer( LPVOID lpParameter );

/* 
 * Process all the simulated interrupts - each represented by a bit in 
 * ulPendingInterrupts variable.
 */
static void prvProcessPseudoInterrupts( void );

/*-----------------------------------------------------------*/

/* The WIN32 simulator runs each task in a thread.  The context switching is
managed by the threads, so the task stack does not have to be managed directly,
although the task stack is still used to hold an xThreadState structure this is
the only thing it will ever hold.  The structure indirectly maps the task handle 
to a thread handle. */
typedef struct
{
	/* Set to true if the task run by the thread yielded control to the pseudo
	interrupt handler manually - either by yielding or when exiting a critical
	section while pseudo interrupts were pending. */
	long lWaitingInterruptAck;			

	/* Handle of the thread that executes the task. */
	void * pvThread;					
} xThreadState;

/* Pseudo interrupts waiting to be processed.  This is a bit mask where each
bit represents one interrupt, so a maximum of 32 interrupts can be simulated. */
static volatile unsigned long ulPendingInterrupts = 0UL;

/* An event used to inform the pseudo interrupt processing thread (a high 
priority thread that simulated interrupt processing) that an interrupt is
pending. */
static void *pvInterruptEvent = NULL;

/* Mutex used to protect all the pseudo interrupt variables that are accessed 
by multiple threads. */
static void *pvInterruptEventMutex = NULL;

/* Events used to manage sequencing. */
static void *pvTickAcknowledgeEvent = NULL, *pvInterruptAcknowledgeEvent = NULL;

/* The critical nesting count for the currently executing task.  This is 
initialised to a non-zero value so interrupts do not become enabled during 
the initialisation phase.  As each task has its own critical nesting value 
ulCriticalNesting will get set to zero when the first task runs.  This 
initialisation is probably not critical in this simulated environment as the
pseudo interrupt handlers do not get created until the FreeRTOS scheduler is 
started anyway. */
static unsigned long ulCriticalNesting = 9999UL;

/* Handlers for all the simulated software interrupts.  The first two positions
are used for the Yield and Tick interrupts so are handled slightly differently,
all the other interrupts can be user defined. */
static void (*vIsrHandler[ portMAX_INTERRUPTS ])( void ) = { 0 };

/* Pointer to the TCB of the currently executing task. */
extern void *pxCurrentTCB;

/*-----------------------------------------------------------*/

static DWORD WINAPI prvSimulatedPeripheralTimer( LPVOID lpParameter )
{
	/* Just to prevent compiler warnings. */
	( void ) lpParameter;

	for(;;)
	{
		/* Wait until the timer expires and we can access the pseudo interrupt 
		variables.  *NOTE* this is not a 'real time' way of generating tick 
		events as the next wake time should be relative to the previous wake 
		time, not the time that Sleep() is called.  It is done this way to 
		prevent overruns in this very non real time simulated/emulated 
		environment. */
		Sleep( portTICK_RATE_MS );

		WaitForSingleObject( pvInterruptEventMutex, INFINITE );

		/* A thread will hold the interrupt event mutex while in a critical
		section, so ulCriticalSection should be zero for this tick event to be
		possible. */
		if( ulCriticalNesting != 0 )
		{
			/* For a break point only. */
			__asm{ NOP };
		}

		/* The timer has expired, generate the simulated tick event. */
		ulPendingInterrupts |= ( 1 << portINTERRUPT_TICK );

		/* The interrupt is now pending - notify the simulated interrupt 
		handler thread. */
		SetEvent( pvInterruptEvent );

		/* Give back the mutex so the pseudo interrupt handler unblocks 
		and can	access the interrupt handler variables.  This high priority
		task will then loop back round after waiting for the lower priority 
		pseudo interrupt handler thread to acknowledge the tick. */
		SignalObjectAndWait( pvInterruptEventMutex, pvTickAcknowledgeEvent, INFINITE, FALSE );
	}
}
/*-----------------------------------------------------------*/

portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
xThreadState *pxThreadState = NULL;

	/* In this simulated case a stack is not initialised, but instead a thread
	is created that will execute the task being created.  The thread handles
	the context switching itself.  The xThreadState object is placed onto
	the stack that was created for the task - so the stack buffer is still
	used, just not in the conventional way.  It will not be used for anything
	other than holding this structure. */
	pxThreadState = ( xThreadState * ) ( pxTopOfStack - sizeof( xThreadState ) );

	/* Create the thread itself. */
	pxThreadState->pvThread = ( void * ) CreateThread( NULL, 0, ( LPTHREAD_START_ROUTINE ) pxCode, pvParameters, CREATE_SUSPENDED, NULL );
	SetThreadPriorityBoost( pxThreadState->pvThread, TRUE );
	pxThreadState->lWaitingInterruptAck = pdFALSE;
	SetThreadPriority( pxThreadState->pvThread, THREAD_PRIORITY_IDLE );
	
	return ( portSTACK_TYPE * ) pxThreadState;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
void *pvHandle;
long lSuccess = pdPASS;
xThreadState *pxThreadState;

	/* Create the events and mutexes that are used to synchronise all the
	threads. */
	pvInterruptEventMutex = CreateMutex( NULL, FALSE, NULL );
	pvInterruptEvent = CreateEvent( NULL, FALSE, FALSE, NULL );
	pvTickAcknowledgeEvent = CreateEvent( NULL, FALSE, FALSE, NULL );
	pvInterruptAcknowledgeEvent = CreateEvent( NULL, FALSE, FALSE, NULL );

	if( ( pvInterruptEventMutex == NULL ) || ( pvInterruptEvent == NULL ) || ( pvTickAcknowledgeEvent == NULL ) || ( pvInterruptAcknowledgeEvent == NULL ) )
	{
		lSuccess = pdFAIL;
	}

	/* Set the priority of this thread such that it is above the priority of 
	the threads that run tasks.  This higher priority is required to ensure
	pseudo interrupts take priority over tasks. */
	SetPriorityClass( GetCurrentProcess(), ABOVE_NORMAL_PRIORITY_CLASS );
	pvHandle = GetCurrentThread();
	if( pvHandle == NULL )
	{
		lSuccess = pdFAIL;
	}
	
	if( lSuccess == pdPASS )
	{
		if( SetThreadPriority( pvHandle, THREAD_PRIORITY_HIGHEST ) == 0 )
		{
			lSuccess = pdFAIL;
		}
		SetThreadPriorityBoost( pvHandle, TRUE );
	}

	if( lSuccess == pdPASS )
	{
		/* Start the thread that simulates the timer peripheral to generate
		tick interrupts. */
		pvHandle = CreateThread( NULL, 0, prvSimulatedPeripheralTimer, NULL, 0, NULL );
		if( pvHandle != NULL )
		{
			SetThreadPriority( pvHandle, THREAD_PRIORITY_HIGHEST );
			SetThreadPriorityBoost( pvHandle, TRUE );
		}
		
		/* Start the highest priority task by obtaining its associated thread 
		state structure, in which is stored the thread handle. */
		pxThreadState = ( xThreadState * ) *( ( unsigned long * ) pxCurrentTCB );
		ulCriticalNesting = portNO_CRITICAL_NESTING;

		/* Bump up the priority of the thread that is going to run, in the
		hope that this will asist in getting the Windows thread scheduler to
		behave as an embedded engineer might expect. */
		SetThreadPriority( pxThreadState->pvThread, THREAD_PRIORITY_ABOVE_NORMAL );
		ResumeThread( pxThreadState->pvThread );

		/* Handle all pseudo interrupts - including yield requests and 
		simulated ticks. */
		prvProcessPseudoInterrupts();
	}	
	
	/* Would not expect to return from prvProcessPseudoInterrupts(), so should 
	not get here. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvProcessPseudoInterrupts( void )
{
long lSwitchRequired;
xThreadState *pxThreadState;
void *pvObjectList[ 2 ];
unsigned long i;

	/* Going to block on the mutex that ensured exclusive access to the pseudo 
	interrupt objects, and the event that signals that a pseudo interrupt
	should be processed. */
	pvObjectList[ 0 ] = pvInterruptEventMutex;
	pvObjectList[ 1 ] = pvInterruptEvent;

	for(;;)
	{
		WaitForMultipleObjects( sizeof( pvObjectList ) / sizeof( void * ), pvObjectList, TRUE, INFINITE );

		/* A thread will hold the interrupt event mutex while in a critical
		section, so this pseudo interrupt handler should only run when
		critical nesting is zero. */
		if( ulCriticalNesting != 0 )
		{
			/* For a break point only. */
			__asm{ NOP };
		}

		/* Used to indicate whether the pseudo interrupt processing has
		necessitated a context switch to another task/thread. */
		lSwitchRequired = pdFALSE;

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

						lSwitchRequired = pdTRUE;

						/* Clear the interrupt pending bit. */
						ulPendingInterrupts &= ~( 1UL << portINTERRUPT_YIELD );
						break;

					case portINTERRUPT_TICK:
					
						/* Process the tick itself. */
						vTaskIncrementTick();
						#if( configUSE_PREEMPTION != 0 )
						{
							/* A context switch is only automatically 
							performed from the tick	interrupt if the 
							pre-emptive scheduler is being used. */
							lSwitchRequired = pdTRUE;
						}
						#endif
							
						/* Clear the interrupt pending bit. */
						ulPendingInterrupts &= ~( 1UL << portINTERRUPT_TICK );
						SetEvent( pvTickAcknowledgeEvent );
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

							/* TODO:  Need to have some sort of handshake 
							event here for non-tick and none yield 
							interrupts. */
						}
						break;
				}
			}
		}

		if( lSwitchRequired != pdFALSE )
		{
			void *pvOldCurrentTCB;

			pvOldCurrentTCB = pxCurrentTCB;

			/* Select the next task to run. */
			vTaskSwitchContext();

			/* If the task selected to enter the running state is not the task
			that is already in the running state. */
			if( pvOldCurrentTCB != pxCurrentTCB )
			{
				/* Suspend the old thread. */
				pxThreadState = ( xThreadState *) *( ( unsigned long * ) pvOldCurrentTCB );
				SetThreadPriority( pxThreadState->pvThread, THREAD_PRIORITY_IDLE );
				SetThreadPriorityBoost( pxThreadState->pvThread, TRUE );
				SuspendThread( pxThreadState->pvThread );
							


				/* NOTE! - Here lies a problem when the preemptive scheduler is 
				used.  It would seem Win32 threads do not stop as soon as a
				call to suspend them is made.  The co-operative scheduler gets
				around this by having the thread block on a semaphore 
				immediately after yielding so it cannot execute any more task
				code until it is once again scheduled to run.  This cannot be
				done if the task is pre-empted though, and I have not found an
				equivalent work around for the preemptive situation. */
				


				/* Obtain the state of the task now selected to enter the 
				Running state. */
				pxThreadState = ( xThreadState * ) ( *( unsigned long *) pxCurrentTCB );

				/* Boost the priority of the thread selected to run a little 
				in an attempt to get the Windows thread scheduler to act a 
				little more like an embedded engineer might expect. */
				SetThreadPriority( pxThreadState->pvThread, THREAD_PRIORITY_ABOVE_NORMAL );
				SetThreadPriorityBoost( pxThreadState->pvThread, TRUE );
				ResumeThread( pxThreadState->pvThread );
			}
		}

		/* On exiting a critical section a task may have blocked on the
		interrupt event when only a tick needed processing, in which case
		it will not have been released from waiting on the event yet. */
		pxThreadState = ( xThreadState * ) ( *( unsigned long *) pxCurrentTCB );
		if( pxThreadState->lWaitingInterruptAck == pdTRUE )
		{
			pxThreadState->lWaitingInterruptAck = pdFALSE;
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
xThreadState *pxThreadState;

	if( ( ulInterruptNumber < portMAX_INTERRUPTS ) && ( pvInterruptEventMutex != NULL ) )
	{
		/* Yield interrupts are processed even when critical nesting is non-zero. */
		WaitForSingleObject( pvInterruptEventMutex, INFINITE );
		ulPendingInterrupts |= ( 1 << ulInterruptNumber );

		/* The pseudo interrupt is now held pending, but don't actually process it
		yet if this call is within a critical section.  It is possible for this to
		be in a critical section as calls to wait for mutexes are accumulative. */
		if( ulCriticalNesting == 0 )
		{
			/* The event handler needs to know to signal the interrupt acknowledge event
			the next time this task runs. */
			pxThreadState = ( xThreadState * ) *( ( unsigned long * ) pxCurrentTCB );
			pxThreadState->lWaitingInterruptAck = pdTRUE;

			SetEvent( pvInterruptEvent );

			/* The interrupt ack event should not be signaled yet - if it is then there
			is an error in the logical simulation. */
			if( WaitForSingleObject( pvInterruptAcknowledgeEvent, 0 ) != WAIT_TIMEOUT )
			{
				/* This line is for a break point only. */
				__asm { NOP };
			}

			SignalObjectAndWait( pvInterruptEventMutex, pvInterruptAcknowledgeEvent, INFINITE, FALSE );
		}
		else
		{
			ReleaseMutex( pvInterruptEventMutex );
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
	if( xTaskGetSchedulerState() != taskSCHEDULER_NOT_STARTED )
	{
		/* The interrupt event mutex is held for the entire critical section,
		effectively disabling (pseudo) interrupts. */
		WaitForSingleObject( pvInterruptEventMutex, INFINITE );
		ulCriticalNesting++;
	}
	else
	{
		ulCriticalNesting++;
	}	
}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
xThreadState *pxThreadState;
long lMutexNeedsReleasing;

	/* The interrupt event mutex should already be held by this thread as it was
	obtained on entry to the critical section. */

	lMutexNeedsReleasing = pdTRUE;

	if( ulCriticalNesting > portNO_CRITICAL_NESTING )
	{
		if( ulCriticalNesting == ( portNO_CRITICAL_NESTING + 1 ) )
		{
			ulCriticalNesting--;

			/* Were any interrupts set to pending while interrupts were 
			(pseudo) disabled? */
			if( ulPendingInterrupts != 0UL )
			{
				SetEvent( pvInterruptEvent );

				/* The event handler needs to know to signal the interrupt 
				acknowledge event the next time this task runs. */
				pxThreadState = ( xThreadState * ) *( ( unsigned long * ) pxCurrentTCB );
				pxThreadState->lWaitingInterruptAck = pdTRUE;

				/* Mutex will be released now, so does not require releasing
				on function exit. */
				lMutexNeedsReleasing = pdFALSE;
				SignalObjectAndWait( pvInterruptEventMutex, pvInterruptAcknowledgeEvent, INFINITE, FALSE );
			}
		}
		else
		{
			/* Tick interrupts will still not be processed as the critical
			nesting depth will not be zero. */
			ulCriticalNesting--;
		}
	}

	if( lMutexNeedsReleasing == pdTRUE )
	{
		ReleaseMutex( pvInterruptEventMutex );
	}
}

