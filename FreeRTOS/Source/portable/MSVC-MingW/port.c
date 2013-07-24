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
static void prvProcessSimulatedInterrupts( void );

/*
 * Interrupt handlers used by the kernel itself.  These are executed from the
 * simulated interrupt handler thread.
 */
static unsigned long prvProcessYieldInterrupt( void );
static unsigned long prvProcessTickInterrupt( void );

/*-----------------------------------------------------------*/

/* The WIN32 simulator runs each task in a thread.  The context switching is
managed by the threads, so the task stack does not have to be managed directly,
although the task stack is still used to hold an xThreadState structure this is
the only thing it will ever hold.  The structure indirectly maps the task handle 
to a thread handle. */
typedef struct
{
	/* Handle of the thread that executes the task. */
	void *pvThread;

} xThreadState;

/* Simulated interrupts waiting to be processed.  This is a bit mask where each
bit represents one interrupt, so a maximum of 32 interrupts can be simulated. */
static volatile unsigned long ulPendingInterrupts = 0UL;

/* An event used to inform the simulated interrupt processing thread (a high 
priority thread that simulated interrupt processing) that an interrupt is
pending. */
static void *pvInterruptEvent = NULL;

/* Mutex used to protect all the simulated interrupt variables that are accessed 
by multiple threads. */
static void *pvInterruptEventMutex = NULL;

/* The critical nesting count for the currently executing task.  This is 
initialised to a non-zero value so interrupts do not become enabled during 
the initialisation phase.  As each task has its own critical nesting value 
ulCriticalNesting will get set to zero when the first task runs.  This 
initialisation is probably not critical in this simulated environment as the
simulated interrupt handlers do not get created until the FreeRTOS scheduler is 
started anyway. */
static unsigned long ulCriticalNesting = 9999UL;

/* Handlers for all the simulated software interrupts.  The first two positions
are used for the Yield and Tick interrupts so are handled slightly differently,
all the other interrupts can be user defined. */
static unsigned long (*ulIsrHandler[ portMAX_INTERRUPTS ])( void ) = { 0 };

/* Pointer to the TCB of the currently executing task. */
extern void *pxCurrentTCB;

/*-----------------------------------------------------------*/

static DWORD WINAPI prvSimulatedPeripheralTimer( LPVOID lpParameter )
{
portTickType xMinimumWindowsBlockTime = ( portTickType ) 20;

	/* Just to prevent compiler warnings. */
	( void ) lpParameter;

	for(;;)
	{
		/* Wait until the timer expires and we can access the simulated interrupt 
		variables.  *NOTE* this is not a 'real time' way of generating tick 
		events as the next wake time should be relative to the previous wake 
		time, not the time that Sleep() is called.  It is done this way to 
		prevent overruns in this very non real time simulated/emulated 
		environment. */
		if( portTICK_RATE_MS < xMinimumWindowsBlockTime )
		{
			Sleep( xMinimumWindowsBlockTime );
		}
		else
		{
			Sleep( portTICK_RATE_MS );
		}

		WaitForSingleObject( pvInterruptEventMutex, INFINITE );

		/* The timer has expired, generate the simulated tick event. */
		ulPendingInterrupts |= ( 1 << portINTERRUPT_TICK );

		/* The interrupt is now pending - notify the simulated interrupt 
		handler thread. */
		SetEvent( pvInterruptEvent );

		/* Give back the mutex so the simulated interrupt handler unblocks 
		and can	access the interrupt handler variables. */
		ReleaseMutex( pvInterruptEventMutex );
	}

	#ifdef __GNUC__
		/* Should never reach here - MingW complains if you leave this line out,
		MSVC complains if you put it in. */
		return 0;
	#endif
}
/*-----------------------------------------------------------*/

portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
xThreadState *pxThreadState = NULL;
char *pcTopOfStack = ( char * ) pxTopOfStack;

	/* In this simulated case a stack is not initialised, but instead a thread
	is created that will execute the task being created.  The thread handles
	the context switching itself.  The xThreadState object is placed onto
	the stack that was created for the task - so the stack buffer is still
	used, just not in the conventional way.  It will not be used for anything
	other than holding this structure. */
	pxThreadState = ( xThreadState * ) ( pcTopOfStack - sizeof( xThreadState ) );

	/* Create the thread itself. */
	pxThreadState->pvThread = CreateThread( NULL, 0, ( LPTHREAD_START_ROUTINE ) pxCode, pvParameters, CREATE_SUSPENDED, NULL );
	SetThreadAffinityMask( pxThreadState->pvThread, 0x01 );
	SetThreadPriorityBoost( pxThreadState->pvThread, TRUE );
	SetThreadPriority( pxThreadState->pvThread, THREAD_PRIORITY_IDLE );
	
	return ( portSTACK_TYPE * ) pxThreadState;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
void *pvHandle;
long lSuccess = pdPASS;
xThreadState *pxThreadState;

	/* Install the interrupt handlers used by the scheduler itself. */
	vPortSetInterruptHandler( portINTERRUPT_YIELD, prvProcessYieldInterrupt );
	vPortSetInterruptHandler( portINTERRUPT_TICK, prvProcessTickInterrupt );

	/* Create the events and mutexes that are used to synchronise all the
	threads. */
	pvInterruptEventMutex = CreateMutex( NULL, FALSE, NULL );
	pvInterruptEvent = CreateEvent( NULL, FALSE, FALSE, NULL );

	if( ( pvInterruptEventMutex == NULL ) || ( pvInterruptEvent == NULL ) )
	{
		lSuccess = pdFAIL;
	}

	/* Set the priority of this thread such that it is above the priority of 
	the threads that run tasks.  This higher priority is required to ensure
	simulated interrupts take priority over tasks. */
	pvHandle = GetCurrentThread();
	if( pvHandle == NULL )
	{
		lSuccess = pdFAIL;
	}
	
	if( lSuccess == pdPASS )
	{
		if( SetThreadPriority( pvHandle, THREAD_PRIORITY_NORMAL ) == 0 )
		{
			lSuccess = pdFAIL;
		}
		SetThreadPriorityBoost( pvHandle, TRUE );
		SetThreadAffinityMask( pvHandle, 0x01 );
	}

	if( lSuccess == pdPASS )
	{
		/* Start the thread that simulates the timer peripheral to generate
		tick interrupts.  The priority is set below that of the simulated 
		interrupt handler so the interrupt event mutex is used for the
		handshake / overrun protection. */
		pvHandle = CreateThread( NULL, 0, prvSimulatedPeripheralTimer, NULL, 0, NULL );
		if( pvHandle != NULL )
		{
			SetThreadPriority( pvHandle, THREAD_PRIORITY_BELOW_NORMAL );
			SetThreadPriorityBoost( pvHandle, TRUE );
			SetThreadAffinityMask( pvHandle, 0x01 );
		}
		
		/* Start the highest priority task by obtaining its associated thread 
		state structure, in which is stored the thread handle. */
		pxThreadState = ( xThreadState * ) *( ( unsigned long * ) pxCurrentTCB );
		ulCriticalNesting = portNO_CRITICAL_NESTING;

		/* Bump up the priority of the thread that is going to run, in the
		hope that this will asist in getting the Windows thread scheduler to
		behave as an embedded engineer might expect. */
		ResumeThread( pxThreadState->pvThread );

		/* Handle all simulated interrupts - including yield requests and 
		simulated ticks. */
		prvProcessSimulatedInterrupts();
	}	
	
	/* Would not expect to return from prvProcessSimulatedInterrupts(), so should 
	not get here. */
	return 0;
}
/*-----------------------------------------------------------*/

static unsigned long prvProcessYieldInterrupt( void )
{
	return pdTRUE;
}
/*-----------------------------------------------------------*/

static unsigned long prvProcessTickInterrupt( void )
{
unsigned long ulSwitchRequired;

	/* Process the tick itself. */
	ulSwitchRequired = ( unsigned long ) xTaskIncrementTick();

	return ulSwitchRequired;
}
/*-----------------------------------------------------------*/

static void prvProcessSimulatedInterrupts( void )
{
unsigned long ulSwitchRequired, i;
xThreadState *pxThreadState;
void *pvObjectList[ 2 ];

	/* Going to block on the mutex that ensured exclusive access to the simulated 
	interrupt objects, and the event that signals that a simulated interrupt
	should be processed. */
	pvObjectList[ 0 ] = pvInterruptEventMutex;
	pvObjectList[ 1 ] = pvInterruptEvent;

	for(;;)
	{
		WaitForMultipleObjects( sizeof( pvObjectList ) / sizeof( void * ), pvObjectList, TRUE, INFINITE );

		/* Used to indicate whether the simulated interrupt processing has
		necessitated a context switch to another task/thread. */
		ulSwitchRequired = pdFALSE;

		/* For each interrupt we are interested in processing, each of which is
		represented by a bit in the 32bit ulPendingInterrupts variable. */
		for( i = 0; i < portMAX_INTERRUPTS; i++ )
		{
			/* Is the simulated interrupt pending? */
			if( ulPendingInterrupts & ( 1UL << i ) )
			{
				/* Is a handler installed? */
				if( ulIsrHandler[ i ] != NULL )
				{
					/* Run the actual handler. */
					if( ulIsrHandler[ i ]() != pdFALSE )
					{
						ulSwitchRequired |= ( 1 << i );
					}
				}

				/* Clear the interrupt pending bit. */
				ulPendingInterrupts &= ~( 1UL << i );
			}
		}

		if( ulSwitchRequired != pdFALSE )
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
				SuspendThread( pxThreadState->pvThread );

				/* Obtain the state of the task now selected to enter the 
				Running state. */
				pxThreadState = ( xThreadState * ) ( *( unsigned long *) pxCurrentTCB );
				ResumeThread( pxThreadState->pvThread );
			}
		}

		ReleaseMutex( pvInterruptEventMutex );
	}
}
/*-----------------------------------------------------------*/

void vPortDeleteThread( void *pvTaskToDelete )
{
xThreadState *pxThreadState;

	WaitForSingleObject( pvInterruptEventMutex, INFINITE );

	/* Find the handle of the thread being deleted. */
	pxThreadState = ( xThreadState * ) ( *( unsigned long *) pvTaskToDelete );
	TerminateThread( pxThreadState->pvThread, 0 );

	ReleaseMutex( pvInterruptEventMutex );
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* This function IS NOT TESTED! */
	TerminateProcess( GetCurrentProcess(), 0 );
}
/*-----------------------------------------------------------*/

void vPortGenerateSimulatedInterrupt( unsigned long ulInterruptNumber )
{
	if( ( ulInterruptNumber < portMAX_INTERRUPTS ) && ( pvInterruptEventMutex != NULL ) )
	{
		/* Yield interrupts are processed even when critical nesting is non-zero. */
		WaitForSingleObject( pvInterruptEventMutex, INFINITE );
		ulPendingInterrupts |= ( 1 << ulInterruptNumber );

		/* The simulated interrupt is now held pending, but don't actually process it
		yet if this call is within a critical section.  It is possible for this to
		be in a critical section as calls to wait for mutexes are accumulative. */
		if( ulCriticalNesting == 0 )
		{
			SetEvent( pvInterruptEvent );			
		}

		ReleaseMutex( pvInterruptEventMutex );
	}
}
/*-----------------------------------------------------------*/

void vPortSetInterruptHandler( unsigned long ulInterruptNumber, unsigned long (*pvHandler)( void ) )
{
	if( ulInterruptNumber < portMAX_INTERRUPTS )
	{
		if( pvInterruptEventMutex != NULL )
		{
			WaitForSingleObject( pvInterruptEventMutex, INFINITE );
			ulIsrHandler[ ulInterruptNumber ] = pvHandler;
			ReleaseMutex( pvInterruptEventMutex );
		}
		else
		{
			ulIsrHandler[ ulInterruptNumber ] = pvHandler;
		}
	}
}
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
	if( xTaskGetSchedulerState() != taskSCHEDULER_NOT_STARTED )
	{
		/* The interrupt event mutex is held for the entire critical section,
		effectively disabling (simulated) interrupts. */
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
			(simulated) disabled? */
			if( ulPendingInterrupts != 0UL )
			{
				SetEvent( pvInterruptEvent );

				/* Mutex will be released now, so does not require releasing
				on function exit. */
				lMutexNeedsReleasing = pdFALSE;
				ReleaseMutex( pvInterruptEventMutex );
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
/*-----------------------------------------------------------*/

