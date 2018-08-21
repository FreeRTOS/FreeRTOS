/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* Standard includes. */
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

#ifdef __GNUC__
	#include "mmsystem.h"
#else
	#pragma comment(lib, "winmm.lib")
#endif

#define portMAX_INTERRUPTS				( ( uint32_t ) sizeof( uint32_t ) * 8UL ) /* The number of bits in an uint32_t. */
#define portNO_CRITICAL_NESTING 		( ( uint32_t ) 0 )

/* The priorities at which the various components of the simulation execute. */
#define portDELETE_SELF_THREAD_PRIORITY			 THREAD_PRIORITY_TIME_CRITICAL /* Must be highest. */
#define portSIMULATED_INTERRUPTS_THREAD_PRIORITY THREAD_PRIORITY_TIME_CRITICAL
#define portSIMULATED_TIMER_THREAD_PRIORITY		 THREAD_PRIORITY_HIGHEST
#define portTASK_THREAD_PRIORITY				 THREAD_PRIORITY_ABOVE_NORMAL

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
static uint32_t prvProcessYieldInterrupt( void );
static uint32_t prvProcessTickInterrupt( void );

/*
 * Called when the process exits to let Windows know the high timer resolution
 * is no longer required.
 */
static BOOL WINAPI prvEndProcess( DWORD dwCtrlType );

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
static volatile uint32_t ulPendingInterrupts = 0UL;

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
static uint32_t ulCriticalNesting = 9999UL;

/* Handlers for all the simulated software interrupts.  The first two positions
are used for the Yield and Tick interrupts so are handled slightly differently,
all the other interrupts can be user defined. */
static uint32_t (*ulIsrHandler[ portMAX_INTERRUPTS ])( void ) = { 0 };

/* Pointer to the TCB of the currently executing task. */
extern void *pxCurrentTCB;

/* Used to ensure nothing is processed during the startup sequence. */
static BaseType_t xPortRunning = pdFALSE;

/*-----------------------------------------------------------*/

static DWORD WINAPI prvSimulatedPeripheralTimer( LPVOID lpParameter )
{
TickType_t xMinimumWindowsBlockTime;
TIMECAPS xTimeCaps;

	/* Set the timer resolution to the maximum possible. */
	if( timeGetDevCaps( &xTimeCaps, sizeof( xTimeCaps ) ) == MMSYSERR_NOERROR )
	{
		xMinimumWindowsBlockTime = ( TickType_t ) xTimeCaps.wPeriodMin;
		timeBeginPeriod( xTimeCaps.wPeriodMin );

		/* Register an exit handler so the timeBeginPeriod() function can be
		matched with a timeEndPeriod() when the application exits. */
		SetConsoleCtrlHandler( prvEndProcess, TRUE );
	}
	else
	{
		xMinimumWindowsBlockTime = ( TickType_t ) 20;
	}

	/* Just to prevent compiler warnings. */
	( void ) lpParameter;

	for( ;; )
	{
		/* Wait until the timer expires and we can access the simulated interrupt
		variables.  *NOTE* this is not a 'real time' way of generating tick
		events as the next wake time should be relative to the previous wake
		time, not the time that Sleep() is called.  It is done this way to
		prevent overruns in this very non real time simulated/emulated
		environment. */
		if( portTICK_PERIOD_MS < xMinimumWindowsBlockTime )
		{
			Sleep( xMinimumWindowsBlockTime );
		}
		else
		{
			Sleep( portTICK_PERIOD_MS );
		}

		configASSERT( xPortRunning );

		WaitForSingleObject( pvInterruptEventMutex, INFINITE );

		/* The timer has expired, generate the simulated tick event. */
		ulPendingInterrupts |= ( 1 << portINTERRUPT_TICK );

		/* The interrupt is now pending - notify the simulated interrupt
		handler thread. */
		if( ulCriticalNesting == 0 )
		{
			SetEvent( pvInterruptEvent );
		}

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

static BOOL WINAPI prvEndProcess( DWORD dwCtrlType )
{
TIMECAPS xTimeCaps;

	( void ) dwCtrlType;

	if( timeGetDevCaps( &xTimeCaps, sizeof( xTimeCaps ) ) == MMSYSERR_NOERROR )
	{
		/* Match the call to timeBeginPeriod( xTimeCaps.wPeriodMin ) made when
		the process started with a timeEndPeriod() as the process exits. */
		timeEndPeriod( xTimeCaps.wPeriodMin );
	}

	return pdFALSE;
}
/*-----------------------------------------------------------*/

StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
xThreadState *pxThreadState = NULL;
int8_t *pcTopOfStack = ( int8_t * ) pxTopOfStack;
const SIZE_T xStackSize = 1024; /* Set the size to a small number which will get rounded up to the minimum possible. */

	/* In this simulated case a stack is not initialised, but instead a thread
	is created that will execute the task being created.  The thread handles
	the context switching itself.  The xThreadState object is placed onto
	the stack that was created for the task - so the stack buffer is still
	used, just not in the conventional way.  It will not be used for anything
	other than holding this structure. */
	pxThreadState = ( xThreadState * ) ( pcTopOfStack - sizeof( xThreadState ) );

	/* Create the thread itself. */
	pxThreadState->pvThread = CreateThread( NULL, xStackSize, ( LPTHREAD_START_ROUTINE ) pxCode, pvParameters, CREATE_SUSPENDED | STACK_SIZE_PARAM_IS_A_RESERVATION, NULL );
	configASSERT( pxThreadState->pvThread ); /* See comment where TerminateThread() is called. */
	SetThreadAffinityMask( pxThreadState->pvThread, 0x01 );
	SetThreadPriorityBoost( pxThreadState->pvThread, TRUE );
	SetThreadPriority( pxThreadState->pvThread, portTASK_THREAD_PRIORITY );

	return ( StackType_t * ) pxThreadState;
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
void *pvHandle = NULL;
int32_t lSuccess;
xThreadState *pxThreadState = NULL;
SYSTEM_INFO xSystemInfo;

	/* This port runs windows threads with extremely high priority.  All the
	threads execute on the same core - to prevent locking up the host only start
	if the host has multiple cores. */
	GetSystemInfo( &xSystemInfo );
	if( xSystemInfo.dwNumberOfProcessors <= 1 )
	{
		printf( "This version of the FreeRTOS Windows port can only be used on multi-core hosts.\r\n" );
		lSuccess = pdFAIL;
	}
	else
	{
		lSuccess = pdPASS;

		/* The highest priority class is used to [try to] prevent other Windows
		activity interfering with FreeRTOS timing too much. */
		if( SetPriorityClass( GetCurrentProcess(), REALTIME_PRIORITY_CLASS ) == 0 )
		{
			printf( "SetPriorityClass() failed\r\n" );
		}

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
	}

	if( lSuccess == pdPASS )
	{
		if( SetThreadPriority( pvHandle, portSIMULATED_INTERRUPTS_THREAD_PRIORITY ) == 0 )
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
		pvHandle = CreateThread( NULL, 0, prvSimulatedPeripheralTimer, NULL, CREATE_SUSPENDED, NULL );
		if( pvHandle != NULL )
		{
			SetThreadPriority( pvHandle, portSIMULATED_TIMER_THREAD_PRIORITY );
			SetThreadPriorityBoost( pvHandle, TRUE );
			SetThreadAffinityMask( pvHandle, 0x01 );
			ResumeThread( pvHandle );
		}

		/* Start the highest priority task by obtaining its associated thread
		state structure, in which is stored the thread handle. */
		pxThreadState = ( xThreadState * ) *( ( size_t * ) pxCurrentTCB );
		ulCriticalNesting = portNO_CRITICAL_NESTING;

		/* Bump up the priority of the thread that is going to run, in the
		hope that this will assist in getting the Windows thread scheduler to
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

static uint32_t prvProcessYieldInterrupt( void )
{
	return pdTRUE;
}
/*-----------------------------------------------------------*/

static uint32_t prvProcessTickInterrupt( void )
{
uint32_t ulSwitchRequired;

	/* Process the tick itself. */
	configASSERT( xPortRunning );
	ulSwitchRequired = ( uint32_t ) xTaskIncrementTick();

	return ulSwitchRequired;
}
/*-----------------------------------------------------------*/

static void prvProcessSimulatedInterrupts( void )
{
uint32_t ulSwitchRequired, i;
xThreadState *pxThreadState;
void *pvObjectList[ 2 ];
CONTEXT xContext;

	/* Going to block on the mutex that ensured exclusive access to the simulated
	interrupt objects, and the event that signals that a simulated interrupt
	should be processed. */
	pvObjectList[ 0 ] = pvInterruptEventMutex;
	pvObjectList[ 1 ] = pvInterruptEvent;

	/* Create a pending tick to ensure the first task is started as soon as
	this thread pends. */
	ulPendingInterrupts |= ( 1 << portINTERRUPT_TICK );
	SetEvent( pvInterruptEvent );

	xPortRunning = pdTRUE;

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
				pxThreadState = ( xThreadState *) *( ( size_t * ) pvOldCurrentTCB );
				SuspendThread( pxThreadState->pvThread );

				/* Ensure the thread is actually suspended by performing a
				synchronous operation that can only complete when the thread is
				actually suspended.  The below code asks for dummy register
				data. */
				xContext.ContextFlags = CONTEXT_INTEGER;
				( void ) GetThreadContext( pxThreadState->pvThread, &xContext );

				/* Obtain the state of the task now selected to enter the
				Running state. */
				pxThreadState = ( xThreadState * ) ( *( size_t *) pxCurrentTCB );
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
uint32_t ulErrorCode;

	/* Remove compiler warnings if configASSERT() is not defined. */
	( void ) ulErrorCode;

	/* Find the handle of the thread being deleted. */
	pxThreadState = ( xThreadState * ) ( *( size_t *) pvTaskToDelete );

	/* Check that the thread is still valid, it might have been closed by
	vPortCloseRunningThread() - which will be the case if the task associated
	with the thread originally deleted itself rather than being deleted by a
	different task. */
	if( pxThreadState->pvThread != NULL )
	{
		WaitForSingleObject( pvInterruptEventMutex, INFINITE );

		/* !!! This is not a nice way to terminate a thread, and will eventually
		result in resources being depleted if tasks frequently delete other
		tasks (rather than deleting themselves) as the task stacks will not be
		freed. */
		ulErrorCode = TerminateThread( pxThreadState->pvThread, 0 );
		configASSERT( ulErrorCode );

		ulErrorCode = CloseHandle( pxThreadState->pvThread );
		configASSERT( ulErrorCode );

		ReleaseMutex( pvInterruptEventMutex );
	}
}
/*-----------------------------------------------------------*/

void vPortCloseRunningThread( void *pvTaskToDelete, volatile BaseType_t *pxPendYield )
{
xThreadState *pxThreadState;
void *pvThread;
uint32_t ulErrorCode;

	/* Remove compiler warnings if configASSERT() is not defined. */
	( void ) ulErrorCode;

	/* Find the handle of the thread being deleted. */
	pxThreadState = ( xThreadState * ) ( *( size_t *) pvTaskToDelete );
	pvThread = pxThreadState->pvThread;

	/* Raise the Windows priority of the thread to ensure the FreeRTOS scheduler
	does not run and swap it out before it is closed.  If that were to happen
	the thread would never run again and effectively be a thread handle and
	memory leak. */
	SetThreadPriority( pvThread, portDELETE_SELF_THREAD_PRIORITY );

	/* This function will not return, therefore a yield is set as pending to
	ensure a context switch occurs away from this thread on the next tick. */
	*pxPendYield = pdTRUE;

	/* Mark the thread associated with this task as invalid so
	vPortDeleteThread() does not try to terminate it. */
	pxThreadState->pvThread = NULL;

	/* Close the thread. */
	ulErrorCode = CloseHandle( pvThread );
	configASSERT( ulErrorCode );

	/* This is called from a critical section, which must be exited before the
	thread stops. */
	taskEXIT_CRITICAL();

	ExitThread( 0 );
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	exit( 0 );
}
/*-----------------------------------------------------------*/

void vPortGenerateSimulatedInterrupt( uint32_t ulInterruptNumber )
{
	configASSERT( xPortRunning );

	if( ( ulInterruptNumber < portMAX_INTERRUPTS ) && ( pvInterruptEventMutex != NULL ) )
	{
		/* Yield interrupts are processed even when critical nesting is
		non-zero. */
		WaitForSingleObject( pvInterruptEventMutex, INFINITE );
		ulPendingInterrupts |= ( 1 << ulInterruptNumber );

		/* The simulated interrupt is now held pending, but don't actually
		process it yet if this call is within a critical section.  It is
		possible for this to be in a critical section as calls to wait for
		mutexes are accumulative. */
		if( ulCriticalNesting == 0 )
		{
			SetEvent( pvInterruptEvent );
		}

		ReleaseMutex( pvInterruptEventMutex );
	}
}
/*-----------------------------------------------------------*/

void vPortSetInterruptHandler( uint32_t ulInterruptNumber, uint32_t (*pvHandler)( void ) )
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
	if( xPortRunning == pdTRUE )
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
int32_t lMutexNeedsReleasing;

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
				configASSERT( xPortRunning );
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

	if( pvInterruptEventMutex != NULL )
	{
		if( lMutexNeedsReleasing == pdTRUE )
		{
			configASSERT( xPortRunning );
			ReleaseMutex( pvInterruptEventMutex );
		}
	}
}
/*-----------------------------------------------------------*/

