/*
 * FreeRTOS+FAT build 191128 - Note:  FreeRTOS+FAT is still in the lab!
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Authors include James Walmsley, Hein Tibosch and Richard Barry
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
 * https://www.FreeRTOS.org
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "ff_headers.h"
#include "event_groups.h"


/* Scheduler include files. */
#ifdef	__WIN32__
	#include "MyMalloc.h"
#else
	#include "FreeRTOS.h"
	#include "task.h"
	#include "semphr.h"
	#include "tcpLogging.h"
#endif

#include "logbuf.h"
#include <string.h>
#include "bitops.h"
#if USE_SOFT_WDT
	#include "softWdt.h"
#endif

#include "thread_mutex.h"

#include "event_groups.h"

#if( FF_DO_TRACE_SEMAPHORE != 0 )
	#include "eventLogging.h"
#endif

/* There are two areas which are protected with a semaphore:
Directories and the FAT area.
The masks below are used when calling Group Event functions. */
#define FF_FAT_LOCK_EVENT_BITS    ( ( const EventBits_t ) FF_FAT_LOCK )
#define FF_DIR_LOCK_EVENT_BITS    ( ( const EventBits_t ) FF_DIR_LOCK )

/* This is not a real lock: it is a bit (or semaphore) will will be given
each time when a sector buffer is released. */
#define FF_BUF_LOCK_EVENT_BITS    ( ( const EventBits_t ) FF_BUF_LOCK )

extern void myTaskDelay (unsigned aTime);

static char cMutexWasCreated = 0;
static pthread_mutex_t xFATMutex;

static void vCreateFATMutex ()
{
	cMutexWasCreated = 1;
	pthread_mutex_init ("FreeRTOS+FAT", &xFATMutex, 0);
}

BaseType_t FF_HasSemaphore (void *pxSemaphore)
{
	// Return pdTRUE if the calling task owns the semaphore
	if (!cMutexWasCreated) vCreateFATMutex ();
	return pthread_has_mutex (&xFATMutex);
}


BaseType_t FF_SemaphoreTaken (void *pxSemaphore)
{
	// Return pdTRUE if the calling task owns the semaphore
	if (!cMutexWasCreated) vCreateFATMutex ();
	return pthread_mutex_islocked (&xFATMutex);
}


#if( FF_DO_TRACE_SEMAPHORE != 0 )
static char mutex_owner[32];
#endif

BaseType_t FF_TrySemaphore( void *pxSemaphore, uint32_t ulTime_ms)
{
BaseType_t rc;
	#if( FF_DO_TRACE_SEMAPHORE != 0 )
	{
		eventLogAdd("Pend_%s\n", pcName);
	}
	#endif /* FF_DO_TRACE_SEMAPHORE */
	if (!cMutexWasCreated) vCreateFATMutex ();
	rc = pthread_mutex_lock (&xFATMutex, ulTime_ms);
	#if( FF_DO_TRACE_SEMAPHORE != 0 )
	if (rc > 0) {
		if(mutex_owner[0] != 0) {
			logPrintf("Pend Try: %s overruled\n", mutex_owner);
		}
		snprintf(mutex_owner, sizeof mutex_owner, pcName);
	}
	#endif /* FF_DO_TRACE_SEMAPHORE */
	return rc;
}
/*-----------------------------------------------------------*/

void FF_PendSemaphore( void *pxSemaphore )
{
	#if( FF_DO_TRACE_SEMAPHORE != 0 )
	{
		eventLogAdd("Pend_%s\n", pcName);
	}
	#endif /* FF_DO_TRACE_SEMAPHORE */

	if (!cMutexWasCreated) vCreateFATMutex ();
	pthread_mutex_lock (&xFATMutex, 120000);
	#if( FF_DO_TRACE_SEMAPHORE != 0 )
	{
		if(mutex_owner[0] != 0) {
			logPrintf("Pend Enter: %s overruled by %s\n", mutex_owner, pcName);
		}
		snprintf(mutex_owner, sizeof mutex_owner, pcName);
	}
	#endif /* FF_DO_TRACE_SEMAPHORE */
}
/*-----------------------------------------------------------*/

void FF_ReleaseSemaphore( void *pxSemaphore )
{
	#if( FF_DO_TRACE_SEMAPHORE != 0 )
	{
		if(strcmp (pcName, mutex_owner) != 0) {
			// FF_GetBuffer2 != FF_GetBuffer
			logPrintf("Pend Exit: %s owned by %s\n", pcName, mutex_owner);
		}
		eventLogAdd("Exit_%s\n", pcName);
		mutex_owner[0] = '\0';
	}
	#endif /* FF_DO_TRACE_SEMAPHORE */

	if (cMutexWasCreated)  {
		pthread_mutex_unlock (&xFATMutex);
	}
}
/*-----------------------------------------------------------*/

void FF_Sleep( uint32_t ulTime_ms )
{
	myTaskDelay (ulTime_ms);
}
/*-----------------------------------------------------------*/

BaseType_t FF_CreateEvents( FF_IOManager_t *pxIOManager )
{
BaseType_t xResult;

	pxIOManager->xEventGroup = xEventGroupCreate();
	if( pxIOManager->xEventGroup != NULL )
	{
		xEventGroupSetBits( pxIOManager->xEventGroup,
			FF_FAT_LOCK_EVENT_BITS | FF_DIR_LOCK_EVENT_BITS | FF_BUF_LOCK_EVENT_BITS );
		xResult = pdTRUE;
	}
	else
	{
		xResult = pdFALSE;
	}

	return xResult;
}
/*-----------------------------------------------------------*/

void FF_LockDirectory( FF_IOManager_t *pxIOManager )
{
	EventBits_t xBits;

	for( ;; )
	{
		/* Called when a task want to make changes to a directory.
		First it waits for the desired bit to come high. */
		xEventGroupWaitBits( pxIOManager->xEventGroup,
			FF_DIR_LOCK_EVENT_BITS, /* uxBitsToWaitFor */
			( EventBits_t )0,       /* xClearOnExit */
			pdFALSE,                /* xWaitForAllBits n.a. */
			pdMS_TO_TICKS( 10000UL ) );

		/* The next operation will only succeed for 1 task at a time,
		because it is an atomary test & set operation: */
		xBits = xEventGroupClearBits( pxIOManager->xEventGroup, FF_DIR_LOCK_EVENT_BITS );

		if( ( xBits & FF_DIR_LOCK_EVENT_BITS ) != 0 )
		{
			/* This task has cleared the desired bit.
			It now 'owns' the resource. */
			break;
		}
	}
}
/*-----------------------------------------------------------*/

void FF_UnlockDirectory( FF_IOManager_t *pxIOManager )
{
	configASSERT( ( xEventGroupGetBits( pxIOManager->xEventGroup ) & FF_DIR_LOCK_EVENT_BITS ) == 0 );
	xEventGroupSetBits( pxIOManager->xEventGroup, FF_DIR_LOCK_EVENT_BITS );
}
/*-----------------------------------------------------------*/

int FF_Has_Lock( FF_IOManager_t *pxIOManager, uint32_t aBits )
{
int iReturn;

	void *handle = xTaskGetCurrentTaskHandle();
	if( ( aBits & FF_FAT_LOCK_EVENT_BITS ) != 0 )
	{
		if( ( pxIOManager->pvFATLockHandle != NULL ) && ( pxIOManager->pvFATLockHandle == handle ) )
		{
			iReturn = pdTRUE;
		}
		else
		{
			iReturn = pdFALSE;
		}
	}
	else
	{
		iReturn = pdFALSE;
	}
	return iReturn;
}

void FF_Assert_Lock( FF_IOManager_t *pxIOManager, uint32_t aBits )
{
	void *handle = xTaskGetCurrentTaskHandle();

	if( ( aBits & FF_FAT_LOCK_EVENT_BITS ) != 0 )
	{
		configASSERT( pxIOManager->pvFATLockHandle != NULL && pxIOManager->pvFATLockHandle == handle );

		/* In case configASSERT() is not defined. */
		( void ) pxIOManager; 
		( void ) handle;
	}
}

void FF_LockFAT( FF_IOManager_t *pxIOManager )
{
EventBits_t xBits;

	configASSERT( FF_Has_Lock( pxIOManager, FF_FAT_LOCK ) == pdFALSE );
	if (FF_Has_Lock( pxIOManager, FF_FAT_LOCK ) != pdFALSE )
	{
		return;
	}

	for( ;; )
	{
		/* Called when a task want to make changes to the FAT area.
		First it waits for the desired bit to come high. */
		xEventGroupWaitBits( pxIOManager->xEventGroup,
			FF_FAT_LOCK_EVENT_BITS, /* uxBitsToWaitFor */
			( EventBits_t )0,       /* xClearOnExit */
			pdFALSE,                /* xWaitForAllBits n.a. */
			pdMS_TO_TICKS( 10000UL ) );

		/* The next operation will only succeed for 1 task at a time,
		because it is an atomary test & set operation: */
		xBits = xEventGroupClearBits( pxIOManager->xEventGroup, FF_FAT_LOCK_EVENT_BITS );

		if( ( xBits & FF_FAT_LOCK_EVENT_BITS ) != 0 )
		{
			/* This task has cleared the desired bit.
			It now 'owns' the resource. */
			pxIOManager->pvFATLockHandle = xTaskGetCurrentTaskHandle();
			break;
		}
	}
}
/*-----------------------------------------------------------*/

void FF_UnlockFAT( FF_IOManager_t *pxIOManager )
{
	configASSERT( ( xEventGroupGetBits( pxIOManager->xEventGroup ) & FF_FAT_LOCK_EVENT_BITS ) == 0 );
	if (FF_Has_Lock( pxIOManager, FF_FAT_LOCK ) != pdFALSE )
	{
		pxIOManager->pvFATLockHandle = NULL;
		xEventGroupSetBits( pxIOManager->xEventGroup, FF_FAT_LOCK_EVENT_BITS );
	}
	else
	{
		FF_PRINTF("FF_UnlockFAT: wasn't locked by me\n");
	}
}
/*-----------------------------------------------------------*/

BaseType_t FF_BufferWait( FF_IOManager_t *pxIOManager, uint32_t xWaitMS )
{
EventBits_t xBits;
BaseType_t xReturn;

	/* This function is called when a task is waiting for a sector buffer
	to become available. */
	xBits = xEventGroupWaitBits( pxIOManager->xEventGroup,
		FF_BUF_LOCK_EVENT_BITS, /* uxBitsToWaitFor */
		FF_BUF_LOCK_EVENT_BITS, /* xClearOnExit */
		pdFALSE,                /* xWaitForAllBits n.a. */
		pdMS_TO_TICKS( xWaitMS ) );
	if( ( xBits & FF_BUF_LOCK_EVENT_BITS ) != 0 )
	{
		xReturn = pdTRUE;
	}
	else
	{
		xReturn = pdFALSE;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void FF_BufferProceed( FF_IOManager_t *pxIOManager )
{
	/* Wake-up all tasks that are waiting for a sector buffer to become available. */
	xEventGroupSetBits( pxIOManager->xEventGroup, FF_BUF_LOCK_EVENT_BITS );
}
/*-----------------------------------------------------------*/
