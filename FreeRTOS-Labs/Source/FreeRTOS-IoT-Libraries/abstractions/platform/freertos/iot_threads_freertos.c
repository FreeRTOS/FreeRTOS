/*
 * Amazon FreeRTOS Platform V1.1.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file iot_threads_freertos.c
 * @brief Implementation of the platform specific functions in iot_threads.h for 
 * FreeRTOS.
 */

/* The config header is always included first. */
#include "iot_config.h"

#include "semphr.h"

/* Platform threads include. */
#include "platform/iot_platform_types_freertos.h"
#include "platform/iot_threads.h"
#include "types/iot_platform_types.h"

/* Configure logs for the functions in this file. */
#ifdef IOT_LOG_LEVEL_PLATFORM
    #define LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_PLATFORM
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "THREAD" )
#include "iot_logging_setup.h"

/*
 * Provide default values for undefined memory allocation functions based on
 * the usage of dynamic memory allocation.
 */
#ifndef IotThreads_Malloc
    #include <stdlib.h>

/**
 * @brief Memory allocation. This function should have the same signature
 * as [malloc](http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #define IotThreads_Malloc    malloc
#endif
#ifndef IotThreads_Free
    #include <stdlib.h>

/**
 * @brief Free memory. This function should have the same signature as
 * [free](http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #define IotThreads_Free    free
#endif

/*-----------------------------------------------------------*/

static void _threadRoutineWrapper( void * pArgument )
{
    threadInfo_t * pThreadInfo = ( threadInfo_t * ) pArgument;

    /* Run the thread routine. */
    pThreadInfo->threadRoutine( pThreadInfo->pArgument );
    IotThreads_Free( pThreadInfo );

    vTaskDelete( NULL );
}

/*-----------------------------------------------------------*/

bool Iot_CreateDetachedThread( IotThreadRoutine_t threadRoutine,
                               void * pArgument,
                               int32_t priority,
                               size_t stackSize )
{
    bool status = true;

    configASSERT( threadRoutine != NULL );

    IotLogDebug( "Creating new thread." );
    threadInfo_t * pThreadInfo = IotThreads_Malloc( sizeof( threadInfo_t ) );

    if( pThreadInfo == NULL )
    {
        IotLogDebug( "Unable to allocate memory for threadRoutine %p.", threadRoutine );
        status = false;
    }

    /* Create the FreeRTOS task that will run the thread. */
    if( status )
    {
        pThreadInfo->threadRoutine = threadRoutine;
        pThreadInfo->pArgument = pArgument;

        if( xTaskCreate( _threadRoutineWrapper,
                         "iot_thread",
                         ( configSTACK_DEPTH_TYPE ) stackSize,
                         pThreadInfo,
                         priority,
                         NULL ) != pdPASS )
        {
            /* Task creation failed. */
            IotLogWarn( "Failed to create thread." );
            IotThreads_Free( pThreadInfo );
            status = false;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

bool IotMutex_Create( IotMutex_t * pNewMutex,
                      bool recursive )
{
    _IotSystemMutex_t * internalMutex = ( _IotSystemMutex_t * ) pNewMutex;

    configASSERT( internalMutex != NULL );

    IotLogDebug( "Creating new mutex %p.", pNewMutex );

    if( recursive )
    {
        ( void ) xSemaphoreCreateRecursiveMutexStatic( &internalMutex->xMutex );
    }
    else
    {
        ( void ) xSemaphoreCreateMutexStatic( &internalMutex->xMutex );
    }

    /* remember the type of mutex */
    if( recursive )
    {
        internalMutex->recursive = pdTRUE;
    }
    else
    {
        internalMutex->recursive = pdFALSE;
    }

    return true;
}

/*-----------------------------------------------------------*/

void IotMutex_Destroy( IotMutex_t * pMutex )
{
    _IotSystemMutex_t * internalMutex = ( _IotSystemMutex_t * ) pMutex;

    configASSERT( internalMutex != NULL );

    vSemaphoreDelete( ( SemaphoreHandle_t ) &internalMutex->xMutex );
}

/*-----------------------------------------------------------*/

bool prIotMutexTimedLock( IotMutex_t * pMutex,
                          TickType_t timeout )
{
    _IotSystemMutex_t * internalMutex = ( _IotSystemMutex_t * ) pMutex;
    BaseType_t lockResult;

    configASSERT( internalMutex != NULL );

    IotLogDebug( "Locking mutex %p.", internalMutex );

    /* Call the correct FreeRTOS mutex take function based on mutex type. */
    if( internalMutex->recursive == pdTRUE )
    {
        lockResult = xSemaphoreTakeRecursive( ( SemaphoreHandle_t ) &internalMutex->xMutex, timeout );
    }
    else
    {
        lockResult = xSemaphoreTake( ( SemaphoreHandle_t ) &internalMutex->xMutex, timeout );
    }

    return( lockResult == pdTRUE );
}

/*-----------------------------------------------------------*/

void IotMutex_Lock( IotMutex_t * pMutex )
{
    prIotMutexTimedLock( pMutex, portMAX_DELAY );
}

/*-----------------------------------------------------------*/

bool IotMutex_TryLock( IotMutex_t * pMutex )
{
    return prIotMutexTimedLock( pMutex, 0 );
}

/*-----------------------------------------------------------*/

void IotMutex_Unlock( IotMutex_t * pMutex )
{
    _IotSystemMutex_t * internalMutex = ( _IotSystemMutex_t * ) pMutex;

    configASSERT( internalMutex != NULL );

    IotLogDebug( "Unlocking mutex %p.", internalMutex );

    /* Call the correct FreeRTOS mutex unlock function based on mutex type. */
    if( internalMutex->recursive == pdTRUE )
    {
        ( void ) xSemaphoreGiveRecursive( ( SemaphoreHandle_t ) &internalMutex->xMutex );
    }
    else
    {
        ( void ) xSemaphoreGive( ( SemaphoreHandle_t ) &internalMutex->xMutex );
    }
}

/*-----------------------------------------------------------*/

bool IotSemaphore_Create( IotSemaphore_t * pNewSemaphore,
                          uint32_t initialValue,
                          uint32_t maxValue )
{
    _IotSystemSemaphore_t * internalSemaphore = ( _IotSystemSemaphore_t * ) pNewSemaphore;

    configASSERT( internalSemaphore != NULL );

    IotLogDebug( "Creating new semaphore %p.", pNewSemaphore );

    ( void ) xSemaphoreCreateCountingStatic( maxValue, initialValue, &internalSemaphore->xSemaphore );

    return true;
}

/*-----------------------------------------------------------*/

uint32_t IotSemaphore_GetCount( IotSemaphore_t * pSemaphore )
{
    _IotSystemSemaphore_t * internalSemaphore = ( _IotSystemSemaphore_t * ) pSemaphore;
    UBaseType_t count = 0;

    configASSERT( internalSemaphore != NULL );

    count = uxSemaphoreGetCount( ( SemaphoreHandle_t ) &internalSemaphore->xSemaphore );

    IotLogDebug( "Semaphore %p has count %d.", pSemaphore, count );

    return ( uint32_t ) count;
}

/*-----------------------------------------------------------*/

void IotSemaphore_Destroy( IotSemaphore_t * pSemaphore )
{
    _IotSystemSemaphore_t * internalSemaphore = ( _IotSystemSemaphore_t * ) pSemaphore;

    configASSERT( internalSemaphore != NULL );

    IotLogDebug( "Destroying semaphore %p.", internalSemaphore );

    vSemaphoreDelete( ( SemaphoreHandle_t ) &internalSemaphore->xSemaphore );
}

/*-----------------------------------------------------------*/

void IotSemaphore_Wait( IotSemaphore_t * pSemaphore )
{
    _IotSystemSemaphore_t * internalSemaphore = ( _IotSystemSemaphore_t * ) pSemaphore;

    configASSERT( internalSemaphore != NULL );

    IotLogDebug( "Waiting on semaphore %p.", internalSemaphore );

    /* Take the semaphore using the FreeRTOS API. */
    if( xSemaphoreTake( ( SemaphoreHandle_t ) &internalSemaphore->xSemaphore,
                        portMAX_DELAY ) != pdTRUE )
    {
        IotLogWarn( "Failed to wait on semaphore %p.",
                    pSemaphore );

        /* There is an assert here because during debugging we could falsely 
         * believe that we are waiting successfully on a semaphore. */
        configASSERT( false );
    }
}

/*-----------------------------------------------------------*/

bool IotSemaphore_TryWait( IotSemaphore_t * pSemaphore )
{
    _IotSystemSemaphore_t * internalSemaphore = ( _IotSystemSemaphore_t * ) pSemaphore;

    configASSERT( internalSemaphore != NULL );

    IotLogDebug( "Attempting to wait on semaphore %p.", internalSemaphore );

    return IotSemaphore_TimedWait( pSemaphore, 0 );
}

/*-----------------------------------------------------------*/

bool IotSemaphore_TimedWait( IotSemaphore_t * pSemaphore,
                             uint32_t timeoutMs )
{
    _IotSystemSemaphore_t * internalSemaphore = ( _IotSystemSemaphore_t * ) pSemaphore;

    configASSERT( internalSemaphore != NULL );

    /* Take the semaphore using the FreeRTOS API. Cast the calculation to 64 bit to avoid overflows. */
    if( xSemaphoreTake( ( SemaphoreHandle_t ) &internalSemaphore->xSemaphore,
                        pdMS_TO_TICKS( timeoutMs ) ) != pdTRUE )
    {
        /* Only warn if timeout > 0. */
        if( timeoutMs > 0 )
        {
            IotLogWarn( "Timeout waiting on semaphore %p.",
                        internalSemaphore );
        }

        return false;
    }

    return true;
}

/*-----------------------------------------------------------*/

void IotSemaphore_Post( IotSemaphore_t * pSemaphore )
{
    _IotSystemSemaphore_t * internalSemaphore = ( _IotSystemSemaphore_t * ) pSemaphore;

    configASSERT( internalSemaphore != NULL );

    IotLogDebug( "Posting to semaphore %p.", internalSemaphore );
    /* Give the semaphore using the FreeRTOS API. */
    BaseType_t result = xSemaphoreGive( ( SemaphoreHandle_t ) &internalSemaphore->xSemaphore );

    if( result == pdFALSE )
    {
        IotLogDebug( "Unable to give semaphore over maximum", internalSemaphore );
    }
}

/*-----------------------------------------------------------*/
