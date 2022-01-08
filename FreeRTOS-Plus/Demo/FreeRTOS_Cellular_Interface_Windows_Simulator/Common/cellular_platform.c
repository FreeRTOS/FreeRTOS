/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://github.com/FreeRTOS
 *
 */

#include <stdbool.h>

#include "cellular_platform.h"

/*-----------------------------------------------------------*/

typedef QueueHandle_t SemaphoreHandle_t;

typedef struct threadInfo
{
    void * pArgument;                   /**< @brief Argument to `threadRoutine`. */
    void ( * threadRoutine )( void * ); /**< @brief Thread function to run. */
} threadInfo_t;

/*-----------------------------------------------------------*/

/**
 * @brief Sends provided buffer to network using transport send.
 *
 * @param[in] pArgument Argument passed to threadRoutine function.
 *
 */
static void prvThreadRoutineWrapper( void * pArgument );

/**
 * @brief Lock mutex with timeout.
 *
 * @param[in] pMutex Mutex to lock.
 * @param[in] timeout Timeout value to lock mutex.
 *
 * @return true if mutex is locked successfully. Otherwise false.
 */
static bool prIotMutexTimedLock( PlatformMutex_t * pMutex,
                                 TickType_t timeout );

/*-----------------------------------------------------------*/

static void prvThreadRoutineWrapper( void * pArgument )
{
    threadInfo_t * pThreadInfo = ( threadInfo_t * ) pArgument;

    /* Run the thread routine. */
    pThreadInfo->threadRoutine( pThreadInfo->pArgument );
    Platform_Free( pThreadInfo );

    vTaskDelete( NULL );
}

/*-----------------------------------------------------------*/

static bool prIotMutexTimedLock( PlatformMutex_t * pMutex,
                                 TickType_t timeout )
{
    BaseType_t lockResult = pdTRUE;

    configASSERT( pMutex != NULL );

    LogDebug( ( "Locking mutex %p.", pMutex ) );

    /* Call the correct FreeRTOS mutex take function based on mutex type. */
    if( pMutex->recursive == pdTRUE )
    {
        lockResult = xSemaphoreTakeRecursive( ( SemaphoreHandle_t ) &pMutex->xMutex, timeout );
    }
    else
    {
        lockResult = xSemaphoreTake( ( SemaphoreHandle_t ) &pMutex->xMutex, timeout );
    }

    return( lockResult == pdTRUE );
}

/*-----------------------------------------------------------*/

bool Platform_CreateDetachedThread( void ( * threadRoutine )( void * ),
                                    void * pArgument,
                                    int32_t priority,
                                    size_t stackSize )
{
    bool status = true;
    threadInfo_t * pThreadInfo = NULL;

    configASSERT( threadRoutine != NULL );

    LogDebug( ( "Creating new thread." ) );

    pThreadInfo = Platform_Malloc( sizeof( threadInfo_t ) );

    if( pThreadInfo == NULL )
    {
        LogDebug( ( "Unable to allocate memory for threadRoutine %p.", threadRoutine ) );
        status = false;
    }

    /* Create the FreeRTOS task that will run the thread. */
    if( status == true )
    {
        pThreadInfo->threadRoutine = threadRoutine;
        pThreadInfo->pArgument = pArgument;

        if( xTaskCreate( prvThreadRoutineWrapper,
                         "Cellular_Thread",
                         ( configSTACK_DEPTH_TYPE ) stackSize,
                         pThreadInfo,
                         priority,
                         NULL ) != pdPASS )
        {
            /* Task creation failed. */
            LogWarn( ( "Failed to create thread." ) );
            Platform_Free( pThreadInfo );
            status = false;
        }
        else
        {
            LogDebug( ( "New thread created." ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

bool PlatformMutex_Create( PlatformMutex_t * pNewMutex,
                           bool recursive )
{
    SemaphoreHandle_t xSemaphore = NULL;
    bool retMutexCreate = false;

    configASSERT( pNewMutex != NULL );

    LogDebug( ( "Creating new mutex %p.", pNewMutex ) );

    if( recursive == true )
    {
        xSemaphore = xSemaphoreCreateRecursiveMutexStatic( &pNewMutex->xMutex );
    }
    else
    {
        xSemaphore = xSemaphoreCreateMutexStatic( &pNewMutex->xMutex );
    }

    /* Remember the type of mutex. */
    if( recursive == true )
    {
        pNewMutex->recursive = pdTRUE;
    }
    else
    {
        pNewMutex->recursive = pdFALSE;
    }

    /* Check the handle value returned by the mutex create function. */
    if( xSemaphore == NULL )
    {
        retMutexCreate = false;
    }
    else
    {
        retMutexCreate = true;
    }

    return retMutexCreate;
}

/*-----------------------------------------------------------*/

void PlatformMutex_Destroy( PlatformMutex_t * pMutex )
{
    configASSERT( pMutex != NULL );

    vSemaphoreDelete( ( SemaphoreHandle_t ) &pMutex->xMutex );
}

/*-----------------------------------------------------------*/

void PlatformMutex_Lock( PlatformMutex_t * pMutex )
{
    prIotMutexTimedLock( pMutex, portMAX_DELAY );
}

/*-----------------------------------------------------------*/

bool PlatformMutex_TryLock( PlatformMutex_t * pMutex )
{
    return prIotMutexTimedLock( pMutex, 0 );
}

/*-----------------------------------------------------------*/

void PlatformMutex_Unlock( PlatformMutex_t * pMutex )
{
    configASSERT( pMutex != NULL );

    LogDebug( ( "Unlocking mutex %p.", pMutex ) );

    /* Call the correct FreeRTOS mutex unlock function based on mutex type. */
    if( pMutex->recursive == pdTRUE )
    {
        ( void ) xSemaphoreGiveRecursive( ( SemaphoreHandle_t ) &pMutex->xMutex );
    }
    else
    {
        ( void ) xSemaphoreGive( ( SemaphoreHandle_t ) &pMutex->xMutex );
    }
}

/*-----------------------------------------------------------*/
