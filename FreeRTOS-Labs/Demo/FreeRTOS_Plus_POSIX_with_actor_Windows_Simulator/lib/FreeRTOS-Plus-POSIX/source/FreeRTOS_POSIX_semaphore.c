/*
 * Amazon FreeRTOS POSIX V1.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file FreeRTOS_POSIX_semaphore.c
 * @brief Implementation of functions in semaphore.h
 */

/* C standard library includes. */
#include <stddef.h>

/* FreeRTOS+POSIX includes. */
#include "FreeRTOS_POSIX.h"
#include "FreeRTOS_POSIX/errno.h"
#include "FreeRTOS_POSIX/semaphore.h"
#include "FreeRTOS_POSIX/utils.h"

#include "atomic.h"


/*-----------------------------------------------------------*/

int sem_destroy( sem_t * sem )
{
    sem_internal_t * pxSem = ( sem_internal_t * ) ( sem );

    /* Free the resources in use by the semaphore. */
    vSemaphoreDelete( ( SemaphoreHandle_t ) &pxSem->xSemaphore );

    return 0;
}

/*-----------------------------------------------------------*/

int sem_getvalue( sem_t * sem,
                  int * sval )
{
    sem_internal_t * pxSem = ( sem_internal_t * ) ( sem );

    /* Get value does not need atomic operation, since -- Open Group
     * states "the updated value represents an actual semaphore value that
     * occurred at some unspecified time during the call, but it need not be the
     * actual value of the semaphore when it is returned to the calling process."
     */
    *sval = pxSem->value;

    return 0;
}

/*-----------------------------------------------------------*/

int sem_init( sem_t * sem,
              int pshared,
              unsigned value )
{
    int iStatus = 0;
    sem_internal_t * pxSem = ( sem_internal_t * ) ( sem );

    /* Silence warnings about unused parameters. */
    ( void ) pshared;

    /* Check value parameter. */
    if( value > SEM_VALUE_MAX )
    {
        errno = EINVAL;
        iStatus = -1;
    }

    /* value is guaranteed to not exceed INT32_MAX, which is the default value of SEM_VALUE_MAX (0x7FFFU). */
    pxSem->value = ( int ) value;

    /* Create the FreeRTOS semaphore.
     * This is only used to queue threads when no semaphore is available.
     * Initializing with semaphore initial count zero.
     * This call will not fail because the memory for the semaphore has already been allocated.
     */
    if( iStatus == 0 )
    {
        ( void ) xSemaphoreCreateCountingStatic( SEM_VALUE_MAX, 0, &pxSem->xSemaphore );
    }

    return iStatus;
}

/*-----------------------------------------------------------*/

int sem_post( sem_t * sem )
{
    sem_internal_t * pxSem = ( sem_internal_t * ) ( sem );

    int iPreviouValue = Atomic_Increment_u32( ( uint32_t * ) &pxSem->value );

    /* If previous semaphore value is equal or larger than zero, there is no
     * thread waiting for this semaphore. Otherwise (<0), call FreeRTOS interface
     * to wake up a thread. */
    if( iPreviouValue < 0 )
    {
        /* Give the semaphore using the FreeRTOS API. */
        ( void ) xSemaphoreGive( ( SemaphoreHandle_t ) &pxSem->xSemaphore );
    }

    return 0;
}

/*-----------------------------------------------------------*/

int sem_timedwait( sem_t * sem,
                   const struct timespec * abstime )
{
    int iStatus = 0;
    sem_internal_t * pxSem = ( sem_internal_t * ) ( sem );
    TickType_t xDelay = portMAX_DELAY;

    if( abstime != NULL )
    {
        /* If the provided timespec is invalid, still attempt to take the
         * semaphore without blocking, per POSIX spec. */
        if( UTILS_ValidateTimespec( abstime ) == false )
        {
            xDelay = 0;
            iStatus = EINVAL;
        }
        else
        {
            struct timespec xCurrentTime = { 0 };

            /* Get current time */
            if( clock_gettime( CLOCK_REALTIME, &xCurrentTime ) != 0 )
            {
                iStatus = EINVAL;
            }
            else
            {
                iStatus = UTILS_AbsoluteTimespecToDeltaTicks( abstime, &xCurrentTime, &xDelay );
            }

            /* If abstime was in the past, still attempt to take the semaphore without
             * blocking, per POSIX spec. */
            if( iStatus == ETIMEDOUT )
            {
                xDelay = 0;
            }
        }
    }

    int iPreviousValue = Atomic_Decrement_u32( ( uint32_t * ) &pxSem->value );

    /* If previous semaphore value is larger than zero, the thread entering this function call
     * can take the semaphore without yielding. Else (<=0), calling into FreeRTOS API to yield.
     */
    if( iPreviousValue > 0 )
    {
        /* Under no circumstance shall the function fail with a timeout if the semaphore can be locked immediately. */
        iStatus = 0;
    }
    else
    {
        /* Take the semaphore using the FreeRTOS API. */
        if( xSemaphoreTake( ( SemaphoreHandle_t ) &pxSem->xSemaphore,
                            xDelay ) != pdTRUE )
        {
            if( iStatus == 0 )
            {
                errno = ETIMEDOUT;
            }
            else
            {
                errno = iStatus;
            }

            iStatus = -1;
        }
        else
        {
            iStatus = 0;
        }
    }

    return iStatus;
}

/*-----------------------------------------------------------*/

int sem_trywait( sem_t * sem )
{
    int iStatus = 0;

    /* Setting an absolute timeout of 0 (i.e. in the past) will cause sem_timedwait
     * to not block. */
    struct timespec xTimeout = { 0 };

    iStatus = sem_timedwait( sem, &xTimeout );

    /* POSIX specifies that this function should set errno to EAGAIN and not
     * ETIMEDOUT. */
    if( ( iStatus == -1 ) && ( errno == ETIMEDOUT ) )
    {
        errno = EAGAIN;
    }

    return iStatus;
}

/*-----------------------------------------------------------*/

int sem_wait( sem_t * sem )
{
    return sem_timedwait( sem, NULL );
}

/*-----------------------------------------------------------*/
