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
 * @file iot_clock_freertos.c
 * @brief Implementation of the platform specific functions in iot_clock.h for 
 * FreeRTOS.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdio.h>

/* Platform clock include. */
#include "platform/iot_platform_types_freertos.h"
#include "platform/iot_clock.h"
#include "task.h"

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

#define LIBRARY_LOG_NAME    ( "CLOCK" )
#include "iot_logging_setup.h"

/*-----------------------------------------------------------*/

/*
 * Time conversion constants.
 */
#define _MILLISECONDS_PER_SECOND    ( 1000 )                                          /**< @brief Milliseconds per second. */
#define _MILLISECONDS_PER_TICK      ( _MILLISECONDS_PER_SECOND / configTICK_RATE_HZ ) /**< Milliseconds per FreeRTOS tick. */

/*-----------------------------------------------------------*/

/*  Private Callback function for timer expiry, delegate work to a Task to free
 *  up the timer task for managing other timers */
static void prvTimerCallback( TimerHandle_t xTimerHandle )
{
    _IotSystemTimer_t * pxTimer = ( _IotSystemTimer_t * ) pvTimerGetTimerID( xTimerHandle );

    /* The value of the timer ID, set in timer_create, should not be NULL. */
    configASSERT( pxTimer != NULL );

    /* Restart the timer if it is periodic. */
    if( pxTimer->xTimerPeriod > 0 )
    {
        xTimerChangePeriod( xTimerHandle, pxTimer->xTimerPeriod, 0 );
    }

    /* Call timer Callback from this task */
    pxTimer->threadRoutine( ( void * ) pxTimer->pArgument );
}

/*-----------------------------------------------------------*/

bool IotClock_GetTimestring( char * pBuffer,
                             size_t bufferSize,
                             size_t * pTimestringLength )
{
    uint64_t milliSeconds = IotClock_GetTimeMs();
    int timestringLength = 0;

    configASSERT( pBuffer != NULL );
    configASSERT( pTimestringLength != NULL );

    /* Convert the localTime struct to a string. */
    timestringLength = snprintf( pBuffer, bufferSize, "%llu", milliSeconds );

    /* Check for error from no string */
    if( timestringLength == 0 )
    {
        return false;
    }

    /* Set the output parameter. */
    *pTimestringLength = timestringLength;

    return true;
}

/*-----------------------------------------------------------*/

uint64_t IotClock_GetTimeMs( void )
{
    TimeOut_t xCurrentTime = { 0 };

    /* This must be unsigned because the behavior of signed integer overflow is undefined. */
    uint64_t ullTickCount = 0ULL;

    /* Get the current tick count and overflow count. vTaskSetTimeOutState()
     * is used to get these values because they are both static in tasks.c. */
    vTaskSetTimeOutState( &xCurrentTime );

    /* Adjust the tick count for the number of times a TickType_t has overflowed. */
    ullTickCount = ( uint64_t ) ( xCurrentTime.xOverflowCount ) << ( sizeof( TickType_t ) * 8 );

    /* Add the current tick count. */
    ullTickCount += xCurrentTime.xTimeOnEntering;

    /* Return the ticks converted to Milliseconds */
    return ullTickCount * _MILLISECONDS_PER_TICK;
}
/*-----------------------------------------------------------*/

void IotClock_SleepMs( uint32_t sleepTimeMs )
{
    vTaskDelay( pdMS_TO_TICKS( sleepTimeMs ) );
}

/*-----------------------------------------------------------*/

bool IotClock_TimerCreate( IotTimer_t * pNewTimer,
                           IotThreadRoutine_t expirationRoutine,
                           void * pArgument )
{
    _IotSystemTimer_t * pxTimer = ( _IotSystemTimer_t * ) pNewTimer;

    configASSERT( pNewTimer != NULL );
    configASSERT( expirationRoutine != NULL );

    IotLogDebug( "Creating new timer %p.", pNewTimer );

    /* Set the timer expiration routine, argument and period */
    pxTimer->threadRoutine = expirationRoutine;
    pxTimer->pArgument = pArgument;
    pxTimer->xTimerPeriod = 0;

    /* Create a new FreeRTOS timer. This call will not fail because the
     * memory for it has already been allocated, so the output parameter is
     * also set. */
    pxTimer->timer = ( TimerHandle_t ) xTimerCreateStatic( "timer",                  /* Timer name. */
                                                           portMAX_DELAY,            /* Initial timer period. Timers are created disarmed. */
                                                           pdFALSE,                  /* Don't auto-reload timer. */
                                                           ( void * ) pxTimer,       /* Timer id. */
                                                           prvTimerCallback,         /* Timer expiration callback. */
                                                           &pxTimer->xTimerBuffer ); /* Pre-allocated memory for timer. */

    return true;
}

/*-----------------------------------------------------------*/

void IotClock_TimerDestroy( IotTimer_t * pTimer )
{
    _IotSystemTimer_t * pTimerInfo = ( _IotSystemTimer_t * ) pTimer;

    configASSERT( pTimerInfo != NULL );
    configASSERT( pTimerInfo->timer != NULL );

    IotLogDebug( "Destroying timer %p.", pTimer );

    if( xTimerIsTimerActive( pTimerInfo->timer ) == pdTRUE )
    {
        /* Stop the FreeRTOS timer. Because the timer is statically allocated, no call
         * to xTimerDelete is necessary. The timer is stopped so that it's not referenced
         * anywhere. xTimerStop will not fail when it has unlimited block time. */
        ( void ) xTimerStop( pTimerInfo->timer, portMAX_DELAY );

        /* Wait until the timer stop command is processed. */
        while( xTimerIsTimerActive( pTimerInfo->timer ) == pdTRUE )
        {
            vTaskDelay( 1 );
        }
    }
}

/*-----------------------------------------------------------*/

bool IotClock_TimerArm( IotTimer_t * pTimer,
                        uint32_t relativeTimeoutMs,
                        uint32_t periodMs )
{
    _IotSystemTimer_t * pTimerInfo = ( _IotSystemTimer_t * ) pTimer;

    configASSERT( pTimerInfo != NULL );

    TimerHandle_t xTimerHandle = pTimerInfo->timer;

    IotLogDebug( "Arming timer %p with timeout %llu and period %llu.",
                 pTimer,
                 relativeTimeoutMs,
                 periodMs );

    /* Set the timer period in ticks */
    pTimerInfo->xTimerPeriod = pdMS_TO_TICKS( periodMs );

    /* Set the timer to expire after relativeTimeoutMs, and restart it. */
    ( void ) xTimerChangePeriod( xTimerHandle, pdMS_TO_TICKS( relativeTimeoutMs ), portMAX_DELAY );

    return true;
}

/*-----------------------------------------------------------*/
