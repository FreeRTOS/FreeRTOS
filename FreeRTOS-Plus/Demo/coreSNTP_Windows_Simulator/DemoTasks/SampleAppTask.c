/*
 * FreeRTOS V202112.00
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/*
 * This file belongs to the demo for showing use of the coreSNTP library for synchronizing
 * system time with internet time and maintaining correct wall-clock time.
 *
 * This file shows how an application task can query Coordinated Universal Time (UTC) from system,
 * that is maintained and synchronized periodically in the SNTP client (daemon) task of the demo
 * project. Refer to the the SNTPClientTask.c file in this project for the SNTP client task.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>
#include <stdint.h>
#include <time.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "common_demo_include.h"

/*-----------------------------------------------------------*/

/**
 * @brief The periodicity of the application task in query and logging system time. This is the time
 * interval between consecutive system clock time queries in the sample application task.
 */
#define CLOCK_QUERY_TASK_DELAY_MS    ( 1000 )

/*-----------------------------------------------------------*/

void printTime( const UTCTime_t * pUnixTime )
{
    struct tm * currTime;
    time_t time;

    /* Obtain the broken-down UTC representation of the current system time. */
    time = pUnixTime->secs;
    currTime = gmtime( &time );

    /* Log the time as both UNIX timestamp and Human Readable time. */
    LogInfo( ( "Time:\nUNIX=%lusecs %lums\nHuman Readable=%lu-%02lu-%02lu %02luh:%02lum:%02lus",
               pUnixTime->secs, pUnixTime->msecs,
               currTime->tm_year + 1900, currTime->tm_mon + 1, currTime->tm_mday,
               currTime->tm_hour, currTime->tm_min, currTime->tm_sec ) );
}

/*************************************************************************************/

/* Sample application task that will query and log system time every second. */
void sampleAppTask( void * pvParameters )
{
    UTCTime_t systemTime;

    while( 1 )
    {
        systemGetWallClockTime( &systemTime );

        printTime( &systemTime );

        vTaskDelay( pdMS_TO_TICKS( CLOCK_QUERY_TASK_DELAY_MS ) );
    }
}

/*-----------------------------------------------------------*/
