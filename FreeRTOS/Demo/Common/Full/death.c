/*
 * FreeRTOS V202107.00
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

/**
 * Create a single persistent task which periodically dynamically creates another
 * four tasks.  The original task is called the creator task, the four tasks it
 * creates are called suicidal tasks.
 *
 * Two of the created suicidal tasks kill one other suicidal task before killing
 * themselves - leaving just the original task remaining.
 *
 * The creator task must be spawned after all of the other demo application tasks
 * as it keeps a check on the number of tasks under the scheduler control.  The
 * number of tasks it expects to see running should never be greater than the
 * number of tasks that were in existence when the creator task was spawned, plus
 * one set of four suicidal tasks.  If this number is exceeded an error is flagged.
 *
 * \page DeathC death.c
 * \ingroup DemoFiles
 * <HR>
 */

/*
 * Changes from V2.0.0
 *
 + Delay periods are now specified using variables and constants of
 +    TickType_t rather than unsigned long.
 */

#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "death.h"
#include "print.h"

#define deathSTACK_SIZE    ( ( unsigned short ) 512 )

/* The task originally created which is responsible for periodically dynamically
 * creating another four tasks. */
static void vCreateTasks( void * pvParameters );

/* The task function of the dynamically created tasks. */
static void vSuicidalTask( void * pvParameters );

/* A variable which is incremented every time the dynamic tasks are created.  This
 * is used to check that the task is still running. */
static volatile short sCreationCount = 0;

/* Used to store the number of tasks that were originally running so the creator
 * task can tell if any of the suicidal tasks have failed to die. */
static volatile unsigned portBASE_TYPE uxTasksRunningAtStart = 0;
static const unsigned portBASE_TYPE uxMaxNumberOfExtraTasksRunning = 5;

/* Used to store a handle to the tasks that should be killed by a suicidal task,
 * before it kills itself. */
TaskHandle_t xCreatedTask1, xCreatedTask2;

/*-----------------------------------------------------------*/

void vCreateSuicidalTasks( unsigned portBASE_TYPE uxPriority )
{
    unsigned portBASE_TYPE * puxPriority;

    /* Create the Creator tasks - passing in as a parameter the priority at which
     * the suicidal tasks should be created. */
    puxPriority = ( unsigned portBASE_TYPE * ) pvPortMalloc( sizeof( unsigned portBASE_TYPE ) );
    *puxPriority = uxPriority;

    xTaskCreate( vCreateTasks, "CREATOR", deathSTACK_SIZE, ( void * ) puxPriority, uxPriority, NULL );

    /* Record the number of tasks that are running now so we know if any of the
     * suicidal tasks have failed to be killed. */
    uxTasksRunningAtStart = uxTaskGetNumberOfTasks();
}
/*-----------------------------------------------------------*/

static void vSuicidalTask( void * pvParameters )
{
    portDOUBLE d1, d2;
    TaskHandle_t xTaskToKill;
    const TickType_t xDelay = ( TickType_t ) 500 / portTICK_PERIOD_MS;

    if( pvParameters != NULL )
    {
        /* This task is periodically created four times.  Tow created tasks are
         * passed a handle to the other task so it can kill it before killing itself.
         * The other task is passed in null. */
        xTaskToKill = *( TaskHandle_t * ) pvParameters;
    }
    else
    {
        xTaskToKill = NULL;
    }

    for( ; ; )
    {
        /* Do something random just to use some stack and registers. */
        d1 = 2.4;
        d2 = 89.2;
        d2 *= d1;
        vTaskDelay( xDelay );

        if( xTaskToKill != NULL )
        {
            /* Make sure the other task has a go before we delete it. */
            vTaskDelay( ( TickType_t ) 0 );
            /* Kill the other task that was created by vCreateTasks(). */
            vTaskDelete( xTaskToKill );
            /* Kill ourselves. */
            vTaskDelete( NULL );
        }
    }
} /*lint !e818 !e550 Function prototype must be as per standard for task functions. */
/*-----------------------------------------------------------*/

static void vCreateTasks( void * pvParameters )
{
    const TickType_t xDelay = ( TickType_t ) 1000 / portTICK_PERIOD_MS;
    unsigned portBASE_TYPE uxPriority;
    const char * const pcTaskStartMsg = "Create task started.\r\n";

    /* Queue a message for printing to say the task has started. */
    vPrintDisplayMessage( &pcTaskStartMsg );

    uxPriority = *( unsigned portBASE_TYPE * ) pvParameters;
    vPortFree( pvParameters );

    for( ; ; )
    {
        /* Just loop round, delaying then creating the four suicidal tasks. */
        vTaskDelay( xDelay );

        xTaskCreate( vSuicidalTask, "SUICIDE1", deathSTACK_SIZE, NULL, uxPriority, &xCreatedTask1 );
        xTaskCreate( vSuicidalTask, "SUICIDE2", deathSTACK_SIZE, &xCreatedTask1, uxPriority, NULL );

        xTaskCreate( vSuicidalTask, "SUICIDE1", deathSTACK_SIZE, NULL, uxPriority, &xCreatedTask2 );
        xTaskCreate( vSuicidalTask, "SUICIDE2", deathSTACK_SIZE, &xCreatedTask2, uxPriority, NULL );

        ++sCreationCount;
    }
}
/*-----------------------------------------------------------*/

/* This is called to check that the creator task is still running and that there
 * are not any more than four extra tasks. */
portBASE_TYPE xIsCreateTaskStillRunning( void )
{
    static short sLastCreationCount = 0;
    short sReturn = pdTRUE;
    unsigned portBASE_TYPE uxTasksRunningNow;

    if( sLastCreationCount == sCreationCount )
    {
        sReturn = pdFALSE;
    }

    sLastCreationCount = sCreationCount;

    uxTasksRunningNow = uxTaskGetNumberOfTasks();

    if( uxTasksRunningNow < uxTasksRunningAtStart )
    {
        sReturn = pdFALSE;
    }
    else if( ( uxTasksRunningNow - uxTasksRunningAtStart ) > uxMaxNumberOfExtraTasksRunning )
    {
        sReturn = pdFALSE;
    }
    else
    {
        /* Everything is okay. */
    }

    return sReturn;
}
