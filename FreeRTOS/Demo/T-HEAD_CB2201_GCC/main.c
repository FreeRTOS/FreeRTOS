/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/* ------------------------ System includes ------------------------------- */
#include <stdlib.h>
#include <string.h>

/* ------------------------ FreeRTOS includes ----------------------------- */
#include "FreeRTOS.h"
#include "task.h"

/* ------------------------ Demo application includes --------------------- */
#include "partest.h"
#include "flash.h"
#include "integer.h"
#include "PollQ.h"
#include "comtest2.h"
#include "semtest.h"
#include "flop.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "serial.h"

/* ------------------------ Defines --------------------------------------- */
/* Constants for the ComTest tasks. */
#define mainCOM_TEST_BAUD_RATE  ( ( unsigned long ) 38400 )
#define mainCOM_TEST_LED        ( -1 )

/* Priorities for the demo application tasks. */
#define mainLED_TASK_PRIORITY       ( tskIDLE_PRIORITY + 3 )
#define mainCOM_TEST_PRIORITY       ( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY     ( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY     ( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY       ( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY        ( tskIDLE_PRIORITY + 2 )

/* Interval in which tasks are checked. */
#define mainCHECK_PERIOD            ( ( TickType_t ) 2000 / portTICK_PERIOD_MS  )

/* Constants used by the vMemCheckTask() task. */
#define mainCOUNT_INITIAL_VALUE     ( ( unsigned long ) 0 )
#define mainNO_TASK                 ( 0 )

/* The size of the memory blocks allocated by the vMemCheckTask() task. */
#define mainMEM_CHECK_SIZE_1        ( ( size_t ) 51 )
#define mainMEM_CHECK_SIZE_2        ( ( size_t ) 52 )
#define mainMEM_CHECK_SIZE_3        ( ( size_t ) 151 )

/* ------------------------ Static variables ------------------------------ */
xComPortHandle  xSTDComPort = NULL;

/* ------------------------ Static functions ------------------------------ */
static          portTASK_FUNCTION( vErrorChecks, pvParameters );
static long prvCheckOtherTasksAreStillRunning( unsigned long
                                                   ulMemCheckTaskCount );
static          portTASK_FUNCTION( vMemCheckTask, pvParameters );

/* ------------------------ Implementation -------------------------------- */
int
main( int argc, char *argv[] )
{
    asm volatile    ( "move.w  #0x2000, %sr\n\t" );

    xSTDComPort = xSerialPortInitMinimal( 38400, 8 );

    /* Start the demo/test application tasks. */
    vStartIntegerMathTasks( tskIDLE_PRIORITY );
    vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
    vStartMathTasks( tskIDLE_PRIORITY );
    vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
    vStartDynamicPriorityTasks(  );
    vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );

    /* Start the check task - which is defined in this file. */
    xTaskCreate( vErrorChecks, "Check", 512, NULL,
                 mainCHECK_TASK_PRIORITY, NULL );

    /* Now all the tasks have been started - start the scheduler. */
    vTaskStartScheduler(  );

    /* Should never get here! */
    return 0;
}



static
portTASK_FUNCTION( vErrorChecks, pvParameters )
{
    unsigned long ulMemCheckTaskRunningCount;
    TaskHandle_t     xCreatedTask;

    /* The parameters are not used in this function. */
    ( void )pvParameters;

    xSerialPortInitMinimal( mainCOM_TEST_BAUD_RATE, 8 );

    for( ;; )
    {
        ulMemCheckTaskRunningCount = mainCOUNT_INITIAL_VALUE;
        xCreatedTask = mainNO_TASK;

        if( xTaskCreate
            ( vMemCheckTask, "MEM_CHECK",
              configMINIMAL_STACK_SIZE, ( void * )&ulMemCheckTaskRunningCount,
              tskIDLE_PRIORITY, &xCreatedTask ) != pdPASS )
        {
            xSerialPutChar( xSTDComPort, 'E', portMAX_DELAY );
        }

        /* Delay until it is time to execute again. */
        vTaskDelay( mainCHECK_PERIOD );

        /* Delete the dynamically created task. */
        if( xCreatedTask != mainNO_TASK )
        {
            vTaskDelete( xCreatedTask );
        }

        if( prvCheckOtherTasksAreStillRunning( ulMemCheckTaskRunningCount ) !=
            pdPASS )
        {
            xSerialPutChar( xSTDComPort, 'E', portMAX_DELAY );
        }
        else
        {
            xSerialPutChar( xSTDComPort, '.', portMAX_DELAY );
        }
    }
}

static long
prvCheckOtherTasksAreStillRunning( unsigned long ulMemCheckTaskCount )
{
    long        lReturn = ( long ) pdPASS;

    /* Check all the demo tasks (other than the flash tasks) to ensure
     * that they are all still running, and that none of them have detected
     * an error.
     */

    if( xAreIntegerMathsTaskStillRunning(  ) != pdTRUE )
    {
        lReturn = ( long ) pdFAIL;
    }

    if( xArePollingQueuesStillRunning(  ) != pdTRUE )
    {
        lReturn = ( long ) pdFAIL;
    }

    if( xAreMathsTaskStillRunning(  ) != pdTRUE )
    {
        lReturn = ( long ) pdFAIL;
    }

    if( xAreSemaphoreTasksStillRunning(  ) != pdTRUE )
    {
        lReturn = ( long ) pdFAIL;
    }

    if( xAreDynamicPriorityTasksStillRunning(  ) != pdTRUE )
    {
        lReturn = ( long ) pdFAIL;
    }

    if( xAreBlockingQueuesStillRunning(  ) != pdTRUE )
    {
        lReturn = ( long ) pdFAIL;
    }
    if( ulMemCheckTaskCount == mainCOUNT_INITIAL_VALUE )
    {
        // The vMemCheckTask did not increment the counter - it must
        // have failed.
        lReturn = ( long ) pdFAIL;
    }
    return lReturn;
}

static void
vMemCheckTask( void *pvParameters )
{
    unsigned long *pulMemCheckTaskRunningCounter;
    void           *pvMem1, *pvMem2, *pvMem3;
    static long lErrorOccurred = pdFALSE;

    /* This task is dynamically created then deleted during each cycle of the
       vErrorChecks task to check the operation of the memory allocator.  Each time
       the task is created memory is allocated for the stack and TCB.  Each time
       the task is deleted this memory is returned to the heap.  This task itself
       exercises the allocator by allocating and freeing blocks.

       The task executes at the idle priority so does not require a delay.

       pulMemCheckTaskRunningCounter is incremented each cycle to indicate to the
       vErrorChecks() task that this task is still executing without error. */

    pulMemCheckTaskRunningCounter = ( unsigned long * )pvParameters;

    for( ;; )
    {
        if( lErrorOccurred == pdFALSE )
        {
            /* We have never seen an error so increment the counter. */
            ( *pulMemCheckTaskRunningCounter )++;
        }

        /* Allocate some memory - just to give the allocator some extra
           exercise.  This has to be in a critical section to ensure the
           task does not get deleted while it has memory allocated. */
        vTaskSuspendAll(  );
        {
            pvMem1 = pvPortMalloc( mainMEM_CHECK_SIZE_1 );
            if( pvMem1 == NULL )
            {
                lErrorOccurred = pdTRUE;
            }
            else
            {
                memset( pvMem1, 0xaa, mainMEM_CHECK_SIZE_1 );
                vPortFree( pvMem1 );
            }
        }
        xTaskResumeAll(  );

        /* Again - with a different size block. */
        vTaskSuspendAll(  );
        {
            pvMem2 = pvPortMalloc( mainMEM_CHECK_SIZE_2 );
            if( pvMem2 == NULL )
            {
                lErrorOccurred = pdTRUE;
            }
            else
            {
                memset( pvMem2, 0xaa, mainMEM_CHECK_SIZE_2 );
                vPortFree( pvMem2 );
            }
        }
        xTaskResumeAll(  );

        /* Again - with a different size block. */
        vTaskSuspendAll(  );
        {
            pvMem3 = pvPortMalloc( mainMEM_CHECK_SIZE_3 );
            if( pvMem3 == NULL )
            {
                lErrorOccurred = pdTRUE;
            }
            else
            {
                memset( pvMem3, 0xaa, mainMEM_CHECK_SIZE_3 );
                vPortFree( pvMem3 );
            }
        }
        xTaskResumeAll(  );
    }
}

void
vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
}

void
vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
}
