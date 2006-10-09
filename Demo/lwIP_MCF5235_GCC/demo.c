/*
    FreeRTOS V4.1.0 - copyright (C) 2003-2006 Richard Barry.
    MCF5235 Port - Copyright (C) 2006 Christian Walter.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    FreeRTOS is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with FreeRTOS; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    A special exception to the GPL can be applied should you wish to distribute
    a combined work that includes FreeRTOS, without being obliged to provide
    the source code for any proprietary components.  See the licensing section
    of http://www.FreeRTOS.org for full details of how and when the exception
    can be applied.

    ***************************************************************************
    See http://www.FreeRTOS.org for documentation, latest information, license
    and contact details.  Please ensure to read the configuration and relevant
    port sections of the online documentation.
    ***************************************************************************
*/

/* ------------------------ System includes ------------------------------- */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>

/* ------------------------ FreeRTOS includes ----------------------------- */
#include "FreeRTOS.h"
#include "task.h"

/* ------------------------ LWIP includes --------------------------------- */
#include "lwip/api.h"
#include "lwip/tcpip.h"
#include "lwip/memp.h"

/* ------------------------ Project includes ------------------------------ */
#include "mcf5xxx.h"
#include "mcf523x.h"
#include "serial.h"

#include "web.h"
#include "integer.h"
#include "PollQ.h"
#include "semtest.h"
#include "BlockQ.h"
#include "dynamic.h"
#include "flop.h"

/* ------------------------ Defines --------------------------------------- */
#define mainCOM_TEST_BAUD_RATE      ( ( unsigned portLONG ) 38400 )

/* Priorities for the demo application tasks. */
#define mainLED_TASK_PRIORITY       ( tskIDLE_PRIORITY + 3 )
#define mainCOM_TEST_PRIORITY       ( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY     ( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY     ( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY       ( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY        ( tskIDLE_PRIORITY + 2 )
#define mainWEB_TASK_PRIORITY       ( tskIDLE_PRIORITY + 3 )
#define STACK_DEFAULT               ( 1024 )

/* Interval in which tasks are checked. */
#define mainCHECK_PERIOD            ( ( portTickType ) 2000 / portTICK_RATE_MS  )

/* Constants used by the vMemCheckTask() task. */
#define mainCOUNT_INITIAL_VALUE     ( ( unsigned portLONG ) 0 )
#define mainNO_TASK                 ( 0 )

/* The size of the memory blocks allocated by the vMemCheckTask() task. */
#define mainMEM_CHECK_SIZE_1        ( ( size_t ) 51 )
#define mainMEM_CHECK_SIZE_2        ( ( size_t ) 52 )
#define mainMEM_CHECK_SIZE_3        ( ( size_t ) 151 )

/* ------------------------ Static variables ------------------------------ */
xComPortHandle  xSTDComPort = NULL;

/* ------------------------ Static functions ------------------------------ */
static          portTASK_FUNCTION( vErrorChecks, pvParameters );
static portLONG prvCheckOtherTasksAreStillRunning( unsigned portLONG
                                                   ulMemCheckTaskCount );
static          portTASK_FUNCTION( vMemCheckTask, pvParameters );

/* ------------------------ Implementation -------------------------------- */
int
main( int argc, char *argv[] )
{
    asm volatile    ( "move.w  #0x2000, %sr\n\t" );

    xSTDComPort = xSerialPortInitMinimal( 38400, 8 );
    vlwIPInit(  );

    /* Start the demo/test application tasks. */
    vStartIntegerMathTasks( tskIDLE_PRIORITY );
    vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
    //vStartMathTasks( tskIDLE_PRIORITY );
    vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
    vStartDynamicPriorityTasks(  );
    vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );

    /* Start the webserver. */
    ( void )sys_thread_new( vBasicWEBServer, NULL, mainWEB_TASK_PRIORITY );

    /* Start the check task - which is defined in this file. */
    xTaskCreate( vErrorChecks, ( signed portCHAR * )"Check", 512, NULL,
                 mainCHECK_TASK_PRIORITY, NULL );
        /* Now all the tasks have been started - start the scheduler. */
    vTaskStartScheduler(  );

    /* Should never get here! */
    return 0;
}

static
portTASK_FUNCTION( vErrorChecks, pvParameters )
{
    unsigned portLONG ulMemCheckTaskRunningCount;
    xTaskHandle     xCreatedTask;

    /* The parameters are not used in this function. */
    ( void )pvParameters;

    for( ;; )
    {
        ulMemCheckTaskRunningCount = mainCOUNT_INITIAL_VALUE;
        xCreatedTask = mainNO_TASK;
        if( xTaskCreate( vMemCheckTask, ( signed portCHAR * )"MEM",
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

        if( prvCheckOtherTasksAreStillRunning( ulMemCheckTaskRunningCount ) != pdPASS )
        {
            xSerialPutChar( xSTDComPort, 'E', portMAX_DELAY );
        }
        else
        {
            xSerialPutChar( xSTDComPort, '.', portMAX_DELAY );
        }
    }
}

static portLONG
prvCheckOtherTasksAreStillRunning( unsigned portLONG ulMemCheckTaskCount )
{
    portLONG        lReturn = ( portLONG ) pdPASS;

    /* Check all the demo tasks (other than the flash tasks) to ensure
     * that they are all still running, and that none of them have detected
     * an error.
     */
    if( xAreIntegerMathsTaskStillRunning(  ) != pdTRUE )
    {
        lReturn = ( portLONG ) pdFAIL;
    }

    if( xArePollingQueuesStillRunning(  ) != pdTRUE )
    {
        lReturn = ( portLONG ) pdFAIL;
    }

    if( xAreSemaphoreTasksStillRunning(  ) != pdTRUE )
    {
        lReturn = ( portLONG ) pdFAIL;
    }

    if( xAreDynamicPriorityTasksStillRunning(  ) != pdTRUE )
    {
        lReturn = ( portLONG ) pdFAIL;
    }

    if( xAreBlockingQueuesStillRunning(  ) != pdTRUE )
    {
        lReturn = ( portLONG ) pdFAIL;
    }

    if( ulMemCheckTaskCount == mainCOUNT_INITIAL_VALUE )
    {
        /* The vMemCheckTask did not increment the counter - it must
         * have failed.
         */
        lReturn = ( portLONG ) pdFAIL;
    }
    return lReturn;
}

static void
vMemCheckTask( void *pvParameters )
{
    unsigned portLONG *pulMemCheckTaskRunningCounter;
    void           *pvMem1, *pvMem2, *pvMem3;
    static portLONG lErrorOccurred = pdFALSE;

    /* This task is dynamically created then deleted during each cycle of the
       vErrorChecks task to check the operation of the memory allocator.  Each time
       the task is created memory is allocated for the stack and TCB.  Each time
       the task is deleted this memory is returned to the heap.  This task itself
       exercises the allocator by allocating and freeing blocks.

       The task executes at the idle priority so does not require a delay.

       pulMemCheckTaskRunningCounter is incremented each cycle to indicate to the
       vErrorChecks() task that this task is still executing without error. */

    pulMemCheckTaskRunningCounter = ( unsigned portLONG * )pvParameters;

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
