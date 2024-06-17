/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/******************************************************************************
*
* This demo is described on the following web page:
* TODO: This link describes the FAT version of this demo.
* https://www.FreeRTOS.org/FreeRTOS-Plus/Fail_Safe_File_System/Fail_Safe_Embedded_File_System_demo.shtml
*
******************************************************************************/

/* Standard includes. */
#include <stdio.h>
#include <stdint.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Priorities at which the tasks are created. */
#define mainUDP_CLI_TASK_PRIORITY    ( tskIDLE_PRIORITY )

/*-----------------------------------------------------------*/

/*
 * Register the generic commands that can be used with FreeRTOS+CLI.
 */
extern void vRegisterSampleCLICommands( void );

/*
 * Register the file system commands that can be used with FreeRTOS+CLI.
 */
extern void vRegisterFileSystemCLICommands( void );

/*
 * The task that implements the UDP command interpreter using FreeRTOS+CLI.
 */
extern void vUDPCommandInterpreterTask( void * pvParameters );

/*
 * Creates and verifies different files on the volume, demonstrating the use of
 * various different API functions.
 */
extern void vCreateAndVerifySampleFiles( void );

/*-----------------------------------------------------------*/

/* See http://www.freertos.org/FreeRTOS-Plus/Fail_Safe_File_System/Fail_Safe_Embedded_File_System_demo.shtml
 * for instructions. */

int main( void )
{
    const uint32_t ulLongTime_ms = 250UL;

    /* Initialise the drive and file system, then create a few example
     * files.  The output from this function just goes to the stdout window,
     * allowing the output to be viewed when the UDP command console is not
     * connected. */
    vCreateAndVerifySampleFiles();

    /* Register generic commands with the FreeRTOS+CLI command interpreter. */
    vRegisterSampleCLICommands();

    /* Register file system related commands with the FreeRTOS+CLI command
     * interpreter. */
    vRegisterFileSystemCLICommands();

    /* Create the task that handles the CLI on a UDP port.  The port number
     * is set using the configUDP_CLI_PORT_NUMBER setting in FreeRTOSConfig.h. */
    xTaskCreate( vUDPCommandInterpreterTask,     /* The function that implements the command interpreter IO handling. */
                 "CLI",                          /* The name of the task - just to assist debugging. */
                 configMINIMAL_STACK_SIZE, NULL, /* The size of the stack allocated to the task. */
                 mainUDP_CLI_TASK_PRIORITY,      /* The priority at which the task will run. */
                 NULL );                         /* A handle to the task is not required, so NULL is passed. */

    /* Start the RTOS scheduler. */
    vTaskStartScheduler();

    /* If all is well, the scheduler will now be running, and the following
     * line will never be reached.  If the following line does execute, then
     * there was insufficient FreeRTOS heap memory available for the idle and/or
     * timer tasks	to be created.  See the memory management section on the
     * FreeRTOS web site for more details (this is standard text that is not
     * really applicable to the Win32 simulator port). */
    for( ; ; )
    {
        Sleep( ulLongTime_ms );
    }
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
    const unsigned long ulMSToSleep = 5;

    /* This function is called on each cycle of the idle task if
     * configUSE_IDLE_HOOK is set to 1 in FreeRTOSConfig.h.  Sleep to reduce CPU
     * load. */
    Sleep( ulMSToSleep );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
    /* vApplicationMallocFailedHook() will only be called if
     * configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
     * function that will get called if a call to pvPortMalloc() fails.
     * pvPortMalloc() is called internally by the kernel whenever a task, queue,
     * timer or semaphore is created.  It is also called by various parts of the
     * demo application.  If heap_1.c, heap_2.c or heap_4.c are used, then the
     * size of the heap available to pvPortMalloc() is defined by
     * configTOTAL_HEAP_SIZE in FreeRTOSConfig.h, and the xPortGetFreeHeapSize()
     * API function can be used to query the size of free heap space that remains
     * (although it does not provide information on how the remaining heap might
     * be fragmented). */
    taskDISABLE_INTERRUPTS();

    for( ; ; )
    {
    }
}
