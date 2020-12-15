/*
 * FreeRTOS V202012.00
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file iot_test_freertos.c
 * @brief Common hooks file for platforms that have not implemented hooks.
 */

#include "FreeRTOS.h"
#include "task.h"

/* It is recommended to implement hooks that use platform specific APIs. This allows
 * for better error messages and recovery. Should platform specific hooks be implemented,
 * add this macro to iot_config.h to avoid compiling these symbols.*/
#ifndef iotconfigUSE_PORT_SPECIFIC_HOOKS

/**
 * @brief Warn user if pvPortMalloc fails.
 *
 * Called if a call to pvPortMalloc() fails because there is insufficient
 * free memory available in the FreeRTOS heap.  pvPortMalloc() is called
 * internally by FreeRTOS API functions that create tasks, queues, software
 * timers, and semaphores.  The size of the FreeRTOS heap is set by the
 * configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h.
 *
 */
    void vApplicationMallocFailedHook()
    {
        configPRINT_STRING( ( "ERROR: Malloc failed to allocate memory\r\n" ) );
        taskDISABLE_INTERRUPTS();

        /* Loop forever */
        for( ; ; )
        {
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Loop forever if stack overflow is detected.
 *
 * If configCHECK_FOR_STACK_OVERFLOW is set to 1,
 * this hook provides a location for applications to
 * define a response to a stack overflow.
 *
 * Use this hook to help identify that a stack overflow
 * has occurred.
 *
 */
    void vApplicationStackOverflowHook( TaskHandle_t xTask,
                                        char * pcTaskName )
    {
        /* Disable unused parameter warnings. */
        ( void ) xTask;
        ( void ) pcTaskName;

        configPRINT_STRING( ( "ERROR: stack overflow with task \r\n" ) );
        portDISABLE_INTERRUPTS();

        /* Loop forever */
        for( ; ; )
        {
        }
    }
#endif /* iotconfigUSE_PORT_SPECIFIC_HOOKS */
