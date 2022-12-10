/*
 * FreeRTOS V202212.00
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

/* Standard includes. */
#include <stdio.h>
#include <time.h>

/* Visual studio intrinsics used so the __debugbreak() function is available
 * should an assert get hit. */
#include <intrin.h>

/* Windows Crypt api for uxRand() */
#include <windows.h>
#include <wincrypt.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------*/

void vAssertCalled( const char * pcFile,
                    uint32_t ulLine )
{
    volatile uint32_t ulBlockVariable = 0UL;
    volatile char * pcFileName = ( volatile char * ) pcFile;
    volatile uint32_t ulLineNumber = ulLine;

    ( void ) pcFileName;
    ( void ) ulLineNumber;

    printf( "vAssertCalled( %s, %u\n", pcFile, ulLine );

    /* Setting ulBlockVariable to a non-zero value in the debugger will allow
     * this function to be exited. */
    taskENTER_CRITICAL();
    {
        while( ulBlockVariable == 0UL )
        {
            __debugbreak();
        }
    }
    taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

UBaseType_t uxRand( void )
{
    HCRYPTPROV hProv = 0;
    BOOL xResult = 0;
    UBaseType_t uxRandNum = 0U;

    xResult = CryptAcquireContextA( &hProv, NULL, NULL, PROV_RSA_FULL, CRYPT_VERIFYCONTEXT );

    configASSERT( xResult );

    xResult = CryptGenRandom( hProv, sizeof( UBaseType_t ), ( uint8_t * ) ( &uxRandNum ) );

    configASSERT( xResult );

    CryptReleaseContext( hProv, 0 );

    return uxRandNum;
}

/*-----------------------------------------------------------*/

#if defined( configUSE_STATIC_ALLOCATION ) && ( configUSE_STATIC_ALLOCATION == 1U )
    /* configUSE_STATIC_ALLOCATION is set to 1, so the application must provide an
    * implementation of vApplicationGetIdleTaskMemory() to provide the memory that is
    * used by the Idle task. */
    void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                        StackType_t ** ppxIdleTaskStackBuffer,
                                        uint32_t * pulIdleTaskStackSize )
    {
        /* If the buffers to be provided to the Idle task are declared inside this
        * function then they must be declared static - otherwise they will be allocated on
        * the stack and so not exists after this function exits. */
        static StaticTask_t xIdleTaskTCB;
        static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

        /* Pass out a pointer to the StaticTask_t structure in which the Idle task's
        * state will be stored. */
        *ppxIdleTaskTCBBuffer = &xIdleTaskTCB;

        /* Pass out the array that will be used as the Idle task's stack. */
        *ppxIdleTaskStackBuffer = uxIdleTaskStack;

        /* Pass out the size of the array pointed to by *ppxIdleTaskStackBuffer.
        * Note that, as the array is necessarily of type StackType_t,
        * configMINIMAL_STACK_SIZE is specified in words, not bytes. */
        *pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
    }

/*-----------------------------------------------------------*/

    #if defined( configUSE_TIMERS ) && ( configUSE_TIMERS == 1U )
        /* configUSE_STATIC_ALLOCATION and configUSE_TIMERS are both set to 1, so the
        * application must provide an implementation of vApplicationGetTimerTaskMemory()
        * to provide the memory that is used by the Timer service task. */
        void vApplicationGetTimerTaskMemory( StaticTask_t ** ppxTimerTaskTCBBuffer,
                                            StackType_t ** ppxTimerTaskStackBuffer,
                                            uint32_t * pulTimerTaskStackSize )
        {
            /* If the buffers to be provided to the Timer task are declared inside this
            * function then they must be declared static - otherwise they will be allocated on
            * the stack and so not exists after this function exits. */
            static StaticTask_t xTimerTaskTCB;
            static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ];

            /* Pass out a pointer to the StaticTask_t structure in which the Timer
            * task's state will be stored. */
            *ppxTimerTaskTCBBuffer = &xTimerTaskTCB;

            /* Pass out the array that will be used as the Timer task's stack. */
            *ppxTimerTaskStackBuffer = uxTimerTaskStack;

            /* Pass out the size of the array pointed to by *ppxTimerTaskStackBuffer.
            * Note that, as the array is necessarily of type StackType_t,
            * configMINIMAL_STACK_SIZE is specified in words, not bytes. */
            *pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
        }
    #endif /*  defined( configUSE_TIMERS ) && ( configUSE_TIMERS == 1U ) */

#endif /* defined( configUSE_STATIC_ALLOCATION ) && ( configUSE_STATIC_ALLOCATION == 1U ) */

/*-----------------------------------------------------------*/

#if( configUSE_MALLOC_FAILED_HOOK == 1U )
    void vApplicationMallocFailedHook( void )
    {
        /*
         * vApplicationMallocFailedHook() will only be called if
         * configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
         * function that will get called if a call to pvPortMalloc() fails.
         * pvPortMalloc() is called internally by the kernel whenever a task, queue,
         * timer or semaphore is created.  It is also called by various parts of the
         * demo application.  If heap_1.c, heap_2.c or heap_4.c is being used, then the
         * size of the    heap available to pvPortMalloc() is defined by
         * configTOTAL_HEAP_SIZE in FreeRTOSConfig.h, and the xPortGetFreeHeapSize()
         * API function can be used to query the size of free heap space that remains
         * (although it does not provide information on how the remaining heap might be
         * fragmented).  See http://www.freertos.org/a00111.html for more
         * information.
         */
        vAssertCalled( __FILE__, __LINE__ );
    }
#endif /* configUSE_MALLOC_FAILED_HOOK == 1U */

/*-----------------------------------------------------------*/

#if( configUSE_IDLE_HOOK == 1U )
    void vApplicationIdleHook( void )
    {
        /*
         * vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
         * to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
         * task.  It is essential that code added to this hook function never attempts
         * to block in any way (for example, call xQueueReceive() with a block time
         * specified, or call vTaskDelay()).  If application tasks make use of the
         * vTaskDelete() API function to delete themselves then it is also important
         * that vApplicationIdleHook() is permitted to return to its calling function,
         * because it is the responsibility of the idle task to clean up memory
         * allocated by the kernel to any task that has since deleted itself.
         */
    }
#endif /* configUSE_IDLE_HOOK */

/*-----------------------------------------------------------*/

#if( configUSE_TICK_HOOK == 1U )
    void vApplicationTickHook( void )
    {
        /*
         * This function will be called by each tick interrupt if
         * configUSE_TICK_HOOK is set to 1 in FreeRTOSConfig.h.  User code can be
         * added here, but the tick hook is called from an interrupt context, so
         * code must not attempt to block, and only the interrupt safe FreeRTOS API
         * functions can be used (those that end in FromISR()).
         */
    }
#endif /* configUSE_TICK_HOOK == 1U */

/*-----------------------------------------------------------*/

#if( configSUPPORT_STATIC_ALLOCATION == 1U )
    /*
    * configSUPPORT_STATIC_ALLOCATION and configUSE_TIMERS are both set to 1, so the
    * application must provide an implementation of vApplicationGetTimerTaskMemory()
    * to provide the memory that is used by the Timer service task.
    */
    void vApplicationGetTimerTaskMemory( StaticTask_t **ppxTimerTaskTCBBuffer,
                                                  StackType_t **ppxTimerTaskStackBuffer,
                                                  uint32_t *pulTimerTaskStackSize )
    {
        /*
         * If the buffers to be provided to the Timer task are declared inside this
         * function then they must be declared static - otherwise they will be allocated on
         * the stack and so not exists after this function exits.
         */
        static StaticTask_t xTimerTaskTCB;
        static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ];

        /*
         * Pass out a pointer to the StaticTask_t structure in which the Timer
         * task's state will be stored.
         */
        *ppxTimerTaskTCBBuffer = &xTimerTaskTCB;

        /* Pass out the array that will be used as the Timer task's stack. */
        *ppxTimerTaskStackBuffer = uxTimerTaskStack;

        /*
         * Pass out the size of the array pointed to by *ppxTimerTaskStackBuffer.
         * Note that, as the array is necessarily of type StackType_t,
         * configMINIMAL_STACK_SIZE is specified in words, not bytes.
         */
        *pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
    }
#endif /* configSUPPORT_STATIC_ALLOCATION == 1U */

/*-----------------------------------------------------------*/

#if( configSUPPORT_STATIC_ALLOCATION == 1U )
    /*
     * configSUPPORT_STATIC_ALLOCATION is set to 1, so the application must provide an
     * implementation of vApplicationGetIdleTaskMemory() to provide the memory that is
     * used by the Idle task.
     */
    void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer,
                                                 StackType_t **ppxIdleTaskStackBuffer,
                                                 uint32_t *pulIdleTaskStackSize )
    {
        /*
         * If the buffers to be provided to the Idle task are declared inside this
         * function then they must be declared static - otherwise they will be allocated on
         * the stack and so not exists after this function exits.
         */
        static StaticTask_t xIdleTaskTCB;
        static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

        /*
         * Pass out a pointer to the StaticTask_t structure in which the Idle task's
         * state will be stored.
         */
        *ppxIdleTaskTCBBuffer = &xIdleTaskTCB;

        /* Pass out the array that will be used as the Idle task's stack. */
        *ppxIdleTaskStackBuffer = uxIdleTaskStack;

        /*
         * Pass out the size of the array pointed to by *ppxIdleTaskStackBuffer.
         * Note that, as the array is necessarily of type StackType_t,
         * configMINIMAL_STACK_SIZE is specified in words, not bytes.
         */
        *pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
    }
#endif /* configSUPPORT_STATIC_ALLOCATION == 1U  */

/*-----------------------------------------------------------*/