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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/***
 * See https://www.FreeRTOS.org/pkcs11/ for configuration and usage instructions.
 ***/

/* Standard includes. */
#include <stdio.h>

/* Visual studio intrinsics used so the __debugbreak() function is available
 * should an assert get hit. */
#include <intrin.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"

/* Windows Crypto includes. */
#include <Windows.h>
#include <wincrypt.h>
#include "mbedtls/entropy.h"

/* PKCS #11 Demo includes. */
#include "demo_helpers.h"
#include "pkcs11_demo_config.h"
#include "pkcs11_demos.h"

/*
 * Private function for starting the various PKCS #11 demos.
 *
 */
static void prvStartPKCS11Demo( void )
{
    configPRINTF( ( "---------STARTING DEMO---------\r\n" ) );
    #if ( configPKCS11_MANAGEMENT_AND_RNG_DEMO == 1 )
        vPKCS11ManagementAndRNGDemo();
    #endif
    #if ( configPKCS11_MECHANISMS_AND_DIGESTS_DEMO == 1 )
        vPKCS11MechanismsAndDigestDemo();
    #endif
    #if ( configPKCS11_OBJECT_DEMO == 1 )
        vPKCS11ObjectDemo();
    #endif
    #if ( configPKCS11_SIGN_AND_VERIFY_DEMO == 1 )
        vPKCS11SignVerifyDemo();
    #endif
    configPRINTF( ( "---------Finished DEMO---------\r\n" ) );
}

/*-----------------------------------------------------------*/

int main( void )
{
    configPRINTF( ( "Creating PKCS #11 Demo Task.\r\n" ) );
    BaseType_t xReturned;
    TaskHandle_t xHandle = NULL;

    mbedtls_threading_set_alt( aws_mbedtls_mutex_init,
                               aws_mbedtls_mutex_free,
                               aws_mbedtls_mutex_lock,
                               aws_mbedtls_mutex_unlock );

    /* Create the PKCS #11 demo task. */
    xReturned = xTaskCreate(
        ( TaskFunction_t ) prvStartPKCS11Demo,
        "PKCS11 Demo",
        configPKCS11_DEMO_STACK_SIZE,
        NULL,
        tskIDLE_PRIORITY + 1,
        &xHandle );
    configASSERT( xReturned == pdPASS );

    /* Start the RTOS scheduler. */
    vTaskStartScheduler();

    /* If all is well, the scheduler will now be running, and the following
     * line will never be reached.  If the following line does execute, then
     * there was insufficient FreeRTOS heap memory available for the idle and/or
     * timer tasks to be created.  See the memory management section on the
     * FreeRTOS web site for more details (this is standard text that is not
     * really applicable to the Win32 simulator port). */
    for( ; ; )
    {
        __debugbreak();
    }
}
/*-----------------------------------------------------------*/

void vLoggingPrintf( const char *pcFormat,
					 ... )
{
va_list arg;

	va_start( arg, pcFormat );
	vprintf( pcFormat, arg );
	va_end( arg );
}
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
    taskDISABLE_INTERRUPTS();
    {
        while( ulBlockVariable == 0UL )
        {
            __debugbreak();
        }
    }
    taskENABLE_INTERRUPTS();
}
/*-----------------------------------------------------------*/

int mbedtls_hardware_poll( void * data,
                           unsigned char * output,
                           size_t len,
                           size_t * olen )
{
    int lStatus = MBEDTLS_ERR_ENTROPY_SOURCE_FAILED;
    HCRYPTPROV hProv = 0;

    /* Unferenced parameter. */
    ( void ) data;

    /*
     * This is port-specific for the Windows simulator, so just use Crypto API.
     */

    if( TRUE == CryptAcquireContextA(
            &hProv, NULL, NULL, PROV_RSA_FULL, CRYPT_VERIFYCONTEXT ) )
    {
        if( TRUE == CryptGenRandom( hProv, len, output ) )
        {
            lStatus = 0;
            *olen = len;
        }

        CryptReleaseContext( hProv, 0 );
    }

    return lStatus;
}

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
/*-----------------------------------------------------------*/
