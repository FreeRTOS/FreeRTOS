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

/***
 * See https://www.FreeRTOS.org/pkcs11/ for configuration and usage instructions.
 ***/

/* Standard includes. */
#include <stdio.h>

/* Visual studio intrinsics used so the __debugbreak() function is available
 * should an assert get hit. */
#include <intrin.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Windows Crypto includes. */
#include <Windows.h>
#include <wincrypt.h>
#include "mbedtls/entropy.h"

/* PKCS #11 Demo includes. */
#include "demo_helpers.h"
#include "pkcs11_demo_config.h"
#include "pkcs11_demos.h"

/*-----------------------------------------------------------*/

extern void vPlatformInitLogging( void );
extern void vPlatformStopLoggingThreadAndFlush( void );

/*-----------------------------------------------------------*/

static void prvPKCS11DemoTask( void * pvParameters )
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

    vPlatformStopLoggingThreadAndFlush();
    exit( 0 );
}

/*-----------------------------------------------------------*/

int main( void )
{
    vPlatformInitLogging();

    /* Create the SNTP client task that is responsible for synchronizing system time with the time servers
     * periodically. This is created as a high priority task to keep the SNTP client operation unhindered. */
    xTaskCreate( prvPKCS11DemoTask,            /* Function that implements the task. */
                 "PKCS11 Demo",                /* Text name for the task - only used for debugging. */
                 configPKCS11_DEMO_STACK_SIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                         /* Task parameter - not used in this case. */
                 configMAX_PRIORITIES - 1,     /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 NULL );

    /* Start the RTOS scheduler. */
    vTaskStartScheduler();

    /* If all is well, the scheduler will now be running, and the following
     * line will never be reached.  If the following line does execute, then
     * there was insufficient FreeRTOS heap memory available for the idle and/or
     * timer tasks to be created.  See the memory management section on the
     * FreeRTOS web site for more details.
     */

    for( ; ; )
    {
        configASSERT( pdFALSE );
    }
}

/*-----------------------------------------------------------*/
