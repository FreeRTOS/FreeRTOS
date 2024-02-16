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
 * See https://www.FreeRTOS.org/iot-device-defender for configuration and usage instructions.
 ***/

/* Standard includes. */
#include <stdio.h>
#include <time.h>
#include <stdint.h>

/* Visual studio intrinsics used so the __debugbreak() function is available
 * should an assert get hit. */
#include <intrin.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* TCP/IP stack includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Demo logging includes. */
#include "logging.h"

/* Demo Specific configs. */
#include "demo_config.h"

/**
 * @brief The task used to demonstrate the Defender API.
 *
 * This task collects metrics from the device using the functions in
 * metrics_collector.h and uses them to build a defender report using functions
 * in report_builder.h. Metrics include the number for bytes written and read
 * over the network, open TCP and UDP ports, and open TCP sockets. The
 * generated report is then published to the AWS IoT Device Defender service.
 *
 * @param[in] pvParameters Parameters as passed at the time of task creation.
 * Not used in this example.
 */
void prvDefenderDemoTask( void * pvParameters );

extern void vPlatformInitIpStack( void );

/*-----------------------------------------------------------*/

int main( void )
{
    vPlatformInitLogging();

    /*
     * This example uses a single application task, which shows that how to use
     * Device Defender library to generate and validate AWS IoT Device Defender
     * MQTT topics, and use the coreMQTT library to communicate with the AWS
     * IoT Device Defender service.
     */
    xTaskCreate( prvDefenderDemoTask,      /* Function that implements the task. */
                 "DemoTask",               /* Text name for the task - only used for debugging. */
                 democonfigDEMO_STACKSIZE, /* Size of stack (in words, not bytes) to allocate for the task. */
                 NULL,                     /* Task parameter - not used in this case. */
                 tskIDLE_PRIORITY,         /* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
                 NULL );                   /* Used to pass out a handle to the created task - not used in this case. */

    /* Initialize the FreeRTOS+TCP Stack */
    vPlatformInitIpStack();

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
