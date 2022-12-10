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

/***
 * See https://www.FreeRTOS.org/coremqtt for configuration and usage instructions,
 * and https://www.freertos.org/mqtt/mqtt-agent-demo.html? for an alternative
 * usage model that runs MQTT in an autonomous background agent task.  See the
 * note below.
 *
 * Note: Single Threaded Vs Multi Threaded
 * There are two coreMQTT usage models, single threaded and multithreaded
 * (multitasking). Using the MQTT library solely from one thread within an
 * otherwise multi-threaded application, as the demos in these subdirectories do,
 * is equivalent to the single threaded use case. Single threaded use cases
 * require the application writer to make repeated explicit calls into the MQTT
 * library. Multithreaded use cases can instead execute the MQTT protocol in the
 * background within an agent (or daemon) task. Executing the MQTT protocol in
 * an agent task removes the need for the application writer to explicitly
 * manage any MQTT state or call the MQTT_ProcessLoop() API function. Using an
 * agent task also enables multiple application tasks to share a single MQTT
 * connection without the need for synchronization primitives such as mutexes.
 ***/

/* Standard includes. */
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo logging includes. */
#include "logging.h"

/* Demo Specific configs. */
#include "demo_config.h"

/*-----------------------------------------------------------*/

extern void vPlatformInitIpStack( void );
extern void vStartSimpleMQTTDemo( void );

/*-----------------------------------------------------------*/

int main( void )
{
    /* Initialize logging */
    vPlatformInitLogging();

    /* Start demo task */
    vStartSimpleMQTTDemo();

    /* Initialize FreeRTOS+TCP */
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
