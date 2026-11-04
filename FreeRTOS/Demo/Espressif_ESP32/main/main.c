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

/*
 * Common/Minimal demo entry point on Espressif targets.
 */

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

#include "esp_log.h"

static const char * TAG = "freertos_demo";

/* Set after main_full() finishes wiring the demo so the tick hook does
 * not dispatch ISR-side exercises before their queues / timers exist. */
static volatile BaseType_t xDemoReady = pdFALSE;

extern void main_full( void );
extern void vFullDemoIdleFunction( void );
extern void vFullDemoTickHookFunction( void );

/* Runs the idle-side helper exactly once (mutex registry round-trip)
 * then self-deletes.  Lives in its own task pinned to Core 0 because
 * vApplicationIdleHook can fire concurrently on either core, which
 * races on the singleton state vFullDemoIdleFunction touches. */
static void prvIdleHelperTask( void * pvParameters )
{
    ( void ) pvParameters;

    vFullDemoIdleFunction();
    vTaskDelete( NULL );
}

void app_main( void )
{
    ESP_LOGI( TAG, "Common/Minimal demo" );
    ESP_LOGI( TAG, "  configNUMBER_OF_CORES = %d", configNUMBER_OF_CORES );
    ESP_LOGI( TAG, "  configUSE_PREEMPTION  = %d", configUSE_PREEMPTION );
    ESP_LOGI( TAG, "  configMAX_PRIORITIES  = %d", configMAX_PRIORITIES );
    ESP_LOGI( TAG, "  configRUN_MULTIPLE_PRIORITIES = %d", configRUN_MULTIPLE_PRIORITIES );

    main_full();

    xDemoReady = pdTRUE;

    xTaskCreatePinnedToCore( prvIdleHelperTask,
                             "IdleHelper",
                             configMINIMAL_STACK_SIZE * 2,
                             NULL,
                             tskIDLE_PRIORITY + 1,
                             NULL,
                             0 );
}

/* Tick hook fires from each core's SysTick; restrict to Core 0 so the
 * single-threaded ISR exercises don't race on shared state. */
void vApplicationTickHook( void )
{
    if( ( xDemoReady == pdTRUE ) && ( xPortGetCoreID() == 0 ) )
    {
        vFullDemoTickHookFunction();
    }
}

/* Idle-time work runs from prvIdleHelperTask (Core-0 pinned) instead of
 * here; leave the hook empty so configUSE_IDLE_HOOK is satisfied. */
void vApplicationIdleHook( void )
{
}
