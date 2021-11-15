/*
 * FreeRTOS V202111.00
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include"queue.h"

/* Interface includes. */
#include "interrupt_handler_task.h"

/**
 * @brief Time to block while waiting for a interrupt request on the interrupt queue.
 */
#define USER_IRQ_RECEIVE_TIMEOUT ( pdMS_TO_TICKS( 1000 ) )

void vInterruptHandlerTask( void * pvParams )
{
    BaseType_t xStatus;
    UserIrqRequest_t xIrqRequest;
    QueueHandle_t xInterruptQueueHandle = ( QueueHandle_t ) pvParams;

    for( ;; )
    {
        xStatus = xQueueReceive( xInterruptQueueHandle,
                                 &( xIrqRequest ),
                                 USER_IRQ_RECEIVE_TIMEOUT );
        if ( xStatus != pdTRUE )
        {
            continue;
        }

        /* If a valid IRQ request is received, invoke the corresponding handler
         * function. */
        xIrqRequest.xHandlerFunction( xIrqRequest.ulData );
    }
}
/*-----------------------------------------------------------*/
