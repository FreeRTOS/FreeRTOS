/*
 * FreeRTOS memory safety proofs with CBMC.
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

#include "FreeRTOS.h"
#include "queue.h"
#include "queue_init.h"
#include "cbmc.h"

/* If the item size is not bounded, the proof does not finish in a reasonable
 *  time due to the involved memcpy commands. */
#ifndef MAX_ITEM_SIZE
    #define MAX_ITEM_SIZE    10
#endif

void harness()
{
    QueueHandle_t xQueue =
        xUnconstrainedQueueBoundedItemSize( MAX_ITEM_SIZE );

    BaseType_t * xHigherPriorityTaskWoken = pvPortMalloc( sizeof( BaseType_t ) );

    if( xQueue )
    {
        void * pvBuffer = pvPortMalloc( xQueue->uxItemSize );

        if( !pvBuffer )
        {
            xQueue->uxItemSize = 0;
        }

        xQueueReceiveFromISR( xQueue, pvBuffer, xHigherPriorityTaskWoken );
    }
}
