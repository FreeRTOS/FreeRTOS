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
 * https://aws.amazon.com/freertos
 * https://www.FreeRTOS.org
 */

#include "FreeRTOS.h"
#include "queue.h"
#include "queue_datastructure.h"
#include "cbmc.h"

void harness()
{
    UBaseType_t uxQueueLength;
    UBaseType_t uxItemSize;
    uint8_t ucQueueType;
    size_t storageSize;

    /* Allow CBMC to run in a reasonable amount of time. */
    __CPROVER_assume( ( uxQueueLength == QUEUE_LENGTH ) || ( uxItemSize == QUEUE_ITEM_SIZE ) );

    /* Prevent overflow in this harness. */
    __CPROVER_assume( ( uxQueueLength > 0 ) && ( ( storageSize / uxQueueLength ) == uxItemSize ) );

    uint8_t * pucQueueStorage = ( uint8_t * ) pvPortMalloc( storageSize );

    StaticQueue_t * pxStaticQueue = ( StaticQueue_t * ) pvPortMalloc( sizeof( StaticQueue_t ) );

    xQueueGenericCreateStatic( uxQueueLength, uxItemSize, pucQueueStorage, pxStaticQueue, ucQueueType );
}
