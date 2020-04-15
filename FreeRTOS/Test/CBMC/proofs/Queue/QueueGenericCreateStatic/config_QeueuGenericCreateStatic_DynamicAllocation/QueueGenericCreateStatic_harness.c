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
#include "queue_datastructure.h"
#include "cbmc.h"

void harness(){
    UBaseType_t uxQueueLength;
    UBaseType_t uxItemSize;

    size_t uxQueueStorageSize;
    uint8_t *pucQueueStorage = (uint8_t *) pvPortMalloc(uxQueueStorageSize);

    StaticQueue_t *pxStaticQueue =
      (StaticQueue_t *) pvPortMalloc(sizeof(StaticQueue_t));

    uint8_t ucQueueType;

    __CPROVER_assume(uxQueueStorageSize < (UINT32_MAX>>8));

    // QueueGenericReset does not check for multiplication overflow
    __CPROVER_assume(uxItemSize < uxQueueStorageSize/uxQueueLength);

    // QueueGenericCreateStatic asserts positive queue length
    __CPROVER_assume(uxQueueLength > ( UBaseType_t ) 0);

    // QueueGenericCreateStatic asserts the following equivalence
    __CPROVER_assume( ( pucQueueStorage && uxItemSize ) ||
                      ( !pucQueueStorage && !uxItemSize ) );

    // QueueGenericCreateStatic asserts nonnull pointer
    __CPROVER_assume(pxStaticQueue);

    xQueueGenericCreateStatic( uxQueueLength, uxItemSize, pucQueueStorage, pxStaticQueue, ucQueueType );
}
