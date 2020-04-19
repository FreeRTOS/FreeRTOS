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
#include "tasksStubs.h"
#include "queue_datastructure.h"
#include "cbmc.h"

QueueHandle_t xMutex;

void vTaskInternalSetTimeOutState( TimeOut_t * const pxTimeOut )
{
	/* QueueSemaphoreTake might be blocked to wait for
	   another process to release a token to the semaphore.
	   This is currently not in the CBMC model. Anyhow,
	   vTaskInternalSetTimeOutState is set a timeout for
	   QueueSemaphoreTake operation. We use this to model a successful
	   release during wait time. */
	UBaseType_t bound;
	__CPROVER_assume((bound >= 0 && xMutex->uxLength >= bound));
	xMutex->uxMessagesWaiting = bound;
}

BaseType_t xTaskGetSchedulerState( void ) {
	BaseType_t ret;
	__CPROVER_assume(ret != taskSCHEDULER_SUSPENDED);
	return ret;
}

void harness() {
	uint8_t ucQueueType;
	xMutex = xQueueCreateMutex(ucQueueType);
	TickType_t xTicksToWait;

	/* Init task stub to make sure that the QueueSemaphoreTake_BOUND - 1
	   loop iteration simulates a time out */
 	vInitTaskCheckForTimeOut(0, QueueSemaphoreTake_BOUND - 1);

	if(xMutex){
		xMutex->cTxLock = PRV_UNLOCK_UNWINDING_BOUND - 1;
		xMutex->cRxLock = PRV_UNLOCK_UNWINDING_BOUND - 1;
		xMutex->uxMessagesWaiting = nondet_UBaseType_t();
		xQueueTakeMutexRecursive(xMutex, xTicksToWait);
	}
}
