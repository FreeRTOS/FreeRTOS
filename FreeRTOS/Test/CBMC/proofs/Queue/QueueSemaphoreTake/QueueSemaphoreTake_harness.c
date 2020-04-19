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
#include "tasksStubs.h"
#include "cbmc.h"

BaseType_t state;
QueueHandle_t xQueue;
BaseType_t counter;

BaseType_t xTaskGetSchedulerState(void)
{
	return state;
}

void vTaskInternalSetTimeOutState( TimeOut_t * const pxTimeOut )
{
	/* QueueSemaphoreTake might be blocked to wait for
	   another process to release a token to the semaphore.
	   This is currently not in the CBMC model. Anyhow,
	   vTaskInternalSetTimeOutState is set a timeout for
	   QueueSemaphoreTake operation. We use this to model a successful
	   release during wait time. */
	UBaseType_t bound;
	__CPROVER_assume((bound >= 0 && xQueue->uxLength >= bound));
	xQueue->uxMessagesWaiting = bound;
}

void harness()
{
	/* Init task stub to make sure that the third loop iteration
	simulates a time out */
	vInitTaskCheckForTimeOut(0, 3);

	xQueue = xUnconstrainedMutex();
	TickType_t xTicksToWait;

	if(state == taskSCHEDULER_SUSPENDED){
		xTicksToWait = 0;
	}
	if (xQueue) {
		/* Bounding the loop in prvUnlockQueue to
		   PRV_UNLOCK_QUEUE_BOUND. As the loop is not relevant
		   in this proof the value might be set to any
		   positive 8-bit integer value. We subtract one,
		   because the bound must be one greater than the
		   amount of loop iterations. */
		__CPROVER_assert(PRV_UNLOCK_QUEUE_BOUND > 0, "Make sure, a valid macro value is chosen.");
		xQueue->cTxLock = PRV_UNLOCK_QUEUE_BOUND - 1;
		xQueue->cRxLock = PRV_UNLOCK_QUEUE_BOUND - 1;
		((&(xQueue->xTasksWaitingToReceive))->xListEnd).pxNext->xItemValue = nondet_ticktype();

		/* This assumptions is required to prevent an overflow in l. 2057 of queue.c
		   in the prvGetDisinheritPriorityAfterTimeout() function. */
		__CPROVER_assume( (
		  ( UBaseType_t ) listGET_ITEM_VALUE_OF_HEAD_ENTRY( &( xQueue->xTasksWaitingToReceive ) )
		   <= ( ( UBaseType_t ) configMAX_PRIORITIES)));
		xQueueSemaphoreTake(xQueue, xTicksToWait);
	}
}
