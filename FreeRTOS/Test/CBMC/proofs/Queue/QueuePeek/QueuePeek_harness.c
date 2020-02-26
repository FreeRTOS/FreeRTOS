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

#ifndef LOCK_BOUND
	#define LOCK_BOUND 4
#endif

#ifndef QUEUE_PEEK_BOUND
	#define QUEUE_PEEK_BOUND 4
#endif

QueueHandle_t xQueue;


/* This method is called to initialize pxTimeOut.
   Setting up the data structure is not interesting for the proof,
   but the harness uses it to model a release
   on the queue after first check. */
void vTaskInternalSetTimeOutState( TimeOut_t * const pxTimeOut ){
	xQueue-> uxMessagesWaiting = nondet_BaseType_t();
}

void harness(){
	xQueue = xUnconstrainedQueueBoundedItemSize(10);

	//Initialise the tasksStubs
	vInitTaskCheckForTimeOut(0, QUEUE_PEEK_BOUND - 1);

	TickType_t xTicksToWait;
	if(xState == taskSCHEDULER_SUSPENDED){
		xTicksToWait = 0;
	}

	if(xQueue){
		__CPROVER_assume(xQueue->cTxLock < LOCK_BOUND - 1);
		__CPROVER_assume(xQueue->cRxLock < LOCK_BOUND - 1);

		void *pvItemToQueue = pvPortMalloc(xQueue->uxItemSize);

		/* In case malloc fails as this is otherwise an invariant violation. */
		if(!pvItemToQueue){
			xQueue->uxItemSize = 0;
		}

		xQueuePeek( xQueue, pvItemToQueue, xTicksToWait );
	}
}
