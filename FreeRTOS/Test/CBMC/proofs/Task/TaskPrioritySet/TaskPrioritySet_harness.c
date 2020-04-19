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

#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

BaseType_t xPrepareTaskLists( TaskHandle_t * xTask );

/*
 * We assume `uxNewPriority` to be a valid priority (avoids failed assert).
 * The harness test first calls two functions included in the tasks.c file
 * that initialize the task lists and other global variables
 */
void harness()
{
	TaskHandle_t xTask;
	UBaseType_t uxNewPriority;
	BaseType_t xTasksPrepared;

	__CPROVER_assume( uxNewPriority < configMAX_PRIORITIES );

	xTasksPrepared = xPrepareTaskLists( &xTask );

	/* Check that this second invocation of xPrepareTaskLists is needed. */
	if ( xPrepareTaskLists( &xTask ) != pdFAIL )
	{
		vTaskPrioritySet( xTask, uxNewPriority );
	}
}
