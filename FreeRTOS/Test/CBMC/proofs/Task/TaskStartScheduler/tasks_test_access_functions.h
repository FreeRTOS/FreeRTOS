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

#include "cbmc.h"

/*
 * We allocate an unconstrained TCB or return NULL if it fails
 */
TaskHandle_t xUnconstrainedTCB( void )
{
	TCB_t * pxTCB = pvPortMalloc(sizeof(TCB_t));

	if ( pxTCB == NULL )
		return NULL;

	return pxTCB;
}

StaticTask_t *pxIdleTaskTCB;
StaticTask_t *pxTimerTaskTCB;
StackType_t  *pxIdleTaskStack;
StackType_t  *pxTimerTaskStack;

/*
 * `pxCurrentTCB` allocation is allowed to fail. The global variables above
 * this comment are used in the stubbed functions `vApplicationGetIdleTaskMemory`
 * and `vApplicationGetTimerTaskMemory` (at the end of this file) and buffer allocation
 * must be succesful for the proof to have no errors
 */
BaseType_t xPrepareTasks( void )
{
	__CPROVER_assert_zero_allocation();

	prvInitialiseTaskLists();

	pxCurrentTCB = xUnconstrainedTCB();

	pxIdleTaskTCB = pvPortMalloc(sizeof(StaticTask_t));
	if (pxIdleTaskTCB == NULL )
	{
		return pdFAIL;
	}

	pxIdleTaskStack = pvPortMalloc( sizeof(StackType_t) * configMINIMAL_STACK_SIZE );
	if ( pxIdleTaskStack == NULL )
	{
		return pdFAIL;
	}

	pxTimerTaskTCB = pvPortMalloc( sizeof(StaticTask_t) );
	if ( pxTimerTaskTCB == NULL )
	{
		return pdFAIL;
	}

	pxTimerTaskStack = pvPortMalloc( sizeof(StackType_t) * configTIMER_TASK_STACK_DEPTH );
	if ( pxTimerTaskStack == NULL )
	{
		return pdFAIL;
	}

	return pdPASS;
}

/*
 * The buffers used here have been succesfully allocated before (global variables)
 */
void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                    StackType_t ** ppxIdleTaskStackBuffer,
                                    uint32_t * pulIdleTaskStackSize )
{
	*ppxIdleTaskTCBBuffer = pxIdleTaskTCB;
	*ppxIdleTaskStackBuffer = pxIdleTaskStack;
    *pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
}

/*
 * The buffers used here have been succesfully allocated before (global variables)
 */
void vApplicationGetTimerTaskMemory( StaticTask_t **ppxTimerTaskTCBBuffer, StackType_t **ppxTimerTaskStackBuffer, uint32_t *pulTimerTaskStackSize )
{
	*ppxTimerTaskTCBBuffer = pxTimerTaskTCB;
	*ppxTimerTaskStackBuffer = pxTimerTaskStack;
	*pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
}
