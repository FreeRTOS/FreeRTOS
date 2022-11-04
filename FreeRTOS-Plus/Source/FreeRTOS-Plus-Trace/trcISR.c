/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for ISR tagging.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

TraceISRInfo_t* pxTraceISRInfo;

traceResult xTraceISRInitialize(TraceISRInfoBuffer_t *pxBuffer)
{
	uint32_t uiCoreIndex;
	uint32_t uiStackIndex;

	TRC_ASSERT_EQUAL_SIZE(TraceISRInfoBuffer_t, TraceISRInfo_t);

	/* This should never fail */
	TRC_ASSERT(pxBuffer != 0);

	pxTraceISRInfo = (TraceISRInfo_t*)pxBuffer;

	for (uiCoreIndex = 0; uiCoreIndex < (TRC_CFG_CORE_COUNT); uiCoreIndex++)
	{
		TraceISRCoreInfo_t* pxCoreInfo = &pxTraceISRInfo->coreInfos[uiCoreIndex];

		/* Initialize ISR stack */
		for (uiStackIndex = 0; uiStackIndex < (TRC_CFG_MAX_ISR_NESTING); uiStackIndex++)
		{
			pxCoreInfo->handleStack[uiStackIndex] = 0;
		}
		
		pxCoreInfo->stackIndex = -1;
		pxCoreInfo->isPendingContextSwitch = 0;
	}
	
	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_ISR);

	return TRC_SUCCESS;
}

traceResult xTraceISRRegister(const char* szName, uint32_t uiPriority, TraceISRHandle_t *pxISRHandle)
{
	TraceEntryHandle_t xEntryHandle;
	TraceEventHandle_t xEventHandle = 0;
	uint32_t i = 0, uiLength = 0, uiValue = 0;

	/* We need to check this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ISR))
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT(pxISRHandle != 0);

	if (szName == 0)
	{
		szName = "";
	}

	/* Always save in symbol table, in case the recording has not yet started */
	/* We need to check this */
	if (xTraceEntryCreate(&xEntryHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetSymbol(xEntryHandle, szName) == TRC_SUCCESS);

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState(xEntryHandle, 0, (TraceUnsignedBaseType_t)uiPriority) == TRC_SUCCESS);

	*pxISRHandle = (TraceISRHandle_t)xEntryHandle;

	for (i = 0; (szName[i] != 0) && (i < 128); i++) {}

	uiLength = i;

	/* We need to check this */
	if (xTraceEventBegin(PSF_EVENT_DEFINE_ISR, uiLength + sizeof(void*) + sizeof(uint32_t), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddPointer(xEventHandle, (void*)xEntryHandle);
		xTraceEventAdd32(xEventHandle, uiPriority);
		xTraceEventAddData(xEventHandle, (void*)szName, uiLength);

		/* Check if we can truncate */
		xTraceEventPayloadRemaining(xEventHandle, &uiValue);
		if (uiValue > 0)
		{
			xTraceEventAdd8(xEventHandle, 0);
		}

		xTraceEventEnd(xEventHandle);
	}

	return TRC_SUCCESS;
}

traceResult xTraceISRBegin(TraceISRHandle_t xISRHandle)
{
	TraceEventHandle_t xEventHandle = 0;
	TRACE_ALLOC_CRITICAL_SECTION();

	(void)xEventHandle;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ISR));

	TRACE_ENTER_CRITICAL_SECTION();

	/* We are at the start of a possible ISR chain.
	 * No context switches should have been triggered now.
	 */
	TraceISRCoreInfo_t* pxCoreInfo = &pxTraceISRInfo->coreInfos[TRC_CFG_GET_CURRENT_CORE()];
	
	if (pxCoreInfo->stackIndex == -1)
	{
		pxCoreInfo->isPendingContextSwitch = 0;
	}

	if (pxCoreInfo->stackIndex < (TRC_CFG_MAX_ISR_NESTING) - 1)
	{
		pxCoreInfo->stackIndex++;
		pxCoreInfo->handleStack[pxCoreInfo->stackIndex] = xISRHandle;

#if (TRC_CFG_INCLUDE_ISR_TRACING == 1)
		/* We need to check this */
		if (xTraceEventBegin(PSF_EVENT_ISR_BEGIN, sizeof(void*), &xEventHandle) == TRC_SUCCESS)
		{
			xTraceEventAddPointer(xEventHandle, (void*)xISRHandle);
			xTraceEventEnd(xEventHandle);
		}
#endif
	}
	else
	{
		TRACE_EXIT_CRITICAL_SECTION();

		xTraceError(TRC_ERROR_ISR_NESTING_OVERFLOW);
		
		return TRC_FAIL;
	}

	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_SUCCESS;
}

traceResult xTraceISREnd(TraceBaseType_t xIsTaskSwitchRequired)
{
	TraceEventHandle_t xEventHandle = 0;
	TRACE_ALLOC_CRITICAL_SECTION();

	(void)xEventHandle;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ISR));

	TRACE_ENTER_CRITICAL_SECTION();
	
	TraceISRCoreInfo_t* pxCoreInfo = &pxTraceISRInfo->coreInfos[TRC_CFG_GET_CURRENT_CORE()];

	/* Is there a pending task-switch? (perhaps from an earlier ISR) */
	pxCoreInfo->isPendingContextSwitch |= xIsTaskSwitchRequired;

	if (pxCoreInfo->stackIndex > 0)
	{
		pxCoreInfo->stackIndex--;

#if (TRC_CFG_INCLUDE_ISR_TRACING == 1)
		/* Store return to interrupted ISR (if nested ISRs)*/
		/* We need to check this */
		if (xTraceEventBegin(PSF_EVENT_ISR_RESUME, sizeof(void*), &xEventHandle) == TRC_SUCCESS)
		{
			xTraceEventAddPointer(xEventHandle, (void*)pxCoreInfo->handleStack[pxCoreInfo->stackIndex]);
			xTraceEventEnd(xEventHandle);
		}
#endif
	}
	else
	{
		pxCoreInfo->stackIndex--;

		/* Store return to interrupted task, if no context switch will occur in between. */
		if ((pxCoreInfo->isPendingContextSwitch == 0) || (xTraceKernelPortIsSchedulerSuspended()))
		{
#if (TRC_CFG_INCLUDE_ISR_TRACING == 1)
			/* We need to check this */
			if (xTraceEventBegin(PSF_EVENT_TASK_ACTIVATE, sizeof(void*), &xEventHandle) == TRC_SUCCESS)
			{
				void *pvCurrentTask = 0;

				xTraceTaskGetCurrent(&pvCurrentTask);
				xTraceEventAddPointer(xEventHandle, pvCurrentTask);
				xTraceEventEnd(xEventHandle);
			}
#endif
		}
	}

	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_SUCCESS;
}

#if ((TRC_CFG_USE_TRACE_ASSERT) == 1)

traceResult xTraceISRGetCurrentNesting(int32_t* puiValue)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ISR));

	/* This should never fail */
	TRC_ASSERT(puiValue != 0);

	TraceISRCoreInfo_t* pxCoreInfo = &pxTraceISRInfo->coreInfos[TRC_CFG_GET_CURRENT_CORE()];
	*puiValue = pxCoreInfo->stackIndex;

	return TRC_SUCCESS;
}

int32_t xTraceISRGetCurrentNestingReturned(void)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ISR));

	return pxTraceISRInfo->coreInfos[TRC_CFG_GET_CURRENT_CORE()].stackIndex;
}

traceResult xTraceISRGetCurrent(TraceISRHandle_t* pxISRHandle)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ISR));

	/* This should never fail */
	TRC_ASSERT(pxISRHandle != 0);

	TraceISRCoreInfo_t* pxCoreInfo = &pxTraceISRInfo->coreInfos[TRC_CFG_GET_CURRENT_CORE()];

	if (pxCoreInfo->stackIndex < 0)
	{
		return TRC_FAIL;
	}

	*pxISRHandle = pxCoreInfo->handleStack[pxCoreInfo->stackIndex];

	return TRC_SUCCESS;
}

#endif

/* DEPRECATED */
TraceISRHandle_t xTraceSetISRProperties(const char* szName, uint32_t uiPriority)
{
	TraceISRHandle_t xISRHandle = 0;

	xTraceISRRegister(szName, uiPriority, &xISRHandle);

	return xISRHandle;
}

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
