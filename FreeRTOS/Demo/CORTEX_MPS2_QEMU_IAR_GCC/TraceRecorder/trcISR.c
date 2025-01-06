/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for ISR tagging.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

TraceISRData_t* pxTraceISRData TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTraceISRInitialize(TraceISRData_t *pxBuffer)
{
	uint32_t uiCoreIndex;
	uint32_t uiStackIndex;

	/* This should never fail */
	TRC_ASSERT(pxBuffer != (void*)0);

	pxTraceISRData = pxBuffer;

	for (uiCoreIndex = 0u; uiCoreIndex < (uint32_t)(TRC_CFG_CORE_COUNT); uiCoreIndex++)
	{
		TraceISRCoreData_t* pxCoreData = &pxTraceISRData->cores[uiCoreIndex];

		/* Initialize ISR stack */
		for (uiStackIndex = 0u; uiStackIndex < (uint32_t)(TRC_CFG_MAX_ISR_NESTING); uiStackIndex++)
		{
			pxCoreData->handleStack[uiStackIndex] = 0;
		}
		
		pxCoreData->stackIndex = -1;
		pxCoreData->isPendingContextSwitch = 0u;
	}
	
	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_ISR);

	return TRC_SUCCESS;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceISRRegister(const char* szName, uint32_t uiPriority, TraceISRHandle_t *pxISRHandle)
{
	TraceEntryHandle_t xEntryHandle;
	uint32_t i, uiLength = 0u;

	/* We need to check this */
	if (xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ISR) == 0U)
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT(pxISRHandle != (void*)0);

	if (szName == (void*)0)
	{
		szName = ""; /*cstat !MISRAC2012-Rule-17.8 Suppress modified function parameter check*/
	}

	/* Always save in symbol table, in case the recording has not yet started */
	/* We need to check this */
	if (xTraceEntryCreate(&xEntryHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	for (i = 0u; (szName[i] != (char)0) && (i < 128u); i++) {} /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/

	uiLength = i;

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetSymbol(xEntryHandle, szName, uiLength) == TRC_SUCCESS);

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState(xEntryHandle, 0u, (TraceUnsignedBaseType_t)uiPriority) == TRC_SUCCESS);

	*pxISRHandle = (TraceISRHandle_t)xEntryHandle;

	return xTraceEventCreateData2(
		PSF_EVENT_DEFINE_ISR,
		(TraceUnsignedBaseType_t)xEntryHandle,
		(TraceUnsignedBaseType_t)uiPriority,
		(TraceUnsignedBaseType_t*)szName,
		uiLength + 1
	);
}

traceResult xTraceISRBegin(TraceISRHandle_t xISRHandle)
{
	TraceISRCoreData_t* pxCoreData;
	TRACE_ALLOC_CRITICAL_SECTION();

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ISR));

	TRACE_ENTER_CRITICAL_SECTION();

	/* We are at the start of a possible ISR chain.
	 * No context switches should have been triggered now.
	 */
	pxCoreData = &pxTraceISRData->cores[TRC_CFG_GET_CURRENT_CORE()];
	
	if (pxCoreData->stackIndex == -1)
	{
		pxCoreData->isPendingContextSwitch = 0u;
	}

	if (pxCoreData->stackIndex < ((TRC_CFG_MAX_ISR_NESTING) - 1))
	{
		pxCoreData->stackIndex++;
		pxCoreData->handleStack[pxCoreData->stackIndex] = xISRHandle;

#if (TRC_CFG_INCLUDE_ISR_TRACING == 1)
		(void)xTraceEventCreate1(PSF_EVENT_ISR_BEGIN, (TraceUnsignedBaseType_t)xISRHandle); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 Suppress conversion from pointer to integer check*/
#endif
	}
	else
	{
		TRACE_EXIT_CRITICAL_SECTION();

		(void)xTraceError(TRC_ERROR_ISR_NESTING_OVERFLOW);
		
		return TRC_FAIL;
	}

	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_SUCCESS;
}

traceResult xTraceISREnd(TraceBaseType_t xIsTaskSwitchRequired)
{
	TraceISRCoreData_t* pxCoreData;
	TRACE_ALLOC_CRITICAL_SECTION();

	(void)xIsTaskSwitchRequired;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ISR));

	TRACE_ENTER_CRITICAL_SECTION();
	
	pxCoreData = &pxTraceISRData->cores[TRC_CFG_GET_CURRENT_CORE()];

	pxCoreData->stackIndex--;

#if (TRC_CFG_INCLUDE_ISR_TRACING == 1)
	/* Is there a pending task-switch? (perhaps from an earlier ISR) */
	pxCoreData->isPendingContextSwitch |= (uint32_t)xIsTaskSwitchRequired;

	if (pxCoreData->stackIndex >= 0)
	{
		/* Store return to interrupted ISR (if nested ISRs)*/
		(void)xTraceEventCreate1(PSF_EVENT_ISR_RESUME, (TraceUnsignedBaseType_t)pxCoreData->handleStack[pxCoreData->stackIndex]); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 Suppress conversion from pointer to integer check*/
	}
	else
	{
		/* Store return to interrupted task, if no context switch will occur in between. */
		if ((pxCoreData->isPendingContextSwitch == 0U) || (xTraceKernelPortIsSchedulerSuspended() == 1U)) /*cstat !MISRAC2004-13.7_b For some kernel ports xTraceKernelPortIsSchedulerSuspended() will never return 1, and that is expected*/ 
		{
			(void)xTraceEventCreate1(PSF_EVENT_TASK_ACTIVATE, (TraceUnsignedBaseType_t)xTraceTaskGetCurrentReturn());  /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 !MISRAC2012-Rule-11.6 Suppress conversion from pointer to integer check*/
		}
	}
#endif

	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_SUCCESS;
}

#if ((TRC_CFG_USE_TRACE_ASSERT) == 1)

traceResult xTraceISRGetCurrentNesting(int32_t* puiValue)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ISR));

	/* This should never fail */
	TRC_ASSERT(puiValue != (void*)0);

	TraceISRCoreData_t* pxCoreData = &pxTraceISRData->cores[TRC_CFG_GET_CURRENT_CORE()];
	*puiValue = pxCoreData->stackIndex;

	return TRC_SUCCESS;
}

int32_t xTraceISRGetCurrentNestingReturned(void)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ISR));

	return pxTraceISRData->cores[TRC_CFG_GET_CURRENT_CORE()].stackIndex;
}

traceResult xTraceISRGetCurrent(TraceISRHandle_t* pxISRHandle)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ISR));

	/* This should never fail */
	TRC_ASSERT(pxISRHandle != (void*)0);

	TraceISRCoreData_t* pxCoreData = &pxTraceISRData->cores[TRC_CFG_GET_CURRENT_CORE()];

	if (pxCoreData->stackIndex < 0)
	{
		return TRC_FAIL;
	}

	*pxISRHandle = pxCoreData->handleStack[pxCoreData->stackIndex];

	return TRC_SUCCESS;
}

#endif

/* DEPRECATED */
/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
TraceISRHandle_t xTraceSetISRProperties(const char* szName, uint32_t uiPriority)
{
	TraceISRHandle_t xISRHandle = 0;

	(void)xTraceISRRegister(szName, uiPriority, &xISRHandle);

	return xISRHandle;
}

#endif
