/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for the stack monitor.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#if (((TRC_CFG_ENABLE_STACK_MONITOR) == 1) && ((TRC_CFG_SCHEDULING_ONLY) == 0))

typedef struct TraceStackMonitorEntry
{
	void *pvTask;
	TraceUnsignedBaseType_t uxPreviousLowWaterMark;
} TraceStackMonitorEntry_t;

typedef struct TraceStackMonitor
{
	TraceStackMonitorEntry_t xEntries[TRC_CFG_STACK_MONITOR_MAX_TASKS];

	uint32_t uiEntryCount;
} TraceStackMonitor_t;

static TraceStackMonitor_t* pxStackMonitor;

traceResult xTraceStackMonitorInitialize(TraceStackMonitorBuffer_t *pxBuffer)
{
	uint32_t i;

	TRC_ASSERT_EQUAL_SIZE(TraceStackMonitorBuffer_t, TraceStackMonitor_t);
	
	/* This should never fail */
	TRC_ASSERT(pxBuffer != 0);

	pxStackMonitor = (TraceStackMonitor_t*)pxBuffer;

	pxStackMonitor->uiEntryCount = 0;

	for (i = 0; i < (TRC_CFG_STACK_MONITOR_MAX_TASKS); i++)
	{
		pxStackMonitor->xEntries[i].pvTask = 0;
	}
	
	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_STACK_MONITOR);

	return TRC_SUCCESS;
}

traceResult xTraceStackMonitorAdd(void *pvTask)
{
	TraceUnsignedBaseType_t uxLowMark;
	
	TRACE_ALLOC_CRITICAL_SECTION();
	
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_STACK_MONITOR));

	if (pvTask == 0)
	{
		/* We don't add null addresses */
		return TRC_FAIL;
	}
	
	TRACE_ENTER_CRITICAL_SECTION();

	if (pxStackMonitor->uiEntryCount >= (TRC_CFG_STACK_MONITOR_MAX_TASKS))
	{
		xTraceDiagnosticsIncrease(TRC_DIAGNOSTICS_STACK_MONITOR_NO_SLOTS);
		
		TRACE_EXIT_CRITICAL_SECTION();
		
		return TRC_FAIL;
	}

	if (xTraceKernelPortGetUnusedStack(pvTask, &uxLowMark) == TRC_SUCCESS)
	{
		pxStackMonitor->xEntries[pxStackMonitor->uiEntryCount].pvTask = pvTask;
		pxStackMonitor->xEntries[pxStackMonitor->uiEntryCount].uxPreviousLowWaterMark = uxLowMark;

		pxStackMonitor->uiEntryCount++;
	}
	
	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_SUCCESS;
}

traceResult xTraceStackMonitorRemove(void* pvTask)
{
	uint32_t i;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_STACK_MONITOR));

	if (pvTask == 0)
	{
		/* We don't add null addresses */
		return TRC_FAIL;
	}

	TRACE_ENTER_CRITICAL_SECTION();

	for (i = 0; i < pxStackMonitor->uiEntryCount; i++)
	{
		if (pxStackMonitor->xEntries[i].pvTask == pvTask)
		{
			if (pxStackMonitor->uiEntryCount > 1 && i != (pxStackMonitor->uiEntryCount - 1))
			{
				/* There are more entries and this is NOT the last entry. Move last entry to this slot. */
				pxStackMonitor->xEntries[i].pvTask = pxStackMonitor->xEntries[pxStackMonitor->uiEntryCount - 1].pvTask;
				pxStackMonitor->xEntries[i].uxPreviousLowWaterMark = pxStackMonitor->xEntries[pxStackMonitor->uiEntryCount - 1].uxPreviousLowWaterMark;

				/* Clear old entry that was moved */
				pxStackMonitor->xEntries[pxStackMonitor->uiEntryCount - 1].pvTask = 0;
				pxStackMonitor->xEntries[pxStackMonitor->uiEntryCount - 1].uxPreviousLowWaterMark = 0;
			}
			else
			{
				/* No other entries or last entry. */
				pxStackMonitor->xEntries[i].pvTask = 0;
				pxStackMonitor->xEntries[i].uxPreviousLowWaterMark = 0;
			}

			pxStackMonitor->uiEntryCount--;

			TRACE_EXIT_CRITICAL_SECTION();

			return TRC_SUCCESS;
		}
	}

	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_FAIL;
}

traceResult xTraceStackMonitorGetAtIndex(uint32_t uiIndex, void **ppvTask, TraceUnsignedBaseType_t *puxLowWaterMark)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_STACK_MONITOR));

	/* This should never fail */
	TRC_ASSERT(ppvTask != 0);

	/* This should never fail */
	TRC_ASSERT(puxLowWaterMark != 0);

	/* This should never fail */
	TRC_ASSERT(uiIndex < (TRC_CFG_STACK_MONITOR_MAX_TASKS));

	*ppvTask = pxStackMonitor->xEntries[uiIndex].pvTask;
	*puxLowWaterMark = pxStackMonitor->xEntries[uiIndex].uxPreviousLowWaterMark;

	return TRC_SUCCESS;
}

traceResult xTraceStackMonitorReport(void)
{
	TraceUnsignedBaseType_t uxLowWaterMark;
	TraceEventHandle_t xEventHandle = 0;
	TraceStackMonitorEntry_t *pxStackMonitorEntry;
	uint32_t uiToReport;
	uint32_t i;
	static uint32_t uiCurrentIndex = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_STACK_MONITOR));
	
	TRACE_ENTER_CRITICAL_SECTION();

	/* Never report more than there are entries */
	uiToReport = TRC_CFG_STACK_MONITOR_MAX_REPORTS <= pxStackMonitor->uiEntryCount ? TRC_CFG_STACK_MONITOR_MAX_REPORTS : pxStackMonitor->uiEntryCount;

	for (i = 0; i < uiToReport; i++)
	{
		/* If uiCurrentIndex is too large, reset it */
		uiCurrentIndex = uiCurrentIndex < pxStackMonitor->uiEntryCount ? uiCurrentIndex : 0;
		
		pxStackMonitorEntry = &pxStackMonitor->xEntries[uiCurrentIndex];

		xTraceKernelPortGetUnusedStack(pxStackMonitorEntry->pvTask, &uxLowWaterMark);

		if (uxLowWaterMark < pxStackMonitorEntry->uxPreviousLowWaterMark)
		{
			pxStackMonitorEntry->uxPreviousLowWaterMark = uxLowWaterMark;
		}

		if (xTraceEventBegin(PSF_EVENT_UNUSED_STACK, sizeof(void*) + sizeof(uint32_t), &xEventHandle) == TRC_SUCCESS)
		{
			xTraceEventAddPointer(xEventHandle, pxStackMonitorEntry->pvTask);
			xTraceEventAdd32(xEventHandle, (uint32_t)pxStackMonitorEntry->uxPreviousLowWaterMark);
			xTraceEventEnd(xEventHandle);
		}

		uiCurrentIndex++;
	}

	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_SUCCESS;
}
#endif /* (((TRC_CFG_ENABLE_STACK_MONITOR) == 1) && ((TRC_CFG_SCHEDULING_ONLY) == 0)) */

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
