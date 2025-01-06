/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for the stack monitor.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) && ((TRC_CFG_ENABLE_STACK_MONITOR) == 1) && ((TRC_CFG_SCHEDULING_ONLY) == 0)

#ifndef TRC_CFG_ALLOW_TASK_DELETE
#define TRC_CFG_ALLOW_TASK_DELETE 1
#endif

static TraceStackMonitorData_t* pxStackMonitor TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTraceStackMonitorInitialize(TraceStackMonitorData_t *pxBuffer)
{
	uint32_t i;
	
	/* This should never fail */
	TRC_ASSERT(pxBuffer != 0);

	pxStackMonitor = pxBuffer;

	pxStackMonitor->uxEntryCount = 0;

	for (i = 0; i < (TRC_CFG_STACK_MONITOR_MAX_TASKS); i++)
	{
		pxStackMonitor->xEntries[i].pvTask = 0;
	}
	
	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_STACK_MONITOR);

	return TRC_SUCCESS;
}

traceResult xTraceStackMonitorAdd(void *pvTask)
{
	TraceUnsignedBaseType_t uxLowMark = 0;
	
	TRACE_ALLOC_CRITICAL_SECTION();
	
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_STACK_MONITOR));

	if (pvTask == 0)
	{
		/* We don't add null addresses */
		return TRC_FAIL;
	}
	
	TRACE_ENTER_CRITICAL_SECTION();

	if (pxStackMonitor->uxEntryCount >= (TRC_CFG_STACK_MONITOR_MAX_TASKS))
	{
		xTraceDiagnosticsIncrease(TRC_DIAGNOSTICS_STACK_MONITOR_NO_SLOTS);
		
		TRACE_EXIT_CRITICAL_SECTION();
		
		return TRC_FAIL;
	}

	if (xTraceKernelPortGetUnusedStack(pvTask, &uxLowMark) == TRC_SUCCESS)
	{
		pxStackMonitor->xEntries[pxStackMonitor->uxEntryCount].pvTask = pvTask;
		pxStackMonitor->xEntries[pxStackMonitor->uxEntryCount].uxPreviousLowWaterMark = uxLowMark;

		pxStackMonitor->uxEntryCount++;
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

	for (i = 0; i < pxStackMonitor->uxEntryCount; i++)
	{
		if (pxStackMonitor->xEntries[i].pvTask == pvTask)
		{
			if (pxStackMonitor->uxEntryCount > 1 && i != (pxStackMonitor->uxEntryCount - 1))
			{
				/* There are more entries and this is NOT the last entry. Move last entry to this slot. */
				pxStackMonitor->xEntries[i].pvTask = pxStackMonitor->xEntries[pxStackMonitor->uxEntryCount - 1].pvTask;
				pxStackMonitor->xEntries[i].uxPreviousLowWaterMark = pxStackMonitor->xEntries[pxStackMonitor->uxEntryCount - 1].uxPreviousLowWaterMark;

				/* Clear old entry that was moved */
				pxStackMonitor->xEntries[pxStackMonitor->uxEntryCount - 1].pvTask = 0;
				pxStackMonitor->xEntries[pxStackMonitor->uxEntryCount - 1].uxPreviousLowWaterMark = 0;
			}
			else
			{
				/* No other entries or last entry. */
				pxStackMonitor->xEntries[i].pvTask = 0;
				pxStackMonitor->xEntries[i].uxPreviousLowWaterMark = 0;
			}

			pxStackMonitor->uxEntryCount--;

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
	TraceUnsignedBaseType_t uxLowWaterMark = 0;
	TraceStackMonitorEntry_t *pxStackMonitorEntry;
	TraceUnsignedBaseType_t uxToReport;
	TraceUnsignedBaseType_t i;
	static uint32_t uiCurrentIndex = 0;

#if (TRC_CFG_ALLOW_TASK_DELETE == 1)
	TRACE_ALLOC_CRITICAL_SECTION();
#endif

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_STACK_MONITOR));

#if (TRC_CFG_ALLOW_TASK_DELETE == 1)
	TRACE_ENTER_CRITICAL_SECTION();
#endif

	/* Never report more than there are entries */
	uxToReport = TRC_CFG_STACK_MONITOR_MAX_REPORTS <= pxStackMonitor->uxEntryCount ? TRC_CFG_STACK_MONITOR_MAX_REPORTS : pxStackMonitor->uxEntryCount;

	for (i = 0; i < uxToReport; i++)
	{
		/* If uiCurrentIndex is too large, reset it */
		uiCurrentIndex = uiCurrentIndex < pxStackMonitor->uxEntryCount ? uiCurrentIndex : 0;
		
		pxStackMonitorEntry = &pxStackMonitor->xEntries[uiCurrentIndex];

		if (xTraceKernelPortGetUnusedStack(pxStackMonitorEntry->pvTask, &uxLowWaterMark) != TRC_SUCCESS)
		{
			uiCurrentIndex++;
			continue;
		}

		if (uxLowWaterMark < pxStackMonitorEntry->uxPreviousLowWaterMark)
		{
			pxStackMonitorEntry->uxPreviousLowWaterMark = uxLowWaterMark;
		}

		xTraceEventCreate2(PSF_EVENT_UNUSED_STACK, (TraceUnsignedBaseType_t)pxStackMonitorEntry->pvTask, pxStackMonitorEntry->uxPreviousLowWaterMark);

		uiCurrentIndex++;
	}

#if (TRC_CFG_ALLOW_TASK_DELETE == 1)
	TRACE_EXIT_CRITICAL_SECTION();
#endif

	return TRC_SUCCESS;
}
#endif
