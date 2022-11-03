/*
* Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of extensions.
*/
#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <stdio.h>

#define TRC_EXTENSION_BASE_EVENT_ID (TRC_EVENT_LAST_ID + 1)
uint32_t uiTraceNextFreeExtensionEventId = TRC_EXTENSION_BASE_EVENT_ID;

#define TRC_EXTENSION_COMBINE_VERSION(_major, _minor, _patch) \
		( \
			((0x000000FF & (_major)) << 24) | \
			((0x000000FF & (_minor)) << 16) | \
			((0x0000FFFF & (_patch)) << 0) \
		)

#define TRC_EXTENSION_STATE_INDEX_VERSION 0
#define TRC_EXTENSION_STATE_INDEX_BASE_EVENT_ID 1
#define TRC_EXTENSION_STATE_INDEX_EVENT_COUNT 2

/* TODO: INITIALIZE */

traceResult xTraceExtensionCreate(const char* szName, uint8_t uiMajor, uint8_t uiMinor, uint16_t uiPatch, uint32_t uiEventCount, TraceExtensionHandle_t* pxExtensionHandle)
{
	TraceObjectHandle_t xObjectHandle;
	TraceUnsignedBaseType_t uxStates[3];

	/* This should never fail */
	TRC_ASSERT(uiEventCount != 0);

	/* This should never fail */
	TRC_ASSERT(pxExtensionHandle != 0);

	uxStates[TRC_EXTENSION_STATE_INDEX_VERSION] = TRC_EXTENSION_COMBINE_VERSION(uiMajor, uiMinor, uiPatch);
	uxStates[TRC_EXTENSION_STATE_INDEX_BASE_EVENT_ID] = uiTraceNextFreeExtensionEventId;
	uxStates[TRC_EXTENSION_STATE_INDEX_EVENT_COUNT] = uiEventCount;

	/* We need to check this */
	if (xTraceObjectRegisterInternal(PSF_EVENT_EXTENSION_CREATE, 0, szName, 3, uxStates, TRC_ENTRY_OPTION_EXTENSION, &xObjectHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	uiTraceNextFreeExtensionEventId += uiEventCount;

	*pxExtensionHandle = (TraceExtensionHandle_t)xObjectHandle;

	return TRC_SUCCESS;
}

traceResult xTraceExtensionGetBaseEventId(TraceExtensionHandle_t xExtensionHandle, uint32_t *puiBaseEventId)
{
	TraceUnsignedBaseType_t uxBaseEventId;

	/* This should never fail */
	TRC_ASSERT(puiBaseEventId != 0);
	
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetState((TraceEntryHandle_t)xExtensionHandle, TRC_EXTENSION_STATE_INDEX_BASE_EVENT_ID, &uxBaseEventId) == TRC_SUCCESS);

	*puiBaseEventId = (uint32_t)uxBaseEventId;

	return TRC_SUCCESS;
}

traceResult xTraceExtensionGetEventId(TraceExtensionHandle_t xExtensionHandle, uint32_t uiLocalEventId, uint32_t *puiGlobalEventId)
{
	TraceUnsignedBaseType_t uxBaseEventId;

	/* This should never fail */
	TRC_ASSERT(puiGlobalEventId != 0);
	
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetState((TraceEntryHandle_t)xExtensionHandle, TRC_EXTENSION_STATE_INDEX_BASE_EVENT_ID, &uxBaseEventId) == TRC_SUCCESS);

	*puiGlobalEventId = (uint32_t)uxBaseEventId + uiLocalEventId;

	return TRC_SUCCESS;
}

traceResult xTraceExtensionGetConfigName(TraceExtensionHandle_t xExtensionHandle, const char **pszName)
{
	return xTraceEntryGetSymbol((TraceEntryHandle_t)xExtensionHandle, pszName);
}

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
