/*
* Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of extensions.
*/
#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#define TRC_EXTENSION_BASE_EVENT_ID (TRC_EVENT_LAST_ID + 1UL)

#define TRC_EXTENSION_COMBINE_VERSION(_major, _minor, _patch) \
		( \
			((0x000000FFUL & (TraceUnsignedBaseType_t)(_major)) << 24) | \
			((0x000000FFUL & (TraceUnsignedBaseType_t)(_minor)) << 16) | \
			((0x0000FFFFUL & (TraceUnsignedBaseType_t)(_patch)) << 0) \
		)

static TraceExtensionData_t *pxExtensionData TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTraceExtensionInitialize(TraceExtensionData_t* const pxBuffer)
{
	/* This should never fail */
	TRC_ASSERT(pxBuffer != (void*)0);
	
	pxExtensionData = pxBuffer;
	
	pxExtensionData->uxNextFreeExtensionEventId = TRC_EXTENSION_BASE_EVENT_ID;
	
	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_EXTENSION);
	
	return TRC_SUCCESS;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceExtensionCreate(const char* szName, uint8_t uiMajor, uint8_t uiMinor, uint16_t uiPatch, uint32_t uiEventCount, TraceExtensionHandle_t* pxExtensionHandle)
{
	TraceObjectHandle_t xObjectHandle;
	TraceUnsignedBaseType_t uxStates[3];

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EXTENSION));

	/* This should never fail */
	TRC_ASSERT(uiEventCount != 0u);

	/* This should never fail */
	TRC_ASSERT(pxExtensionHandle != (void*)0);

	/* This should never fail */
	TRC_ASSERT(pxExtensionHandle != (void*)0);

	/* This should never fail */
	TRC_ASSERT(szName != (void*)0);

	/* This should never fail */
	TRC_ASSERT(szName[0] != (char)0); /*cstat !MISRAC2004-17.4_b We need to check the first characted*/ /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/

	uxStates[TRC_EXTENSION_STATE_INDEX_VERSION] = TRC_EXTENSION_COMBINE_VERSION(uiMajor, uiMinor, uiPatch);
	uxStates[TRC_EXTENSION_STATE_INDEX_BASE_EVENT_ID] = pxExtensionData->uxNextFreeExtensionEventId;
	uxStates[TRC_EXTENSION_STATE_INDEX_EVENT_COUNT] = uiEventCount;

	/* We need to check this */
	if (xTraceObjectRegisterInternal(PSF_EVENT_EXTENSION_CREATE, (void*)0, szName, 3u, uxStates, TRC_ENTRY_OPTION_EXTENSION, &xObjectHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	pxExtensionData->uxNextFreeExtensionEventId += uiEventCount;

	*pxExtensionHandle = (TraceExtensionHandle_t)xObjectHandle;

	return TRC_SUCCESS;
}

traceResult xTraceExtensionGetBaseEventId(TraceExtensionHandle_t xExtensionHandle, uint32_t *puiBaseEventId)
{
	TraceUnsignedBaseType_t uxBaseEventId;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EXTENSION));

	/* This should never fail */
	TRC_ASSERT(puiBaseEventId != (void*)0);
	
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetState((TraceEntryHandle_t)xExtensionHandle, TRC_EXTENSION_STATE_INDEX_BASE_EVENT_ID, &uxBaseEventId) == TRC_SUCCESS);

	*puiBaseEventId = (uint32_t)uxBaseEventId;

	return TRC_SUCCESS;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceExtensionGetConfigName(TraceExtensionHandle_t xExtensionHandle, const char **pszName)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EXTENSION));
	
	return xTraceEntryGetSymbol((TraceEntryHandle_t)xExtensionHandle, pszName);
}

#endif
