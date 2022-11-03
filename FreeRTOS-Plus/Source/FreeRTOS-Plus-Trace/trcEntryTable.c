/*
* Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of the entry table.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#define VALIDATE_ENTRY_HANDLE(xEntryHandle) ((((TraceUnsignedBaseType_t)(xEntryHandle) >= (TraceUnsignedBaseType_t)pxEntryTable) && ((TraceUnsignedBaseType_t)(xEntryHandle) < ((TraceUnsignedBaseType_t)pxEntryTable + sizeof(TraceEntryTable_t)))))

#define GIVE_ENTRY_INDEX(xIndex) xIndexTable.axFreeIndexes[xIndexTable.uiFreeIndexCount] = (xIndex); xIndexTable.uiFreeIndexCount++

#define GET_FREE_INDEX_COUNT() xIndexTable.uiFreeIndexCount

#define CALCULATE_ENTRY_INDEX(xEntryHandle) (TraceEntryIndex_t)(((TraceUnsignedBaseType_t)((TraceUnsignedBaseType_t)(xEntryHandle) - (TraceUnsignedBaseType_t)pxEntryTable) / sizeof(TraceEntry_t)))

#if (TRC_ENTRY_TABLE_SLOTS > 256)
typedef uint16_t TraceEntryIndex_t;
#else
typedef uint8_t TraceEntryIndex_t;
#endif /* (TRC_CFG_ENTRY_TABLE_SLOTS > 256) */

typedef struct EntryIndexTable
{
	TraceEntryIndex_t axFreeIndexes[TRC_ENTRY_TABLE_SLOTS];
	uint32_t uiFreeIndexCount;
} TraceEntryIndexTable_t;

typedef struct TraceEntryTable
{
	uint32_t uiSlots;
	uint32_t uiEntrySymbolLength;
	uint32_t uiEntryStateCount;
	TraceEntry_t axEntries[TRC_ENTRY_TABLE_SLOTS];
} TraceEntryTable_t;

/* Private function definitions */
traceResult prvEntryIndexInitialize(TraceEntryIndexTable_t *pxIndexTable);
traceResult prvEntryIndexTake(TraceEntryIndex_t *pxIndex);

/* Variables */
static TraceEntryTable_t *pxEntryTable;
static TraceEntryIndexTable_t xIndexTable;

traceResult xTraceEntryTableInitialize(TraceEntryTableBuffer_t *pxBuffer)
{
	uint32_t i, j;

	TRC_ASSERT_EQUAL_SIZE(TraceEntryTableBuffer_t, TraceEntryTable_t);

	/* This should never fail */
	TRC_ASSERT(pxBuffer != 0);

	/* This should never fail */
	TRC_ASSERT((TRC_ENTRY_TABLE_SLOTS) != 0);

	pxEntryTable = (TraceEntryTable_t*)pxBuffer;

	pxEntryTable->uiSlots = TRC_ENTRY_TABLE_SLOTS;
	pxEntryTable->uiEntrySymbolLength = TRC_ENTRY_TABLE_SLOT_SYMBOL_SIZE;
	pxEntryTable->uiEntryStateCount = TRC_ENTRY_TABLE_STATE_COUNT;

	for (i = 0; i < TRC_ENTRY_TABLE_SLOTS; i++)
	{
		pxEntryTable->axEntries[i].pvAddress = 0;
		for (j = 0; j < TRC_ENTRY_TABLE_STATE_COUNT; j++)
		{
			pxEntryTable->axEntries[i].xStates[j] = 0;
		}
		pxEntryTable->axEntries[i].szSymbol[0] = 0;
	}

	prvEntryIndexInitialize(&xIndexTable);

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY);

	return TRC_SUCCESS;
}

traceResult xTraceEntryCreate(TraceEntryHandle_t *pxEntryHandle)
{
	uint32_t i;
	TraceEntryIndex_t xIndex;
	TraceEntry_t *pxEntry;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* We always check this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY))
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT(pxEntryHandle != 0);

	TRACE_ENTER_CRITICAL_SECTION();

	if (prvEntryIndexTake(&xIndex) != TRC_SUCCESS)
	{
		xTraceDiagnosticsIncrease(TRC_DIAGNOSTICS_ENTRY_SLOTS_NO_ROOM);

		TRACE_EXIT_CRITICAL_SECTION();

		return TRC_FAIL;
	}

	pxEntry = &pxEntryTable->axEntries[xIndex];
	
	pxEntry->pvAddress = (void*)pxEntry; /* We set a temporary address */

	for (i = 0; i < TRC_ENTRY_TABLE_STATE_COUNT; i++)
	{
		pxEntry->xStates[i] = 0;
	}

	pxEntry->uiOptions = 0;
	pxEntry->szSymbol[0] = 0;

	*pxEntryHandle = (TraceEntryHandle_t)pxEntry;

	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_SUCCESS;
}

traceResult xTraceEntryDelete(TraceEntryHandle_t xEntryHandle)
{
	TraceEntryIndex_t xIndex;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle));

	/* Calculate the index based on the entry address */
	/* Does not need to be locked. */
	/* This should never fail */
	xIndex = CALCULATE_ENTRY_INDEX(xEntryHandle);

	TRC_ASSERT(xIndex < TRC_ENTRY_TABLE_SLOTS);

	TRACE_ENTER_CRITICAL_SECTION();

	if (((TraceEntry_t*)xEntryHandle)->pvAddress == 0)
	{
		/* Someone else has deleted this already? */
		TRACE_EXIT_CRITICAL_SECTION();

		return TRC_FAIL;
	}

	/* A valid address, so we assume it is OK. */
	/* For good measure, we clear the address field */
	((TraceEntry_t*)xEntryHandle)->pvAddress = 0;

	/* Give back the index */
	GIVE_ENTRY_INDEX(xIndex);

	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_SUCCESS;
}

traceResult xTraceEntryFind(void* pvAddress, TraceEntryHandle_t* pxEntryHandle)
{
	uint32_t i;
	TraceEntry_t* pxEntry;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(pxEntryHandle != 0);

	/* This should never fail */
	TRC_ASSERT(pvAddress != 0);

	for (i = 0; i < TRC_ENTRY_TABLE_SLOTS; i++)
	{
		pxEntry = (TraceEntry_t*)(((uint32_t)pxEntryTable->axEntries) + (i * sizeof(TraceEntry_t)));
		if (pxEntry->pvAddress == pvAddress)
		{
			*pxEntryHandle = (TraceEntryHandle_t)pxEntry;

			return TRC_SUCCESS;
		}
	}

	return TRC_FAIL;
}

traceResult xTraceEntrySetSymbol(TraceEntryHandle_t xEntryHandle, const char* szSymbol)
{
	uint32_t i;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	if (szSymbol == 0)
	{
		szSymbol = "";
	}

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle));

	for (i = 0; i < (TRC_ENTRY_TABLE_SYMBOL_LENGTH); i++)
	{
		((TraceEntry_t*)xEntryHandle)->szSymbol[i] = szSymbol[i];	/* We do this first to ensure we also get the 0 termination, if there is one */

		if (szSymbol[i] == 0)
		{
			break;
		}
	}

	/* Check the length of "name", if longer than TRC_ENTRY_TABLE_SYMBOL_LENGTH */
	while ((szSymbol[i] != 0) && i < 128)
	{
		i++;
	}

	/* Remember the longest symbol name */
	xTraceDiagnosticsSetIfHigher(TRC_DIAGNOSTICS_ENTRY_SYMBOL_LONGEST_LENGTH, i);

	return TRC_SUCCESS;
}

traceResult xTraceEntryGetCount(uint32_t* puiCount)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(puiCount != 0);

	*puiCount = TRC_ENTRY_TABLE_SLOTS - GET_FREE_INDEX_COUNT();

	return TRC_SUCCESS;
}

traceResult xTraceEntryGetAtIndex(uint32_t index, TraceEntryHandle_t* pxEntryHandle)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(index < TRC_ENTRY_TABLE_SLOTS);

	/* This should never fail */
	TRC_ASSERT(pxEntryHandle != 0);

	*pxEntryHandle = (TraceEntryHandle_t)((uint32_t)(pxEntryTable->axEntries) + (index * sizeof(TraceEntry_t)));

	return TRC_SUCCESS;
}

#if ((TRC_CFG_USE_TRACE_ASSERT) == 1)

traceResult xTraceEntryCreateWithAddress(void* pvAddress, TraceEntryHandle_t* pxEntryHandle)
{
	/* This should never fail */
	TRC_ASSERT(pvAddress != 0);

	return TRC_ENTRY_CREATE_WITH_ADDRESS(pvAddress, pxEntryHandle);
}

traceResult xTraceEntrySetState(TraceEntryHandle_t xEntryHandle, uint32_t uiStateIndex, TraceUnsignedBaseType_t uxState)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(uiStateIndex < (TRC_ENTRY_TABLE_STATE_COUNT));

	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle));

	return TRC_ENTRY_SET_STATE(xEntryHandle, uiStateIndex, uxState);
}

traceResult xTraceEntrySetOptions(TraceEntryHandle_t xEntryHandle, uint32_t uiMask)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle));
	
	return TRC_ENTRY_SET_OPTIONS(xEntryHandle, uiMask);
}

traceResult xTraceEntryClearOptions(TraceEntryHandle_t xEntryHandle, uint32_t uiMask)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle));
	
	return TRC_ENTRY_CLEAR_OPTIONS(xEntryHandle, uiMask);
}

traceResult xTraceEntryGetAddress(TraceEntryHandle_t xEntryHandle, void **ppvAddress)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(ppvAddress != 0);

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle));

	return TRC_ENTRY_GET_ADDRESS(xEntryHandle, ppvAddress);
}

traceResult xTraceEntryGetSymbol(TraceEntryHandle_t xEntryHandle, const char** pszSymbol)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(pszSymbol != 0);

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle));

	return TRC_ENTRY_GET_SYMBOL(xEntryHandle, pszSymbol);
}

traceResult xTraceEntryGetState(TraceEntryHandle_t xEntryHandle, uint32_t uiStateIndex, TraceUnsignedBaseType_t *puxState)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(puxState != 0);

	/* This should never fail */
	TRC_ASSERT(uiStateIndex < TRC_ENTRY_TABLE_STATE_COUNT);

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle));

	return TRC_ENTRY_GET_STATE(xEntryHandle, uiStateIndex, puxState);
}

traceResult xTraceEntryGetOptions(TraceEntryHandle_t xEntryHandle, uint32_t *puiOptions)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(puiOptions != 0);

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle));

	return TRC_ENTRY_GET_OPTIONS(xEntryHandle, puiOptions);
}

#endif /* ((TRC_CFG_USE_TRACE_ASSERT) == 1) */

/* PRIVATE FUNCTIONS */

traceResult prvEntryIndexInitialize(TraceEntryIndexTable_t* pxIndexTable)
{
	uint32_t i;

	for (i = 0; i < TRC_ENTRY_TABLE_SLOTS; i++)
	{
		pxIndexTable->axFreeIndexes[i] = (TraceEntryIndex_t)i;
	}

	xIndexTable.uiFreeIndexCount = TRC_ENTRY_TABLE_SLOTS;

	return TRC_SUCCESS;
}

traceResult prvEntryIndexTake(TraceEntryIndex_t *pxIndex)
{
	/* Critical Section must be active! */
	TraceEntryIndex_t xIndex;

	if (xIndexTable.uiFreeIndexCount == 0)
	{
		return TRC_FAIL;
	}

	/* Always take the first item */
	xIndex = xIndexTable.axFreeIndexes[0];
	xIndexTable.uiFreeIndexCount--;

	/* Move the last item to the first slot, to avoid holes */
	xIndexTable.axFreeIndexes[0] = xIndexTable.axFreeIndexes[xIndexTable.uiFreeIndexCount];

#if (TRC_ENTRY_TABLE_SLOTS > 256)
	xIndexTable.axFreeIndexes[xIndexTable.uiFreeIndexCount] = UINT16_MAX;
#else
	xIndexTable.axFreeIndexes[xIndexTable.uiFreeIndexCount] = UINT8_MAX;
#endif

	*pxIndex = xIndex;
	return TRC_SUCCESS;
}

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
