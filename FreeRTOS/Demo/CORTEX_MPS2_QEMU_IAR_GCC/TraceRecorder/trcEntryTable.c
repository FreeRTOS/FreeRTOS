/*
* Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of the entry table.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <string.h>

/* (EntryAddress >= FirstEntryAddress) && (EntryAddress < EntryAddressOutsideArray) */
#define VALIDATE_ENTRY_HANDLE(xEntryHandle) (((void*)(xEntryHandle) >= (void*)&pxEntryTable->axEntries[0]) && ((void*)(xEntryHandle) < (void*)&pxEntryTable->axEntries[TRC_ENTRY_TABLE_SLOTS]))

/*cstat !MISRAC2004-19.4 Suppress macro check*/
#define GIVE_ENTRY_INDEX(xIndex) pxIndexTable->axFreeIndexes[pxIndexTable->uiFreeIndexCount] = (xIndex); pxIndexTable->uiFreeIndexCount++

/*cstat !MISRAC2004-19.4 Suppress macro check*/
#define GET_FREE_INDEX_COUNT() pxIndexTable->uiFreeIndexCount

/* Index = (EntryAddress - FirstEntryAddress) / EntrySize */
#define CALCULATE_ENTRY_INDEX(xEntryHandle) (TraceEntryIndex_t)(((TraceUnsignedBaseType_t)(xEntryHandle) - (TraceUnsignedBaseType_t)&pxEntryTable->axEntries[0]) / sizeof(TraceEntry_t))

/* Private function definitions */
static traceResult prvEntryIndexInitialize(void);
static traceResult prvEntryIndexTake(TraceEntryIndex_t *pxIndex);

/* Variables */
static TraceEntryTable_t *pxEntryTable TRC_CFG_RECORDER_DATA_ATTRIBUTE;
static TraceEntryIndexTable_t *pxIndexTable TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTraceEntryIndexTableInitialize(TraceEntryIndexTable_t* const pxBuffer)
{
	/* This should never fail */
	TRC_ASSERT(pxBuffer != (void*)0);

	pxIndexTable = pxBuffer;
	
	return prvEntryIndexInitialize();
}

traceResult xTraceEntryTableInitialize(TraceEntryTable_t* const pxBuffer)
{
	uint32_t i, j;

	/* This should never fail */
	TRC_ASSERT(pxBuffer != (void*)0);

	/* This should never fail */
	TRC_ASSERT((TRC_ENTRY_TABLE_SLOTS) != 0);

	pxEntryTable = pxBuffer;

	pxEntryTable->uxSlots = (TraceUnsignedBaseType_t)(TRC_ENTRY_TABLE_SLOTS);
	pxEntryTable->uxEntrySymbolLength = (TraceUnsignedBaseType_t)(TRC_ENTRY_TABLE_SLOT_SYMBOL_SIZE);
	pxEntryTable->uxEntryStateCount = (TraceUnsignedBaseType_t)(TRC_ENTRY_TABLE_STATE_COUNT);

	for (i = 0u; i < (uint32_t)(TRC_ENTRY_TABLE_SLOTS); i++)
	{
		pxEntryTable->axEntries[i].pvAddress = 0;
		for (j = 0u; j < TRC_ENTRY_TABLE_STATE_COUNT; j++)
		{
			pxEntryTable->axEntries[i].xStates[j] = (TraceUnsignedBaseType_t)0;
		}
		pxEntryTable->axEntries[i].szSymbol[0] = (char)0; /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
	}

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
	if (xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY) == 0U)
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT(pxEntryHandle != (void*)0);

	TRACE_ENTER_CRITICAL_SECTION();

	if (prvEntryIndexTake(&xIndex) != TRC_SUCCESS)
	{
		(void)xTraceDiagnosticsIncrease(TRC_DIAGNOSTICS_ENTRY_SLOTS_NO_ROOM);

		TRACE_EXIT_CRITICAL_SECTION();

		return TRC_FAIL;
	}

	pxEntry = &pxEntryTable->axEntries[xIndex];
	
	pxEntry->pvAddress = (void*)pxEntry; /* We set a temporary address */

	for (i = 0u; i < (uint32_t)(TRC_ENTRY_TABLE_STATE_COUNT); i++)
	{
		pxEntry->xStates[i] = (TraceUnsignedBaseType_t)0;
	}

	pxEntry->uiOptions = 0u;
	pxEntry->szSymbol[0] = (char)0; /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/

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
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle)); /*cstat !MISRAC2004-17.3 !MISRAC2012-Rule-18.3 Suppress pointer comparison check*/

	/* Calculate the index based on the entry address */
	/* Does not need to be locked. */
	/* This should never fail */
	xIndex = CALCULATE_ENTRY_INDEX(xEntryHandle); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 Suppress conversion from pointer to integer check*/ /*cstat !MISRAC2004-17.2 !MISRAC2012-Rule-18.2 !MISRAC2012-Rule-18.4 Suppress pointer comparison check*/

	TRC_ASSERT((uint32_t)xIndex < (uint32_t)(TRC_ENTRY_TABLE_SLOTS));

	TRACE_ENTER_CRITICAL_SECTION();

	if (((TraceEntry_t*)xEntryHandle)->pvAddress == 0)
	{
		/* Someone else has deleted this already? */
		TRACE_EXIT_CRITICAL_SECTION();

		return TRC_FAIL;
	}

	/* A valid address, so we assume it is OK. */
	/* We clear the address field which is used on host to see if entries are active. */
	((TraceEntry_t*)xEntryHandle)->pvAddress = 0;

	/* Give back the index */
	GIVE_ENTRY_INDEX(xIndex);

	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_SUCCESS;
}

traceResult xTraceEntryFind(const void* const pvAddress, TraceEntryHandle_t* pxEntryHandle)
{
	uint32_t i;
	TraceEntry_t* pxEntry;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(pxEntryHandle != (void*)0);

	/* This should never fail */
	TRC_ASSERT(pvAddress != (void*)0);

	for (i = 0u; i < (uint32_t)(TRC_ENTRY_TABLE_SLOTS); i++)
	{
		pxEntry = &pxEntryTable->axEntries[i];
		if (pxEntry->pvAddress == pvAddress)
		{
			*pxEntryHandle = (TraceEntryHandle_t)pxEntry;

			return TRC_SUCCESS;
		}
	}

	return TRC_FAIL;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceEntrySetSymbol(const TraceEntryHandle_t xEntryHandle, const char* szSymbol, uint32_t uiLength)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	if (szSymbol == (void*)0)
	{
		szSymbol = ""; /*cstat !MISRAC2012-Rule-17.8 Suppress modified function parameter check*/
		uiLength = 0u; /*cstat !MISRAC2012-Rule-17.8 Suppress modified function parameter check*/
	}

	/* Remember the longest symbol name */
	(void)xTraceDiagnosticsSetIfHigher(TRC_DIAGNOSTICS_ENTRY_SYMBOL_LONGEST_LENGTH, (int32_t)uiLength);

	if (uiLength >= (uint32_t)(TRC_ENTRY_TABLE_SYMBOL_LENGTH))
	{
		/* No room for null termination. Set to max. */
		uiLength = (uint32_t)(TRC_ENTRY_TABLE_SYMBOL_LENGTH); /*cstat !MISRAC2012-Rule-17.8 Suppress modified function parameter check*/
	}
	else
	{
		/* Include null termination by increasing the size by 1 */
		uiLength = uiLength + 1u; /*cstat !MISRAC2012-Rule-17.8 Suppress modified function parameter check*/
	}

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle)); /*cstat !MISRAC2004-17.3 !MISRAC2012-Rule-18.3 Suppress pointer comparison check*/

	/* This will also copy the null termination, if possible */
	memcpy(((TraceEntry_t*)xEntryHandle)->szSymbol, szSymbol, uiLength);

	return TRC_SUCCESS;
}

traceResult xTraceEntryGetCount(uint32_t* puiCount)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(puiCount != (void*)0);

	*puiCount = (uint32_t)(TRC_ENTRY_TABLE_SLOTS) - GET_FREE_INDEX_COUNT();

	return TRC_SUCCESS;
}

traceResult xTraceEntryGetAtIndex(uint32_t index, TraceEntryHandle_t* pxEntryHandle)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(index < (uint32_t)(TRC_ENTRY_TABLE_SLOTS));

	/* This should never fail */
	TRC_ASSERT(pxEntryHandle != (void*)0);

	*pxEntryHandle = (TraceEntryHandle_t)&pxEntryTable->axEntries[index];

	return TRC_SUCCESS;
}

#if ((TRC_CFG_USE_TRACE_ASSERT) == 1)

traceResult xTraceEntryCreateWithAddress(void* const pvAddress, TraceEntryHandle_t* pxEntryHandle)
{
	/* This should never fail */
	TRC_ASSERT(pvAddress != (void*)0);

	return TRC_ENTRY_CREATE_WITH_ADDRESS(pvAddress, pxEntryHandle);
}

traceResult xTraceEntrySetState(const TraceEntryHandle_t xEntryHandle, TraceUnsignedBaseType_t uxStateIndex, TraceUnsignedBaseType_t uxState)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(uxStateIndex < (TraceUnsignedBaseType_t)(TRC_ENTRY_TABLE_STATE_COUNT));

	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle)); /*cstat !MISRAC2004-17.3 !MISRAC2012-Rule-18.3 Suppress pointer comparison check*/

	return TRC_ENTRY_SET_STATE(xEntryHandle, uxStateIndex, uxState);
}

traceResult xTraceEntrySetOptions(const TraceEntryHandle_t xEntryHandle, uint32_t uiMask)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle)); /*cstat !MISRAC2004-17.3 !MISRAC2012-Rule-18.3 Suppress pointer comparison check*/
	
	return TRC_ENTRY_SET_OPTIONS(xEntryHandle, uiMask);
}

traceResult xTraceEntryClearOptions(const TraceEntryHandle_t xEntryHandle, uint32_t uiMask)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle)); /*cstat !MISRAC2004-17.3 !MISRAC2012-Rule-18.3 Suppress pointer comparison check*/
	
	return TRC_ENTRY_CLEAR_OPTIONS(xEntryHandle, uiMask);
}

traceResult xTraceEntryGetAddress(const TraceEntryHandle_t xEntryHandle, void **ppvAddress)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(ppvAddress != (void*)0);

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle)); /*cstat !MISRAC2004-17.3 !MISRAC2012-Rule-18.3 Suppress pointer comparison check*/

	return TRC_ENTRY_GET_ADDRESS(xEntryHandle, ppvAddress);
}

void* xTraceEntryGetAddressReturn(const TraceEntryHandle_t xEntryHandle)
{
	/* This should never fail */
	TRC_ASSERT_CUSTOM_ON_FAIL(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY), return (void*)0);

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT_CUSTOM_ON_FAIL(VALIDATE_ENTRY_HANDLE(xEntryHandle), return (void*)0); /*cstat !MISRAC2004-17.3 !MISRAC2012-Rule-18.3 Suppress pointer comparison check*/

	return TRC_ENTRY_GET_ADDRESS_RETURN(xEntryHandle);
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceEntryGetSymbol(const TraceEntryHandle_t xEntryHandle, const char** pszSymbol)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(pszSymbol != (void*)0);

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle)); /*cstat !MISRAC2004-17.3 !MISRAC2012-Rule-18.3 Suppress pointer comparison check*/

	return TRC_ENTRY_GET_SYMBOL(xEntryHandle, pszSymbol);
}

traceResult xTraceEntryGetState(const TraceEntryHandle_t xEntryHandle, TraceUnsignedBaseType_t uxStateIndex, TraceUnsignedBaseType_t *puxState)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(puxState != (void*)0);

	/* This should never fail */
	TRC_ASSERT(uxStateIndex < (TraceUnsignedBaseType_t)(TRC_ENTRY_TABLE_STATE_COUNT));

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle)); /*cstat !MISRAC2004-17.3 !MISRAC2012-Rule-18.3 Suppress pointer comparison check*/

	return TRC_ENTRY_GET_STATE(xEntryHandle, uxStateIndex, puxState);
}

/*cstat !MISRAC2012-Rule-8.13 Suppress const check for xEntryHandle*/
TraceUnsignedBaseType_t xTraceEntryGetStateReturn(const TraceEntryHandle_t xEntryHandle, TraceUnsignedBaseType_t uxStateIndex)
{
	return TRC_ENTRY_GET_STATE_RETURN(xEntryHandle, uxStateIndex);
}

traceResult xTraceEntryGetOptions(const TraceEntryHandle_t xEntryHandle, uint32_t *puiOptions)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ENTRY));

	/* This should never fail */
	TRC_ASSERT(puiOptions != (void*)0);

	/* Does not need to be locked. */
	/* This should never fail */
	TRC_ASSERT(VALIDATE_ENTRY_HANDLE(xEntryHandle)); /*cstat !MISRAC2004-17.3 !MISRAC2012-Rule-18.3 Suppress pointer comparison check*/

	return TRC_ENTRY_GET_OPTIONS(xEntryHandle, puiOptions);
}

#endif /* ((TRC_CFG_USE_TRACE_ASSERT) == 1) */

/* PRIVATE FUNCTIONS */

static traceResult prvEntryIndexInitialize(void)
{
	uint32_t i;

	for (i = 0u; i < (uint32_t)(TRC_ENTRY_TABLE_SLOTS); i++)
	{
		pxIndexTable->axFreeIndexes[i] = (TraceEntryIndex_t)i;
	}

	pxIndexTable->uiFreeIndexCount = TRC_ENTRY_TABLE_SLOTS;

	return TRC_SUCCESS;
}

static traceResult prvEntryIndexTake(TraceEntryIndex_t *pxIndex)
{
	/* Critical Section must be active! */
	TraceEntryIndex_t xIndex;

	if (pxIndexTable->uiFreeIndexCount == 0u)
	{
		return TRC_FAIL;
	}

	/* Always take the first item */
	xIndex = pxIndexTable->axFreeIndexes[0];
	pxIndexTable->uiFreeIndexCount--;

	/* Move the last item to the first slot, to avoid holes */
	pxIndexTable->axFreeIndexes[0] = pxIndexTable->axFreeIndexes[pxIndexTable->uiFreeIndexCount];

#if (TRC_ENTRY_TABLE_SLOTS > 256)
	pxIndexTable->axFreeIndexes[pxIndexTable->uiFreeIndexCount] = UINT16_MAX;
#else
	pxIndexTable->axFreeIndexes[pxIndexTable->uiFreeIndexCount] = UINT8_MAX;
#endif

	*pxIndex = xIndex;
	return TRC_SUCCESS;
}

#endif
