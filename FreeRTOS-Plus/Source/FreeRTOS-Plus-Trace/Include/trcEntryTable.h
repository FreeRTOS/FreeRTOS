/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*/

/**
 * @file 
 * 
 * @brief Public trace entry table APIs.
 */

#ifndef TRC_ENTRY_TABLE_H
#define TRC_ENTRY_TABLE_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_entry_table_apis Trace Entry Table APIs
 * @ingroup trace_recorder_apis
 * @{
 */

#define TRC_ENTRY_CREATE_WITH_ADDRESS(_pvAddress, _pxEntryHandle) (xTraceEntryCreate(_pxEntryHandle) == TRC_SUCCESS ? (((TraceEntry_t*)*(_pxEntryHandle))->pvAddress = (_pvAddress), TRC_SUCCESS) : TRC_FAIL)
#define TRC_ENTRY_SET_STATE(xEntryHandle, uiStateIndex, uxState) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(((TraceEntry_t*)(xEntryHandle))->xStates[uiStateIndex] = (uxState), TRC_SUCCESS)
#define TRC_ENTRY_SET_OPTIONS(xEntryHandle, uiMask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(((TraceEntry_t*)(xEntryHandle))->uiOptions |= (uiMask), TRC_SUCCESS)
#define TRC_ENTRY_CLEAR_OPTIONS(xEntryHandle, uiMask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(((TraceEntry_t*)(xEntryHandle))->uiOptions &= ~(uiMask), TRC_SUCCESS)
#define TRC_ENTRY_GET_ADDRESS(xEntryHandle, ppvAddress) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(*(ppvAddress) = ((TraceEntry_t*)(xEntryHandle))->pvAddress, TRC_SUCCESS)
#define TRC_ENTRY_GET_SYMBOL(xEntryHandle, pszSymbol) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(*(pszSymbol) = ((TraceEntry_t*)(xEntryHandle))->szSymbol, TRC_SUCCESS)
#define TRC_ENTRY_GET_STATE(xEntryHandle, uiStateIndex, puxState) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(*(puxState) = ((TraceEntry_t*)(xEntryHandle))->xStates[uiStateIndex], TRC_SUCCESS)
#define TRC_ENTRY_GET_OPTIONS(xEntryHandle, puiOptions) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(*(puiOptions) = ((TraceEntry_t*)(xEntryHandle))->uiOptions, TRC_SUCCESS)

#define TRC_ENTRY_TABLE_SLOTS (TRC_CFG_ENTRY_SLOTS)
#define TRC_ENTRY_TABLE_STATE_COUNT (3)
#define TRC_ENTRY_TABLE_SYMBOL_LENGTH (TRC_CFG_ENTRY_SYMBOL_MAX_LENGTH)
#define TRC_ENTRY_TABLE_SLOT_SYMBOL_SIZE ((((sizeof(char) * TRC_ENTRY_TABLE_SYMBOL_LENGTH) + (sizeof(uint32_t) - 1)) / sizeof(uint32_t)) * sizeof(uint32_t))

/** Trace Entry Structure */
typedef struct TraceEntry
{
	void* pvAddress;												/**< */
	TraceUnsignedBaseType_t xStates[TRC_ENTRY_TABLE_STATE_COUNT];	/**< */
	uint32_t uiOptions;												/**< */
	char szSymbol[TRC_ENTRY_TABLE_SLOT_SYMBOL_SIZE];				/**< */
} TraceEntry_t;

#define TRC_ENTRY_TABLE_SIZE (sizeof(uint32_t) + sizeof(uint32_t) + sizeof(uint32_t) + (sizeof(TraceEntry_t) * (TRC_ENTRY_TABLE_SLOTS)))

/** Trace Entry Table Buffer Structure */
typedef struct TraceEntryTableBuffer
{
	uint8_t buffer[(TRC_ENTRY_TABLE_SIZE)]; /**< */
} TraceEntryTableBuffer_t;

/**
 * @internal Initialize trace entry table.
 * 
 * This routine initializes the trace entry table which maps objects to
 * symbolic identifiers, state information, and options.
 * 
 * @param[in] pxBuffer Pointer to uninitialized trace entry table buffer.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntryTableInitialize(TraceEntryTableBuffer_t* pxBuffer);

/**
 * @brief Creates trace entry.
 * 
 * @param[out] pxEntryHandle Pointer to uninitialized trace entry handle.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntryCreate(TraceEntryHandle_t *pxEntryHandle);

/**
 * @brief Deletes trace entry.
 * 
 * @param[in] xEntryHandle Pointer to initialized trace entry handle.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntryDelete(TraceEntryHandle_t xEntryHandle);

/**
 * @brief Finds trace entry mapped to object address.
 * 
 * @param[in] pvAddress Address of object.
 * @param[out] pxEntryHandle Pointer to uninitialized trace entry handle.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntryFind(void* pvAddress, TraceEntryHandle_t* pxEntryHandle);

/**
 * @brief Gets the number of entries in the trace entry table.
 * 
 * @param[out] puiCount Count.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntryGetCount(uint32_t* puiCount);

/**
 * @brief Gets trace table entry at index. 
 * 
 * @param[in] index Entry index.
 * @param[out] pxEntryHandle Pointer to uninitialized trace entry handle. 
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntryGetAtIndex(uint32_t index, TraceEntryHandle_t* pxEntryHandle);

/**
 * @brief Sets symbol for entry.
 * 
 * @param[in] xEntryHandle Pointer to initialized trace entry handle.
 * @param[out] szSymbol Pointer to symbol string, set by function
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntrySetSymbol(TraceEntryHandle_t xEntryHandle, const char* szSymbol);

#if ((TRC_CFG_USE_TRACE_ASSERT) == 1)

/**
 * @brief Creates trace entry mapped to memory address.
 * 
 * @param[in] pvAddress Address.
 * @param[out] pxEntryHandle Pointer to uninitialized trace entry handle.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntryCreateWithAddress(void* pvAddress, TraceEntryHandle_t* pxEntryHandle);

/**
 * @brief Sets trace entry state.
 * 
 * @param[in] xEntryHandle Pointer to initialized trace entry handle.
 * @param[in] uiStateIndex Index of state (< TRC_ENTRY_TABLE_STATE_COUNT).
 * @param[in] uxState State.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntrySetState(TraceEntryHandle_t xEntryHandle, uint32_t uiStateIndex, TraceUnsignedBaseType_t uxState);

/**
 * @brief Sets trace entry option(s).
 * 
 * @param[in] xEntryHandle Pointer to initialized trace entry handle.
 * @param[in] uiMask Option(s) set mask.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntrySetOptions(TraceEntryHandle_t xEntryHandle, uint32_t uiMask);

/**
 * @brief Clears trace entry option(s).
 * 
 * @param[in] xEntryHandle Pointer to initialized trace entry handle.
 * @param[in] uiMask Options(s) clear mask.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntryClearOptions(TraceEntryHandle_t xEntryHandle, uint32_t uiMask);

/**
 * @brief Gets linked address for trace entry.
 * 
 * @param[in] xEntryHandle Pointer to initialized trace entry handle.
 * @param[out] ppvAddress Address.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntryGetAddress(TraceEntryHandle_t xEntryHandle, void **ppvAddress);

/**
 * @brief Gets symbol for trace entry.
 * 
 * @param[in] xEntryHandle Pointer to initialized trace entry handle.
 * @param[out] pszSymbol Symbol.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntryGetSymbol(TraceEntryHandle_t xEntryHandle, const char** pszSymbol);

/**
 * @brief Gets state for trace entry.
 * 
 * @param[in] xEntryHandle Pointer to initialized trace entry handle.
 * @param[in] uiStateIndex State index (< TRC_ENTRY_TABLE_STATE_COUNT).
 * @param[out] puxState State.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntryGetState(TraceEntryHandle_t xEntryHandle, uint32_t uiStateIndex, TraceUnsignedBaseType_t *puxState);

/**
 * @brief Gets options for trace entry.
 * 
 * @param[in] xEntryHandle Pointer to initialized trace entry handle.
 * @param[out] puiOptions Options.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEntryGetOptions(TraceEntryHandle_t xEntryHandle, uint32_t *puiOptions);

#else

#define xTraceEntryCreateWithAddress TRC_ENTRY_CREATE_WITH_ADDRESS

#define xTraceEntrySetState TRC_ENTRY_SET_STATE
#define xTraceEntrySetOptions TRC_ENTRY_SET_OPTIONS
#define xTraceEntryClearOptions TRC_ENTRY_CLEAR_OPTIONS

#define xTraceEntryGetAddress TRC_ENTRY_GET_ADDRESS
#define xTraceEntryGetSymbol TRC_ENTRY_GET_SYMBOL
#define xTraceEntryGetState TRC_ENTRY_GET_STATE
#define xTraceEntryGetOptions TRC_ENTRY_GET_OPTIONS

#endif /* ((TRC_CFG_USE_TRACE_ASSERT) == 1) */

/** @} */

#ifdef __cplusplus
}
#endif

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /* TRC_ENTRY_TABLE_H */
