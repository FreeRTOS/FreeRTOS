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
 * @brief Public trace object APIs.
 */

#ifndef TRC_OBJECT_H
#define TRC_OBJECT_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_object_apis Trace Object APIs
 * @ingroup trace_recorder_apis
 * @{
 */

/**
 * @brief Registers trace object.
 * 
 * @param[in] uiEventCode Event code.
 * @param[in] pvObject Object.
 * @param[in] szName Name.
 * @param[in] uxStateCount State count. 
 * @param[in] uxStates States.
 * @param[in] uxOptions Options.
 * @param[out] pxObjectHandle Pointer to uninitialized trace object.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceObjectRegisterInternal(uint32_t uiEventCode, void* pvObject, const char* szName, TraceUnsignedBaseType_t uxStateCount, TraceUnsignedBaseType_t uxStates[], TraceUnsignedBaseType_t uxOptions, TraceObjectHandle_t* pxObjectHandle);

/**
 * @brief Registers trace object.
 * 
 * @param[in] uiEventCode Event code.
 * @param[in] pvObject Object.
 * @param[in] szName Name.
 * @param[in] uxState State.
 * @param[out] pxObjectHandle Pointer to uninitialized trace object.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceObjectRegister(uint32_t uiEventCode, void *pvObject, const char* szName, TraceUnsignedBaseType_t uxState, TraceObjectHandle_t *pxObjectHandle);

/**
 * @brief Unregisters trace object.
 * 
 * @param[in] xObjectHandle Pointer to initialized trace object.
 * @param[in] uiEventCode Event code.
 * @param[in] uxState State.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceObjectUnregister(TraceObjectHandle_t xObjectHandle, uint32_t uiEventCode, TraceUnsignedBaseType_t uxState);

/**
 * @brief Sets trace object name.
 * 
 * @param[in] xObjectHandle Pointer to initialized trace object.
 * @param[in] szName Name.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceObjectSetName(TraceObjectHandle_t xObjectHandle, const char *szName);

/**
 * @brief Sets trace object state.
 * 
 * @param[in] xObjectHandle Pointer to initialized trace object.
 * @param[in] uxState State.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceObjectSetState(xObjectHandle, uxState) xTraceObjectSetSpecificState(xObjectHandle, 0, uxState)

/**
 * @brief Sets trace object specific state state.
 * 
 * @param[in] xObjectHandle Pointer to initialized trace object.
 * @param[in] uiIndex State Index.
 * @param[in] uxState State.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceObjectSetSpecificState(xObjectHandle, uiIndex, uxState) xTraceEntrySetState((TraceEntryHandle_t)(xObjectHandle), uiIndex, uxState)

/**
 * @brief Sets trace object options.
 * 
 * @param[in] xObjectHandle Pointer to initialized trace object.
 * @param[in] uiOptions Options.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceObjectSetOptions(xObjectHandle, uiOptions) xTraceEntrySetOptions((TraceEntryHandle_t)(xObjectHandle), uiOptions)

/**
 * @brief Registers trace object without trace object handle.
 * 
 * @param[in] uiEventCode Event code.
 * @param[in] pvObject Object.
 * @param[in] szName Name.
 * @param[in] uxState State.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceObjectRegisterWithoutHandle(uint32_t uiEventCode, void* pvObject, const char* szName, TraceUnsignedBaseType_t uxState);

/**
 * @brief Unregisters trace object without trace object handle.
 * 
 * @param[in] uiEventCode Event code.
 * @param[in] pvObject Object.
 * @param[in] uxState State.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceObjectUnregisterWithoutHandle(uint32_t uiEventCode, void* pvObject, TraceUnsignedBaseType_t uxState);

/**
 * @brief Set trace object name without trace object handle.
 * 
 * @param[in] pvObject Object.
 * @param[in] szName Name.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceObjectSetNameWithoutHandle(void* pvObject, const char* szName);

/**
 * @brief Set trace object state without trace object handle.
 * 
 * @param[in] pvObject Object.
 * @param[in] uxState State.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceObjectSetStateWithoutHandle(pvObject, uxState) xTraceObjectSetSpecificStateWithoutHandle(pvObject, 0, uxState)

/**
 * @brief Sets trace object specific state without trace object
 * handle.
 * 
 * @param[in] pvObject Object. 
 * @param[in] uiIndex State index.
 * @param[in] uxState State.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceObjectSetSpecificStateWithoutHandle(void* pvObject, uint32_t uiIndex, TraceUnsignedBaseType_t uxState);

/**
 * @brief Sets trace object options without trace object handle.
 * 
 * @param[in] pvObject Object.
 * @param[in] uiOptions Options.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceObjectSetOptionsWithoutHandle(void* pvObject, uint32_t uiOptions);

/** @} */

#ifdef __cplusplus
}
#endif

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /* TRC_OBJECT_H */
