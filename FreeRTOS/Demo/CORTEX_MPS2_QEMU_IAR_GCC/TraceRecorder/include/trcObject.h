/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
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

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

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
traceResult xTraceObjectRegisterInternal(uint32_t uiEventCode, void* const pvObject, const char* szName, TraceUnsignedBaseType_t uxStateCount, const TraceUnsignedBaseType_t uxStates[], TraceUnsignedBaseType_t uxOptions, TraceObjectHandle_t* pxObjectHandle);

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
traceResult xTraceObjectRegister(uint32_t uiEventCode, void* const pvObject, const char* szName, TraceUnsignedBaseType_t uxState, TraceObjectHandle_t *pxObjectHandle);

/**
 * @brief Registers trace object with two initial states.
 * 
 * @param[in] uiEventCode Event code.
 * @param[in] pvObject Object.
 * @param[in] szName Name.
 * @param[in] uxState1 State 1.
 * @param[in] uxState2 State 2.
 * @param[out] pxObjectHandle Pointer to uninitialized trace object.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceObjectRegister2(uint32_t uiEventCode, void* const pvObject, const char* szName, TraceUnsignedBaseType_t uxState1,  TraceUnsignedBaseType_t uxState2, TraceObjectHandle_t *pxObjectHandle);

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
 * @brief Registers trace object with two initial states without trace object handle.
 * 
 * @param[in] uiEventCode Event code.
 * @param[in] pvObject Object.
 * @param[in] szName Name.
 * @param[in] uxState1 State 1.
 * @param[in] uxState2 State 2.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceObjectRegisterWithoutHandle2(uint32_t uiEventCode, void* pvObject, const char* szName, TraceUnsignedBaseType_t uxState1, TraceUnsignedBaseType_t uxState2);

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

#else

#define xTraceObjectRegisterInternal(_uiEventCode, _pvObject, _szName, _uxStateCount, _uxStates, _uxOptions, _pxObjectHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_8((void)(_uiEventCode), (void)(_pvObject), (void)(_szName), (void)(_uxStateCount), (void)(_uxStates), (void)(_uxOptions), (void)(_pxObjectHandle), TRC_SUCCESS)

#define xTraceObjectRegister(_uiEventCode, _pvObject, _szName, _uxState, _pxObjectHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_6((void)(_uiEventCode), (void)(_pvObject), (void)(_szName), (void)(_uxState), (void)(_pxObjectHandle), TRC_SUCCESS)

#define xTraceObjectUnregister(_xObjectHandle, _uiEventCode, _uxState) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(_xObjectHandle), (void)(_uiEventCode), (void)(_uxState), TRC_SUCCESS)

#define xTraceObjectSetName(_xObjectHandle, _szName) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_xObjectHandle), (void)(_szName), TRC_SUCCESS)

#define xTraceObjectSetState(_xObjectHandle, _uxState) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_xObjectHandle), (void)(_uxState), TRC_SUCCESS)

#define xTraceObjectSetSpecificState(_xObjectHandle, _uiIndex, _uxState) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(_xObjectHandle), (void)(_uiIndex), (void)(_uxState), TRC_SUCCESS)

#define xTraceObjectSetOptions(_xObjectHandle, _uiOptions) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_xObjectHandle), (void)(_uiOptions), TRC_SUCCESS)

#define xTraceObjectRegisterWithoutHandle(_uiEventCode, _pvObject, _szName, _uxState) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_5((void)(_uiEventCode), (void)(_pvObject), (void)(_szName), (void)(_uxState), TRC_SUCCESS)

#define xTraceObjectUnregisterWithoutHandle(_uiEventCode, _pvObject, _uxState) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(_uiEventCode), (void)(_pvObject), (void)(_uxState), TRC_SUCCESS)

#define xTraceObjectSetNameWithoutHandle(_pvObject, _szName) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_pvObject), (void)(_szName), TRC_SUCCESS)

#define xTraceObjectSetStateWithoutHandle(_pvObject, _uxState) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_pvObject), (void)(_uxState), TRC_SUCCESS)

#define xTraceObjectSetSpecificStateWithoutHandle(_pvObject, _uiIndex, _uxState) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(_pvObject), (void)(_uiIndex), (void)(_uxState), TRC_SUCCESS)

#define xTraceObjectSetOptionsWithoutHandle(_pvObject, _uiOptions) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_pvObject), (void)(_uiOptions), TRC_SUCCESS)

#endif

#endif
