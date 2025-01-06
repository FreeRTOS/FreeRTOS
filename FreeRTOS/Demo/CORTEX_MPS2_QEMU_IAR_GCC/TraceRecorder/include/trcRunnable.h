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
 * @brief Public trace runnable APIs.
 */

#ifndef TRC_RUNNABLE_H
#define TRC_RUNNABLE_H

typedef enum TraceRunnableRegisterMethod
{
	TRC_RUNNABLE_REGISTER_METHOD_USE_ENTRY_TABLE,
	TRC_RUNNABLE_REGISTER_METHOD_USE_STRING_ADDRESS,
	TRC_RUNNABLE_REGISTER_METHOD_USE_HANDLE_ADDRESS,
} TraceRunnableRegisterMethod_t;

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_runnable_apis Trace Runnable APIs
 * @ingroup trace_recorder_apis
 * @{
 */

/**
 * @brief Registers a runnable. Can be called multiple times, will not create additional entries.
 * 
 * @param[in] szName Name.
 * @param[in] uxRegisterMethod Indicates how to register the runnable. Since there can be thousands of runnables, storing in entry table is not always a good idea.
 *				TRC_RUNNABLE_REGISTER_METHOD_USE_ENTRY_TABLE: Store in entry table normally and handle will point to entry.
 *				TRC_RUNNABLE_REGISTER_METHOD_USE_STRING_ADDRESS: For this method the string address must be unique and will be used as handle value.
 *				TRC_RUNNABLE_REGISTER_METHOD_USE_HANDLE_ADDRESS: For this method the handle address must be unique and will be used as handle value.
 * @param[out] pxRunnableHandle Pointer to zero-initialized TraceRunnableHandle_t. If handle that is pointed to is not 0 no entry will be created.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceRunnableRegister(const char* szName, TraceRunnableRegisterMethod_t uxRegisterMethod, TraceRunnableHandle_t* pxRunnableHandle);

/**
 * @brief Creates an event indicating a runnable started.
 * 
 * @param[in] xRunnableHandle Runnable handle.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceRunnableStart(xRunnableHandle) xTraceEventCreate1(PSF_EVENT_RUNNABLE_START, (TraceUnsignedBaseType_t)(xRunnableHandle))

/**
 * @brief Creates an event indicating a runnable stopped.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceRunnableStop() xTraceEventCreate0(PSF_EVENT_RUNNABLE_STOP)

/**
 * @brief Registers a set of static runnables. Requires XML configuration to properly interpret.
 *
 * @param[in] szName Name.
 * @param[in] uiMajor Major version.
 * @param[in] uiMinor Minor version.
 * @param[in] uiPatch Patch version.
 * @param[in] uiRunnableCount Runnables count.
 * @param[out] pxRunnableSetHandle Pointer to uninitialized TraceRunnableStaticSetHandle_t.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceRunnableRegisterStaticSet(szName, uiMajor, uiMinor, uiPatch, uiRunnableCount, pxRunnableSetHandle) xTraceExtensionCreate(szName, uiMajor, uiMinor, uiPatch, uiRunnableCount, pxRunnableSetHandle)

/**
 * @brief Start a static runnable. Requires XML configuration to properly interpret.
 *
 * @param[in] xRunnableSetHandle Handle to initialized runnable set.
 * @param[in] uiRunnableId Index in the runnable set.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceRunnableStartStatic(xRunnableSetHandle, uiRunnableId) xTraceEventCreate0(xTraceExtensionGetEventId(xRunnableSetHandle, uiRunnableId))

/**
 * @brief Stop a static runnable. Requires XML configuration to properly interpret.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceRunnableStopStatic() xTraceRunnableStop()

/** @} */

#ifdef __cplusplus
}
#endif

#else

#define xTraceRunnableRegister(_szName, _uxRegisterMethod, _pxRunnableHandle) \
	TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(_szName), (void)(_uxRegisterMethod), (void)(_pxRunnableHandle), TRC_SUCCESS)

#define xTraceRunnableStart(_xRunnableHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(_xRunnableHandle), TRC_SUCCESS)

#define xTraceRunnableStop() (TRC_SUCCESS)

#define xTraceRunnableRegisterStaticSet(_szName, _uiMajor, _uiMinor, _uiPatch, _uiRunnableCount, _pxRunnableSetHandle) \
	TRC_COMMA_EXPR_TO_STATEMENT_EXPR_7((void)(_szName), (void)(_uiMajor), (void)(_uiMinor), (void)(_uiPatch), (void)(_uiRunnableCount), (void)(_pxRunnableSetHandle), TRC_SUCCESS)

#define xTraceRunnableStartStatic(_xRunnableSetHandle, _uiRunnableId) \
	TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_xRunnableSetHandle), (void)(_uiRunnableId), TRC_SUCCESS)

#define xTraceRunnableStopStatic() (TRC_SUCCESS)

#endif

#endif
