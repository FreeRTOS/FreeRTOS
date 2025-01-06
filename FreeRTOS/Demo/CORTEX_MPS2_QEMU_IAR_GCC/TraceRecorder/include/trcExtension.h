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
 * @brief Public trace extension APIs.
 */

#ifndef TRC_EXTENSION_H
#define TRC_EXTENSION_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

#define TRC_EXTENSION_STATE_INDEX_VERSION 0
#define TRC_EXTENSION_STATE_INDEX_BASE_EVENT_ID 1
#define TRC_EXTENSION_STATE_INDEX_EVENT_COUNT 2

/**
 * @defgroup trace_extension_apis Trace Extension APIs
 * @ingroup trace_recorder_apis
 * @{
 */

typedef struct TraceExtensionData	/* Aligned */
{
	TraceUnsignedBaseType_t uxNextFreeExtensionEventId;
} TraceExtensionData_t;

/**
 * @brief Initializes the Extension trace system
 * 
 * @param[in] pxBuffer Pointer to memory that is used by the extension trace system
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceExtensionInitialize(TraceExtensionData_t* const pxBuffer);

/**
 * @brief Creates trace extension.
 * 
 * @param[in] szName Name.
 * @param[in] uiMajor Major version.
 * @param[in] uiMinor Minor version.
 * @param[in] uiPatch Patch version.
 * @param[in] uiEventCount Event count.
 * @param[out] pxExtensionHandle Pointer to uninitialized extension handle.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceExtensionCreate(const char *szName, uint8_t uiMajor, uint8_t uiMinor, uint16_t uiPatch, uint32_t uiEventCount, TraceExtensionHandle_t *pxExtensionHandle);

/**
 * @brief Gets extension base event id.
 * 
 * @param[in] xExtensionHandle Pointer to initialized extension handle.
 * @param[out] puiBaseEventId Base event id.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceExtensionGetBaseEventId(TraceExtensionHandle_t xExtensionHandle, uint32_t *puiBaseEventId);

/**
 * @brief Gets extension configuration name.
 *
 * @param[in] xExtensionHandle Pointer to initialized extension handle.
 * @param[out] pszName Name.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceExtensionGetConfigName(TraceExtensionHandle_t xExtensionHandle, const char** pszName);

/**
 * @brief Returns extension event id.
 * 
 * @param[in] xExtensionHandle Pointer to initialized extension handle.
 * @param[in] uiLocalEventId Local event id.
 * 
 * @returns Extension event id
 */
#define xTraceExtensionGetEventId(xExtensionHandle, uiLocalEventId) ((uint32_t)xTraceEntryGetStateReturn((TraceEntryHandle_t)(xExtensionHandle), TRC_EXTENSION_STATE_INDEX_BASE_EVENT_ID) + (uiLocalEventId))

/** @} */

#ifdef __cplusplus
}
#endif

#else

#define xTraceExtensionCreate(szName, uiMajor, uiMinor, uiPatch, uiEventCount, pxExtensionHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_7((void)(szName), (void)(uiMajor), (void)(uiMinor), (void)(uiPatch), (void)(uiEventCount), (void)(pxExtensionHandle), TRC_SUCCESS)

#define xTraceExtensionGetBaseEventId(xExtensionHandle, puiBaseEventId) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(xExtensionHandle), (void)(puiBaseEventId), TRC_SUCCESS)

#define xTraceExtensionGetConfigName(xExtensionHandle, pszName) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(xExtensionHandle), (void)(pszName), TRC_SUCCESS)

#define xTraceExtensionGetEventId(xExtensionHandle, uiLocalEventId) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(xExtensionHandle), (void)(uiLocalEventId), 0)

#endif

#endif
