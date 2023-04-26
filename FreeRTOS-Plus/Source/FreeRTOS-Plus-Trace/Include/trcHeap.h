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
 * @brief Public trace heap APIs.
 */

#ifndef TRC_HEAP_H
#define TRC_HEAP_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#ifndef TRC_USE_HEAPS
#define TRC_USE_HEAPS 1
#endif

#if (TRC_USE_HEAPS == 1)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_heap_apis Trace Heap APIs
 * @ingroup trace_recorder_apis
 * @{
 */

/**
 * @brief Creates trace heap.
 * 
 * @param[in] szName Name.
 * @param[in] uxCurrent Current level.
 * @param[in] uxHighWaterMark High water mark
 * @param[in] uxMax Maximum level.
 * @param[out] pxHeapHandle Pointer to uninitialized trace heap handle.
 * @return traceResult 
 */
traceResult xTraceHeapCreate(const char *szName, TraceUnsignedBaseType_t uxCurrent, TraceUnsignedBaseType_t uxHighWaterMark, TraceUnsignedBaseType_t uxMax, TraceHeapHandle_t *pxHeapHandle);

/**
 * @brief Signals trace heap alloc.
 * 
 * @param[in] xHeapHandle Pointer to initialized trace heap handle.
 * @param[in] pvAddress Address. 
 * @param[in] uxSize Size.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceHeapAlloc(TraceHeapHandle_t xHeapHandle, void *pvAddress, TraceUnsignedBaseType_t uxSize);

/**
 * @brief Signals trace heap free.
 * 
 * @param[in] xHeapHandle Pointer to initialized trace heap handle.
 * @param[in] pvAddress Address.
 * @param[in] uxSize Size.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceHeapFree(TraceHeapHandle_t xHeapHandle, void* pvAddress, TraceUnsignedBaseType_t uxSize);

/**
 * @brief Gets trace heap current allocation size.
 * 
 * @param[in] xHeapHandle Pointer to initialized trace heap handle.
 * @param[out] puxCurrent Current.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceHeapGetCurrent(TraceHeapHandle_t xHeapHandle, TraceUnsignedBaseType_t *puxCurrent);

/**
 * @brief Gets trace heap high water mark.
 * 
 * @param[in] xHeapHandle Pointer to initialized trace heap handle.
 * @param[out] puxHighWaterMark High water mark.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceHeapGetHighWaterMark(TraceHeapHandle_t xHeapHandle, TraceUnsignedBaseType_t *puxHighWaterMark);

/**
 * @brief Gets trace heap max size.
 * 
 * @param[in] xHeapHandle Pointer to initialized trace heap handle.
 * @param[out] puxMax Max.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceHeapGetMax(TraceHeapHandle_t xHeapHandle, TraceUnsignedBaseType_t *puxMax);

/** @} */

#ifdef __cplusplus
}
#endif

#else

#define xTraceHeapCreate(szName, uxCurrent, uxHighWaterMark, uxMax, pxHeapHandle) ((void)szName, (void)uxCurrent, (void)uxHighWaterMark, (void)uxMax, pxHeapHandle != 0 ? TRC_SUCCESS : TRC_FAIL)

#define xTraceHeapAlloc(xHeapHandle, pvAddress, uxSize) ((void)xHeapHandle, (void)pvAddress, (void)uxSize, TRC_SUCCESS)

#define xTraceHeapFree(xHeapHandle, pvAddress, uxSize) ((void)xHeapHandle, (void)pvAddress, (void)uxSize, TRC_SUCCESS)

#define xTraceHeapGetCurrent(xHeapHandle, puxCurrent) ((void)xHeapHandle, puxCurrent != 0 ? *puxCurrent = 0 : 0, puxCurrent != 0 ? TRC_SUCCESS : TRC_FAIL)

#define xTraceHeapGetHighWaterMark(xHeapHandle, puxHighWaterMark) ((void)xHeapHandle, puxHighWaterMark != 0 ? *puxHighWaterMark = 0 : 0, puxHighWaterMark != 0 ? TRC_SUCCESS : TRC_FAIL)

#define xTraceHeapGetMax(xHeapHandle, puxMax) ((void)xHeapHandle, puxMax != 0 ? *puxMax = 0 : 0, puxMax != 0 ? TRC_SUCCESS : TRC_FAIL)

#endif /* (TRC_USE_HEAPS == 1) */

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /* TRC_HEAP_H */
