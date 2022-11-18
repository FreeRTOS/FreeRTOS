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
 * @brief Public trace assert APIs.
 */

#ifndef TRC_ASSERT_H
#define TRC_ASSERT_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_assert_apis Trace Asserts APIs
 * @ingroup trace_recorder_apis
 * @{
 */

#ifndef TRC_CFG_USE_TRACE_ASSERT
#error "TRC_CFG_USE_TRACE_ASSERT is not defined. Please define it in trcConfig.h"
#endif

#if ((TRC_CFG_USE_TRACE_ASSERT) == 1)

/* Standard assert */
#define TRC_ASSERT(__condition) if (!(__condition)) { prvTraceAssertCreate(__FILE__, __LINE__); return TRC_FAIL; }

#define TRC_ASSERT_ALWAYS_EVALUATE TRC_ASSERT

/* Standard assert with custom on fail actions */
#define TRC_ASSERT_CUSTOM_ON_FAIL(__condition, __custom_on_fail) if (!(__condition)) { prvTraceAssertCreate(__FILE__, __LINE__); __custom_on_fail; }

#define TRC_ASSERT_CUSTOM_ON_FAIL_ALWAYS_EVALUATE TRC_ASSERT_CUSTOM_ON_FAIL

#if (defined(TRC_CFG_TEST_MODE) && (TRC_CFG_TEST_MODE) == 1)

/* Asserts that two types have an equal size. Condition passed to function to avoid compilers warning about unreachable code due to constant value. */
#define TRC_ASSERT_EQUAL_SIZE(x, y) if (!prvTraceAssertCheckCondition((TraceBaseType_t)(sizeof(x) == sizeof(y)))) { prvTraceAssertCreate(__FILE__, __LINE__); return TRC_FAIL; }

/**
 * @brief Inlined condition check to get around some compiler warnings for unused variables.
 *
 * @param[in] condition The condition
 */
inline TraceBaseType_t prvTraceAssertCheckCondition(TraceBaseType_t condition)
{
	return condition;
}

#else

#define TRC_ASSERT_EQUAL_SIZE(x, y) 

#endif

#define TRC_ASSERT_BUFFER_SIZE (sizeof(TraceEntryHandle_t))

typedef struct TraceAssertBuffer
{
	uint8_t buffer[TRC_ASSERT_BUFFER_SIZE];
} TraceAssertBuffer_t;

/**
 * @internal Initializes assert system
 *
 * @param[in] pxBuffer The assert data buffer
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceAssertInitialize(TraceAssertBuffer_t *pxBuffer);

/**
 * @internal Creates an assert
 *
 * @param[in] szFilePath File name
 * @param[in] uxLineNumber Line number
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
void prvTraceAssertCreate(const char* szFilePath, TraceUnsignedBaseType_t uxLineNumber);

/**
 * @brief Retrieves the assert and line number
 *
 * @param[out] pxFileNameStringHandle File name string handle
 * @param[out] puxLineNumber Line number
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceAssertGet(TraceStringHandle_t* pxFileNameStringHandle, TraceUnsignedBaseType_t* puxLineNumber);

#else /* ((TRC_CFG_USE_TRACE_ASSERT) == 1) */

#define TRC_ASSERT(__condition) 

#define TRC_ASSERT_ALWAYS_EVALUATE(__condition) (void)(__condition)

#define TRC_ASSERT_CUSTOM_ON_FAIL(__condition, __custom_on_fail) 

#define TRC_ASSERT_CUSTOM_ON_FAIL_ALWAYS_EVALUATE(__condition, __custom_on_fail) (__condition)

#define TRC_ASSERT_EQUAL_SIZE(x, y)

typedef struct TraceAssertBuffer
{
	uint32_t buffer[1];
} TraceAssertBuffer_t;

#define xTraceAssertInitialize(pxBuffer) ((void)pxBuffer, TRC_SUCCESS)

#define xTraceAssertGet(pxFileNameStringHandle, puxLineNumber) ((void)pxFileNameStringHandle, (void)puxLineNumber, TRC_FAIL)

#endif /* ((TRC_CFG_USE_TRACE_ASSERT) == 1) */

/** @} */

#ifdef __cplusplus
}
#endif

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /* TRC_ASSERT_H */
