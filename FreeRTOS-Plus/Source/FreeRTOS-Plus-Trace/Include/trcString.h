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
 * @brief Public trace string APIs.
 */

#ifndef TRC_STRING_H
#define TRC_STRING_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_string_apis Trace String APIs
 * @ingroup trace_recorder_apis
 * @{
 */

/**
 * @brief Registers a trace string.
 * 
 * This routine registers a strings in the recorder, e.g. for names of user
 * event channels.
 *
 * Example:
 *	 TraceStringHandle_t myEventHandle;
 *	 xTraceStringRegister("MyUserEvent", &myEventHandle);
 *	 ...
 *	 xTracePrintF(myEventHandle, "My value is: %d", myValue);
 * 
 * @param[in] szString String.
 * @param[out] pString Pointer to uninitialized trace string.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStringRegister(const char *szString, TraceStringHandle_t* pString);

/**
 * @brief Registers a trace string. 
 * 
 * @deprecated Remains for backward compability with pre v4.6 versions
 * of the recorder.
 * 
 * @param[in] name Name.
 * 
 * @return TraceStringHandle_t 
 */
TraceStringHandle_t xTraceRegisterString(const char *name);

/** @} */

#ifdef __cplusplus
}
#endif

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /* TRC_STRING_H */
