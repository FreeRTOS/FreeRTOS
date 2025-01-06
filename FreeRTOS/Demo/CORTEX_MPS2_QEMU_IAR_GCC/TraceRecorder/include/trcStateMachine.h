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
 * @brief Public trace state machine APIs.
 */

#ifndef TRC_STATE_MACHINE_H
#define TRC_STATE_MACHINE_H

#include <trcTypes.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_state_machine_apis Trace State Machine APIs
 * @ingroup trace_recorder_apis
 * @{
 */

/**
 * @brief Creates trace state machine.
 * 
 * @param[in] szName Name.
 * @param[out] pxStateMachineHandle Pointer to uninitialized trace state machine. 
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStateMachineCreate(const char *szName, TraceStateMachineHandle_t *pxStateMachineHandle);

/**
 * @brief Creates trace state machine state.
 * 
 * @param[in] xStateMachineHandle Pointer to initialized trace state machine.
 * @param[in] szName Name.
 * @param[out] pxStateHandle Pointer to uninitialized trace state machine state.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStateMachineStateCreate(TraceStateMachineHandle_t xStateMachineHandle, const char *szName, TraceStateMachineStateHandle_t *pxStateHandle);

/**
 * @brief Sets trace state machine state.
 * 
 * @param[in] xStateMachineHandle Pointer to initialized trace state machine.
 * @param[in] xStateHandle Pointer to initialized trace state machine state.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStateMachineSetState(TraceStateMachineHandle_t xStateMachineHandle, TraceStateMachineStateHandle_t xStateHandle);

/** @} */

#ifdef __cplusplus
}
#endif

#else

#define xTraceStateMachineCreate(__szName, __pxStateMachineHandle) ((void)(__szName), (void)(__pxStateMachineHandle), TRC_SUCCESS)

#define xTraceStateMachineStateCreate(__xStateMachineHandle, __szName, __pxStateHandle) ((void)(__xStateMachineHandle), (void)(__szName), (void)(__pxStateHandle), TRC_SUCCESS)

#define xTraceStateMachineSetState(__xStateMachineHandle, __xStateHandle) ((void)(__xStateMachineHandle), (void)(__xStateHandle), TRC_SUCCESS)

#endif

#endif
