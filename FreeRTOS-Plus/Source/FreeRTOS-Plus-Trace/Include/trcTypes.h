/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The common types.
*/

#ifndef TRC_TYPES_H
#define TRC_TYPES_H

#include <stdint.h>
#include <trcConfig.h>
#include <trcHardwarePort.h>

#ifdef __cplusplus
extern "C" {
#endif

#ifndef TRC_BASE_TYPE
#define TRC_BASE_TYPE int32_t
#endif

#ifndef TRC_UNSIGNED_BASE_TYPE
#define TRC_UNSIGNED_BASE_TYPE uint32_t
#endif

typedef TRC_UNSIGNED_BASE_TYPE TraceUnsignedBaseType_t;

typedef TRC_BASE_TYPE TraceBaseType_t;

typedef TraceUnsignedBaseType_t traceResult;

typedef TraceUnsignedBaseType_t TraceEventHandle_t;

typedef TraceUnsignedBaseType_t TraceISRHandle_t;

typedef TraceUnsignedBaseType_t TraceEntryHandle_t;

typedef TraceUnsignedBaseType_t TraceTaskHandle_t;

typedef TraceUnsignedBaseType_t TraceObjectHandle_t;

typedef TraceUnsignedBaseType_t TraceExtensionHandle_t;

typedef TraceUnsignedBaseType_t TraceHeapHandle_t;

typedef TraceUnsignedBaseType_t TraceIntervalHandle_t;

typedef TraceUnsignedBaseType_t TraceStateMachineHandle_t;

typedef TraceUnsignedBaseType_t TraceStateMachineStateHandle_t;

typedef TraceUnsignedBaseType_t TraceStringHandle_t;

typedef TraceUnsignedBaseType_t TraceCounterHandle_t;

typedef void (*TraceCounterCallback_t)(TraceCounterHandle_t xCounterHandle);

/* DEPRECATED. Backwards compatibility */
typedef TraceStringHandle_t traceString;

#ifdef __cplusplus
}
#endif

#endif /* TRC_TYPES_H */
