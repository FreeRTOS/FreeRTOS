/*******************************************************************************
 * Tracealyzer v2.5.0 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcKernel.h
 *
 * Functions used by trcKernelHooks.h.
 *
 * Terms of Use
 * This software is copyright Percepio AB. The recorder library is free for
 * use together with Percepio products. You may distribute the recorder library
 * in its original form, including modifications in trcHardwarePort.c/.h
 * given that these modification are clearly marked as your own modifications
 * and documented in the initial comment section of these source files.
 * This software is the intellectual property of Percepio AB and may not be
 * sold or in other ways commercially redistributed without explicit written
 * permission by Percepio AB.
 *
 * Disclaimer
 * The trace tool and recorder library is being delivered to you AS IS and
 * Percepio AB makes no warranty as to its use or performance. Percepio AB does
 * not and cannot warrant the performance or results you may obtain by using the
 * software or documentation. Percepio AB make no warranties, express or
 * implied, as to noninfringement of third party rights, merchantability, or
 * fitness for any particular purpose. In no event will Percepio AB, its
 * technology partners, or distributors be liable to you for any consequential,
 * incidental or special damages, including any lost profits or lost savings,
 * even if a representative of Percepio AB has been advised of the possibility
 * of such damages, or for any claim by any third party. Some jurisdictions do
 * not allow the exclusion or limitation of incidental, consequential or special
 * damages, or the exclusion of implied warranties or limitations on how long an
 * implied warranty may last, so the above limitations may not apply to you.
 *
 * Copyright Percepio AB, 2013.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRCKERNEL_H
#define TRCKERNEL_H

#include "trcKernelPort.h"

#if (USE_TRACEALYZER_RECORDER == 1)

/* Internal functions */

#if !defined INCLUDE_READY_EVENTS || INCLUDE_READY_EVENTS == 1
void vTraceStoreTaskReady(objectHandleType handle);
#endif

void vTraceStoreLowPower(uint32_t flag);

void vTraceStoreTaskswitch(objectHandleType task_handle);

void vTraceStoreKernelCall(uint32_t eventcode, traceObjectClass objectClass, uint32_t byteParam);

void vTraceStoreKernelCallWithNumericParamOnly(uint32_t evtcode,
                                               uint32_t param);

void vTraceStoreKernelCallWithParam(uint32_t evtcode, traceObjectClass objectClass,
                                    uint32_t objectNumber, uint8_t param);

void vTraceSetTaskInstanceFinished(objectHandleType handle);

void vTraceSetPriorityProperty(uint8_t objectclass, uint8_t id, uint8_t value);

uint8_t uiTraceGetPriorityProperty(uint8_t objectclass, uint8_t id);

void vTraceSetObjectState(uint8_t objectclass, uint8_t id, uint8_t value);

uint8_t uiTraceGetObjectState(uint8_t objectclass, uint8_t id);

#if (INCLUDE_OBJECT_DELETE == 1)

void vTraceStoreObjectNameOnCloseEvent(objectHandleType handle,
                                       traceObjectClass objectclass);

void vTraceStoreObjectPropertiesOnCloseEvent(objectHandleType handle,
                                             traceObjectClass objectclass);
#endif

/* Internal constants for task state */
#define TASK_STATE_INSTANCE_NOT_ACTIVE 0
#define TASK_STATE_INSTANCE_ACTIVE 1
#define TASK_STATE_INSTANCE_MARKED_FINISHED 2


#endif

#endif