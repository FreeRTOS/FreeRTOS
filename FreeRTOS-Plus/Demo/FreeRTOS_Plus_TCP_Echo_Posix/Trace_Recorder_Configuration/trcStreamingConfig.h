/*
 * Trace Recorder for Tracealyzer v4.8.1
 * Copyright 2023 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Configuration parameters for the trace recorder library in streaming mode.
 * Read more at http://percepio.com/2016/10/05/rtos-tracing/
 */

#ifndef TRC_STREAMING_CONFIG_H
    #define TRC_STREAMING_CONFIG_H

    #ifdef __cplusplus
    extern "C" {
    #endif

/**
 * @def TRC_CFG_ENTRY_SLOTS
 * @brief The maximum number of objects and symbols that can be stored. This includes:
 * - Task names
 * - Named ISRs (vTraceSetISRProperties)
 * - Named kernel objects (vTraceStoreKernelObjectName)
 * - User event channels (xTraceStringRegister)
 *
 * If this value is too small, not all symbol names will be stored and the
 * trace display will be affected. In that case, there will be warnings
 * (as User Events) from TzCtrl task, that monitors this.
 */
    #define TRC_CFG_ENTRY_SLOTS                50

/**
 * @def TRC_CFG_ENTRY_SYMBOL_MAX_LENGTH
 * @brief The maximum length of symbol names, including:
 * - Task names
 * - Named ISRs (vTraceSetISRProperties)
 * - Named kernel objects (vTraceStoreKernelObjectName)
 * - User event channel names (xTraceStringRegister)
 *
 * If longer symbol names are used, they will be truncated by the recorder,
 * which will affect the trace display. In that case, there will be warnings
 * (as User Events) from TzCtrl task, that monitors this.
 */
    #define TRC_CFG_ENTRY_SYMBOL_MAX_LENGTH    28

    #ifdef __cplusplus
}
    #endif

#endif /* TRC_STREAMING_CONFIG_H */
