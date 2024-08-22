/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Kernel port configuration parameters for snapshot mode.
 */

#ifndef TRC_KERNEL_PORT_SNAPSHOT_CONFIG_H
    #define TRC_KERNEL_PORT_SNAPSHOT_CONFIG_H

    #ifdef __cplusplus
    extern "C" {
    #endif

/**
 * @def TRC_CFG_NTASK, TRC_CFG_NISR, TRC_CFG_NQUEUE, TRC_CFG_NSEMAPHORE...
 * @brief A group of macros which should be defined as integer values, zero or larger.
 *
 * These define the capacity of the Object Property Table, i.e., the maximum
 * number of objects active at any given point, within each object class (e.g.,
 * task, queue, semaphore, ...).
 *
 * If tasks or other objects are deleted in your system, this
 * setting does not limit the total amount of objects created, only the number
 * of objects that have been successfully created but not yet deleted.
 *
 * Using too small values will cause vTraceError to be called, which stores an
 * error message in the trace that is shown when opening the trace file. The
 * error message can also be retrieved using xTraceGetLastError.
 *
 * It can be wise to start with large values for these constants,
 * unless you are very confident on these numbers. Then do a recording and
 * check the actual usage by selecting View menu -> Trace Details ->
 * Resource Usage -> Object Table.
 */
    #define TRC_CFG_NTASK                     150
    #define TRC_CFG_NISR                      90
    #define TRC_CFG_NQUEUE                    90
    #define TRC_CFG_NSEMAPHORE                90
    #define TRC_CFG_NMUTEX                    90
    #define TRC_CFG_NTIMER                    250
    #define TRC_CFG_NEVENTGROUP               90
    #define TRC_CFG_NSTREAMBUFFER             50
    #define TRC_CFG_NMESSAGEBUFFER            50

/**
 * @def TRC_CFG_NAME_LEN_TASK, TRC_CFG_NAME_LEN_QUEUE, ...
 * @brief Macros that specify the maximum lengths (number of characters) for names of
 * kernel objects, such as tasks and queues. If longer names are used, they will
 * be truncated when stored in the recorder.
 */
    #define TRC_CFG_NAME_LEN_TASK             15
    #define TRC_CFG_NAME_LEN_ISR              15
    #define TRC_CFG_NAME_LEN_QUEUE            15
    #define TRC_CFG_NAME_LEN_SEMAPHORE        15
    #define TRC_CFG_NAME_LEN_MUTEX            15
    #define TRC_CFG_NAME_LEN_TIMER            15
    #define TRC_CFG_NAME_LEN_EVENTGROUP       15
    #define TRC_CFG_NAME_LEN_STREAMBUFFER     15
    #define TRC_CFG_NAME_LEN_MESSAGEBUFFER    15

    #ifdef __cplusplus
}
    #endif

#endif /* TRC_KERNEL_PORT_SNAPSHOT_CONFIG_H */
