/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Configuration parameters for trace recorder library in snapshot mode.
 * Read more at http://percepio.com/2016/10/05/rtos-tracing/
 */

#ifndef TRC_SNAPSHOT_CONFIG_H
#define TRC_SNAPSHOT_CONFIG_H

#ifdef __cplusplus
    extern "C" {
#endif

/**
 * @def TRC_CFG_SNAPSHOT_MODE
 * @brief Macro which should be defined as one of:
 * - TRC_SNAPSHOT_MODE_RING_BUFFER
 * - TRC_SNAPSHOT_MODE_STOP_WHEN_FULL
 * Default is TRC_SNAPSHOT_MODE_RING_BUFFER.
 *
 * With TRC_CFG_SNAPSHOT_MODE set to TRC_SNAPSHOT_MODE_RING_BUFFER, the
 * events are stored in a ring buffer, i.e., where the oldest events are
 * overwritten when the buffer becomes full. This allows you to get the last
 * events leading up to an interesting state, e.g., an error, without having
 * to store the whole run since startup.
 *
 * When TRC_CFG_SNAPSHOT_MODE is TRC_SNAPSHOT_MODE_STOP_WHEN_FULL, the
 * recording is stopped when the buffer becomes full. This is useful for
 * recording events following a specific state, e.g., the startup sequence.
 */
#define TRC_CFG_SNAPSHOT_MODE            TRC_SNAPSHOT_MODE_RING_BUFFER

/**
 * @def TRC_CFG_EVENT_BUFFER_SIZE
 * @brief Macro which should be defined as an integer value.
 *
 * This defines the capacity of the event buffer, i.e., the number of records
 * it may store. Most events use one record (4 byte), although some events
 * require multiple 4-byte records. You should adjust this to the amount of RAM
 * available in the target system.
 *
 * Default value is 1000, which means that 4000 bytes is allocated for the
 * event buffer.
 */
#define TRC_CFG_EVENT_BUFFER_SIZE        250000

/**
 * @def TRC_CFG_INCLUDE_FLOAT_SUPPORT
 * @brief Macro which should be defined as either zero (0) or one (1).
 *
 * If this is zero (0), the support for logging floating point values in
 * vTracePrintF is stripped out, in case floating point values are not used or
 * supported by the platform used.
 *
 * Floating point values are only used in vTracePrintF and its subroutines, to
 * allow for storing float (%f) or double (%lf) arguments.
 *
 * vTracePrintF can be used with integer and string arguments in either case.
 *
 * Default value is 0.
 */
#define TRC_CFG_INCLUDE_FLOAT_SUPPORT    0

/**
 * @def TRC_CFG_SYMBOL_TABLE_SIZE
 * @brief Macro which should be defined as an integer value.
 *
 * This defines the capacity of the symbol table, in bytes. This symbol table
 * stores User Events labels and names of deleted tasks, queues, or other kernel
 * objects. If you don't use User Events or delete any kernel
 * objects you set this to a very low value. The minimum recommended value is 4.
 * A size of zero (0) is not allowed since a zero-sized array may result in a
 * 32-bit pointer, i.e., using 4 bytes rather than 0.
 *
 * Default value is 800.
 */
#define TRC_CFG_SYMBOL_TABLE_SIZE        8000

#if ( TRC_CFG_SYMBOL_TABLE_SIZE == 0 )
    #error "TRC_CFG_SYMBOL_TABLE_SIZE may not be zero!"
#endif

/******************************************************************************
 *** ADVANCED SETTINGS ********************************************************
 ******************************************************************************
 * The remaining settings are not necessary to modify but allows for optimizing
 * the recorder setup for your specific needs, e.g., to exclude events that you
 * are not interested in, in order to get longer traces.
 *****************************************************************************/

/**
 * @def TRC_CFG_HEAP_SIZE_BELOW_16M
 * @brief An integer constant that can be used to reduce the buffer usage of memory
 * allocation events (malloc/free). This value should be 1 if the heap size is
 * below 16 MB (2^24 byte), and you can live with reported addresses showing the
 * lower 24 bits only. If 0, you get the full 32-bit addresses.
 *
 * Default value is 0.
 */
#define TRC_CFG_HEAP_SIZE_BELOW_16M                0

/**
 * @def TRC_CFG_USE_IMPLICIT_IFE_RULES
 * @brief Macro which should be defined as either zero (0) or one (1).
 * Default is 1.
 *
 * Tracealyzer groups the events into "instances" based on Instance Finish
 * Events (IFEs), produced either by default rules or calls to the recorder
 * functions xTraceTaskInstanceFinishedNow and xTraceTaskInstanceFinishedNext.
 *
 * If TRC_CFG_USE_IMPLICIT_IFE_RULES is one (1), the default IFE rules is
 * used, resulting in a "typical" grouping of events into instances.
 * If these rules don't give appropriate instances in your case, you can
 * override the default rules using xTraceTaskInstanceFinishedNow/Next for one
 * or several tasks. The default IFE rules are then disabled for those tasks.
 *
 * If TRC_CFG_USE_IMPLICIT_IFE_RULES is zero (0), the implicit IFE rules are
 * disabled globally. You must then call xTraceTaskInstanceFinishedNow or
 * xTraceTaskInstanceFinishedNext to manually group the events into instances,
 * otherwise the tasks will appear a single long instance.
 *
 * The default IFE rules count the following events as "instance finished":
 * - Task delay, delay until
 * - Task suspend
 * - Blocking on "input" operations, i.e., when the task is waiting for the
 *   next a message/signal/event. But only if this event is blocking.
 */
#define TRC_CFG_USE_IMPLICIT_IFE_RULES             1

/**
 * @def TRC_CFG_USE_16BIT_OBJECT_HANDLES
 * @brief Macro which should be defined as either zero (0) or one (1).
 *
 * If set to 0 (zero), the recorder uses 8-bit handles to identify kernel
 * objects such as tasks and queues. This limits the supported number of
 * concurrently active objects to 255 of each type (tasks, queues, mutexes,
 * etc.) Note: 255, not 256, since handle 0 is reserved.
 *
 * If set to 1 (one), the recorder uses 16-bit handles to identify kernel
 * objects such as tasks and queues. This limits the supported number of
 * concurrent objects to 65535 of each type (object class). However, since the
 * object property table is limited to 64 KB, the practical limit is about
 * 3000 objects in total.
 *
 * Default is 0 (8-bit handles)
 *
 * NOTE: An object with handle above 255 will use an extra 4-byte record in
 * the event buffer whenever the object is referenced. Moreover, some internal
 * tables in the recorder gets slightly larger when using 16-bit handles.
 */
#define TRC_CFG_USE_16BIT_OBJECT_HANDLES           0

/**
 * @def TRC_CFG_USE_SEPARATE_USER_EVENT_BUFFER
 * @brief Macro which should be defined as an integer value.
 *
 * Set TRC_CFG_USE_SEPARATE_USER_EVENT_BUFFER to 1 to enable the
 * separate user event buffer (UB).
 * In this mode, user events are stored separately from other events,
 * e.g., RTOS events. Thereby you can get a much longer history of
 * user events as they don't need to share the buffer space with more
 * frequent events.
 *
 * The UB is typically used with the snapshot ring-buffer mode, so the
 * recording can continue when the main buffer gets full. And since the
 * main buffer then overwrites the earliest events, Tracealyzer displays
 * "Unknown Actor" instead of task scheduling for periods with UB data only.
 *
 * In UB mode, user events are structured as UB channels, which contains
 * a channel name and a default format string. Register a UB channel using
 * xTraceRegisterUBChannel.
 *
 * Events and data arguments are written using vTraceUBEvent and
 * vTraceUBData. They are designed to provide efficient logging of
 * repeating events, using the same format string within each channel.
 *
 * Examples:
 *  TraceStringHandle_t chn1;
 *  TraceStringHandle_t fmt1;
 *  xTraceStringRegister("Channel 1", &chn1);
 *  xTraceStringRegister("Event!", &fmt1);
 *  traceUBChannel UBCh1 = xTraceRegisterUBChannel(chn1, fmt1);
 *
 *  TraceStringHandle_t chn2;
 *  TraceStringHandle_t fmt2;
 *  xTraceStringRegister("Channel 2", &chn2);
 *  xTraceStringRegister("X: %d, Y: %d", &fmt2);
 *  traceUBChannel UBCh2 = xTraceRegisterUBChannel(chn2, fmt2);
 *
 *  // Result in "[Channel 1] Event!"
 *	vTraceUBEvent(UBCh1);
 *
 *  // Result in "[Channel 2] X: 23, Y: 19"
 *	vTraceUBData(UBCh2, 23, 19);
 *
 * You can also use the other user event functions, like xTracePrintF.
 * as they are then rerouted to the UB instead of the main event buffer.
 * vTracePrintF then looks up the correct UB channel based on the
 * provided channel name and format string, or creates a new UB channel
 * if no match is found. The format string should therefore not contain
 * "random" messages but mainly format specifiers. Random strings should
 * be stored using %s and with the string as an argument.
 *
 *  // Creates a new UB channel ("Channel 2", "%Z: %d")
 *  xTracePrintF(chn2, "%Z: %d", value1);
 *
 *  // Finds the existing UB channel
 *  xTracePrintF(chn2, "%Z: %d", value2);
 */
#define TRC_CFG_USE_SEPARATE_USER_EVENT_BUFFER     0

/**
 * @def TRC_CFG_SEPARATE_USER_EVENT_BUFFER_SIZE
 * @brief Macro which should be defined as an integer value.
 *
 * This defines the capacity of the user event buffer (UB), in number of slots.
 * A single user event can use multiple slots, depending on the arguments.
 *
 * Only applicable if TRC_CFG_USE_SEPARATE_USER_EVENT_BUFFER is 1.
 */
#define TRC_CFG_SEPARATE_USER_EVENT_BUFFER_SIZE    200

/**
 * @def TRC_CFG_UB_CHANNELS
 * @brief Macro which should be defined as an integer value.
 *
 * This defines the number of User Event Buffer Channels (UB channels).
 * These are used to structure the events when using the separate user
 * event buffer, and contains both a User Event Channel (the name) and
 * a default format string for the channel.
 *
 * Only applicable if TRC_CFG_USE_SEPARATE_USER_EVENT_BUFFER is 1.
 */
#define TRC_CFG_UB_CHANNELS                        32

#ifdef __cplusplus
}
#endif

#endif /*TRC_SNAPSHOT_CONFIG_H*/
