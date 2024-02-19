/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Main configuration parameters for the trace recorder library.
 * More settings can be found in trcStreamingConfig.h and trcSnapshotConfig.h.
 */

#ifndef TRC_CONFIG_H
    #define TRC_CONFIG_H

    #ifdef __cplusplus
    extern "C" {
    #endif

/******************************************************************************
 * Include of processor header file
 *
 * Here you may need to include the header file for your processor. This is
 * required at least for the ARM Cortex-M port, that uses the ARM CMSIS API.
 * Try that in case of build problems. Otherwise, remove the #error line below.
 *****************************************************************************/
/*#error "Trace Recorder: Please include your processor's header file here and remove this line." */

/**
 * @def TRC_CFG_HARDWARE_PORT
 * @brief Specify what hardware port to use (i.e., the "timestamping driver").
 *
 * All ARM Cortex-M MCUs are supported by "TRC_HARDWARE_PORT_ARM_Cortex_M".
 * This port uses the DWT cycle counter for Cortex-M3/M4/M7 devices, which is
 * available on most such devices. In case your device don't have DWT support,
 * you will get an error message opening the trace. In that case, you may
 * force the recorder to use SysTick timestamping instead, using this define:
 *
 * #define TRC_CFG_ARM_CM_USE_SYSTICK
 *
 * For ARM Cortex-M0/M0+ devices, SysTick mode is used automatically.
 *
 * See trcHardwarePort.h for available ports and information on how to
 * define your own port, if not already present.
 */
    #define TRC_CFG_HARDWARE_PORT                 TRC_HARDWARE_PORT_Win64

/**
 * @def TRC_CFG_SCHEDULING_ONLY
 * @brief Macro which should be defined as an integer value.
 *
 * If this setting is enabled (= 1), only scheduling events are recorded.
 * If disabled (= 0), all events are recorded (unless filtered in other ways).
 *
 * Default value is 0 (= include additional events).
 */
    #define TRC_CFG_SCHEDULING_ONLY               0

/**
 * @def TRC_CFG_INCLUDE_MEMMANG_EVENTS
 * @brief Macro which should be defined as either zero (0) or one (1).
 *
 * This controls if malloc and free calls should be traced. Set this to zero (0)
 * to exclude malloc/free calls, or one (1) to include such events in the trace.
 *
 * Default value is 1.
 */
    #define TRC_CFG_INCLUDE_MEMMANG_EVENTS        1

/**
 * @def TRC_CFG_INCLUDE_USER_EVENTS
 * @brief Macro which should be defined as either zero (0) or one (1).
 *
 * If this is zero (0), all code related to User Events is excluded in order
 * to reduce code size. Any attempts of storing User Events are then silently
 * ignored.
 *
 * User Events are application-generated events, like "printf" but for the
 * trace log, generated using vTracePrint and vTracePrintF.
 * The formatting is done on host-side, by Tracealyzer. User Events are
 * therefore much faster than a console printf and can often be used
 * in timing critical code without problems.
 *
 * Note: In streaming mode, User Events are used to provide error messages
 * and warnings from the recorder (in case of incorrect configuration) for
 * display in Tracealyzer. Disabling user events will also disable these
 * warnings. You can however still catch them by calling xTraceErrorGetLast
 * or by putting breakpoints in xTraceError and xTraceWarning.
 *
 * Default value is 1.
 */
    #define TRC_CFG_INCLUDE_USER_EVENTS           1

/**
 * @def TRC_CFG_INCLUDE_ISR_TRACING
 * @brief Macro which should be defined as either zero (0) or one (1).
 *
 * If this is zero (0), the code for recording Interrupt Service Routines is
 * excluded, in order to reduce code size. This means that any calls to
 * vTraceStoreISRBegin/vTraceStoreISREnd will be ignored.
 * This does not completely disable ISR tracing, in cases where an ISR is
 * calling a traced kernel service. These events will still be recorded and
 * show up in anonymous ISR instances in Tracealyzer, with names such as
 * "ISR sending to <queue name>".
 * To disable such tracing, please refer to vTraceSetFilterGroup and
 * vTraceSetFilterMask.
 *
 * Default value is 1.
 *
 * Note: tracing ISRs requires that you insert calls to vTraceStoreISRBegin
 * and vTraceStoreISREnd in your interrupt handlers.
 */
    #define TRC_CFG_INCLUDE_ISR_TRACING           1

/**
 * @def TRC_CFG_INCLUDE_READY_EVENTS
 * @brief Macro which should be defined as either zero (0) or one (1).
 *
 * If one (1), events are recorded when tasks enter scheduling state "ready".
 * This allows Tracealyzer to show the initial pending time before tasks enter
 * the execution state, and present accurate response times.
 * If zero (0), "ready events" are not created, which allows for recording
 * longer traces in the same amount of RAM.
 *
 * Default value is 1.
 */
    #define TRC_CFG_INCLUDE_READY_EVENTS          1

/**
 * @def TRC_CFG_INCLUDE_OSTICK_EVENTS
 * @brief Macro which should be defined as either zero (0) or one (1).
 *
 * If this is one (1), events will be generated whenever the OS clock is
 * increased. If zero (0), OS tick events are not generated, which allows for
 * recording longer traces in the same amount of RAM.
 *
 * Default value is 1.
 */
    #define TRC_CFG_INCLUDE_OSTICK_EVENTS         1

/**
 * @def TRC_CFG_ENABLE_STACK_MONITOR
 * @brief If enabled (1), the recorder periodically reports the unused stack space of
 * all active tasks.
 * The stack monitoring runs in the Tracealyzer Control task, TzCtrl. This task
 * is always created by the recorder when in streaming mode.
 * In snapshot mode, the TzCtrl task is only used for stack monitoring and is
 * not created unless this is enabled.
 */
    #define TRC_CFG_ENABLE_STACK_MONITOR          1

/**
 * @def TRC_CFG_STACK_MONITOR_MAX_TASKS
 * @brief Macro which should be defined as a non-zero integer value.
 *
 * This controls how many tasks that can be monitored by the stack monitor.
 * If this is too small, some tasks will be excluded and a warning is shown.
 *
 * Default value is 10.
 */
    #define TRC_CFG_STACK_MONITOR_MAX_TASKS       10

/**
 * @def TRC_CFG_STACK_MONITOR_MAX_REPORTS
 * @brief Macro which should be defined as a non-zero integer value.
 *
 * This defines how many tasks that will be subject to stack usage analysis for
 * each execution of the Tracealyzer Control task (TzCtrl). Note that the stack
 * monitoring cycles between the tasks, so this does not affect WHICH tasks that
 * are monitored, but HOW OFTEN each task stack is analyzed.
 *
 * This setting can be combined with TRC_CFG_CTRL_TASK_DELAY to tune the
 * frequency of the stack monitoring. This is motivated since the stack analysis
 * can take some time to execute.
 * However, note that the stack analysis runs in a separate task (TzCtrl) that
 * can be executed on low priority. This way, you can avoid that the stack
 * analysis disturbs any time-sensitive tasks.
 *
 * Default value is 1.
 */
    #define TRC_CFG_STACK_MONITOR_MAX_REPORTS     1

/**
 * @def TRC_CFG_CTRL_TASK_PRIORITY
 * @brief The scheduling priority of the Tracealyzer Control (TzCtrl) task.
 *
 * In streaming mode, TzCtrl is used to receive start/stop commands from
 * Tracealyzer and in some cases also to transmit the trace data (for stream
 * ports that uses the internal buffer, like TCP/IP). For such stream ports,
 * make sure the TzCtrl priority is high enough to ensure reliable periodic
 * execution and transfer of the data, but low enough to avoid disturbing any
 * time-sensitive functions.
 *
 * In Snapshot mode, TzCtrl is only used for the stack usage monitoring and is
 * not created if stack monitoring is disabled. TRC_CFG_CTRL_TASK_PRIORITY should
 * be low, to avoid disturbing any time-sensitive tasks.
 */
    #define TRC_CFG_CTRL_TASK_PRIORITY            1

/**
 * @def TRC_CFG_CTRL_TASK_DELAY
 * @brief The delay between loops of the TzCtrl task (see TRC_CFG_CTRL_TASK_PRIORITY),
 * which affects the frequency of the stack monitoring.
 *
 * In streaming mode, this also affects the trace data transfer if you are using
 * a stream port leveraging the internal buffer (like TCP/IP). A shorter delay
 * increases the CPU load of TzCtrl somewhat, but may improve the performance of
 * of the trace streaming, especially if the trace buffer is small.
 */
    #define TRC_CFG_CTRL_TASK_DELAY               2

/**
 * @def TRC_CFG_CTRL_TASK_STACK_SIZE
 * @brief The stack size of the Tracealyzer Control (TzCtrl) task.
 * See TRC_CFG_CTRL_TASK_PRIORITY for further information about TzCtrl.
 */
    #define TRC_CFG_CTRL_TASK_STACK_SIZE          4096

/**
 * @def TRC_CFG_RECORDER_BUFFER_ALLOCATION
 * @brief Specifies how the recorder buffer is allocated (also in case of streaming, in
 * port using the recorder's internal temporary buffer)
 *
 * Values:
 * TRC_RECORDER_BUFFER_ALLOCATION_STATIC  - Static allocation (internal)
 * TRC_RECORDER_BUFFER_ALLOCATION_DYNAMIC - Malloc in vTraceEnable
 * TRC_RECORDER_BUFFER_ALLOCATION_CUSTOM  - Use vTraceSetRecorderDataBuffer
 *
 * Static and dynamic mode does the allocation for you, either in compile time
 * (static) or in runtime (malloc).
 * The custom mode allows you to control how and where the allocation is made,
 * for details see TRC_ALLOC_CUSTOM_BUFFER and vTraceSetRecorderDataBuffer().
 */
    #define TRC_CFG_RECORDER_BUFFER_ALLOCATION    TRC_RECORDER_BUFFER_ALLOCATION_STATIC

/**
 * @def TRC_CFG_MAX_ISR_NESTING
 * @brief Defines how many levels of interrupt nesting the recorder can handle, in
 * case multiple ISRs are traced and ISR nesting is possible. If this
 * is exceeded, the particular ISR will not be traced and the recorder then
 * logs an error message. This setting is used to allocate an internal stack
 * for keeping track of the previous execution context (4 byte per entry).
 *
 * This value must be a non-zero positive constant, at least 1.
 *
 * Default value: 8
 */
    #define TRC_CFG_MAX_ISR_NESTING               8

/**
 * @def TRC_CFG_ISR_TAILCHAINING_THRESHOLD
 * @brief Macro which should be defined as an integer value.
 *
 * If tracing multiple ISRs, this setting allows for accurate display of the
 * context-switching also in cases when the ISRs execute in direct sequence.
 *
 * vTraceStoreISREnd normally assumes that the ISR returns to the previous
 * context, i.e., a task or a preempted ISR. But if another traced ISR
 * executes in direct sequence, Tracealyzer may incorrectly display a minimal
 * fragment of the previous context in between the ISRs.
 *
 * By using TRC_CFG_ISR_TAILCHAINING_THRESHOLD you can avoid this. This is
 * however a threshold value that must be measured for your specific setup.
 * See http://percepio.com/2014/03/21/isr_tailchaining_threshold/
 *
 * The default setting is 0, meaning "disabled" and that you may get an
 * extra fragments of the previous context in between tail-chained ISRs.
 *
 * Note: This setting has separate definitions in trcSnapshotConfig.h and
 * trcStreamingConfig.h, since it is affected by the recorder mode.
 */
    #define TRC_CFG_ISR_TAILCHAINING_THRESHOLD    0

/**
 * @def TRC_CFG_RECORDER_DATA_INIT
 * @brief Macro which states wether the recorder data should have an initial value.
 *
 * In very specific cases where traced objects are created before main(),
 * the recorder will need to be started even before that. In these cases,
 * the recorder data would be initialized by vTraceEnable(TRC_INIT) but could
 * then later be overwritten by the initialization value.
 * If this is an issue for you, set TRC_CFG_RECORDER_DATA_INIT to 0.
 * The following code can then be used before any traced objects are created:
 *
 *	extern uint32_t RecorderEnabled;
 *	RecorderEnabled = 0;
 *	xTraceInitialize();
 *
 * After the clocks are properly initialized, use vTraceEnable(...) to start
 * the tracing.
 *
 * Default value is 1.
 */
    #define TRC_CFG_RECORDER_DATA_INIT            1

/**
 * @def TRC_CFG_RECORDER_DATA_ATTRIBUTE
 * @brief When setting TRC_CFG_RECORDER_DATA_INIT to 0, you might also need to make
 * sure certain recorder data is placed in a specific RAM section to avoid being
 * zeroed out after initialization. Define TRC_CFG_RECORDER_DATA_ATTRIBUTE as
 * that attribute.
 *
 * Example:
 * #define TRC_CFG_RECORDER_DATA_ATTRIBUTE __attribute__((section(".bss.trace_recorder_data")))
 *
 * Default value is empty.
 */
    #define TRC_CFG_RECORDER_DATA_ATTRIBUTE

/**
 * @def TRC_CFG_USE_TRACE_ASSERT
 * @brief Enable or disable debug asserts. Information regarding any assert that is
 * triggered will be in trcAssert.c.
 */
    #define TRC_CFG_USE_TRACE_ASSERT    1

    #ifdef __cplusplus
}
    #endif

#endif /* _TRC_CONFIG_H */
