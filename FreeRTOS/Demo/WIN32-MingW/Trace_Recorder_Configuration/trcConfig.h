/*******************************************************************************
 * Tracealyzer v2.4.1 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcConfig.h
 *
 * Configuration parameters for the trace recorder library. Before using the 
 * trace recorder library, please check that the default settings are 
 * appropriate for your system, and if necessary adjust these. Most likely, you 
 * will need to adjust the NTask, NISR, NQueue, NMutex and NSemaphore values to 
 * reflect the number of such objects in your system. These may be 
 * over-approximated, although larger values values implies more RAM usage.
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

#ifndef TRCCONFIG_H
#define TRCCONFIG_H

#include <stdint.h>

/*******************************************************************************
 * CONFIGURATION RELATED TO CAPACITY AND ALLOCATION 
 ******************************************************************************/

/*******************************************************************************
 * EVENT_BUFFER_SIZE
 *
 * Macro which should be defined as an integer value.
 *
 * This defines the capacity of the event buffer, i.e., the number of records
 * it may store. Each registered event typically use one record (4 byte), but
 * vTracePrintF may use multiple records depending on the number of data args.
 ******************************************************************************/

#define EVENT_BUFFER_SIZE 100000 /* Adjust wrt. to available RAM */


/*******************************************************************************
 * USE_LINKER_PRAGMA
 *
 * Macro which should be defined as an integer value, default is 0.
 *
 * If this is 1, the header file "recorderdata_linker_pragma.h" is included just
 * before the declaration of RecorderData (in trcBase.c), i.e., the trace data 
 * structure. This allows the user to specify a pragma with linker options. 
 *
 * Example (for IAR Embedded Workbench and NXP LPC17xx):
 * #pragma location="AHB_RAM_MEMORY"
 * 
 * This example instructs the IAR linker to place RecorderData in another RAM 
 * bank, the AHB RAM. This can also be used for other compilers with a similar
 * pragmas for linker options.
 * 
 * Note that this only applies if using static allocation, see below.
 ******************************************************************************/

#define USE_LINKER_PRAGMA 0


/*******************************************************************************
 * SYMBOL_TABLE_SIZE
 *
 * Macro which should be defined as an integer value.
 *
 * This defines the capacity of the symbol table, in bytes. This symbol table 
 * stores User Events labels and names of deleted tasks, queues, or other kernel
 * objects. Note that the names of active objects not stored here but in the 
 * Object Table. Thus, if you don't use User Events or delete any kernel 
 * objects you set this to zero (0) to minimize RAM usage.
 ******************************************************************************/
#define SYMBOL_TABLE_SIZE 5000

/*******************************************************************************
 * USE_SEPARATE_USER_EVENT_BUFFER
 *
 * Macro which should be defined as an integer value.
 * Default is zero (0).
 *
 * This enables and disables the use of the separate user event buffer.
 *
 * Note: When using the separate user event buffer, you may get an artificial
 * task instance named "Unknown actor". This is added as a placeholder when the 
 * user event history is longer than the task scheduling history.
 ******************************************************************************/
#define USE_SEPARATE_USER_EVENT_BUFFER 0

/*******************************************************************************
 * USER_EVENT_BUFFER_SIZE
 *
 * Macro which should be defined as an integer value.
 *
 * This defines the capacity of the user event buffer, in number of slots.
 * A single user event can use between 1 and X slots, depending on the data.
 *
 * Only in use if USE_SEPARATE_USER_EVENT_BUFFER is set to 1.
 ******************************************************************************/
#define USER_EVENT_BUFFER_SIZE 500

/*******************************************************************************
 * USER_EVENT_CHANNELS
 *
 * Macro which should be defined as an integer value.
 *
 * This defines the number of allowed user event channels.
 *
 * Only in use if USE_SEPARATE_USER_EVENT_BUFFER is set to 1.
 ******************************************************************************/
#define CHANNEL_FORMAT_PAIRS 32

/*******************************************************************************
 * NTask, NISR, NQueue, NSemaphore, NMutex
 *
 * A group of Macros which should be defined as an integer value of zero (0) 
 * or larger.
 *
 * This defines the capacity of the Object Property Table - the maximum number
 * of objects active at any given point within each object class.
 * 
 * NOTE: In case objects are deleted and created during runtime, this setting
 * does not limit the total amount of objects, only the number of concurrently
 * active objects. 
 *
 * Using too small values will give an error message through the vTraceError
 * routine, which makes the error message appear when opening the trace data
 * in Tracealyzer. If you are using the recorder status monitor task,
 * any error messages are displayed in console prints, assuming that the
 * print macro has been defined properly (vConsolePrintMessage). 
 *
 * It can be wise to start with very large values for these constants, 
 * unless you are very confident on these numbers. Then do a recording and
 * check the actual usage in Tracealyzer. This is shown by selecting
 * View -> Trace Details -> Resource Usage -> Object Table
 * 
 * NOTE 2: Remember to account for all tasks created by the kernel, such as the 
 * IDLE task, timer task, and any tasks created by other 3rd party 
 * software components, such as communication stacks. The recorder also has an 
 * optional monitor task to account for, if this is used.
 * Moreover, one task slot is used to indicate "(startup)", i.e., a fictive 
 * task that represent the time before the scheduler starts. 
 * NTask should thus be at least 2-3 slots larger than your application task count.
 *
 ******************************************************************************/
#define NTask             100
#define NISR              20
#define NQueue            60
#define NSemaphore        60
#define NMutex            60

/* Maximum object name length for each class (includes zero termination) */
#define NameLenTask       15
#define NameLenISR        15
#define NameLenQueue      15
#define NameLenSemaphore  15
#define NameLenMutex      15

/******************************************************************************
 * TRACE_DESCRIPTION
 *
 * Macro which should be defined as a string.
 *
 * This string is stored in the trace and displayed in Tracealyzer. Can be
 * used to store, e.g., system version or build date. This is also used to store
 * internal error messages from the recorder, which if occurs overwrites the
 * value defined here. This may be maximum 256 chars.
 *****************************************************************************/
#define TRACE_DESCRIPTION "Tracealyzer Recorder Test Program"

/******************************************************************************
 * TRACE_DESCRIPTION_MAX_LENGTH
 *
 * The maximum length (including zero termination) for the TRACE_DESCRIPTION
 * string. Since this string also is used for internal error messages from the 
 * recorder do not make it too short, as this may truncate the error messages.
 * Default is 80. 
 * Maximum allowed length is 256 - the trace will fail to load if longer.
 *****************************************************************************/
#define TRACE_DESCRIPTION_MAX_LENGTH 80


/******************************************************************************
 * TRACE_DATA_ALLOCATION
 *
 * This defines how to allocate the recorder data structure, i.e., using a 
 * static declaration or using a dynamic allocation in runtime (malloc).
 *
 * Should be one of these two options:
 * - TRACE_DATA_ALLOCATION_STATIC (default)
 * - TRACE_DATA_ALLOCATION_DYNAMIC
 *
 * Using static allocation has the benefits of compile-time errors if the buffer 
 * is too large (too large constants in trcConfig.h) and no need to call the 
 * initialization routine (xTraceInitTraceData).
 *
 * Using dynamic allocation may give more flexibility in some cases.
 *****************************************************************************/

#define TRACE_DATA_ALLOCATION TRACE_DATA_ALLOCATION_STATIC


/******************************************************************************
 * CONFIGURATION REGARDING WHAT CODE/FEATURES TO INCLUDE
 *****************************************************************************/

/******************************************************************************
 * USE_TRACE_ASSERT
 *
 * Macro which should be defined as either zero (0) or one (1). 
 * Default is 0.
 *
 * If this is one (1), the TRACE_ASSERT macro will verify that a condition is 
 * true. If the condition is false, vTraceError() will be called.
 *****************************************************************************/
#define USE_TRACE_ASSERT 1

/******************************************************************************
 * INCLUDE_FLOAT_SUPPORT
 *
 * Macro which should be defined as either zero (0) or one (1). 
 * Default is 1.
 *
 * If this is zero (0), all references to floating point values are removed,
 * in case floating point values are not supported by the platform used.
 * Floating point values are only used in vTracePrintF and its subroutines, to 
 * store float (%f) or double (%lf) argments. 
 *
 * Note: vTracePrintF can still be used with integer and string arguments in
 * either case.
 *****************************************************************************/
#define INCLUDE_FLOAT_SUPPORT 0

/******************************************************************************
 * INCLUDE_USER_EVENTS
 *
 * Macro which should be defined as either zero (0) or one (1). 
 * Default is 1.
 *
 * If this is zero (0) the code for creating User Events is excluded to
 * reduce code size. User Events are application-generated events, like 
 * "printf" but for the trace log instead of console output. User Events are 
 * much faster than a printf and can therefore be used in timing critical code.
 * See vTraceUserEvent() and vTracePrintF() in trcUser.h
 * 
 * Note that Tracealyzer Standard Edition or Professional Edition is required
 * for User Events, they are not displayed in Tracealyzer Free Edition.
 *****************************************************************************/
#define INCLUDE_USER_EVENTS 1

/*****************************************************************************
 * INCLUDE_READY_EVENTS
 *
 * Macro which should be defined as either zero (0) or one (1). 
 * Default is 1.
 *
 * If this is zero (0), the code for recording Ready events is 
 * excluded. Note, this will make it impossible to calculate the correct
 * response times.
 *****************************************************************************/
#define INCLUDE_READY_EVENTS 1

/*****************************************************************************
 * INCLUDE_NEW_TIME_EVENTS
 *
 * Macro which should be defined as either zero (0) or one (1). 
 * Default is 0.
 *
 * If this is zero (1), events will be generated whenever the os clock is
 * increased.
 *****************************************************************************/
#define INCLUDE_NEW_TIME_EVENTS 0

/*****************************************************************************
 * INCLUDE_ISR_TRACING
 *
 * Macro which should be defined as either zero (0) or one (1). 
 * Default is 1.
 *
 * If this is zero (0), the code for recording Interrupt Service Routines is 
 * excluded to reduce code size.
 * 
 * Note, if the kernel has no central interrupt dispatcher, recording ISRs 
 * require that you insert calls to vTraceStoreISRBegin and vTraceStoreISREnd 
 * in your interrupt handlers.
 *****************************************************************************/
#define INCLUDE_ISR_TRACING 1

/******************************************************************************
 * INCLUDE_OBJECT_DELETE
 * 
 * Macro which should be defined as either zero (0) or one (1). 
 * Default is 1.
 *
 * This must be enabled (1) if tasks, queues or other 
 * traced kernel objects are deleted at runtime. If no deletes are made, this 
 * can be set to 0 in order to exclude the delete-handling code.
 *****************************************************************************/
#define INCLUDE_OBJECT_DELETE 0

/******************************************************************************
 * CONFIGURATION RELATED TO BEHAVIOR
 *****************************************************************************/

/******************************************************************************
 * TRACE_RECORDER_STORE_MODE
 *
 * Macro which should be defined as one of:
 * - TRACE_STORE_MODE_RING_BUFFER
 * - TRACE_STORE_MODE_STOP_WHEN_FULL
 * Default is TRACE_STORE_MODE_RING_BUFFER.
 *
 * With TRACE_RECORDER_STORE_MODE set to TRACE_STORE_MODE_RING_BUFFER, the events are 
 * stored in a ring buffer, i.e., where the oldest events are overwritten when 
 * the buffer becomes full. This allows you to get the last events leading up 
 * to an interesting state, e.g., an error, without having a large trace buffer
 * for string the whole run since startup. In this mode, the recorder can run
 * "forever" as the buffer never gets full, i.e., in the sense that it always
 * has room for more events.
 *
 * To fetch the trace in mode TRACE_STORE_MODE_RING_BUFFER, you need to first halt the
 * system using your debugger and then do a RAM dump, or to explicitly stop the
 * recorder using vTraceStop() and then store/upload the trace data using a
 * task that you need to provide yourself. The trace data is found in the struct
 * RecorderData, initialized in trcBase.c.
 *
 * Note that, if you upload the trace using a RAM dump, i.e., when the system is 
 * halted on a breakpoint or by a debugger command, there is no need to stop the 
 * recorder first.
 *
 * When TRACE_RECORDER_STORE_MODE is TRACE_STORE_MODE_STOP_WHEN_FULL, the recording is
 * stopped when the buffer becomes full. When the recorder stops itself this way
 * vTracePortEnd() is called which allows for custom actions, such as triggering
 * a task that stores the trace buffer, i.e., in case taking a RAM dump
 * using an on-chip debugger is not possible. In the Windows port, vTracePortEnd
 * saves the trace to file directly, but this is not recommended in a real-time
 * system since the scheduler is blocked during the processing of vTracePortEnd.
 *****************************************************************************/

#define TRACE_RECORDER_STORE_MODE TRACE_STORE_MODE_RING_BUFFER

/******************************************************************************
 * STOP_AFTER_N_EVENTS
 *
 * Macro which should be defined as an integer value, or not defined.
 * Default is -1
 *
 * STOP_AFTER_N_EVENTS is intended for tests of the ring buffer mode (when
 * RECORDER_STORE_MODE is STORE_MODE_RING_BUFFER). It stops the recording when
 * the specified number of events has been observed. This value can be larger
 * than the buffer size, to allow for test of the "wrapping around" that occurs
 * in ring buffer mode . A negative value (or no definition of this macro)
 * disables this feature.
 *****************************************************************************/
#define STOP_AFTER_N_EVENTS -1

/******************************************************************************
 * USE_IMPLICIT_IFE_RULES
 *
 * Macro which should be defined as either zero (0) or one (1). 
 * Default is 1.
 *
 * ### Instance Finish Events (IFE) ###
 *
 * For tasks with "infinite" main loops (non-terminating tasks), the concept
 * of a task instance has no clear definition, it is an application-specific
 * thing. Tracealyzer allows you to define Instance Finish Events (IFEs),
 * which marks the point in a cyclic task when the "task instance" ends.
 * The IFE is a blocking kernel call, typically in the main loop of a task
 * which typically reads a message queue, waits for a semaphore or performs
 * an explicit delay.
 *
 * If USE_IMPLICIT_IFE_RULES is one (1), the kernel macros (trcKernelPort.h)
 * will define what kernel calls are considered by default to be IFEs.
 *
 * However, Implicit IFEs only applies to blocking kernel calls. If a
 * service reads a message without blocking, it does not create a new
 * instance since no blocking occurred.
 *
 * Moreover, the actual IFE might sometimes be another blocking call. We 
 * therefore allow for user-defined Explicit IFEs by calling
 *
 *     vTraceTaskInstanceIsFinished()
 *
 * right before the kernel call considered as IFE. This does not create an
 * additional event but instead stores the service code and object handle
 * of the IFE call as properties of the task.
 *
 * If using Explicit IFEs and the task also calls an Implicit IFE, this may 
 * result in additional incorrect task instances.
 * This is solved by disabling the Implicit IFEs for the task, by adding
 * a call to
 * 
 *     vTraceTaskSkipDefaultInstanceFinishedEvents()
 * 
 * in the very beginning of that task. This allows you to combine Explicit IFEs
 * for some tasks with Implicit IFEs for the rest of the tasks, if
 * USE_IMPLICIT_IFE_RULES is 1.
 *
 * By setting USE_IMPLICIT_IFE_RULES to zero (0), the implicit IFEs are disabled
 * for all tasks. Tasks will then be considered to have a single instance only, 
 * covering all execution fragments, unless you define an explicit IFE in each
 * task by calling vTraceTaskInstanceIsFinished before the blocking call.
 *****************************************************************************/
#define USE_IMPLICIT_IFE_RULES 1

/******************************************************************************
 * INCLUDE_SAVE_TO_FILE
 *
 * Macro which should be defined as either zero (0) or one (1).
 * Default is 0.
 *
 * If enabled (1), the recorder will include code for saving the trace
 * to a local file system.
 ******************************************************************************/
#ifdef WIN32
    #define INCLUDE_SAVE_TO_FILE 1
#else
    #define INCLUDE_SAVE_TO_FILE 0
#endif

/******************************************************************************
 * TRACE_PROGRESS_MONITOR_TASK_PRIORITY
 *
 * Macro which sets the priority of the "recorder status monitor" task.
 *
 * This task, vTraceMonitorTask in trcUser.c, periodically writes
 * the recorder status using the vTraceConsoleMessage macro, which is to
 * be mapped to your console "printf" routine. The task is named TraceMon but 
 * is intentionally excluded from the demo trace.
 *
 * Default is tskIDLE_PRIORITY + 1
 * Note that if your system constantly has a high CPU load from high-priority 
 * tasks, this might not be get a chance to execute.
 * 
 * See vTraceMonitorTask in trcUser.c
 *****************************************************************************/
#define TRACE_PROGRESS_MONITOR_TASK_PRIORITY (tskIDLE_PRIORITY + 1)

/******************************************************************************
 * TRACE_PROGRESS_MONITOR_TASK_STACKSIZE
 *
 * Macro which sets the stack size of the "recorder status monitor" task.
 *
 * This task, vTraceMonitorTask in trcUser.c, periodically writes
 * the recorder status using the vTraceConsoleMessage macro, which is to
 * be mapped to your console "printf" routine. The task is intentionally 
 * excluded from the demo trace.
 *
 * See vTraceMonitorTask in trcUser.c
 *****************************************************************************/
#define TRACE_PROGRESS_MONITOR_TASK_STACKSIZE 500

/******************************************************************************
 * TRACE_PROGRESS_MONITOR_TASK_PERIOD
 *
 * Macro which sets the period of the "recorder status monitor" task.
 *
 * This task, vTraceMonitorTask in trcUser.c, periodically writes
 * the recorder status using the vTraceConsoleMessage macro, which is to
 * be mapped to your console "printf" routine. The task is named TraceMon but 
 * is intentionally excluded from the demo trace.
 *
 * Default is 1000 ticks (typically 1 second). On the Windows port, a lower 
 * value is suggested since the Windows port runs very slowly, often 20-40
 * times slower than the simulated time.
 *
 * See vTraceMonitorTask in trcUser.c
 *****************************************************************************/
#ifdef WIN32
    #define TRACE_PROGRESS_MONITOR_TASK_PERIOD 100
#else
    #define TRACE_PROGRESS_MONITOR_TASK_PERIOD 1000
#endif

/******************************************************************************
 * TEAM_LICENSE_CODE
 *
 * Macro which defines a string - the team license code.
 * If no team license is available, this should be an empty string "".
 * This should be maximum 32 chars, including zero-termination.
 *****************************************************************************/
#define TEAM_LICENSE_CODE ""

#endif

