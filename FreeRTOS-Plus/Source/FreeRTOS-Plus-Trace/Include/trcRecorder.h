/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v4.3.11
 * Percepio AB, www.percepio.com
 *
 * trcRecorder.h
 *
 * The public API of the trace recorder.
 *
 * Terms of Use
 * This file is part of the trace recorder library (RECORDER), which is the 
 * intellectual property of Percepio AB (PERCEPIO) and provided under a
 * license as follows.
 * The RECORDER may be used free of charge for the purpose of recording data
 * intended for analysis in PERCEPIO products. It may not be used or modified
 * for other purposes without explicit permission from PERCEPIO.
 * You may distribute the RECORDER in its original source code form, assuming
 * this text (terms of use, disclaimer, copyright notice) is unchanged. You are
 * allowed to distribute the RECORDER with minor modifications intended for
 * configuration or porting of the RECORDER, e.g., to allow using it on a 
 * specific processor, processor family or with a specific communication
 * interface. Any such modifications should be documented directly below
 * this comment block.  
 *
 * Disclaimer
 * The RECORDER is being delivered to you AS IS and PERCEPIO makes no warranty
 * as to its use or performance. PERCEPIO does not and cannot warrant the 
 * performance or results you may obtain by using the RECORDER or documentation.
 * PERCEPIO make no warranties, express or implied, as to noninfringement of
 * third party rights, merchantability, or fitness for any particular purpose.
 * In no event will PERCEPIO, its technology partners, or distributors be liable
 * to you for any consequential, incidental or special damages, including any
 * lost profits or lost savings, even if a representative of PERCEPIO has been
 * advised of the possibility of such damages, or for any claim by any third
 * party. Some jurisdictions do not allow the exclusion or limitation of
 * incidental, consequential or special damages, or the exclusion of implied
 * warranties or limitations on how long an implied warranty may last, so the
 * above limitations may not apply to you. 
 *
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2018.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRC_RECORDER_H
#define TRC_RECORDER_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include <stddef.h>
#include <stdarg.h>

#define TRC_ACKNOWLEDGED (0xABC99123)

#include "trcConfig.h"
#include "trcPortDefines.h"

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT)

typedef uint16_t traceString;
typedef uint8_t traceUBChannel;
typedef uint8_t traceObjectClass;

#if (TRC_CFG_USE_16BIT_OBJECT_HANDLES == 1)
typedef uint16_t traceHandle;
#else /* (TRC_CFG_USE_16BIT_OBJECT_HANDLES == 1) */
typedef uint8_t traceHandle;
#endif /* (TRC_CFG_USE_16BIT_OBJECT_HANDLES == 1) */
	
#include "trcHardwarePort.h"
#include "trcKernelPort.h"

/* Not yet available in snapshot mode */
#define vTraceConsoleChannelPrintF(fmt, ...) (void)(fmt)
#define prvTraceStoreEvent0(...)
#define prvTraceStoreEvent1(...)
#define prvTraceStoreEvent2(...)
#define prvTraceStoreEvent3(...)
#define prvTraceStoreEvent(...)
#define prvTraceStoreStringEvent(...)

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT) */

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

typedef const char* traceString;
typedef const void* traceHandle;

#include "trcHardwarePort.h"
#include "trcStreamingPort.h"
#include "trcKernelPort.h"

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#define TRC_STATE_IN_STARTUP 0
#define TRC_STATE_IN_TASKSWITCH 1
#define TRC_STATE_IN_APPLICATION 2

/* The user event channel for recorder warnings, must be defined in trcKernelPort.c */
extern traceString trcWarningChannel;

#define TRACE_GET_LOW16(value) ((uint16_t)((value) & 0x0000FFFF))
#define TRACE_GET_HIGH16(value) ((uint16_t)(((value) >> 16) & 0x0000FFFF))
#define TRACE_SET_LOW16(current, value)  (((current) & 0xFFFF0000) | (value))
#define TRACE_SET_HIGH16(current, value) (((current) & 0x0000FFFF) | (((uint32_t)(value)) << 16))

/******************************************************************************/
/*** Common API - both Snapshot and Streaming mode ****************************/
/******************************************************************************/

/******************************************************************************
* vTraceEnable(int startOption);
*
* Initializes and optionally starts the trace, depending on the start option.
* To use the trace recorder, the startup must call vTraceEnable before any RTOS
* calls are made (including "create" calls). Three start options are provided:
* 
* TRC_START: Starts the tracing directly. In snapshot mode this allows for 
* starting the trace at any point in your code, assuming vTraceEnable(TRC_INIT)
* has been called in the startup.
* Can also be used for streaming without Tracealyzer control, e.g. to a local
* flash file system (assuming such a "stream port", see trcStreamingPort.h).
* 
* TRC_START_AWAIT_HOST: For streaming mode only. Initializes the trace recorder
* if necessary and waits for a Start command from Tracealyzer ("Start Recording"
* button). This call is intentionally blocking! By calling vTraceEnable with
* this option from the startup code, you start tracing at this point and capture
* the early events.
*
* TRC_INIT: Initializes the trace recorder, but does not start the tracing.
* In snapshot mode, this must be followed by a vTraceEnable(TRC_START) sometime
* later.
*
* Usage examples:
* 
* Snapshot trace, from startup:
* 	<board init>
* 	vTraceEnable(TRC_START);
* 	<RTOS init>
*
* Snapshot trace, from a later point:
* 	<board init>
* 	vTraceEnable(TRC_INIT);
* 	<RTOS init>
* 	...
* 	vTraceEnable(TRC_START); // e.g., in task context, at some relevant event
* 
* Streaming trace, from startup:
*	<board init>	
*	vTraceEnable(TRC_START_AWAIT_HOST); // Blocks!
*	<RTOS init>
*
* Streaming trace, from a later point:
*	<board startup>
*	vTraceEnable(TRC_INIT);
*	<RTOS startup>
*	
******************************************************************************/
void vTraceEnable(int startOption);

/******************************************************************************
 * vTracePrintF
 *
 * Generates "User Events", with formatted text and data, similar to a "printf".
 * User Events can be used for very efficient logging from your application code.
 * It is very fast since the actual string formatting is done on the host side, 
 * when the trace is displayed. The execution time is just some microseconds on
 * a 32-bit MCU.
 *
 * User Events are shown as yellow labels in the main trace view of $PNAME.
 *
 * An advantage of User Events is that data can be plotted in the "User Event
 * Signal Plot" view, visualizing any data you log as User Events, discrete
 * states or control system signals (e.g. system inputs or outputs).
 *
 * You may group User Events into User Event Channels. The yellow User Event 
 * labels show the logged string, preceded by the channel name within brackets.
 * 
 * Example:
 *
 *  "[MyChannel] Hello World!"
 *
 * The User Event Channels are shown in the View Filter, which makes it easy to
 * select what User Events you wish to display. User Event Channels are created
 * using xTraceRegisterString().
 *
 * Example:
 *
 *	 traceString adc_uechannel = xTraceRegisterString("ADC User Events");
 *	 ...
 *	 vTracePrintF(adc_uechannel,
 *				 "ADC channel %d: %d volts",
 *				 ch, adc_reading);
 *
 * The following format specifiers are supported in both modes:
 * %d - signed integer. 
 * %u - unsigned integer.
 * %X - hexadecimal, uppercase. 
 * %x - hexadecimal, lowercase.
 * %s - string (see comment below)
 *
 * For integer formats (%d, %u, %x, %X) you may also use width and padding.
 * If using -42 as data argument, two examples are:
 *    "%05d" -> "-0042"
 *     "%5d" -> "  -42".
 *
 * String arguments are supported in both snapshot and streaming, but in streaming
 * mode you need to use xTraceRegisterString and use the returned traceString as
 * the argument. In snapshot you simply provide a char* as argument.
 *
 * Snapshot: vTracePrintF(myChn, "my string: %s", str);
 * Streaming: vTracePrintF(myChn, "my string: %s", xTraceRegisterString(str));
 * 
 * In snapshot mode you can specify 8-bit or 16-bit arguments to reduce RAM usage:
 *     %hd -> 16 bit (h) signed integer (d).
 *     %bu -> 8 bit (b) unsigned integer (u).
 *
 * However, in streaming mode all data arguments are assumed to be 32 bit wide. 
 * Width specifiers (e.g. %hd) are accepted but ignored (%hd treated like %d).
 *
 * The maximum event size also differs between the modes. In streaming this is
 * limited by a maximum payload size of 52 bytes, including format string and
 * data arguments. So if using one data argument, the format string is limited
 * to 48 byte, etc. If this is exceeded,  the format string is truncated and you
 * get a warning in Tracealyzer.
 *
 * In snapshot mode you are limited to maximum 15 arguments, that must not exceed
 * 32 bytes in total (not counting the format string). If exceeded, the recorder
 * logs an internal error (displayed when opening the trace) and stops recording. 
 ******************************************************************************/
#if (TRC_CFG_SCHEDULING_ONLY == 0) && (TRC_CFG_INCLUDE_USER_EVENTS == 1)
void vTracePrintF(traceString chn, const char* fmt, ...);
#else
#define vTracePrintF(chn, fmt, ...) (void)(chn), (void)(fmt) /* Comma operator is used to avoid "unused variable" compiler warnings in a single statement */
#endif

/******************************************************************************
 * vTraceVPrintF
 *
 * vTracePrintF variant that accepts a va_list.
 * See vTracePrintF documentation for further details.
 *
 ******************************************************************************/
#if (TRC_CFG_SCHEDULING_ONLY == 0) && (TRC_CFG_INCLUDE_USER_EVENTS == 1)
void vTraceVPrintF(traceString eventLabel, const char* formatStr, va_list vl);
#else
#define vTraceVPrintF(chn, formatStr, vl) (void)(chn), (void)(formatStr), (void)(vl) /* Comma operator is used to avoid "unused variable" compiler warnings in a single statement */
#endif

/******************************************************************************
* vTracePrint
*
* A faster version of vTracePrintF, that only allows for logging a string.
*
* Example:
*
*	 traceString chn = xTraceRegisterString("MyChannel");
*	 ...
*	 vTracePrint(chn, "Hello World!");
******************************************************************************/
#if (TRC_CFG_SCHEDULING_ONLY == 0) && (TRC_CFG_INCLUDE_USER_EVENTS == 1)
void vTracePrint(traceString chn, const char* str);
#else
#define vTracePrint(chn, str) (void)(chn), (void)(str) /* Comma operator is used to avoid "unused variable" compiler warnings in a single statement */
#endif


/*******************************************************************************
* vTraceConsoleChannelPrintF
*
* Wrapper for vTracePrint, using the default channel. Can be used as a drop-in
* replacement for printf and similar functions, e.g. in a debug logging macro.
*
* Example:
*
*	 // Old: #define LogString debug_console_printf
*
*    // New, log to Tracealyzer instead:
*	 #define LogString vTraceConsoleChannelPrintF 
*	 ...
*	 LogString("My value is: %d", myValue);
******************************************************************************/
#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)
void vTraceConsoleChannelPrintF(const char* fmt, ...);
#endif

/*******************************************************************************
* xTraceRegisterString
*
* Register strings in the recorder, e.g. for names of user event channels.
*
* Example:
*	 myEventHandle = xTraceRegisterString("MyUserEvent");
*	 ...
*	 vTracePrintF(myEventHandle, "My value is: %d", myValue);
******************************************************************************/
#if (TRC_CFG_SCHEDULING_ONLY == 0) && (TRC_CFG_INCLUDE_USER_EVENTS == 1)
traceString xTraceRegisterString(const char* name);
#else
#define xTraceRegisterString(x) ((void)(x), (traceString)0) /* Comma operator in parenthesis is used to avoid "unused variable" compiler warnings and return 0 in a single statement */
#endif

/*******************************************************************************
 * vTraceSet...Name(void* object, const char* name)
 *
 * Parameter object: pointer to the kernel object that shall be named
 * Parameter name: the name to set
 *
 * Kernel-specific functions for setting names of kernel objects, for display in
 * Tracealyzer.
 ******************************************************************************/
/* See trcKernelPort.h for details (kernel-specific) */

/*******************************************************************************
 * xTraceSetISRProperties
 *
 * Stores a name and priority level for an Interrupt Service Routine, to allow
 * for better visualization. Returns a traceHandle used by vTraceStoreISRBegin.
 *
 * Example:
 *	 #define PRIO_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	 ...
 *	 traceHandle Timer1Handle = xTraceSetISRProperties("ISRTimer1", PRIO_ISR_TIMER1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin(Timer1Handle);
 *		 ...
 *		 vTraceStoreISREnd(0);
 *	 }
 ******************************************************************************/
traceHandle xTraceSetISRProperties(const char* name, uint8_t priority);

/*******************************************************************************
 * vTraceStoreISRBegin
 *
 * Registers the beginning of an Interrupt Service Routine, using a traceHandle
 * provided by xTraceSetISRProperties.
 *
 * Example:
 *	 #define PRIO_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	 ...
 *	 traceHandle Timer1Handle = xTraceSetISRProperties("ISRTimer1", PRIO_ISR_TIMER1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin(Timer1Handle);
 *		 ...
 *		 vTraceStoreISREnd(0);
 *	 }
 ******************************************************************************/
void vTraceStoreISRBegin(traceHandle handle);

/*******************************************************************************
 * vTraceStoreISREnd
 *
 * Registers the end of an Interrupt Service Routine.
 *
 * The parameter pendingISR indicates if the interrupt has requested a
 * task-switch (= 1), e.g., by signaling a semaphore. Otherwise (= 0) the 
 * interrupt is assumed to return to the previous context.
 *
 * Example:
 *	 #define PRIO_OF_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	 traceHandle traceHandleIsrTimer1 = 0; // The ID set by the recorder
 *	 ...
 *	 traceHandleIsrTimer1 = xTraceSetISRProperties("ISRTimer1", PRIO_OF_ISR_TIMER1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin(traceHandleIsrTimer1);
 *		 ...
 *		 vTraceStoreISREnd(0);
 *	 }
 ******************************************************************************/
void vTraceStoreISREnd(int isTaskSwitchRequired);

/*******************************************************************************
 * vTraceInstanceFinishNow
 *
 * Creates an event that ends the current task instance at this very instant.
 * This makes the viewer to splits the current fragment at this point and begin
 * a new actor instance, even if no task-switch has occurred.
 *****************************************************************************/
void vTraceInstanceFinishedNow(void);

/*******************************************************************************
 * vTraceInstanceFinishedNext
 *
 * Marks the current "task instance" as finished on the next kernel call.
 *
 * If that kernel call is blocking, the instance ends after the blocking event
 * and the corresponding return event is then the start of the next instance.
 * If the kernel call is not blocking, the viewer instead splits the current
 * fragment right before the kernel call, which makes this call the first event
 * of the next instance.
 *****************************************************************************/
void vTraceInstanceFinishedNext(void);

/*******************************************************************************
 * xTraceGetLastError
 *
 * Returns the last error or warning as a string, or NULL if none.
 *****************************************************************************/
const char* xTraceGetLastError(void);

/*******************************************************************************
 * vTraceClearError
 *
 * Clears any errors.
 *****************************************************************************/
void vTraceClearError(void);

/*******************************************************************************
* vTraceStop
*
* Stops the recording. Intended for snapshot mode or if streaming without 
* Tracealyzer control (e.g., to a device file system).
******************************************************************************/
void vTraceStop(void);

/******************************************************************************
* vTraceSetFrequency
*
* Registers the clock rate of the time source for the event timestamping.
* This is normally not required, but if the default value (TRC_HWTC_FREQ_HZ)
* should be incorrect for your setup, you can override it using this function.
*
* Must be called prior to vTraceEnable, and the time source is assumed to
* have a fixed clock frequency after the startup.
*
* Note that, in snapshot mode, the value is divided by the TRC_HWTC_DIVISOR.
* This is a software "prescaler" that is also applied on the timestamps.
*****************************************************************************/
void vTraceSetFrequency(uint32_t frequency);

/*******************************************************************************
* vTraceSetRecorderDataBuffer
*
* The trcConfig.h setting TRC_CFG_RECORDER_BUFFER_ALLOCATION allows for selecting
* custom allocation (TRC_RECORDER_BUFFER_ALLOCATION_CUSTOM), which allows you to
* control where the recorder trace buffer is allocated.
*
* When custom allocation is selected, use TRC_ALLOC_CUSTOM_BUFFER to make the
* allocation (in global context) and then call vTraceSetRecorderDataBuffer to 
* register the allocated buffer. This supports both snapshot and streaming,
* and has no effect if using other allocation modes than CUSTOM. 
*
* NOTE: vTraceSetRecorderDataBuffer must be called before vTraceEnable.
******************************************************************************/
#if (TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_CUSTOM)
void vTraceSetRecorderDataBuffer(void* pRecorderData);
#else
#define vTraceSetRecorderDataBuffer(pRecorderData) /* If not CUSTOM, pRecorderData will be an undefined symbol (same as in TRC_ALLOC_CUSTOM_BUFFER), so no (void) here */
#endif


/*******************************************************************************
* TRC_ALLOC_CUSTOM_BUFFER
*
* If using custom allocation of the trace buffer (i.e., your trcConfig.h has the
* setting TRC_RECORDER_BUFFER_ALLOCATION_CUSTOM), this macro allows you to declare
* the trace buffer in a portable way that works both in snapshot and streaming.
*
* This macro has no effect if using another allocation mode, so you can easily 
* switch between different recording modes and configurations, using the same 
* initialization code.
*
* This translates to a single static allocation, on which you can apply linker
* directives to place it in a particular memory region.
*
* - Snapshot mode: "RecorderDataType <name>"
*
* - Streaming mode: "char <name> [<size>]", 
*   where <size> is defined in trcStreamingConfig.h.
*
* Example:
*
*   // GCC example: place myTraceBuffer in section .tz, defined in the .ld file.
*   TRC_ALLOC_CUSTOM_BUFFER(myTraceBuffer) __attribute__((section(".tz")));
*   
*   int main(void)
*   {
*      ...
*      vTraceSetRecorderDataBuffer(&myTraceBuffer); // Note the "&"
*      ...
*      vTraceEnable(TRC_INIT); // Initialize the data structure
******************************************************************************/
#if (TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_CUSTOM)
	#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT)
		#define TRC_ALLOC_CUSTOM_BUFFER(bufname) RecorderDataType bufname;
	#elif (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)
		#ifdef TRC_CFG_RTT_BUFFER_SIZE_UP /* J-Link RTT */
			#define TRC_ALLOC_CUSTOM_BUFFER(bufname) char bufname [TRC_CFG_RTT_BUFFER_SIZE_UP];  /* Not static in this case, since declared in user code */
		#else
			#define TRC_ALLOC_CUSTOM_BUFFER(bufname) char bufname [(TRC_CFG_PAGED_EVENT_BUFFER_PAGE_COUNT) * (TRC_CFG_PAGED_EVENT_BUFFER_PAGE_SIZE)];
		#endif
	#endif
#else
	#define TRC_ALLOC_CUSTOM_BUFFER(bufname) /* If not CUSTOM, bufname will be an undefined symbol (same as in vTraceSetRecorderDataBuffer), so no (void) here */
#endif

/******************************************************************************
* xTraceIsRecordingEnabled
*
* Returns true (1) if the recorder is enabled (i.e. is recording), otherwise 0.
******************************************************************************/
int xTraceIsRecordingEnabled(void);

/*******************************************************************************
* vTraceSetFilterGroup
*
* Sets the "filter group" to assign when creating RTOS objects, such as tasks,
* queues, semaphores and mutexes. This together with vTraceSetFilterMask 
* allows you to control what events that are recorded, based on the 
* objects they refer to.
*
* There are 16 filter groups named FilterGroup0 .. FilterGroup15.
*
* Note: We don't recommend filtering out the Idle task, so make sure to call 
* vTraceSetFilterGroup just before initializing the RTOS, in order to assign
* such "default" objects to the right Filter Group (typically group 0).
*
* Example:
*  
*		// Assign tasks T1 to FilterGroup0 (default)
*		<Create Task T1>  
*
*		// Assign Q1 and Q2 to FilterGroup1
*		vTraceSetFilterGroup(FilterGroup1);
*		<Create Queue Q1> 
*		<Create Queue Q2>
*
*		// Assigns Q3 to FilterGroup2
*		vTraceSetFilterGroup(FilterGroup2);
*		<Create Queue Q3>
*
*		// Only include FilterGroup0 and FilterGroup2, exclude FilterGroup1 (Q1 and Q2) from the trace
*		vTraceSetFilterMask( FilterGroup0 | FilterGroup2 );
*
*		// Assign the default RTOS objects (e.g. Idle task) to FilterGroup0
*		vTraceSetFilterGroup(FilterGroup0);
*		<Start the RTOS scheduler>
*
* Note that you may define your own names for the filter groups using
* preprocessor definitions, to make the code easier to understand.
*
* Example:
*
*		#define BASE FilterGroup0
*		#define USB_EVENTS FilterGroup1
*		#define CAN_EVENTS FilterGroup2
*
* Note that filtering per event type (regardless of object) is also available
* in trcConfig.h.
******************************************************************************/
void vTraceSetFilterGroup(uint16_t filterGroup);

/******************************************************************************
* vTraceSetFilterMask
*
* Sets the "filter mask" that is used to filter the events by object. This can
* be used to reduce the trace data rate, i.e., if your streaming interface is
* a bottleneck or if you want longer snapshot traces without increasing the
* buffer size.
*
* Note: There are two kinds of filters in the recorder. The other filter type
* excludes all events of certain kinds (e.g., OS ticks). See trcConfig.h.
*
* The filtering is based on bitwise AND with the Filter Group ID, assigned
* to RTOS objects such as tasks, queues, semaphores and mutexes. 
* This together with vTraceSetFilterGroup allows you to control what
* events that are recorded, based on the objects they refer to.
*
* See example for vTraceSetFilterGroup.
******************************************************************************/
void vTraceSetFilterMask(uint16_t filterMask);

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT)

/******************************************************************************/
/*** Extended API for Snapshot mode *******************************************/
/******************************************************************************/

/******************************************************************************
* TRACE_STOP_HOOK - Hook Pointer Data Type
*
* Declares a data type for a call back function that will be invoked whenever
* the recorder is stopped.
*
* Snapshot mode only!
******************************************************************************/
typedef void(*TRACE_STOP_HOOK)(void);

/*******************************************************************************
* vTraceStopHookPtr
*
* Points to a call back function that is called from vTraceStop().
*
* Snapshot mode only!
******************************************************************************/
extern TRACE_STOP_HOOK vTraceStopHookPtr;

/*******************************************************************************
* vTraceSetStopHook
*
* Sets a function to be called when the recorder is stopped.
*
* Snapshot mode only!
******************************************************************************/
void vTraceSetStopHook(TRACE_STOP_HOOK stopHookFunction);

/*******************************************************************************
* uiTraceStart
*
* [DEPRECATED] Use vTraceEnable instead.
*
* Starts the recorder. The recorder will not be started if an error has been
* indicated using prvTraceError, e.g. if any of the Nx constants in
* trcSnapshotConfig.h has a too small value (TRC_CFG_NTASK, TRC_CFG_NQUEUE, etc).
*
* Returns 1 if the recorder was started successfully.
* Returns 0 if the recorder start was prevented due to a previous internal
* error. In that case, check xTraceGetLastError to get the error message.
* Any error message is also presented when opening a trace file.
*
* Snapshot mode only!
******************************************************************************/
uint32_t uiTraceStart(void);

/*******************************************************************************
* vTraceStart
*
* [DEPRECATED] Use vTraceEnable instead.
*
* Starts the recorder. The recorder will not be started if an error has been
* indicated using prvTraceError, e.g. if any of the Nx constants in
* trcSnapshotConfig.h has a too small value (TRC_CFG_NTASK, TRC_CFG_NQUEUE, etc).
*
* Snapshot mode only!
******************************************************************************/
void vTraceStart(void);

/*******************************************************************************
* vTraceClear
*
* Resets the recorder. Only necessary if a restart is desired - this is not
* needed in the startup initialization.
*
* Snapshot mode only!
******************************************************************************/
void vTraceClear(void);


/*****************************************************************************/
/*** INTERNAL SNAPSHOT FUNCTIONS *********************************************/
/*****************************************************************************/

#define TRC_UNUSED

#ifndef TRC_CFG_INCLUDE_OBJECT_DELETE
#define TRC_CFG_INCLUDE_OBJECT_DELETE 0
#endif

#ifndef TRC_CFG_INCLUDE_READY_EVENTS
#define TRC_CFG_INCLUDE_READY_EVENTS 1
#endif

#ifndef TRC_CFG_INCLUDE_OSTICK_EVENTS
#define TRC_CFG_INCLUDE_OSTICK_EVENTS 0
#endif

/* This macro will create a task in the object table */
#undef trcKERNEL_HOOKS_TASK_CREATE
#define trcKERNEL_HOOKS_TASK_CREATE(SERVICE, CLASS, pxTCB) \
	TRACE_SET_OBJECT_NUMBER(TASK, pxTCB); \
	TRACE_SET_OBJECT_FILTER(TASK, pxTCB, CurrentFilterGroup); \
	prvTraceSetObjectName(TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB), TRACE_GET_TASK_NAME(pxTCB)); \
	prvTraceSetPriorityProperty(TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB), TRACE_GET_TASK_PRIORITY(pxTCB)); \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, pxTCB) & CurrentFilterMask) \
			prvTraceStoreKernelCall(SERVICE, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB));

/* This macro will remove the task and store it in the event buffer */
#undef trcKERNEL_HOOKS_TASK_DELETE
#define trcKERNEL_HOOKS_TASK_DELETE(SERVICE, SERVICE_NAME, SERVICE_PROP, pxTCB) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, pxTCB) & CurrentFilterMask) \
			prvTraceStoreKernelCall(SERVICE, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB)); \
	prvTraceStoreObjectNameOnCloseEvent(SERVICE_NAME, TRACE_GET_TASK_NUMBER(pxTCB), TRACE_CLASS_TASK); \
	prvTraceStoreObjectPropertiesOnCloseEvent(SERVICE_PROP, TRACE_GET_TASK_NUMBER(pxTCB), TRACE_CLASS_TASK); \
	prvTraceSetPriorityProperty(TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB), TRACE_GET_TASK_PRIORITY(pxTCB)); \
	prvTraceSetObjectState(TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB), TASK_STATE_INSTANCE_NOT_ACTIVE); \
	prvTraceFreeObjectHandle(TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB));


/* This macro will setup a task in the object table */
#undef trcKERNEL_HOOKS_OBJECT_CREATE
#define trcKERNEL_HOOKS_OBJECT_CREATE(SERVICE, CLASS, pxObject)\
	TRACE_SET_OBJECT_NUMBER(CLASS, pxObject);\
	TRACE_SET_OBJECT_FILTER(CLASS, pxObject, CurrentFilterGroup); \
	prvMarkObjectAsUsed(TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject),  TRACE_GET_OBJECT_NUMBER(CLASS, pxObject));\
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(CLASS, pxObject) & CurrentFilterMask) \
			prvTraceStoreKernelCall(SERVICE, TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject), TRACE_GET_OBJECT_NUMBER(CLASS, pxObject)); \
	prvTraceSetObjectState(TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject), TRACE_GET_OBJECT_NUMBER(CLASS, pxObject), 0);

/* This macro will remove the object and store it in the event buffer */
#undef trcKERNEL_HOOKS_OBJECT_DELETE
#define trcKERNEL_HOOKS_OBJECT_DELETE(SERVICE, SERVICE_NAME, SERVICE_PROP, CLASS, pxObject) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(CLASS, pxObject) & CurrentFilterMask) \
			prvTraceStoreKernelCall(SERVICE, TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject), TRACE_GET_OBJECT_NUMBER(CLASS, pxObject)); \
	prvTraceStoreObjectNameOnCloseEvent(SERVICE_NAME, TRACE_GET_OBJECT_NUMBER(CLASS, pxObject), TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject)); \
	prvTraceStoreObjectPropertiesOnCloseEvent(SERVICE_PROP, TRACE_GET_OBJECT_NUMBER(CLASS, pxObject), TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject)); \
	prvTraceFreeObjectHandle(TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject), TRACE_GET_OBJECT_NUMBER(CLASS, pxObject));

/* This macro will create a call to a kernel service with a certain result, with an object as parameter */
#undef trcKERNEL_HOOKS_KERNEL_SERVICE
#define trcKERNEL_HOOKS_KERNEL_SERVICE(SERVICE, CLASS, pxObject) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(CLASS, pxObject) & CurrentFilterMask) \
			prvTraceStoreKernelCall(SERVICE, TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject), TRACE_GET_OBJECT_NUMBER(CLASS, pxObject));

/* This macro will create a call to a kernel service with a certain result, with a null object as parameter */
#undef trcKERNEL_HOOKS_KERNEL_SERVICE_NULL_OBJECT
#define trcKERNEL_HOOKS_KERNEL_SERVICE_NULL_OBJECT(SERVICE, TRACECLASS) \
	if (TRACE_GET_TASK_FILTER(TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreKernelCall(SERVICE, TRACECLASS, 0);

/* This macro will create a call to a kernel service with a certain result, with an object as parameter */
#undef trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM
#define trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(SERVICE, CLASS, pxObject, param) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(CLASS, pxObject) & CurrentFilterMask) \
			prvTraceStoreKernelCallWithParam(SERVICE, TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject), TRACE_GET_OBJECT_NUMBER(CLASS, pxObject), (uint32_t)param);

/* This macro will create a call to a kernel service with a certain result, with a null object and other value as parameter */
#undef trcKERNEL_HOOKS_KERNEL_SERVICE_NULL_OBJECT_WITH_PARAM
#define trcKERNEL_HOOKS_KERNEL_SERVICE_NULL_OBJECT_WITH_PARAM(SERVICE, TRACECLASS, param) \
	if (TRACE_GET_TASK_FILTER(TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreKernelCallWithParam(SERVICE, TRACECLASS, 0, param);

/* This macro will create a call to a kernel service with a certain result, with an object as parameter */
#undef trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_NUMERIC_PARAM_ONLY
#define trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_NUMERIC_PARAM_ONLY(SERVICE, param) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreKernelCallWithNumericParamOnly(SERVICE, (uint32_t)param);

/* This macro will create a call to a kernel service with a certain result, with an object as parameter */
#undef trcKERNEL_HOOKS_KERNEL_SERVICE_FROM_ISR
#define trcKERNEL_HOOKS_KERNEL_SERVICE_FROM_ISR(SERVICE, CLASS, pxObject) \
	if (TRACE_GET_OBJECT_FILTER(CLASS, pxObject) & CurrentFilterMask) \
		prvTraceStoreKernelCall(SERVICE, TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject), TRACE_GET_OBJECT_NUMBER(CLASS, pxObject));

/* This macro will create a call to a kernel service with a certain result, with a null object as parameter */
#undef trcKERNEL_HOOKS_KERNEL_SERVICE_NULL_OBJECT_FROM_ISR
#define trcKERNEL_HOOKS_KERNEL_SERVICE_NULL_OBJECT_FROM_ISR(SERVICE, TRACECLASS) \
	prvTraceStoreKernelCall(SERVICE, TRACECLASS, 0);

/* This macro will create a call to a kernel service with a certain result, with an object as parameter */
#undef trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM_FROM_ISR
#define trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM_FROM_ISR(SERVICE, CLASS, pxObject, param) \
	if (TRACE_GET_OBJECT_FILTER(CLASS, pxObject) & CurrentFilterMask) \
		prvTraceStoreKernelCallWithParam(SERVICE, TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject), TRACE_GET_OBJECT_NUMBER(CLASS, pxObject), (uint32_t)param);

/* This macro will create a call to a kernel service with a certain result, with a null object and other value as parameter */
#undef trcKERNEL_HOOKS_KERNEL_SERVICE_NULL_OBJECT_WITH_PARAM_FROM_ISR
#define trcKERNEL_HOOKS_KERNEL_SERVICE_NULL_OBJECT_WITH_PARAM_FROM_ISR(SERVICE, TRACECLASS, param) \
	prvTraceStoreKernelCallWithParam(SERVICE, TRACECLASS, 0, param);

/* This macro will create a call to a kernel service with a certain result, with an object as parameter */
#undef trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_NUMERIC_PARAM_ONLY_FROM_ISR
#define trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_NUMERIC_PARAM_ONLY_FROM_ISR(SERVICE, param) \
	prvTraceStoreKernelCallWithNumericParamOnly(SERVICE, (uint32_t)param);

/* This macro will set the state for an object */
#undef trcKERNEL_HOOKS_SET_OBJECT_STATE
#define trcKERNEL_HOOKS_SET_OBJECT_STATE(CLASS, pxObject, STATE) \
	prvTraceSetObjectState(TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject), TRACE_GET_OBJECT_NUMBER(CLASS, pxObject), (uint8_t)STATE);

/* This macro will flag a certain task as a finished instance */
#undef trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED
#define trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceSetTaskInstanceFinished(TRACE_GET_TASK_NUMBER(TRACE_GET_CURRENT_TASK()));

#if (TRC_CFG_INCLUDE_READY_EVENTS == 1)
/* This macro will create an event to indicate that a task became Ready */
#undef trcKERNEL_HOOKS_MOVED_TASK_TO_READY_STATE
#define trcKERNEL_HOOKS_MOVED_TASK_TO_READY_STATE(pxTCB) \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxTCB) & CurrentFilterMask) \
		prvTraceStoreTaskReady(TRACE_GET_TASK_NUMBER(pxTCB));
#else /*(TRC_CFG_INCLUDE_READY_EVENTS == 1)*/
#undef trcKERNEL_HOOKS_MOVED_TASK_TO_READY_STATE
#define trcKERNEL_HOOKS_MOVED_TASK_TO_READY_STATE(pxTCB)
#endif /*(TRC_CFG_INCLUDE_READY_EVENTS == 1)*/

/* This macro will update the internal tick counter and call prvTracePortGetTimeStamp(0) to update the internal counters */
#undef trcKERNEL_HOOKS_INCREMENT_TICK
#define trcKERNEL_HOOKS_INCREMENT_TICK() \
	{ \
		extern uint32_t uiTraceTickCount; \
		uiTraceTickCount++; \
		prvTracePortGetTimeStamp(0); \
	}

#if (TRC_CFG_INCLUDE_OSTICK_EVENTS == 1)
/* This macro will create an event indicating that the OS tick count has increased */
#undef trcKERNEL_HOOKS_NEW_TIME
#define trcKERNEL_HOOKS_NEW_TIME(SERVICE, xValue) \
	prvTraceStoreKernelCallWithNumericParamOnly(SERVICE, xValue);
#else /*(TRC_CFG_INCLUDE_OSTICK_EVENTS == 1)*/
#undef trcKERNEL_HOOKS_NEW_TIME
#define trcKERNEL_HOOKS_NEW_TIME(SERVICE, xValue)
#endif /*(TRC_CFG_INCLUDE_OSTICK_EVENTS == 1)*/

/* This macro will create a task switch event to the currently executing task */
#undef trcKERNEL_HOOKS_TASK_SWITCH
#define trcKERNEL_HOOKS_TASK_SWITCH( pxTCB ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxTCB) & CurrentFilterMask) \
		prvTraceStoreTaskswitch(TRACE_GET_TASK_NUMBER(pxTCB));

/* This macro will create an event to indicate that the task has been suspended */
#undef trcKERNEL_HOOKS_TASK_SUSPEND
#define trcKERNEL_HOOKS_TASK_SUSPEND(SERVICE, pxTCB) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, pxTCB) & CurrentFilterMask) \
			prvTraceStoreKernelCall(SERVICE, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB)); \
	prvTraceSetTaskInstanceFinished((uint8_t)TRACE_GET_TASK_NUMBER(pxTCB));

/* This macro will create an event to indicate that a task has called a wait/delay function */
#undef trcKERNEL_HOOKS_TASK_DELAY
#define trcKERNEL_HOOKS_TASK_DELAY(SERVICE, pxTCB, xValue) \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxTCB) & CurrentFilterMask) \
	{ \
		prvTraceStoreKernelCallWithNumericParamOnly(SERVICE, xValue); \
		prvTraceSetTaskInstanceFinished((uint8_t)TRACE_GET_TASK_NUMBER(pxTCB)); \
	}

/* This macro will create an event to indicate that a task has gotten its priority changed */
#undef trcKERNEL_HOOKS_TASK_PRIORITY_CHANGE
#define trcKERNEL_HOOKS_TASK_PRIORITY_CHANGE(SERVICE, pxTCB, uxNewPriority) \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxTCB) & CurrentFilterMask) \
	{ \
		prvTraceStoreKernelCallWithParam(SERVICE, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB), prvTraceGetPriorityProperty(TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB)));\
		prvTraceSetPriorityProperty(TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB), (uint8_t)uxNewPriority); \
	}

/* This macro will create an event to indicate that the task has been resumed */
#undef trcKERNEL_HOOKS_TASK_RESUME
#define trcKERNEL_HOOKS_TASK_RESUME(SERVICE, pxTCB) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, pxTCB) & CurrentFilterMask) \
			prvTraceStoreKernelCall(SERVICE, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB));

#undef trcKERNEL_HOOKS_TASK_RESUME_FROM_ISR
#define trcKERNEL_HOOKS_TASK_RESUME_FROM_ISR(SERVICE, pxTCB) \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxTCB) & CurrentFilterMask) \
		prvTraceStoreKernelCall(SERVICE, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxTCB));

#if !defined TRC_CFG_INCLUDE_READY_EVENTS || TRC_CFG_INCLUDE_READY_EVENTS == 1
	void prvTraceSetReadyEventsEnabled(int status);
	void prvTraceStoreTaskReady(traceHandle handle);
#else
	#define prvTraceSetReadyEventsEnabled(status)
#endif

void prvTraceStoreLowPower(uint32_t flag);

void prvTraceStoreTaskswitch(traceHandle task_handle);


#if (TRC_CFG_SCHEDULING_ONLY == 0)

void prvTraceStoreKernelCall(uint32_t eventcode, traceObjectClass objectClass, uint32_t byteParam);

void prvTraceStoreKernelCallWithNumericParamOnly(uint32_t evtcode, uint32_t param);

void prvTraceStoreKernelCallWithParam(uint32_t evtcode, traceObjectClass objectClass,
									uint32_t objectNumber, uint32_t param);
#else

#define prvTraceStoreKernelCall(eventcode, objectClass, byteParam) {}
#define prvTraceStoreKernelCallWithNumericParamOnly(evtcode, param) {}
#define prvTraceStoreKernelCallWithParam(evtcode, objectClass, objectNumber, param) {}

#endif

/*******************************************************************************
* prvTraceInitTraceData
*
* Allocates and initializes the recorder data structure, based on the constants
* in trcConfig.h. This allows for allocating the data on the heap, instead of
* using a static declaration.
******************************************************************************/
void prvTraceInitTraceData(void);

void prvTraceSetTaskInstanceFinished(traceHandle handle);

void prvTraceSetPriorityProperty(uint8_t objectclass, traceHandle id, uint8_t value);

uint8_t prvTraceGetPriorityProperty(uint8_t objectclass, traceHandle id);

void prvTraceSetObjectState(uint8_t objectclass, traceHandle id, uint8_t value);

void prvMarkObjectAsUsed(traceObjectClass objectclass, traceHandle handle);

void prvTraceStoreObjectNameOnCloseEvent(uint8_t evtcode, traceHandle handle,
										traceObjectClass objectclass);

void prvTraceStoreObjectPropertiesOnCloseEvent(uint8_t evtcode, traceHandle handle,
											 traceObjectClass objectclass);

/* Internal constants for task state */
#define TASK_STATE_INSTANCE_NOT_ACTIVE 0
#define TASK_STATE_INSTANCE_ACTIVE 1


#if (TRC_CFG_INCLUDE_ISR_TRACING == 0)

#undef vTraceSetISRProperties
#define vTraceSetISRProperties(handle, name, priority) (void)(handle), (void)(name), (void)(priority) /* Comma operator is used to avoid "unused variable" compiler warnings in a single statement */

#undef vTraceStoreISRBegin
#define vTraceStoreISRBegin(x) (void)(x)

#undef vTraceStoreISREnd
#define vTraceStoreISREnd(x) (void)(x)

#undef xTraceSetISRProperties
#define xTraceSetISRProperties(name, priority) ((void)(name), (void)(priority), (traceHandle)0) /* Comma operator in parenthesis is used to avoid "unused variable" compiler warnings and return 0 in a single statement */

#endif /*(TRC_CFG_INCLUDE_ISR_TRACING == 0)*/

/*******************************************************************************
 * xTraceGetTraceBuffer
 *
 * Returns a pointer to the recorder data structure. Use this together with
 * uiTraceGetTraceBufferSize if you wish to implement an own store/upload
 * solution, e.g., in case a debugger connection is not available for uploading
 * the data.
 ******************************************************************************/
void* xTraceGetTraceBuffer(void);

/*******************************************************************************
 * uiTraceGetTraceBufferSize
 *
 * Gets the size of the recorder data structure. For use together with
 * vTraceGetTraceBuffer if you wish to implement an own store/upload solution,
 * e.g., in case a debugger connection is not available for uploading the data.
 ******************************************************************************/
uint32_t uiTraceGetTraceBufferSize(void);

#if (TRC_CFG_SCHEDULING_ONLY == 1)
#undef TRC_CFG_INCLUDE_USER_EVENTS
#define TRC_CFG_INCLUDE_USER_EVENTS 0
#endif /*(TRC_CFG_SCHEDULING_ONLY == 1)*/

#if ((TRC_CFG_INCLUDE_USER_EVENTS == 1) && (TRC_CFG_SCHEDULING_ONLY == 0))

#if (TRC_CFG_USE_SEPARATE_USER_EVENT_BUFFER == 1)
traceUBChannel xTraceRegisterUBChannel(traceString channel, traceString formatStr);
void vTraceUBData(traceUBChannel channel, ...);
void vTraceUBEvent(traceUBChannel channel);
#endif /*(TRC_CFG_USE_SEPARATE_USER_EVENT_BUFFER == 1)*/

#else /*((TRC_CFG_INCLUDE_USER_EVENTS == 1) && (TRC_CFG_SCHEDULING_ONLY == 0))*/

#undef vTracePrint
#define vTracePrint(chn, ...) (void)(chn)
#undef vTracePrintF
#define vTracePrintF(chn, fmt, ...) (void)(chn), (void)(fmt) /* Comma operator is used to avoid "unused variable" compiler warnings in a single statement */
#undef vTraceVPrintF
#define vTraceVPrintF(chn, formatStr, vl) (void)(chn), (void)(formatStr), (void)(vl) /* Comma operator is used to avoid "unused variable" compiler warnings in a single statement */
#undef xTraceRegisterString
#define xTraceRegisterString(x) ((void)(x), (traceString)0) /* Comma operator in parenthesis is used to avoid "unused variable" compiler warnings and return 0 in a single statement */
#undef xTraceRegisterChannelFormat
#define xTraceRegisterChannelFormat(eventLabel, formatStr) ((void)(eventLabel), (void)(formatStr), 0) /* Comma operator in parenthesis is used to avoid "unused variable" compiler warnings and return 0 in a single statement */
#undef vTraceUBData
#define vTraceUBData(label, ...) (void)(label)
#undef vTraceChannelPrint
#define vTraceChannelPrint(label) (void)(label)

#endif /*(TRC_CFG_INCLUDE_USER_EVENTS == 1)*/

#define NEventCodes 0x100

/* Our local critical sections for the recorder */
#define trcCRITICAL_SECTION_BEGIN() {TRACE_ENTER_CRITICAL_SECTION(); recorder_busy++;}
#define trcCRITICAL_SECTION_END() {recorder_busy--; TRACE_EXIT_CRITICAL_SECTION();}

#if (TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_ARM_Cortex_M)
	#define trcSR_ALLOC_CRITICAL_SECTION_ON_CORTEX_M_ONLY TRACE_ALLOC_CRITICAL_SECTION
	#define trcCRITICAL_SECTION_BEGIN_ON_CORTEX_M_ONLY trcCRITICAL_SECTION_BEGIN
	#define trcCRITICAL_SECTION_END_ON_CORTEX_M_ONLY trcCRITICAL_SECTION_END
#else
	#define trcSR_ALLOC_CRITICAL_SECTION_ON_CORTEX_M_ONLY() {}
	#define trcCRITICAL_SECTION_BEGIN_ON_CORTEX_M_ONLY() recorder_busy++;
	#define trcCRITICAL_SECTION_END_ON_CORTEX_M_ONLY() recorder_busy--;
#endif

/******************************************************************************
 * ObjectHandleStack
 * This data-structure is used to provide a mechanism for 1-byte trace object
 * handles. This way, only 1 byte is necessary instead of 4 bytes (a pointer)
 * when storing a reference to an object. This allows for up to 255 objects of
 * each object class active at any given moment. There can be more "historic"
 * objects, that have been deleted - that number is only limited by the size of
 * the symbol table.
 *
 * Note that handle zero (0) is not used, it is a code for an invalid handle.
 *
 * This data structure keeps track of the FREE handles, not the handles in use.
 * This data structure contains one stack per object class. When a handle is
 * allocated to an object, the next free handle is popped from the stack. When
 * a handle is released (on object delete), it is pushed back on the stack.
 * Note that there is no initialization code that pushed the free handles
 * initially, that is not necessary due to the following optimization:
 *
 * The stack of handles (objectHandles) is initially all zeros. Since zero
 * is not a valid handle, that is a signal of additional handles needed.
 * If a zero is received when popping a new handle, it is replaced by the
 * index of the popped handle instead.
 *****************************************************************************/
typedef struct
{
	/* For each object class, the index of the next handle to allocate */
	uint16_t indexOfNextAvailableHandle[ TRACE_NCLASSES ];

	/* The lowest index of this class (constant) */
	uint16_t lowestIndexOfClass[ TRACE_NCLASSES ];

	/* The highest index of this class (constant) */
	uint16_t highestIndexOfClass[ TRACE_NCLASSES ];

	/* The highest use count for this class (for statistics) */
	uint16_t handleCountWaterMarksOfClass[ TRACE_NCLASSES ];

	/* The free object handles - a set of stacks within this array */
	traceHandle objectHandles[ TRACE_KERNEL_OBJECT_COUNT ];

} objectHandleStackType;

extern objectHandleStackType objectHandleStacks;

/******************************************************************************
 * Object Property Table
 * The Object Table contains name and other properties of the objects (tasks,
 * queues, mutexes, etc). The below data structures defines the properties of
 * each object class and are used to cast the byte buffer into a cleaner format.
 *
 * The values in the object table are continuously overwritten and always
 * represent the current state. If a property is changed during runtime, the OLD
 * value should be stored in the trace buffer, not the new value (since the new
 * value is found in the Object Property Table).
 *
 * For close events this mechanism is the old names are stored in the symbol
 * table), for "priority set" (the old priority is stored in the event data)
 * and for "isActive", where the value decides if the task switch event type
 * should be "new" or "resume".
 ******************************************************************************/

typedef struct
{
	/* = NCLASSES */
	uint32_t NumberOfObjectClasses;

	uint32_t ObjectPropertyTableSizeInBytes;

	/* This is used to calculate the index in the dynamic object table
	(handle - 1 - nofStaticObjects = index)*/
#if (TRC_CFG_USE_16BIT_OBJECT_HANDLES == 1)
	traceHandle NumberOfObjectsPerClass[2*((TRACE_NCLASSES+1)/2)];
#else
	traceHandle NumberOfObjectsPerClass[4*((TRACE_NCLASSES+3)/4)];
#endif

	/* Allocation size rounded up to the closest multiple of 4 */
	uint8_t NameLengthPerClass[ 4*((TRACE_NCLASSES+3)/4) ];

	uint8_t TotalPropertyBytesPerClass[ 4*((TRACE_NCLASSES+3)/4) ];

	/* Allocation size rounded up to the closest multiple of 2 */
	uint16_t StartIndexOfClass[ 2*((TRACE_NCLASSES+1)/2) ];

	/* The actual handles issued, should be Initiated to all zeros */
	uint8_t objbytes[ 4*((TRACE_OBJECT_TABLE_SIZE+3)/4) ];
} ObjectPropertyTableType;

/* Symbol table data structure */
typedef struct
{
	/* = SYMBOL_HISTORY_TABLE_SIZE_IN_BYTES */
	uint32_t symTableSize;

	/* Entry 0 is reserved. Any reference to entry 0 implies NULL*/
	uint32_t nextFreeSymbolIndex;

	/* Size rounded up to closest multiple of 4, to avoid alignment issues*/
	uint8_t symbytes[4*(((TRC_CFG_SYMBOL_TABLE_SIZE)+3)/4)];

	/* Used for lookups - Up to 64 linked lists within the symbol table
	connecting all entries with the same 6 bit checksum.
	This field holds the current list heads. Should be initiated to zeros */
	uint16_t latestEntryOfChecksum[64];
} symbolTableType;


/*******************************************************************************
 * The data structures of the different events, all 4 bytes long
 ******************************************************************************/

typedef struct
{
	uint8_t type;
	uint8_t objHandle;
	uint16_t dts;	/* differential timestamp - time since last event */
} TSEvent, TREvent;

typedef struct
{
	uint8_t type;
	uint8_t dummy;
	uint16_t dts;	/* differential timestamp - time since last event */
} LPEvent;

typedef struct
{
	uint8_t type;
	uint8_t objHandle;
	uint16_t dts;	/* differential timestamp - time since last event */
} KernelCall;

typedef struct
{
	uint8_t type;
	uint8_t objHandle;
	uint8_t param;
	uint8_t dts;	/* differential timestamp - time since last event */
} KernelCallWithParamAndHandle;

typedef struct
{
	uint8_t type;
	uint8_t dts;	/* differential timestamp - time since last event */
	uint16_t param;
} KernelCallWithParam16;

typedef struct
{
	uint8_t type;
	uint8_t objHandle;		/* the handle of the closed object */
	uint16_t symbolIndex;	/* the name of the closed object */
} ObjCloseNameEvent;

typedef struct
{
	uint8_t type;
	uint8_t arg1;
	uint8_t arg2;
	uint8_t arg3;
} ObjClosePropEvent;

typedef struct
{
	uint8_t type;
	uint8_t unused1;
	uint8_t unused2;
	uint8_t dts;
} TaskInstanceStatusEvent;

typedef struct
{
	uint8_t type;
	uint8_t dts;
	uint16_t payload;		 /* the name of the user event */
} UserEvent;

typedef struct
{
	uint8_t type;

	/* 8 bits extra for storing DTS, if it does not fit in ordinary event
	(this one is always MSB if used) */
	uint8_t xts_8;

	/* 16 bits extra for storing DTS, if it does not fit in ordinary event. */
	uint16_t xts_16;
} XTSEvent;

typedef struct
{
	uint8_t type;

	uint8_t xps_8;
	uint16_t xps_16;
} XPSEvent;

typedef struct{
	uint8_t type;
	uint8_t dts;
	uint16_t size;
} MemEventSize;

typedef struct{
	uint8_t type;
	uint8_t addr_high;
	uint16_t addr_low;
} MemEventAddr;

/*******************************************************************************
 * The separate user event buffer structure. Can be enabled in trcConfig.h.
 ******************************************************************************/

#if (TRC_CFG_USE_SEPARATE_USER_EVENT_BUFFER == 1)
typedef struct
{
	traceString name;
	traceString defaultFormat;
} ChannelFormatPair;

typedef struct
{
	uint16_t bufferID;
	uint16_t version;
	uint32_t wraparoundCounter;
	uint32_t numberOfSlots;
	uint32_t nextSlotToWrite;
	uint8_t numberOfChannels;
	uint8_t padding1;
	uint8_t padding2;
	uint8_t padding3;
	ChannelFormatPair channels[(TRC_CFG_UB_CHANNELS)+1];
	uint8_t channelBuffer[((TRC_CFG_SEPARATE_USER_EVENT_BUFFER_SIZE) + 3) & 0xFFFFFFFC]; /* 1 byte per slot, with padding for 4 byte alignment */
	uint8_t dataBuffer[(TRC_CFG_SEPARATE_USER_EVENT_BUFFER_SIZE) * 4]; /* 4 bytes per slot */

} UserEventBuffer;
#endif

/*******************************************************************************
 * The main data structure, read by Tracealyzer from the RAM dump
 ******************************************************************************/

typedef struct
{
	volatile uint8_t startmarker0; /* Volatile is important, see init code. */
	volatile uint8_t startmarker1;
	volatile uint8_t startmarker2;
	volatile uint8_t startmarker3;
	volatile uint8_t startmarker4;
	volatile uint8_t startmarker5;
	volatile uint8_t startmarker6;
	volatile uint8_t startmarker7;
	volatile uint8_t startmarker8;
	volatile uint8_t startmarker9;
	volatile uint8_t startmarker10;
	volatile uint8_t startmarker11;

	/* Used to determine Kernel and Endianess */
	uint16_t version;

	/* Currently 5 */
	uint8_t minor_version;

	/* This should be 0 if lower IRQ priority values implies higher priority
	levels, such as on ARM Cortex M. If the opposite scheme is used, i.e.,
	if higher IRQ priority values means higher priority, this should be 1. */
	uint8_t irq_priority_order;

	/* sizeof(RecorderDataType) - just for control */
	uint32_t filesize;

	/* Current number of events recorded */
	uint32_t numEvents;

	/* The buffer size, in number of event records */
	uint32_t maxEvents;

	/* The event buffer index, where to write the next event */
	uint32_t nextFreeIndex;

	/* 1 if the buffer is full, 0 otherwise */
	uint32_t bufferIsFull;

	/* The frequency of the clock/timer/counter used as time base */
	uint32_t frequency;

	/* The absolute timestamp of the last stored event, in the native
	timebase, modulo frequency! */
	uint32_t absTimeLastEvent;

	/* The number of seconds in total - lasts for 136 years */
	uint32_t absTimeLastEventSecond;

	/* 1 if the recorder has been started, 0 if not yet started or stopped.
	This is a 32 bit variable due to alignment issues. */
	uint32_t recorderActive;

	/* If > 0, tells the maximum time between two traced ISRs that execute
	back-to-back. If the time between vTraceStoreISREnd and a directly
	following vTraceISRBegin is above isrTailchainingThreshold, we assume a
	return to the previous context in between the ISRs, otherwise we assume
	the have executed back-to-back and don't show any fragment of the previous
	context in between. */ 
	uint32_t isrTailchainingThreshold;

	/* Not used, remains for compatibility and future use */
	uint8_t notused[24];

	/* The amount of heap memory remaining at the last malloc or free event */
	uint32_t heapMemUsage;

	/* 0xF0F0F0F0 - for control only */
	int32_t debugMarker0;

	/* Set to value of TRC_CFG_USE_16BIT_OBJECT_HANDLES */
	uint32_t isUsing16bitHandles;

	/* The Object Property Table holds information about currently active
	tasks, queues, and other recorded objects. This is updated on each
	create call and includes object name and other properties. */
	ObjectPropertyTableType ObjectPropertyTable;

	/* 0xF1F1F1F1 - for control only */
	int32_t debugMarker1;

	/* The Symbol Table stores strings for User Events and is also used to
	store names of deleted objects, which still may be in the trace but no
	longer are available. */
	symbolTableType SymbolTable;

	/* For inclusion of float support, and for endian detection of floats.
	The value should be (float)1 or (uint32_t)0 */
#if (TRC_CFG_INCLUDE_FLOAT_SUPPORT == 1)
	float exampleFloatEncoding;
#else
	uint32_t exampleFloatEncoding;
#endif
	/* This is non-zero if an internal error occurred in the recorder, e.g., if
	one of the Nxxx constants was too small. The systemInfo string will then
	contain an error message that is displayed when attempting to view the
	trace file. */
	uint32_t internalErrorOccured;

	/* 0xF2F2F2F2 - for control only */
	int32_t debugMarker2;

	/* Error messages from the recorder. */
	char systemInfo[80];

	/* 0xF3F3F3F3 - for control only */
	int32_t debugMarker3;

	/* The event data, in 4-byte records */
	uint8_t eventData[ (TRC_CFG_EVENT_BUFFER_SIZE) * 4 ];

#if (TRC_CFG_USE_SEPARATE_USER_EVENT_BUFFER == 1)
	UserEventBuffer userEventBuffer;
#endif

	/* This should always be 0 */
	uint32_t endOfSecondaryBlocks;

	uint8_t endmarker0;
	uint8_t endmarker1;
	uint8_t endmarker2;
	uint8_t endmarker3;
	uint8_t endmarker4;
	uint8_t endmarker5;
	uint8_t endmarker6;
	uint8_t endmarker7;
	uint8_t endmarker8;
	uint8_t endmarker9;
	uint8_t endmarker10;
	uint8_t endmarker11;
} RecorderDataType;

extern RecorderDataType* RecorderDataPtr;

/* Internal functions */

/* Signal an error. */
void prvTraceError(const char* msg);

/*******************************************************************************
 * prvTracePortGetTimeStamp
 *
 * Returns the current time based on the HWTC macros which provide a hardware
 * isolation layer towards the hardware timer/counter.
 *
 * The HWTC macros and prvTracePortGetTimeStamp is the main porting issue
 * or the trace recorder library. Typically you should not need to change
 * the code of prvTracePortGetTimeStamp if using the HWTC macros.
 *
 ******************************************************************************/
void prvTracePortGetTimeStamp(uint32_t *puiTimestamp);

traceHandle prvTraceGetObjectHandle(traceObjectClass objectclass);

void prvTraceFreeObjectHandle(traceObjectClass objectclass,
							traceHandle handle);

/* Private function. Use the public functions in trcKernelPort.h */
void prvTraceSetObjectName(traceObjectClass objectclass,
							traceHandle handle,
							const char* name);

/* Internal macros */

#define TRACE_PROPERTY_NAME_GET(objectclass, objecthandle) \
(const char*)(& RecorderDataPtr->ObjectPropertyTable.objbytes \
[uiIndexOfObject(objecthandle, objectclass)])

#define TRACE_PROPERTY_OBJECT_STATE(objectclass, handle) \
RecorderDataPtr->ObjectPropertyTable.objbytes[uiIndexOfObject(handle, objectclass) \
+ RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[objectclass]]

#define TRACE_PROPERTY_ACTOR_PRIORITY(objectclass, handle) \
RecorderDataPtr->ObjectPropertyTable.objbytes[uiIndexOfObject(handle, objectclass) \
+ RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[objectclass] + 1]

/* DEBUG ASSERTS */
#if defined TRC_CFG_USE_TRACE_ASSERT && TRC_CFG_USE_TRACE_ASSERT != 0
#define TRACE_ASSERT(eval, msg, defRetVal) \
if (!(eval)) \
{ \
	prvTraceError("TRACE_ASSERT: " msg); \
	return defRetVal; \
}
#else
#define TRACE_ASSERT(eval, msg, defRetVal)
#endif

#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT)*/

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

/******************************************************************************
 * Default values for STREAM PORT macros
 *
 * As a normal user, this is nothing you don't need to bother about. This is
 * only important if you want to define your own custom streaming interface.
 *
 * You may override these in your own trcStreamingPort.h to create a custom
 * stream port, and thereby stream the trace on any host-target interface.
 * These default values are suitable for most cases, except the J-Link port. 
 ******************************************************************************/

/******************************************************************************
 * TRC_STREAM_PORT_USE_INTERNAL_BUFFER
 *
 * There are two kinds of stream ports, those that store the event to the 
 * internal buffer (with periodic flushing by the TzCtrl task) and those that
 * write directly to the streaming interface. Most stream ports use the 
 * recorder's internal buffer, except for the SEGGER J-Link port (also uses a
 * RAM buffer, but one defined in the SEGGER code).
 *
 * If the stream port (trcStreamingPort.h) defines this as zero (0), it is 
 * expected to transmit the data directly using TRC_STREAM_PORT_COMMIT_EVENT.
 * Otherwise it is expected that the trace data is stored in the internal buffer
 * and the TzCtrl task will then send the buffer pages when they become full.
 ******************************************************************************/
#ifndef TRC_STREAM_PORT_USE_INTERNAL_BUFFER
#define TRC_STREAM_PORT_USE_INTERNAL_BUFFER 1
#endif

 /******************************************************************************
 * TRC_STREAM_PORT_ON_TRACE_BEGIN
 *
 * Defining any actions needed in the stream port when the recording is activated.
 *******************************************************************************/
#ifndef TRC_STREAM_PORT_ON_TRACE_BEGIN
	#define TRC_STREAM_PORT_ON_TRACE_BEGIN() /* Do nothing */
#endif

 /******************************************************************************
 * TRC_STREAM_PORT_ON_TRACE_END
 *
 * Defining any actions needed in the stream port when the tracing stops.
 * Empty by default.
 *******************************************************************************/
#ifndef TRC_STREAM_PORT_ON_TRACE_END
#define TRC_STREAM_PORT_ON_TRACE_END() /* Do nothing */
#endif

 /******************************************************************************
 * TRC_STREAM_PORT_ALLOCATE_EVENT
 *
 * This macro is used to allocate memory for each event record, just before
 * assigning the record fields.
 * Depending on "TRC_STREAM_PORT_USE_INTERNAL_BUFFER", this either allocates
 * space in the paged event buffer, or on the local stack. In the latter case,
 * the COMMIT event is used to write the data to the streaming interface.
 *
 * The BLOCKING option is only used within vTraceEnable, to ensure the full
 * header, object table and symbol table is transferred without data loss.
 ******************************************************************************/
#ifndef TRC_STREAM_PORT_ALLOCATE_EVENT
#if (TRC_STREAM_PORT_USE_INTERNAL_BUFFER == 1)
	#define TRC_STREAM_PORT_ALLOCATE_EVENT(_type, _ptrData, _size) \
	_type* _ptrData; \
	_ptrData = (_type*)prvPagedEventBufferGetWritePointer(_size);
	
	/**************************************************************************
     If your application gets stuck in TRC_STREAM_PORT_ALLOCATE_EVENT_BLOCKING,
     it means it fails to transfer the header, object table or symbol table
     during vTraceEnable.
     This occurs if the trace buffer is too small to accomodate these in full,
     i.e. before the streaming interface is started and begins to transfer.
	 
	 Note that this is intentionally blocking to avoid data loss, but only
     used within vTraceEnable.
    **************************************************************************/
   
	#define TRC_STREAM_PORT_ALLOCATE_EVENT_BLOCKING(_type, _ptrData, _size) \
	_type* _ptrData; \
	do { _ptrData = (_type*)prvPagedEventBufferGetWritePointer(_size); } while (_ptrData == NULL);

#else
	#define TRC_STREAM_PORT_ALLOCATE_EVENT(_type, _ptrData, _size) _type _tmpArray[_size / sizeof(_type)]; _type* _ptrData = _tmpArray;
	#define TRC_STREAM_PORT_ALLOCATE_EVENT_BLOCKING(_type, _ptrData, _size) _type _tmpArray[_size / sizeof(_type)]; _type* _ptrData = _tmpArray;
#endif
#endif

 /******************************************************************************
 * TRC_STREAM_PORT_ALLOCATE_DYNAMIC_EVENT
 *
 * This macro is used to allocate memory for each event record, just before
 * assigning the record fields. 
 * This has the same purpose as TRC_STREAM_PORT_ALLOCATE_EVENT and by default
 * it has the same definition as TRC_STREAM_PORT_ALLOCATE_EVENT. This is used
 * for events carrying variable-sized payload, such as strings.
 * In the SEGGER RTT port, we need this in order to make a worst-case
 * allocation on the stack. 
 ******************************************************************************/
#ifndef TRC_STREAM_PORT_ALLOCATE_DYNAMIC_EVENT
#if (TRC_STREAM_PORT_USE_INTERNAL_BUFFER == 1)
	#define TRC_STREAM_PORT_ALLOCATE_DYNAMIC_EVENT(_type, _ptrData, _size) TRC_STREAM_PORT_ALLOCATE_EVENT(_type, _ptrData, _size) /* We do the same thing as for non-dynamic event sizes */
#else
	#define TRC_STREAM_PORT_ALLOCATE_DYNAMIC_EVENT(_type, _ptrData, _size) _type _tmpArray[sizeof(largestEventType) / sizeof(_type)]; _type* _ptrData = _tmpArray;
#endif
#endif

 /******************************************************************************
 * TRC_STREAM_PORT_COMMIT_EVENT
 * TRC_STREAM_PORT_COMMIT_EVENT_BLOCKING
 *
 * The COMMIT macro is used to write a single event record directly to the 
 * streaming inteface, without first storing the event in the internal buffer.
 * This is currently only used in the SEGGER J-Link RTT port. 
 *
 * The BLOCKING version is used when sending the initial trace header, which is
 * important to receive in full. Otherwise, when using non-blocking RTT transfer
 * this may be corrupted if using an RTT buffer smaller than the combined size
 * of the header, object table and symbol table.
 *
 * This relies on the TRC_STREAM_PORT_WRITE_DATA macro, defined in by the 
 * stream port in trcStreamingPort.h. The COMMIT macro calls 
 * prvTraceWarning(TRC_STREAM_PORT_WRITE_DATA) if a non-zero value is returned
 * from TRC_STREAM_PORT_WRITE_DATA. If zero (0) is returned, it is assumed 
 * that all data was successfully written.
 *
 * In ports using the internal buffer, this macro has no purpose as the events
 * are written to the internal buffer instead. They are then flushed to the
 * streaming interface in the TzCtrl task using TRC_STREAM_PORT_WRITE_DATA.
 ******************************************************************************/
#ifndef TRC_STREAM_PORT_COMMIT_EVENT
#if (TRC_STREAM_PORT_USE_INTERNAL_BUFFER == 1)
	#define TRC_STREAM_PORT_COMMIT_EVENT(_ptrData, _size) /* Not used */
	#define TRC_STREAM_PORT_COMMIT_EVENT_BLOCKING(_ptrData, _size) /* Not used */
#else
	#define TRC_STREAM_PORT_COMMIT_EVENT(_ptrData, _size) \
	{ \
		int32_t dummy = 0; \
		(void)dummy; \
		if (TRC_STREAM_PORT_WRITE_DATA(_ptrData, _size, &dummy) != 0) \
		{ \
			vTraceStop(); \
		} \
	}
	
	/* Only used during vTraceEnable */
	#define TRC_STREAM_PORT_COMMIT_EVENT_BLOCKING(_ptrData, _size) \
	{ \
		char* ptrWrite = (char*)_ptrData; \
		uint32_t writeSize = _size; \
		uint32_t attemptCounter = 0; \
		int32_t bytesWritten; \
		int32_t status; \
		do \
		{ \
			bytesWritten = 0; \
			status = TRC_STREAM_PORT_WRITE_DATA(ptrWrite, writeSize, &bytesWritten); \
			if (status != 0) \
			{ \
				prvTraceError(PSF_ERROR_STREAM_PORT_WRITE); \
				break; \
			} \
			ptrWrite += bytesWritten; \
			writeSize -= bytesWritten; \
			attemptCounter++; \
		} while (writeSize > 0); \
		\
		if (attemptCounter > 1) \
		{ \
			prvTraceWarning(PSF_WARNING_STREAM_PORT_INITIAL_BLOCKING); \
		} \
	}

#endif
#endif

/******************************************************************************
 * TRC_STREAM_PORT_READ_DATA (defined in trcStreamingPort.h)
 *
 * Defining how to read data from host (commands from Tracealyzer).
 *
 * If there is no direct interface to host (e.g., if streaming to a file
 * system) this should be defined as 0. Instead use vTraceEnable(TRC_START) and
 * vTraceStop() to control the recording from target.
 *
 * Parameters:
 *
 * - _ptrData: a pointer to a data buffer, where the received data shall be 
 *             stored (TracealyzerCommandType*).
 *
 * - _size: the number of bytes to read (int).
 *
 * - _ptrBytesRead: a pointer to an integer (int), that should be assigned
 *					with the number of bytes that was received.
 *
 * Example:
 * 
 * 	int32_t myRead(void* ptrData, uint32_t size, int32_t* ptrBytesRead);
 * 
 *	#define TRC_STREAM_PORT_READ_DATA(_ptrData, _size, _ptrBytesRead) \
 *          myRead(_ptrData, _size, _ptrBytesRead)
 *
 * Your "myRead" function should return 0 if successful, i.e. if at least some 
 * bytes were received. A non-zero value should be returned if the streaming
 * interface returned an error (e.g. a closed socket), which results in the
 * recorder calling prvTraceWarning with the error code 
 * PSF_WARNING_STREAM_PORT_WRITE.
 *
 * If developing your own custom stream port and using the default internal
 * buffer, it is important that the _ptrBytesRead parameter is assigned
 * correctly by "myRead", i.e. with the number of bytes actually written. 
 * Otherwise the data stream may get out of sync in case the streaming interface
 * can't swallow all data at once. 
 ******************************************************************************/
#ifndef TRC_STREAM_PORT_READ_DATA
#error "No definition for TRC_STREAM_PORT_READ_DATA (should be in trcStreamingPort.h)"
#endif

/******************************************************************************
 * TRC_STREAM_PORT_WRITE_DATA (defined in trcStreamingPort.h)
 *
 * Defining how to write trace data to the streaming interface. 
 *
 * Parameters:
 *
 * - _ptrData: a pointer (void*) to the data to write.
 *
 * - _size: the number of bytes to write (uint32_t).
 *
 * - _ptrBytesWritten: a pointer to an integer (int32_t), that should be
 *						assigned with the number of bytes actually written.
 *
 * Example:
 *
 * 	int32_t myWrite(void* ptrData, uint32_t size, int32_t* ptrBytesWritten);
 *
 *	#define TRC_STREAM_PORT_WRITE_DATA(_ptrData, _size, _ptrBytesWritten) \
 *			myWrite(_ptrData, _size, _ptrBytesWritten) 
 *  
 * Your "myWrite" function should return 0 if successful, i.e. if at least some 
 * bytes were sent. A non-zero value should be returned if the streaming interface
 * returned an error (e.g. a closed socket), which results in the recorder calling
 * prvTraceWarning with the error code PSF_WARNING_STREAM_PORT_WRITE.
 * 
 * If developing your own custom stream port and using the default internal
 * buffer, it is important that the _ptrBytesWritten parameter is assigned
 * correctly by "myWrite", i.e. with the number of bytes actually written. 
 * Otherwise the data stream may get out of sync in case the streaming interface
 * can't swallow all data at once.
 *
 * Assuming TRC_STREAM_PORT_USE_INTERNAL_BUFFER is 1 (default), the TzCtrl task
 * will use this macro to send one buffer page at a time. In case all data can't
 * be written at once (if _ptrBytesWritten is less than _size), the TzCtrl task
 * is smart enough to make repeated calls (with updated parameters) in order to 
 * send the remaining data.
 * 
 * However, if TRC_STREAM_PORT_USE_INTERNAL_BUFFER is 0, this is used from the
 * COMMIT macro, directly in the "event functions". In that case, the
 * _ptrBytesWritten parameter will be NULL and should be ignored by the write
 * function. In this case, it is assumed that all data can be sent in a single
 * call, otherwise the write function should return a non-zero error code.
 ******************************************************************************/
#ifndef TRC_STREAM_PORT_WRITE_DATA
#error "No definition for TRC_STREAM_PORT_WRITE_DATA (should be in trcStreamingPort.h)"
#endif

/******************************************************************************
* Data structure declaration, depending on  TRC_CFG_RECORDER_BUFFER_ALLOCATION
*******************************************************************************/
#if (TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_STATIC)
	
	/* Static allocation. */
	
	/* If not defined in trcStreamingPort.h */
	#ifndef TRC_STREAM_PORT_ALLOCATE_FIELDS
		#define TRC_STREAM_PORT_ALLOCATE_FIELDS() \
		char _TzTraceData[(TRC_CFG_PAGED_EVENT_BUFFER_PAGE_COUNT) * (TRC_CFG_PAGED_EVENT_BUFFER_PAGE_SIZE)];       	
		extern char _TzTraceData[(TRC_CFG_PAGED_EVENT_BUFFER_PAGE_COUNT) * (TRC_CFG_PAGED_EVENT_BUFFER_PAGE_SIZE)];
	#endif
	
	/* If not defined in trcStreamingPort.h */
	#ifndef TRC_STREAM_PORT_MALLOC
		#define TRC_STREAM_PORT_MALLOC() /* Static allocation. Not used. */
	#endif
#else
	/* For Dynamic or Custom Allocation mode */
	
	/* If not defined in trcStreamingPort.h */
	#ifndef TRC_STREAM_PORT_ALLOCATE_FIELDS
		#define TRC_STREAM_PORT_ALLOCATE_FIELDS() char* _TzTraceData = NULL;
		extern char* _TzTraceData;
	#endif
	
	/* If not defined in trcStreamingPort.h */
	#ifndef TRC_STREAM_PORT_MALLOC
		#if (TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_DYNAMIC)
			#define TRC_STREAM_PORT_MALLOC() \
			_TzTraceData = TRC_PORT_MALLOC((TRC_CFG_PAGED_EVENT_BUFFER_PAGE_COUNT) * (TRC_CFG_PAGED_EVENT_BUFFER_PAGE_SIZE));
			extern char* _TzTraceData;
		#else
			#define TRC_STREAM_PORT_MALLOC()  /* Custom allocation. Not used. */
		#endif
	#endif
#endif

#ifndef TRC_STREAM_PORT_INIT
	#define TRC_STREAM_PORT_INIT() \
			TRC_STREAM_PORT_MALLOC(); /* Empty if static allocation mode */ \
			prvPagedEventBufferInit(_TzTraceData);
#endif


/* Signal an error. */
void prvTraceError(int errCode);

/* Signal an warning (does not stop the recorder). */
void prvTraceWarning(int errCode);

/******************************************************************************/
/*** ERROR AND WARNING CODES (check using xTraceGetLastError) *****************/
/******************************************************************************/

#define PSF_ERROR_NONE 0
#define PSF_ERROR_EVENT_CODE_TOO_LARGE 1
#define PSF_ERROR_ISR_NESTING_OVERFLOW 2
#define PSF_ERROR_DWT_NOT_SUPPORTED 3
#define PSF_ERROR_DWT_CYCCNT_NOT_SUPPORTED 4
#define PSF_ERROR_TZCTRLTASK_NOT_CREATED 5
#define PSF_ERROR_STREAM_PORT_WRITE 6

#define PSF_WARNING_SYMBOL_TABLE_SLOTS 7
#define PSF_WARNING_SYMBOL_MAX_LENGTH 8
#define PSF_WARNING_OBJECT_DATA_SLOTS 9
#define PSF_WARNING_STRING_TOO_LONG 10
#define PSF_WARNING_STREAM_PORT_READ 11
#define PSF_WARNING_STREAM_PORT_WRITE 12
#define PSF_WARNING_STREAM_PORT_INITIAL_BLOCKING 13
#define PSF_WARNING_STACKMON_NO_SLOTS 14

/******************************************************************************/
/*** INTERNAL STREAMING FUNCTIONS *********************************************/
/******************************************************************************/

/* Saves a symbol name in the symbol table and returns the slot address */
void* prvTraceSaveSymbol(const char *name);

/* Saves a string in the symbol table for an object (task name etc.) */
void prvTraceSaveObjectSymbol(void* address, const char *name);

/* Deletes a symbol name (task name etc.) from symbol table */
void prvTraceDeleteSymbol(void *address);

/* Saves an object data entry (task base priority) in object data table */
void prvTraceSaveObjectData(const void *address, uint32_t data);

/* Removes an object data entry (task base priority) from object data table */
void prvTraceDeleteObjectData(void *address);

/* Store an event with zero parameters (event ID only) */
void prvTraceStoreEvent0(uint16_t eventID);

/* Store an event with one 32-bit parameter (pointer address or an int) */
void prvTraceStoreEvent1(uint16_t eventID,
	uint32_t param1);

/* Store an event with two 32-bit parameters */
void prvTraceStoreEvent2(uint16_t eventID,
	uint32_t param1,
	uint32_t param2);

/* Store an event with three 32-bit parameters */
void prvTraceStoreEvent3(uint16_t eventID,
	uint32_t param1,
	uint32_t param2,
	uint32_t param3);

/* Stores an event with <nParam> 32-bit integer parameters */
void prvTraceStoreEvent(int nParam, uint16_t EventID, ...);

/* Stories an event with a string and <nParam> 32-bit integer parameters */
void prvTraceStoreStringEvent(int nArgs, uint16_t eventID, const char* str, ...);

/* Initializes the paged event buffer used by certain stream ports */
void prvPagedEventBufferInit(char* buffer);

/* Retrieve a pointer to the paged event buffer */
void* prvPagedEventBufferGetWritePointer(int sizeOfEvent);

/* Transfer a full buffer page */
uint32_t prvPagedEventBufferTransfer(void);

/* The data structure for commands (a bit overkill) */
typedef struct
{
	unsigned char cmdCode;
	unsigned char param1;
	unsigned char param2;
	unsigned char param3;
	unsigned char param4;
	unsigned char param5;
	unsigned char checksumLSB;
	unsigned char checksumMSB;
} TracealyzerCommandType;

/* Checks if the provided command is a valid command */
int prvIsValidCommand(TracealyzerCommandType* cmd);

/* Executed the received command (Start or Stop) */
void prvProcessCommand(TracealyzerCommandType* cmd);

#define vTraceSetStopHook(x) (void)(x)

#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/

#else /* when TRC_USE_TRACEALYZER_RECORDER == 0 */

#define vTraceEnable(x) (void)(x)
#define xTraceRegisterString(x) ((void)(x), (traceString)0) /* Comma operator in parenthesis is used to avoid "unused variable" compiler warnings and return 0 in a single statement */
#define vTracePrint(chn, ...) (void)(chn)
#define vTracePrintF(chn, fmt, ...) (void)(chn), (void)(fmt) /* Comma operator is used to avoid "unused variable" compiler warnings in a single statement */
#define vTraceVPrintF(chn, formatStr, vl) (void)(chn), (void)(formatStr), (void)(vl) /* Comma operator is used to avoid "unused variable" compiler warnings in a single statement */
#define vTraceInstanceFinishedNow()
#define vTraceInstanceFinishedNext()
#define vTraceStoreISRBegin(x) (void)(x)
#define vTraceStoreISREnd(x) (void)(x)
#define xTraceSetISRProperties(a, b) ((void)(a), (void)(b), (traceHandle)0) /* Comma operator in parenthesis is used to avoid "unused variable" compiler warnings and return 0 in a single statement */
#define vTraceStoreKernelObjectName(a, b) (void)(a), (void)(b) /* Comma operator is used to avoid "unused variable" compiler warnings in a single statement */
#define xTraceRegisterChannelFormat(eventLabel, formatStr) ((void)(eventLabel), (void)(formatStr), 0) /* Comma operator in parenthesis is used to avoid "unused variable" compiler warnings and return 0 in a single statement */
#define vTraceChannelPrint(label) (void)(label)
#define vTraceUBData(label, ...) (void)(label)

#define vTraceSetFilterGroup(x) (void)(x)
#define vTraceSetFilterMask(x) (void)(x)

#define prvTraceSetReadyEventsEnabled(status) (void)(status)

#define vTraceExcludeTask(handle) (void)(handle)

#define uiTraceStart() (1)
#define vTraceStart()
#define vTraceStop()

#ifndef vTraceSetRecorderDataBuffer
#define vTraceSetRecorderDataBuffer(pRecorderData) /* No (void) here - ignore parameter since undefined symbol if custom allocation is not used */
#endif

#define vTraceConsoleChannelPrintF(fmt, ...) (void)(fmt)

#ifndef TRC_ALLOC_CUSTOM_BUFFER
#define TRC_ALLOC_CUSTOM_BUFFER(bufname)
#endif

#define xTraceIsRecordingEnabled() (0)

#define vTraceSetStopHook(x) (void)(x)

#endif /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/

#ifdef __cplusplus
}
#endif

#endif /* TRC_RECORDER_H */
