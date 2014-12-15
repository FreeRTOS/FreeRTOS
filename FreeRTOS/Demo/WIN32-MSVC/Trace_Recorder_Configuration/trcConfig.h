/*******************************************************************************
 * Tracealyzer v2.7.0 Recorder Library
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
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2014.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRCCONFIG_H
#define TRCCONFIG_H

/******************************************************************************
 * SELECTED_PORT
 *
 * Macro that specifies what hardware port that should be used.
 * Available ports are:
 *
 * Port Name							Code	 Official	OS supported
 * PORT_APPLICATION_DEFINED				-2		-			-
 * PORT_NOT_SET							-1		-			-
 * PORT_HWIndependent					0		Yes			Any
 * PORT_Win32							1		Yes			FreeRTOS on Win32
 * PORT_Atmel_AT91SAM7					2		No			Any
 * PORT_Atmel_UC3A0						3		No			Any
 * PORT_ARM_CortexM						4		Yes			Any
 * PORT_Renesas_RX600					5		Yes			Any
 * PORT_Microchip_dsPIC_AND_PIC24		6		Yes			Any
 * PORT_TEXAS_INSTRUMENTS_TMS570		7		No			Any
 * PORT_TEXAS_INSTRUMENTS_MSP430		8		No			Any
 * PORT_MICROCHIP_PIC32MX				9		Yes			Any
 * PORT_XILINX_PPC405					10		No			FreeRTOS
 * PORT_XILINX_PPC440					11		No			FreeRTOS
 * PORT_XILINX_MICROBLAZE				12		No			Any
 * PORT_NXP_LPC210X						13		No			Any
 * PORT_MICROCHIP_PIC32MZ				14		Yes			Any
 * PORT_ARM_CORTEX_A9					15		No			Any
 *****************************************************************************/

#ifndef WIN32
	// Set the port setting here!
	#define SELECTED_PORT PORT_NOT_SET

	#if (SELECTED_PORT == PORT_NOT_SET)
		#error "You need to define SELECTED_PORT here!"
	#endif
#else
	// For Win32 demo projects this is set automatically
	#define SELECTED_PORT PORT_Win32
#endif

/******************************************************************************
 * FREERTOS_VERSION
 *
 * Specify what version of FreeRTOS that is used. This is necessary compensate
 * for renamed symbols in the FreeRTOS kernel (does not build if incorrect).
 *
 * FREERTOS_VERSION_7_3_OR_7_4 (= 1)		If using FreeRTOS v7.3.0 - v7.4.2
 * FREERTOS_VERSION_7_5_OR_7_6 (= 2)		If using FreeRTOS v7.5.0 - v7.6.0
 * FREERTOS_VERSION_8_0_OR_LATER (= 3)		If using FreeRTOS v8.0.0 or later
 *****************************************************************************/
#define FREERTOS_VERSION	FREERTOS_VERSION_8_0_OR_LATER

/******************************************************************************
 * TRACE_RECORDER_STORE_MODE
 *
 * Macro which should be defined as one of:
 * - TRACE_STORE_MODE_RING_BUFFER
 * - TRACE_STORE_MODE_STOP_WHEN_FULL
 * Default is TRACE_STORE_MODE_RING_BUFFER.
 *
 * With TRACE_RECORDER_STORE_MODE set to TRACE_STORE_MODE_RING_BUFFER, the
 * events are stored in a ring buffer, i.e., where the oldest events are
 * overwritten when the buffer becomes full. This allows you to get the last
 * events leading up to an interesting state, e.g., an error, without having
 * to store the whole run since startup.
 *
 * When TRACE_RECORDER_STORE_MODE is TRACE_STORE_MODE_STOP_WHEN_FULL, the
 * recording is stopped when the buffer becomes full. This is useful for
 * recording events following a specific state, e.g., the startup sequence.
 *****************************************************************************/
#define TRACE_RECORDER_STORE_MODE TRACE_STORE_MODE_RING_BUFFER

/*******************************************************************************
 * TRACE_SCHEDULING_ONLY
 *
 * Macro which should be defined as an integer value.
 *
 * If this setting is enabled (= 1), only scheduling events are recorded.
 * If disabled (= 0), all events are recorded.
 *
 * Users of FreeRTOS+Trace Free Edition only displays scheduling events, so this
 * option can be used to avoid storing unsupported events.
 *
 * Default value is 0 (store all enabled events).
 *
 ******************************************************************************/
#define TRACE_SCHEDULING_ONLY 0

/*******************************************************************************
 * EVENT_BUFFER_SIZE
 *
 * Macro which should be defined as an integer value.
 *
 * This defines the capacity of the event buffer, i.e., the number of records
 * it may store. Most events use one record (4 byte), although some events
 * require multiple 4-byte records. You should adjust this to the amount of RAM
 * available in the target system.
 *
 * Default value is 1000, which means that 4000 bytes is allocated for the
 * event buffer.
 ******************************************************************************/
#define EVENT_BUFFER_SIZE 15000

/*******************************************************************************
 * NTask, NISR, NQueue, NSemaphore, NMutex
 *
 * A group of macros which should be defined as integer values, zero or larger.
 *
 * These define the capacity of the Object Property Table, i.e., the maximum
 * number of objects active at any given point, within each object class (e.g.,
 * task, queue, semaphore, ...).
 *
 * If tasks or other other objects are deleted in your system, this
 * setting does not limit the total amount of objects created, only the number
 * of objects that have been successfully created but not yet deleted.
 *
 * Using too small values will cause vTraceError to be called, which stores an
 * error message in the trace that is shown when opening the trace file.
 *
 * It can be wise to start with large values for these constants,
 * unless you are very confident on these numbers. Then do a recording and
 * check the actual usage by selecting View menu -> Trace Details ->
 * Resource Usage -> Object Table.
 ******************************************************************************/
#define NTask			100
#define NISR			60
#define NQueue			60
#define NSemaphore		60
#define NMutex			60
#define NTimer			200
#define NEventGroup		60

/******************************************************************************
 * INCLUDE_MEMMANG_EVENTS
 *
 * Macro which should be defined as either zero (0) or one (1).
 *
 * This controls if malloc and free calls should be traced. Set this to zero to
 * exclude malloc/free calls, or one (1) to include such events in the trace.
 *
 * Default value is 1.
 *****************************************************************************/
#define INCLUDE_MEMMANG_EVENTS 1

/******************************************************************************
 * INCLUDE_USER_EVENTS
 *
 * Macro which should be defined as either zero (0) or one (1).
 *
 * If this is zero (0) the code for creating User Events is excluded to
 * reduce code size. User Events are application-generated events, like
 * "printf" but for the trace log instead of console output. User Events are
 * much faster than a printf and can therefore be used in timing critical code.
 * See vTraceUserEvent() and vTracePrintF() in trcUser.h
 *
 * Default value is 1.
 *
 * Note that User Events are only displayed in Professional Edition.
 *****************************************************************************/
#define INCLUDE_USER_EVENTS 1

/*****************************************************************************
 * INCLUDE_ISR_TRACING
 *
 * Macro which should be defined as either zero (0) or one (1).
 *
 * If this is zero (0), the code for recording Interrupt Service Routines is
 * excluded to reduce code size.
 *
 * Default value is 1.
 *
 * Note, if the kernel has no central interrupt dispatcher, recording ISRs
 * require that you insert calls to vTraceStoreISRBegin and vTraceStoreISREnd
 * in your interrupt handlers.
 *****************************************************************************/
#define INCLUDE_ISR_TRACING 1

/*****************************************************************************
 * INCLUDE_READY_EVENTS
 *
 * Macro which should be defined as either zero (0) or one (1).
 *
 * If one (1), events are recorded when tasks enter scheduling state "ready".
 * This uses a lot of space in the event buffer, so excluding "ready events"
 * will allow for longer traces. Including ready events however allows for
 * showing the initial pending time before tasks enter the execution state, and
 * for presenting accurate response times.
 *
 * Default value is 1.
 *****************************************************************************/
#define INCLUDE_READY_EVENTS 1

/*****************************************************************************
 * INCLUDE_NEW_TIME_EVENTS
 *
 * Macro which should be defined as either zero (0) or one (1).
 *
 * If this is zero (1), events will be generated whenever the OS clock is
 * increased.
 *
 * Default value is 0.
 *****************************************************************************/
#define INCLUDE_NEW_TIME_EVENTS 1

/******************************************************************************
 * INCLUDE_FLOAT_SUPPORT
 *
 * Macro which should be defined as either zero (0) or one (1).
 *
 * If this is zero (0), all references to floating point values are removed,
 * in case floating point values are not supported by the platform used.
 * Floating point values are only used in vTracePrintF and its subroutines, to
 * store float (%f) or double (%lf) arguments.
 *
 * vTracePrintF can be used with integer and string arguments in either case.
 *
 * Default value is 1.
 *****************************************************************************/
#define INCLUDE_FLOAT_SUPPORT 0

/******************************************************************************
 * INCLUDE_OBJECT_DELETE
 *
 * Macro which should be defined as either zero (0) or one (1).
 *
 * This must be enabled (1) if tasks, queues or other
 * traced kernel objects are deleted at runtime. If no deletes are made, this
 * can be set to 0 in order to exclude the delete-handling code.
 *
 * Default value is 1.
 *****************************************************************************/
#define INCLUDE_OBJECT_DELETE 1

/*******************************************************************************
 * SYMBOL_TABLE_SIZE
 *
 * Macro which should be defined as an integer value.
 *
 * This defines the capacity of the symbol table, in bytes. This symbol table
 * stores User Events labels and names of deleted tasks, queues, or other kernel
 * objects. If you don't use User Events or delete any kernel
 * objects you set this to a very low value. The minimum recommended value is 4.
 * A size of zero (0) is not allowed since a zero-sized array may result in a
 * 32-bit pointer, i.e., using 4 bytes rather than 0.
 *
 * Default value is 800.
 ******************************************************************************/
#define SYMBOL_TABLE_SIZE 5000

#if (SYMBOL_TABLE_SIZE == 0)
#error "SYMBOL_TABLE_SIZE may not be zero!"
#endif

/******************************************************************************
 * NameLenTask, NameLenQueue, ...
 *
 * Macros that specify the maximum lengths (number of characters) for names of
 * kernel objects, such as tasks and queues. If longer names are used, they will
 * be truncated when stored in the recorder.
 *****************************************************************************/
#define NameLenTask			15
#define NameLenISR			15
#define NameLenQueue		15
#define NameLenSemaphore	15
#define NameLenMutex		15
#define NameLenTimer		15
#define NameLenEventGroup 	15

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
 *** ADVANCED SETTINGS ********************************************************
 ******************************************************************************
 * The remaining settings are not necessary to modify but allows for optimizing
 * the recorder setup for your specific needs, e.g., to exclude events that you
 * are not interested in, in order to get longer traces.
 *****************************************************************************/

/******************************************************************************
* HEAP_SIZE_BELOW_16M
*
* An integer constant that can be used to reduce the buffer usage of memory
* allocation events (malloc/free). This value should be 1 if the heap size is
* below 16 MB (2^24 byte), and you can live with reported addresses showing the
* lower 24 bits only. If 0, you get the full 32-bit addresses.
*
* Default value is 0.
******************************************************************************/
#define HEAP_SIZE_BELOW_16M 0

/******************************************************************************
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

/******************************************************************************
 * USE_IMPLICIT_IFE_RULES
 *
 * Macro which should be defined as either zero (0) or one (1).
 * Default is 1.
 *
 * Tracealyzer groups the events into actor instances, based on context-switches
 * and a definition of "Instance Finish Events", or IFEs. These are kernel calls
 * considered to be the last event in a task instance. Some kernel calls are
 * considered IFEs by default (e.g., delay functions), but it is also possible
 * to specify this individually for each task (see vTraceTaskInstanceFinish).
 *
 * If USE_IMPLICIT_IFE_RULES is one (1), the default IFEs will be enabled, which
 * gives a "typical" grouping of events into instances. You can combine this
 * with calls to vTraceTaskInstanceFinish for specific tasks.
 *
 * If USE_IMPLICIT_IFE_RULES is zero (0), the implicit IFEs are disabled and all
 * events withing each task is then shown as a single instance, unless  you call
 * vTraceTaskInstanceFinish() at suitable locations to mark the IFEs.
 *****************************************************************************/
#define USE_IMPLICIT_IFE_RULES 1

/******************************************************************************
 * USE_16BIT_OBJECT_HANDLES
 *
 * Macro which should be defined as either zero (0) or one (1).
 *
 * If set to 0 (zero), the recorder uses 8-bit handles to identify kernel
 * objects such as tasks and queues. This limits the supported number of
 * concurrently active objects to 255 of each type (object class).
 *
 * If set to 1 (one), the recorder uses 16-bit handles to identify kernel
 * objects such as tasks and queues. This limits the supported number of
 * concurrent objects to 65535 of each type (object class). However, since the
 * object property table is limited to 64 KB, the practical limit is about
 * 3000 objects in total.
 *
 * Default is 0.
 *
 * NOTE: An object with handle above 255 will use an extra 4-byte record in
 * the event buffer whenever referenced. Moreover, some internal tables in the
 * recorder gets larger when using 16-bit handles. The additional RAM usage is
 * 5-10 byte plus 1 byte per kernel object i.e., task, queue, mutex, etc.
 *****************************************************************************/
#define USE_16BIT_OBJECT_HANDLES 0

/******************************************************************************
 * USE_TRACE_ASSERT
 *
 * Macro which should be defined as either zero (0) or one (1).
 * Default is 1.
 *
 * If this is one (1), the TRACE_ASSERT macro will verify that a condition is
 * true. If the condition is false, vTraceError() will be called.
 * This is used on several places in the recorder code for sanity checks on
 * parameters. Can be switched off to reduce CPU usage of the tracing.
 *****************************************************************************/
#define USE_TRACE_ASSERT 1

/*******************************************************************************
 * USE_SEPARATE_USER_EVENT_BUFFER
 *
 * Macro which should be defined as an integer value.
 * Default is zero (0).
 *
 * This enables and disables the use of the separate user event buffer. Using
 * this separate buffer has the benefit of not overwriting the user events with
 * kernel events (usually generated at a much higher rate), i.e., when using
 * ring-buffer mode.
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
#define USER_EVENT_BUFFER_SIZE 10

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

#endif

