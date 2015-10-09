/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v3.0.2
 * Percepio AB, www.percepio.com
 *
 * trcConfig.h
 *
 * Configuration parameters for the streaming version trace recorder library.
 * Before using the trace recorder library, please check that the default
 * settings are appropriate for your system, and if necessary adjust these.
 *
 * Terms of Use
 * This software (the "Tracealyzer Recorder Library") is the intellectual
 * property of Percepio AB and may not be sold or in other ways commercially
 * redistributed without explicit written permission by Percepio AB.
 *
 * Separate conditions applies for the SEGGER branded source code included.
 *
 * The recorder library is free for use together with Percepio products.
 * You may distribute the recorder library in its original form, but public
 * distribution of modified versions require approval by Percepio AB.
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
 * Copyright Percepio AB, 2015.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRC_CONFIG_H
#define TRC_CONFIG_H

#ifdef __cplusplus
extern “C” {
#endif

/*******************************************************************************
 * Configuration Macro: TRC_RECORDER_HARDWARE_PORT
 *
 * Specify what hardware is used.
 *
 * See trcHardwarePort.h for available ports, or to define your own.
 ******************************************************************************/
#define TRC_RECORDER_HARDWARE_PORT TRC_PORT_ARM_Cortex_M

/******************************************************************************
 * BSP and other project specific includes
 * 
 * Include the necessary header files.
 *****************************************************************************/
#include "board.h"

/******************************************************************************
 * TRC_FREERTOS_VERSION
 * 
 * Specify what version of FreeRTOS that is used. This is necessary compensate 
 * for renamed symbols in the FreeRTOS kernel (does not build if incorrect).
 * 
 * TRC_FREERTOS_VERSION_7_3_OR_7_4 (= 1)		If using FreeRTOS v7.3.0 - v7.4.2
 * TRC_FREERTOS_VERSION_7_5_OR_7_6 (= 2)		If using FreeRTOS v7.5.0 - v7.6.0
 * TRC_FREERTOS_VERSION_8_0_OR_LATER (= 3)		If using FreeRTOS v8.0.0 or later
 *****************************************************************************/
#define TRC_FREERTOS_VERSION_NOT_SET			0
#define TRC_FREERTOS_VERSION_7_3_OR_7_4			1
#define TRC_FREERTOS_VERSION_7_5_OR_7_6			2
#define TRC_FREERTOS_VERSION_8_0_OR_LATER		3

#define TRC_FREERTOS_VERSION	TRC_FREERTOS_VERSION_8_0_OR_LATER

/*******************************************************************************
 * Configuration Macro: TRC_SYMBOL_TABLE_SLOTS
 *
 * The maximum number of symbols names that can be stored. This includes:
 * - Task names
 * - Named ISRs (vTraceSetISRProperties)
 * - Named kernel objects (vTraceStoreKernelObjectName)
 * - User event channels (vTraceStoreUserEventChannelName)
 *
 * If this value is too small, not all symbol names will be stored and the
 * trace display will be affected. In that case, there will be warnings
 * (as User Events) from TzCtrl task, that monitors this.
 ******************************************************************************/
#define TRC_SYMBOL_TABLE_SLOTS 30

/*******************************************************************************
 * Configuration Macro: TRC_SYMBOL_MAX_LENGTH
 *
 * The maximum length of symbol names, including:
 * - Task names
 * - Named ISRs (vTraceSetISRProperties)
 * - Named kernel objects (vTraceStoreKernelObjectName)
 * - User event channel names (vTraceStoreUserEventChannelName)
 *
 * If longer symbol names are used, they will be truncated by the recorder,
 * which will affect the trace display. In that case, there will be warnings
 * (as User Events) from TzCtrl task, that monitors this.
 ******************************************************************************/
#define TRC_SYMBOL_MAX_LENGTH 25

/*******************************************************************************
 * Configuration Macro: TRC_OBJECT_DATA_SLOTS
 *
 * The maximum number of object data entries (used for task priorities) that can
 * be stored at the same time. Must be sufficient for all tasks, otherwise there
 * will be warnings (as User Events) from TzCtrl task, that monitors this.
 ******************************************************************************/
#define TRC_OBJECT_DATA_SLOTS 20

/*******************************************************************************
 * Configuration Macro: TRC_RTT_UP_BUFFER_INDEX
 *
 * Defines the RTT buffer to use for writing the trace data. Make sure that
 * the PC application has the same setting (File->Settings).
 *
 ******************************************************************************/
#define TRC_RTT_UP_BUFFER_INDEX 0

/*******************************************************************************
 * Configuration Macro: TRC_RTT_DOWN_BUFFER_INDEX
 *
 * Defines the RTT buffer to use for reading the trace data. Make sure that
 * the PC application has the same setting (File->Settings).
 *
 ******************************************************************************/
#define TRC_RTT_DOWN_BUFFER_INDEX 0

/*******************************************************************************
 * Configuration Macro: TRC_CTRL_TASK_STACK_SIZE
 *
 * The stack size of the TzCtrl task, that receive commands.
 * We are aiming to remove this extra task in future versions.
 ******************************************************************************/
#define TRC_CTRL_TASK_STACK_SIZE (configMINIMAL_STACK_SIZE * 2)

/*******************************************************************************
 * Configuration Macro: TRC_CTRL_TASK_PRIORITY
 *
 * The priority of the TzCtrl task, that receive commands from.
 * We are aiming to remove this extra task in future versions.
 ******************************************************************************/
#define TRC_CTRL_TASK_PRIORITY 1

/*******************************************************************************
 * Configuration Macro: TRC_CTRL_TASK_DELAY
 *
 * The delay between every loop of the TzCtrl task. A high delay will reduce the
 * CPU load, but may cause missed events if the TzCtrl task is performing the 
 * trace transfer.
 ******************************************************************************/
#define TRC_CTRL_TASK_DELAY ((10 * configTICK_RATE_HZ) / 1000)

/*******************************************************************************
 * Configuration Macro: TRC_MEASURE_BLOCKING_TIME
 *
 * If using SEGGER_RTT_MODE_BLOCK_IF_FIFO_FULL, this activates detection and
 * warnings in case of blocking in SEGGER_RTT_Write (if too small buffer).
 *
 * If enabling this option (set to 1) warnings are given as User Events if
 * blocking occurs, including the longest blocking time. These warnings are
 * given on the channel "Blocking on trace buffer".
 *
 * Note: If you get such warnings, you can study the blocking time in the User
 * Event Signal Plot to get an overview of the magnitude of the blocking and
 * decide if acceptable.
 *
 * To eliminate or at least reduce occurrences of blocking:
 *
 * - Verify the J-Link Speed in the Settings dialog of the PC application.
 *   Default is 4 MHz, but can be increased a lot depending on your J-Link.
 *
 *   Note: If you set the speed higher than your J-Link can manage, the J-Link
 *   driver will instead use the fastest supported speed. The actual speed used
 *   is shown in the title of the trace receiver window.
 *
 * - Increase the buffer size (BUFFER_SIZE_UP in SEGGER_RTT_Conf.h).
 *
 * - Reduce the amount of data produced, e.g., by removing frequent User Events.
 ******************************************************************************/
#define TRC_MEASURE_BLOCKING_TIME 0

/*******************************************************************************
 * Configuration Macro: TRC_BLOCKING_MIN_CYCLES
 *
 * Threshold value for deciding if SEGGER_RTT_Write has blocked. Most events
 * take 200-300 cycles on ARM Cortex-M MCUs, so anything above 500 cycles should
 * be due to blocking on a full buffer (i.e., waiting for the debugger to read
 * the RTT buffer data and make room for more...).
 ******************************************************************************/
#define TRC_BLOCKING_MIN_CYCLES 500

/*******************************************************************************
 * Configuration Macro: TRC_RECORDER_BUFFER_ALLOCATION
 *
 * Specifies how the recorder buffer is allocated.
 *
 * Values:
 * TRC_RECORDER_BUFFER_ALLOCATION_STATIC
 * TRC_RECORDER_BUFFER_ALLOCATION_DYNAMIC
 ******************************************************************************/
#define TRC_RECORDER_BUFFER_ALLOCATION TRC_RECORDER_BUFFER_ALLOCATION_STATIC

/*******************************************************************************
 * Configuration Macro: TRC_RECORDER_TRANSFER_METHOD
 *
 * Specifies what type of transfer method is used.
 *
 * Values:
 * TRC_RECORDER_TRANSFER_METHOD_JLINK_RTT_BLOCK
 * TRC_RECORDER_TRANSFER_METHOD_JLINK_RTT_NOBLOCK
 * TRC_RECORDER_TRANSFER_METHOD_TCPIP
 * TRC_RECORDER_TRANSFER_METHOD_CUSTOM
 ******************************************************************************/
#define TRC_RECORDER_TRANSFER_METHOD TRC_RECORDER_TRANSFER_METHOD_JLINK_RTT_BLOCK

/*******************************************************************************
 * Configuration Macro: TRC_STREAM_CUSTOM_BLOCKING_TRANSFER
 *
 * Note: Only active if TRC_RECORDER_TRANSFER_METHOD_CUSTOM is used.
 *
 * Specifies how the custom transfer method handles full buffers.
 *
 * Values:
 * 0 - The custom transfer method skips sending the data if the buffer is full.
 * 1 - The custom transfer method blocks on send if the buffer is full.
 ******************************************************************************/
 #define TRC_STREAM_CUSTOM_BLOCKING_TRANSFER 

/*******************************************************************************
 * Configuration Macro: TRC_STREAM_CUSTOM_ALLOCATE_FIELDS
 *
 * Note: Only active if TRC_RECORDER_TRANSFER_METHOD_CUSTOM is used.
 *
 * Macro that should allocate any buffers needed for the transfer method.
 * See trcStreamPort.h for examples.
 ******************************************************************************/
#define TRC_STREAM_CUSTOM_ALLOCATE_FIELDS() 

/*******************************************************************************
 * Configuration Macro: TRC_STREAM_CUSTOM_INIT
 *
 * Note: Only active if TRC_RECORDER_TRANSFER_METHOD_CUSTOM is used.
 *
 * Used to initialize and set up the transfer method.
 * See trcStreamPort.h for examples.
 ******************************************************************************/
#define TRC_STREAM_CUSTOM_INIT() 

/*******************************************************************************
 * Configuration Macro: TRC_STREAM_CUSTOM_ALLOCATE_EVENT
 *
 * Note: Only active if TRC_RECORDER_TRANSFER_METHOD_CUSTOM is used.
 *
 * Specifies how the trace events that should be sent using the transfer method
 * are allocated first.
 * See trcStreamPort.h for examples.
 ******************************************************************************/
#define TRC_STREAM_CUSTOM_ALLOCATE_EVENT(_type, _ptr, _size) 

/*******************************************************************************
 * Configuration Macro: TRC_STREAM_CUSTOM_COMMIT_EVENT
 *
 * Note: Only active if TRC_RECORDER_TRANSFER_METHOD_CUSTOM is used.
 *
 * Specifies how trace events are sent/written.
 * See trcStreamPort.h for examples.
 ******************************************************************************/
#define TRC_STREAM_CUSTOM_COMMIT_EVENT(_ptr, _size) 

/*******************************************************************************
 * Configuration Macro: TRC_STREAM_CUSTOM_READ_DATA
 *
 * Note: Only active if TRC_RECORDER_TRANSFER_METHOD_CUSTOM is used.
 *
 * Specifies how data is read using the transfer method.
 * See trcStreamPort.h for examples.
 ******************************************************************************/
#define TRC_STREAM_CUSTOM_READ_DATA(_ptrData, _size, _ptrBytesRead) 

/*******************************************************************************
 * Configuration Macro: TRC_STREAM_CUSTOM_PERIODIC_SEND_DATA
 *
 * Note: Only active if TRC_RECORDER_TRANSFER_METHOD_CUSTOM is used.
 *
 * Specifies how data is sent periodically. Used by certain transfer methods.
 * See trcStreamPort.h for examples.
 ******************************************************************************/
#define TRC_STREAM_CUSTOM_PERIODIC_SEND_DATA(_ptrBytesSent) 

/*******************************************************************************
 * Configuration Macro: TRC_STREAM_CUSTOM_ON_TRACE_BEGIN
 *
 * Note: Only active if TRC_RECORDER_TRANSFER_METHOD_CUSTOM is used.
 *
 * Called on tracing is started. Use this to perform any necessary steps to 
 * properly start the trace, such as clearing buffers.
 ******************************************************************************/
#define TRC_STREAM_CUSTOM_ON_TRACE_BEGIN() 

/*******************************************************************************
 * Configuration Macro: TRC_STREAM_CUSTOM_ON_TRACE_END
 *
 * Note: Only active if TRC_RECORDER_TRANSFER_METHOD_CUSTOM is used.
 *
 * Called when tracing is disabled. Use this to perform any necessary steps to 
 * properly shut down the tracing, such as clearing buffers.
 ******************************************************************************/
#define TRC_STREAM_CUSTOM_ON_TRACE_END() 

#ifdef __cplusplus
}
#endif

#endif /* TRC_CONFIG_H */
