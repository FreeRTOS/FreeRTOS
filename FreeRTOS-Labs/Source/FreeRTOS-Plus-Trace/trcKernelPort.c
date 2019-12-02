/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v4.1.5
 * Percepio AB, www.percepio.com
 *
 * trcKernelPort.c
 *
 * The FreeRTOS-specific parts of the trace recorder
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

#include "FreeRTOS.h"

#if (!defined(TRC_USE_TRACEALYZER_RECORDER) && configUSE_TRACE_FACILITY == 1)
#error Trace Recorder: You need to include trcRecorder.h at the end of your FreeRTOSConfig.h!
#endif

#if (defined(TRC_USE_TRACEALYZER_RECORDER) && TRC_USE_TRACEALYZER_RECORDER == 1)

#ifndef TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS
 /* TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS is missing in trcConfig.h. */
#error "TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS must be defined in trcConfig.h."
#endif

#ifndef TRC_CFG_INCLUDE_TIMER_EVENTS
 /* TRC_CFG_INCLUDE_TIMER_EVENTS is missing in trcConfig.h. */
#error "TRC_CFG_INCLUDE_TIMER_EVENTS must be defined in trcConfig.h."
#endif

#ifndef TRC_CFG_INCLUDE_PEND_FUNC_CALL_EVENTS
 /* TRC_CFG_INCLUDE_PEND_FUNC_CALL_EVENTS is missing in trcConfig.h. */
#error "TRC_CFG_INCLUDE_PEND_FUNC_CALL_EVENTS must be defined in trcConfig.h."
#endif

#ifndef TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS
 /* TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS is missing in trcConfig.h. Define this as 1 if using FreeRTOS v10 or later and like to trace stream buffer or message buffer events, otherwise 0. */
#error "TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS must be defined in trcConfig.h."
#endif

#if (configUSE_TICKLESS_IDLE != 0 && (TRC_HWTC_TYPE == TRC_OS_TIMER_INCR || TRC_HWTC_TYPE == TRC_OS_TIMER_DECR))
	/* 	
		The below error message is to alert you on the following issue:
		
		The hardware port selected in trcConfig.h uses the operating system timer for the 
		timestamping, i.e., the periodic interrupt timer that drives the OS tick interrupt.
				
		When using "tickless idle" mode, the recorder needs an independent time source in
		order to correctly record the durations of the idle times. Otherwise, the trace may appear
		to have a different length than in reality, and the reported CPU load is also affected.
		
		You may override this warning by defining the TRC_CFG_ACKNOWLEDGE_TICKLESS_IDLE_WARNING
		macro in your trcConfig.h file. But then the time scale may be incorrect during
		tickless idle periods.
		
		To get this correct, override the default timestamping by setting TRC_CFG_HARDWARE_PORT
		in trcConfig.h to TRC_HARDWARE_PORT_APPLICATION_DEFINED and define the HWTC macros
		accordingly, using a free running counter or an independent periodic interrupt timer.
		See trcHardwarePort.h for details.
				
		For ARM Cortex-M3, M4 and M7 MCUs this is not an issue, since the recorder uses the 
		DWT cycle counter for timestamping in these cases.		
	*/
	
	#ifndef TRC_CFG_ACKNOWLEDGE_TICKLESS_IDLE_WARNING
	#error Trace Recorder: This timestamping mode is not recommended with Tickless Idle.
	#endif
#endif /* (configUSE_TICKLESS_IDLE != 0 && (TRC_HWTC_TYPE == TRC_OS_TIMER_INCR || TRC_HWTC_TYPE == TRC_OS_TIMER_DECR)) */
	
#include "task.h"
#include "queue.h"

#if (TRC_CFG_INCLUDE_TIMER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X)
/* If the project does not include the FreeRTOS timers, TRC_CFG_INCLUDE_TIMER_EVENTS must be set to 0 */
#include "timers.h"
#endif /* (TRC_CFG_INCLUDE_TIMER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X) */

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X)
/* If the project does not include the FreeRTOS event groups, TRC_CFG_INCLUDE_TIMER_EVENTS must be set to 0 */
#include "event_groups.h"
#endif /* (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X) */

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)
/* If the project does not include the FreeRTOS stream buffers, TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS must be set to 0 */
#include "stream_buffer.h"
#endif /* (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */

uint32_t prvTraceGetQueueNumber(void* handle);

#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_8_X)

extern unsigned char ucQueueGetQueueNumber( xQueueHandle pxQueue );
extern void vQueueSetQueueNumber( xQueueHandle pxQueue, unsigned char ucQueueNumber );
extern unsigned char ucQueueGetQueueType( xQueueHandle pxQueue );

uint32_t prvTraceGetQueueNumber(void* handle)
{
	return (uint32_t)ucQueueGetQueueNumber(handle);
}
#else 
uint32_t prvTraceGetQueueNumber(void* handle)
{
	return (uint32_t)uxQueueGetQueueNumber(handle);
}
#endif /* (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_8_X) */

uint8_t prvTraceGetQueueType(void* handle)
{
	// This is either declared in header file in FreeRTOS 8 and later, or as extern above
	return ucQueueGetQueueType(handle);
}

/* Tasks */
uint16_t prvTraceGetTaskNumberLow16(void* handle)
{
	return TRACE_GET_LOW16(uxTaskGetTaskNumber(handle));
}

uint16_t prvTraceGetTaskNumberHigh16(void* handle)
{
	return TRACE_GET_HIGH16(uxTaskGetTaskNumber(handle));
}

void prvTraceSetTaskNumberLow16(void* handle, uint16_t value)
{
	vTaskSetTaskNumber(handle, TRACE_SET_LOW16(uxTaskGetTaskNumber(handle), value));
}

void prvTraceSetTaskNumberHigh16(void* handle, uint16_t value)
{
	vTaskSetTaskNumber(handle, TRACE_SET_HIGH16(uxTaskGetTaskNumber(handle), value));
}

uint16_t prvTraceGetQueueNumberLow16(void* handle)
{
	return TRACE_GET_LOW16(prvTraceGetQueueNumber(handle));
}

uint16_t prvTraceGetQueueNumberHigh16(void* handle)
{
	return TRACE_GET_HIGH16(prvTraceGetQueueNumber(handle));
}

void prvTraceSetQueueNumberLow16(void* handle, uint16_t value)
{
	vQueueSetQueueNumber(handle, TRACE_SET_LOW16(prvTraceGetQueueNumber(handle), value));
}

void prvTraceSetQueueNumberHigh16(void* handle, uint16_t value)
{
	vQueueSetQueueNumber(handle, TRACE_SET_HIGH16(prvTraceGetQueueNumber(handle), value));
}

#if (TRC_CFG_INCLUDE_TIMER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

uint16_t prvTraceGetTimerNumberLow16(void* handle)
{
	return TRACE_GET_LOW16(uxTimerGetTimerNumber(handle));
}

uint16_t prvTraceGetTimerNumberHigh16(void* handle)
{
	return TRACE_GET_HIGH16(uxTimerGetTimerNumber(handle));
}

void prvTraceSetTimerNumberLow16(void* handle, uint16_t value)
{
	vTimerSetTimerNumber(handle, TRACE_SET_LOW16(uxTimerGetTimerNumber(handle), value));
}

void prvTraceSetTimerNumberHigh16(void* handle, uint16_t value)
{
	vTimerSetTimerNumber(handle, TRACE_SET_HIGH16(uxTimerGetTimerNumber(handle), value));
}
#endif /* (TRC_CFG_INCLUDE_TIMER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

uint16_t prvTraceGetEventGroupNumberLow16(void* handle)
{
	return TRACE_GET_LOW16(uxEventGroupGetNumber(handle));
}

uint16_t prvTraceGetEventGroupNumberHigh16(void* handle)
{
	return TRACE_GET_HIGH16(uxEventGroupGetNumber(handle));
}

void prvTraceSetEventGroupNumberLow16(void* handle, uint16_t value)
{
	vEventGroupSetNumber(handle, TRACE_SET_LOW16(uxEventGroupGetNumber(handle), value));
}

void prvTraceSetEventGroupNumberHigh16(void* handle, uint16_t value)
{
	vEventGroupSetNumber(handle, TRACE_SET_HIGH16(uxEventGroupGetNumber(handle), value));
}
#endif /* (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

uint16_t prvTraceGetStreamBufferNumberLow16(void* handle)
{
	return TRACE_GET_LOW16(uxStreamBufferGetStreamBufferNumber(handle));
}

uint16_t prvTraceGetStreamBufferNumberHigh16(void* handle)
{
	return TRACE_GET_HIGH16(uxStreamBufferGetStreamBufferNumber(handle));
}

void prvTraceSetStreamBufferNumberLow16(void* handle, uint16_t value)
{
	vStreamBufferSetStreamBufferNumber(handle, TRACE_SET_LOW16(uxStreamBufferGetStreamBufferNumber(handle), value));
}

void prvTraceSetStreamBufferNumberHigh16(void* handle, uint16_t value)
{
	vStreamBufferSetStreamBufferNumber(handle, TRACE_SET_HIGH16(uxStreamBufferGetStreamBufferNumber(handle), value));
}
#endif /* (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)
	
static void* pCurrentTCB = NULL;
#if (defined(configENABLE_BACKWARD_COMPATIBILITY) && configENABLE_BACKWARD_COMPATIBILITY == 0)
/* We're explicitly not using compatibility mode */
static TaskHandle_t HandleTzCtrl = NULL;       /* TzCtrl task TCB */
#else
/* We're using compatibility mode, or we're running an old kernel */
static xTaskHandle HandleTzCtrl = NULL;       /* TzCtrl task TCB */
#endif

#if defined(configSUPPORT_STATIC_ALLOCATION)
#if (configSUPPORT_STATIC_ALLOCATION == 1)
static StackType_t stackTzCtrl[TRC_CFG_CTRL_TASK_STACK_SIZE];
static StaticTask_t tcbTzCtrl;
#endif
#endif

/* Monitored by TzCtrl task, that give warnings as User Events */
extern volatile uint32_t NoRoomForSymbol;
extern volatile uint32_t NoRoomForObjectData;
extern volatile uint32_t LongestSymbolName;
extern volatile uint32_t MaxBytesTruncated;

/* Keeps track of previous values, to only react on changes. */
static uint32_t NoRoomForSymbol_last = 0;
static uint32_t NoRoomForObjectData_last = 0;
static uint32_t LongestSymbolName_last = 0;
static uint32_t MaxBytesTruncated_last = 0;

/* User Event Channel for giving warnings regarding NoRoomForSymbol etc. */
traceString trcWarningChannel;

#define TRC_PORT_MALLOC(size) pvPortMalloc(size)

TRC_STREAM_PORT_ALLOCATE_FIELDS()

/* Called by TzCtrl task periodically (Normally every 100 ms) */
static void prvCheckRecorderStatus(void);

extern void prvTraceWarning(int errCode);

/* The TzCtrl task - receives commands from Tracealyzer (start/stop) */
static portTASK_FUNCTION( TzCtrl, pvParameters );

/*******************************************************************************
 * vTraceEnable
 *
 * Function that enables the tracing and creates the control task. It will halt
 * execution until a Start command has been received if haltUntilStart is true.
 *
 ******************************************************************************/
void vTraceEnable(int startOption)
{
	int32_t bytes = 0;
	int32_t status;
	extern uint32_t RecorderEnabled;
	TracealyzerCommandType msg;

	/* Only do this first time...*/
	if (HandleTzCtrl == NULL)
	{
		TRC_STREAM_PORT_INIT();
		
		/* Note: Requires that TRC_CFG_INCLUDE_USER_EVENTS is 1. */
		trcWarningChannel = xTraceRegisterString("Warnings from Recorder");

		/* Creates the TzCtrl task - receives trace commands (start, stop, ...) */
		#if defined(configSUPPORT_STATIC_ALLOCATION) && (configSUPPORT_STATIC_ALLOCATION == 1)
		HandleTzCtrl = xTaskCreateStatic(TzCtrl, STRING_CAST("TzCtrl"), TRC_CFG_CTRL_TASK_STACK_SIZE, NULL, TRC_CFG_CTRL_TASK_PRIORITY, stackTzCtrl, &tcbTzCtrl);
		#else
		xTaskCreate( TzCtrl, STRING_CAST("TzCtrl"), TRC_CFG_CTRL_TASK_STACK_SIZE, NULL, TRC_CFG_CTRL_TASK_PRIORITY, &HandleTzCtrl );
		#endif

		if (HandleTzCtrl == NULL)
		{
			prvTraceError(PSF_ERROR_TZCTRLTASK_NOT_CREATED);
		}
	}

	if (startOption == TRC_START_AWAIT_HOST)
	{
		/* We keep trying to read commands until the recorder has been started */
		do
		{
			bytes = 0;
			
			status = TRC_STREAM_PORT_READ_DATA(&msg, sizeof(TracealyzerCommandType), (int32_t*)&bytes);
			
			if (status != 0)
			{
				prvTraceWarning(PSF_WARNING_STREAM_PORT_READ);
			}

			if ((status == 0) && (bytes == sizeof(TracealyzerCommandType)))
			{
				if (prvIsValidCommand(&msg))
				{
					if (msg.cmdCode == CMD_SET_ACTIVE && msg.param1 == 1)
					{
						/* On start, init and reset the timestamping */
						TRC_PORT_SPECIFIC_INIT();
					}
					
					prvProcessCommand(&msg);
				}
			}
		}
		while (RecorderEnabled == 0);
	}
	else if (startOption == TRC_START)
	{
		/* We start streaming directly - this assumes that the interface is ready! */
		TRC_PORT_SPECIFIC_INIT();
		
		msg.cmdCode = CMD_SET_ACTIVE;
		msg.param1 = 1;
		prvProcessCommand(&msg);
	}
	else
	{
		/* On TRC_INIT */
		TRC_PORT_SPECIFIC_INIT();
	}
}

#if (TRC_CFG_SCHEDULING_ONLY == 0)
/*******************************************************************************
 * vTraceSetQueueName(void* object, const char* name)
 *
 * Parameter object: pointer to the Queue that shall be named
 * Parameter name: the name to set (const string literal)
 *
 * Sets a name for Queue objects for display in Tracealyzer.
 ******************************************************************************/
void vTraceSetQueueName(void* object, const char* name)
{
	vTraceStoreKernelObjectName(object, name);
}

/*******************************************************************************
 * vTraceSetSemaphoreName(void* object, const char* name)
 *
 * Parameter object: pointer to the Semaphore that shall be named
 * Parameter name: the name to set (const string literal)
 *
 * Sets a name for Semaphore objects for display in Tracealyzer.
 ******************************************************************************/
void vTraceSetSemaphoreName(void* object, const char* name)
{
	vTraceStoreKernelObjectName(object, name);
}

/*******************************************************************************
 * vTraceSetMutexName(void* object, const char* name)
 *
 * Parameter object: pointer to the Mutex that shall be named
 * Parameter name: the name to set (const string literal)
 *
 * Sets a name for Mutex objects for display in Tracealyzer.
 ******************************************************************************/
void vTraceSetMutexName(void* object, const char* name)
{
	vTraceStoreKernelObjectName(object, name);
}

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X)
/*******************************************************************************
* vTraceSetEventGroupName(void* object, const char* name)
*
* Parameter object: pointer to the vTraceSetEventGroupName that shall be named
* Parameter name: the name to set (const string literal)
*
* Sets a name for EventGroup objects for display in Tracealyzer.
******************************************************************************/
void vTraceSetEventGroupName(void* object, const char* name)
{
	vTraceStoreKernelObjectName(object, name);
}
#endif /* (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X) */

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)
/*******************************************************************************
* vTraceSetStreamBufferName(void* object, const char* name)
*
* Parameter object: pointer to the StreamBuffer that shall be named
* Parameter name: the name to set (const string literal)
*
* Sets a name for StreamBuffer objects for display in Tracealyzer.
******************************************************************************/
void vTraceSetStreamBufferName(void* object, const char* name)
{
	vTraceStoreKernelObjectName(object, name);
}

/*******************************************************************************
* vTraceSetMessageBufferName(void* object, const char* name)
*
* Parameter object: pointer to the MessageBuffer that shall be named
* Parameter name: the name to set (const string literal)
*
* Sets a name for MessageBuffer objects for display in Tracealyzer.
******************************************************************************/
void vTraceSetMessageBufferName(void* object, const char* name)
{
	vTraceStoreKernelObjectName(object, name);
}
#endif /* (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */

#endif /* (TRC_CFG_SCHEDULING_ONLY == 0) */

/*******************************************************************************
 * prvGetCurrentTaskHandle
 *
 * Function that returns the handle to the currently executing task.
 *
 ******************************************************************************/
void* prvTraceGetCurrentTaskHandle(void)
{
	return xTaskGetCurrentTaskHandle();
}

/*******************************************************************************
 * prvIsNewTCB
 *
 * Tells if this task is already executing, or if there has been a task-switch.
 * Assumed to be called within a trace hook in kernel context.
 ******************************************************************************/
uint32_t prvIsNewTCB(void* pNewTCB)
{
	if (pCurrentTCB != pNewTCB)
	{
		pCurrentTCB = pNewTCB;
		return 1;
	}
	return 0;
}

/*******************************************************************************
 * prvTraceIsSchedulerSuspended
 *
 * Returns true if the RTOS scheduler currently is disabled, thus preventing any
 * task-switches from occurring. Only called from vTraceStoreISREnd.
 ******************************************************************************/
unsigned char prvTraceIsSchedulerSuspended(void)
{
    /* Assumed to be available in FreeRTOS. According to the FreeRTOS docs, 
	INCLUDE_xTaskGetSchedulerState or configUSE_TIMERS must be set to 1 in
	FreeRTOSConfig.h for this function to be available. */

	return xTaskGetSchedulerState() == taskSCHEDULER_SUSPENDED;
}


/*******************************************************************************
 * prvCheckRecorderStatus
 *
 * Called by TzCtrl task periodically (every 100 ms - seems reasonable).
 * Checks a number of diagnostic variables and give warnings as user events,
 * in most cases including a suggested solution.
 ******************************************************************************/
static void prvCheckRecorderStatus(void)
{
	if (NoRoomForSymbol > NoRoomForSymbol_last)
	{
		if (NoRoomForSymbol > 0)
		{
			prvTraceWarning(PSF_WARNING_SYMBOL_TABLE_SLOTS);
		}
		NoRoomForSymbol_last = NoRoomForSymbol;
	}

	if (NoRoomForObjectData > NoRoomForObjectData_last)
	{
		if (NoRoomForObjectData > 0)
		{
			prvTraceWarning(PSF_WARNING_OBJECT_DATA_SLOTS);
		}
		NoRoomForObjectData_last = NoRoomForObjectData;
	}

	if (LongestSymbolName > LongestSymbolName_last)
	{
		if (LongestSymbolName > (TRC_CFG_SYMBOL_MAX_LENGTH))
		{
			prvTraceWarning(PSF_WARNING_SYMBOL_MAX_LENGTH);
		}
		LongestSymbolName_last = LongestSymbolName;
	}

	if (MaxBytesTruncated > MaxBytesTruncated_last)
	{
		if (MaxBytesTruncated > 0)
		{
			prvTraceWarning(PSF_WARNING_STRING_TOO_LONG);
		}
		MaxBytesTruncated_last = MaxBytesTruncated;
	}
}

/*******************************************************************************
 * TzCtrl
 *
 * Task for sending the trace data from the internal buffer to the stream 
 * interface (assuming TRC_STREAM_PORT_USE_INTERNAL_BUFFER == 1) and for
 * receiving commands from Tracealyzer. Also does some diagnostics.
 ******************************************************************************/
static portTASK_FUNCTION( TzCtrl, pvParameters )
{
	TracealyzerCommandType msg;
	int32_t bytes = 0;
	int32_t status = 0;
	(void)pvParameters;

	while (1)
	{
		do
		{
			/* Listen for new commands */
			bytes = 0;
			status = TRC_STREAM_PORT_READ_DATA(&msg, sizeof(TracealyzerCommandType), (int32_t*)&bytes);

			if (status != 0)
			{
				prvTraceWarning(PSF_WARNING_STREAM_PORT_READ);
			}

			if ((status == 0) && (bytes == sizeof(TracealyzerCommandType)))
			{
				if (prvIsValidCommand(&msg))
				{
					prvProcessCommand(&msg); /* Start or Stop currently... */
				}
			}

/* If the internal buffer is disabled, the COMMIT macro instead sends the data directly 
   from the "event functions" (using TRC_STREAM_PORT_WRITE_DATA). */			
#if (TRC_STREAM_PORT_USE_INTERNAL_BUFFER == 1)
			/* If there is a buffer page, this sends it to the streaming interface using TRC_STREAM_PORT_WRITE_DATA. */
			bytes = prvPagedEventBufferTransfer();
#endif			
			
		/* If there was data sent or received (bytes != 0), loop around and repeat, if there is more data to send or receive.
		Otherwise, step out of this loop and sleep for a while. */		
		
		} while (bytes != 0);

		prvCheckRecorderStatus();

		vTaskDelay(TRC_CFG_CTRL_TASK_DELAY);
	}
}

#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/


#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT)

/* Internal flag to tell the context of tracePEND_FUNC_CALL_FROM_ISR */
int uiInEventGroupSetBitsFromISR = 0;

/******************************************************************************
 * TraceQueueClassTable
 * Translates a FreeRTOS QueueType into trace objects classes (TRACE_CLASS_).
 * Has one entry for each QueueType, gives TRACE_CLASS ID.
 ******************************************************************************/
traceObjectClass TraceQueueClassTable[5] = {
	TRACE_CLASS_QUEUE,
	TRACE_CLASS_MUTEX,
	TRACE_CLASS_SEMAPHORE,
	TRACE_CLASS_SEMAPHORE,
	TRACE_CLASS_MUTEX
};

#if (TRC_CFG_SCHEDULING_ONLY == 0)
/*******************************************************************************
 * vTraceSetQueueName(void* object, const char* name)
 *
 * Parameter object: pointer to the Queue that shall be named
 * Parameter name: the name to set (const string literal)
 *
 * Sets a name for Queue objects for display in Tracealyzer.
 ******************************************************************************/
void vTraceSetQueueName(void* object, const char* name)
{
	prvTraceSetObjectName(TRACE_CLASS_QUEUE, TRACE_GET_OBJECT_NUMBER(QUEUE, object), name);
}

/*******************************************************************************
 * vTraceSetSemaphoreName(void* object, const char* name)
 *
 * Parameter object: pointer to the Semaphore that shall be named
 * Parameter name: the name to set (const string literal)
 *
 * Sets a name for Semaphore objects for display in Tracealyzer.
 ******************************************************************************/
void vTraceSetSemaphoreName(void* object, const char* name)
{
	prvTraceSetObjectName(TRACE_CLASS_SEMAPHORE, TRACE_GET_OBJECT_NUMBER(QUEUE, object), name);
}

/*******************************************************************************
 * vTraceSetMutexName(void* object, const char* name)
 *
 * Parameter object: pointer to the Mutex that shall be named
 * Parameter name: the name to set (const string literal)
 *
 * Sets a name for Semaphore objects for display in Tracealyzer.
 ******************************************************************************/
void vTraceSetMutexName(void* object, const char* name)
{
	prvTraceSetObjectName(TRACE_CLASS_MUTEX, TRACE_GET_OBJECT_NUMBER(QUEUE, object), name);
}

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X)
/*******************************************************************************
* vTraceSetEventGroupName(void* object, const char* name)
*
* Parameter object: pointer to the EventGroup that shall be named
* Parameter name: the name to set (const string literal)
*
* Sets a name for EventGroup objects for display in Tracealyzer.
******************************************************************************/
void vTraceSetEventGroupName(void* object, const char* name)
{
	prvTraceSetObjectName(TRACE_CLASS_EVENTGROUP, TRACE_GET_OBJECT_NUMBER(EVENTGROUP, object), name);
}
#endif /* (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X) */

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)
/*******************************************************************************
* vTraceSetStreamBufferName(void* object, const char* name)
*
* Parameter object: pointer to the StreamBuffer that shall be named
* Parameter name: the name to set (const string literal)
*
* Sets a name for StreamBuffer objects for display in Tracealyzer.
******************************************************************************/
void vTraceSetStreamBufferName(void* object, const char* name)
{
	prvTraceSetObjectName(TRACE_CLASS_STREAMBUFFER, TRACE_GET_OBJECT_NUMBER(STREAMBUFFER, object), name);
}

/*******************************************************************************
* vTraceSetMessageBufferName(void* object, const char* name)
*
* Parameter object: pointer to the MessageBuffer that shall be named
* Parameter name: the name to set (const string literal)
*
* Sets a name for MessageBuffer objects for display in Tracealyzer.
******************************************************************************/
void vTraceSetMessageBufferName(void* object, const char* name)
{
	prvTraceSetObjectName(TRACE_CLASS_MESSAGEBUFFER, TRACE_GET_OBJECT_NUMBER(STREAMBUFFER, object), name);
}
#endif /* (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */

#endif /* (TRC_CFG_SCHEDULING_ONLY == 0) */

void* prvTraceGetCurrentTaskHandle()
{
	return xTaskGetCurrentTaskHandle();
}

/* Initialization of the object property table */
void vTraceInitObjectPropertyTable()
{
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectClasses = TRACE_NCLASSES;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[0] = TRC_CFG_NQUEUE;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[1] = TRC_CFG_NSEMAPHORE;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[2] = TRC_CFG_NMUTEX;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[3] = TRC_CFG_NTASK;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[4] = TRC_CFG_NISR;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[5] = TRC_CFG_NTIMER;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[6] = TRC_CFG_NEVENTGROUP;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[7] = TRC_CFG_NSTREAMBUFFER;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[8] = TRC_CFG_NMESSAGEBUFFER;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[0] = TRC_CFG_NAME_LEN_QUEUE;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[1] = TRC_CFG_NAME_LEN_SEMAPHORE;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[2] = TRC_CFG_NAME_LEN_MUTEX;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[3] = TRC_CFG_NAME_LEN_TASK;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[4] = TRC_CFG_NAME_LEN_ISR;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[5] = TRC_CFG_NAME_LEN_TIMER;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[6] = TRC_CFG_NAME_LEN_EVENTGROUP;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[7] = TRC_CFG_NAME_LEN_STREAMBUFFER;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[8] = TRC_CFG_NAME_LEN_MESSAGEBUFFER;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[0] = PropertyTableSizeQueue;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[1] = PropertyTableSizeSemaphore;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[2] = PropertyTableSizeMutex;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[3] = PropertyTableSizeTask;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[4] = PropertyTableSizeISR;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[5] = PropertyTableSizeTimer;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[6] = PropertyTableSizeEventGroup;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[7] = PropertyTableSizeStreamBuffer;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[8] = PropertyTableSizeMessageBuffer;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[0] = StartIndexQueue;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[1] = StartIndexSemaphore;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[2] = StartIndexMutex;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[3] = StartIndexTask;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[4] = StartIndexISR;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[5] = StartIndexTimer;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[6] = StartIndexEventGroup;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[7] = StartIndexStreamBuffer;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[8] = StartIndexMessageBuffer;
	RecorderDataPtr->ObjectPropertyTable.ObjectPropertyTableSizeInBytes = TRACE_OBJECT_TABLE_SIZE;
}

/* Initialization of the handle mechanism, see e.g, prvTraceGetObjectHandle */
void vTraceInitObjectHandleStack()
{
	objectHandleStacks.indexOfNextAvailableHandle[0] = objectHandleStacks.lowestIndexOfClass[0] = 0;
	objectHandleStacks.indexOfNextAvailableHandle[1] = objectHandleStacks.lowestIndexOfClass[1] = (TRC_CFG_NQUEUE);
	objectHandleStacks.indexOfNextAvailableHandle[2] = objectHandleStacks.lowestIndexOfClass[2] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE);
	objectHandleStacks.indexOfNextAvailableHandle[3] = objectHandleStacks.lowestIndexOfClass[3] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX);
	objectHandleStacks.indexOfNextAvailableHandle[4] = objectHandleStacks.lowestIndexOfClass[4] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK);
	objectHandleStacks.indexOfNextAvailableHandle[5] = objectHandleStacks.lowestIndexOfClass[5] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR);
	objectHandleStacks.indexOfNextAvailableHandle[6] = objectHandleStacks.lowestIndexOfClass[6] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER);
	objectHandleStacks.indexOfNextAvailableHandle[7] = objectHandleStacks.lowestIndexOfClass[7] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) + (TRC_CFG_NEVENTGROUP);
	objectHandleStacks.indexOfNextAvailableHandle[8] = objectHandleStacks.lowestIndexOfClass[8] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) + (TRC_CFG_NEVENTGROUP) + (TRC_CFG_NSTREAMBUFFER);

	objectHandleStacks.highestIndexOfClass[0] = (TRC_CFG_NQUEUE) - 1;
	objectHandleStacks.highestIndexOfClass[1] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) - 1;
	objectHandleStacks.highestIndexOfClass[2] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) - 1;
	objectHandleStacks.highestIndexOfClass[3] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) - 1;
	objectHandleStacks.highestIndexOfClass[4] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) - 1;
	objectHandleStacks.highestIndexOfClass[5] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) - 1;
	objectHandleStacks.highestIndexOfClass[6] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) + (TRC_CFG_NEVENTGROUP) - 1;
	objectHandleStacks.highestIndexOfClass[7] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) + (TRC_CFG_NEVENTGROUP) + (TRC_CFG_NSTREAMBUFFER) - 1;
	objectHandleStacks.highestIndexOfClass[8] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) + (TRC_CFG_NEVENTGROUP) + (TRC_CFG_NSTREAMBUFFER) + (TRC_CFG_NMESSAGEBUFFER) - 1;
}

/* Returns the "Not enough handles" error message for this object class */
const char* pszTraceGetErrorNotEnoughHandles(traceObjectClass objectclass)
{
	switch(objectclass)
	{
	case TRACE_CLASS_TASK:
		return "Not enough TASK handles - increase TRC_CFG_NTASK in trcSnapshotConfig.h";
	case TRACE_CLASS_ISR:
		return "Not enough ISR handles - increase TRC_CFG_NISR in trcSnapshotConfig.h";
	case TRACE_CLASS_SEMAPHORE:
		return "Not enough SEMAPHORE handles - increase TRC_CFG_NSEMAPHORE in trcSnapshotConfig.h";
	case TRACE_CLASS_MUTEX:
		return "Not enough MUTEX handles - increase TRC_CFG_NMUTEX in trcSnapshotConfig.h";
	case TRACE_CLASS_QUEUE:
		return "Not enough QUEUE handles - increase TRC_CFG_NQUEUE in trcSnapshotConfig.h";
	case TRACE_CLASS_TIMER:
		return "Not enough TIMER handles - increase TRC_CFG_NTIMER in trcSnapshotConfig.h";
	case TRACE_CLASS_EVENTGROUP:
		return "Not enough EVENTGROUP handles - increase TRC_CFG_NEVENTGROUP in trcSnapshotConfig.h";
	case TRACE_CLASS_STREAMBUFFER:
		return "Not enough STREAMBUFFER handles - increase TRC_CFG_NSTREAMBUFFER in trcSnapshotConfig.h";
	case TRACE_CLASS_MESSAGEBUFFER:
		return "Not enough MESSAGEBUFFER handles - increase TRC_CFG_NMESSAGEBUFFER in trcSnapshotConfig.h";
	default:
		return "pszTraceGetErrorHandles: Invalid objectclass!";
	}
}

/*******************************************************************************
 * prvTraceIsSchedulerSuspended
 *
 * Returns true if the RTOS scheduler currently is disabled, thus preventing any
 * task-switches from occurring. Only called from vTraceStoreISREnd.
 ******************************************************************************/
#if (TRC_CFG_INCLUDE_ISR_TRACING == 1)
unsigned char prvTraceIsSchedulerSuspended(void)
{
    /* Assumed to be available in FreeRTOS. According to the FreeRTOS docs, 
	INCLUDE_xTaskGetSchedulerState or configUSE_TIMERS must be set to 1 in
	FreeRTOSConfig.h for this function to be available. */

	return xTaskGetSchedulerState() == taskSCHEDULER_SUSPENDED;
}
#endif

#endif /* Snapshot mode */

#endif /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/
