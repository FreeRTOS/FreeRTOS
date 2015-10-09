/*******************************************************************************
 * Tracealyzer v3.0.2 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcUser.c
 *
 * The public API of the trace recorder library.
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
#include "trcUser.h"

#if (USE_TRACEALYZER_RECORDER == 1)

#include <string.h>
#include <stdarg.h>
#include <stdint.h>

TRACE_STOP_HOOK vTraceStopHookPtr = (TRACE_STOP_HOOK)0;

extern uint8_t inExcludedTask;
extern int8_t nISRactive;
extern objectHandleType handle_of_last_logged_task;
extern uint32_t dts_min;
extern uint32_t hwtc_count_max_after_tick;
extern uint32_t hwtc_count_sum_after_tick;
extern uint32_t hwtc_count_sum_after_tick_counter;
extern char* traceErrorMessage;

/*** Private functions *******************************************************/
void vTracePrintF_Helper(traceLabel eventLabel, const char* formatStr, va_list vl);

#if (USE_SEPARATE_USER_EVENT_BUFFER == 1)
void vTraceChannelPrintF_Helper(UserEventChannel channelPair, va_list vl);
static void prvTraceUserEventHelper1(UserEventChannel channel, traceLabel eventLabel, traceLabel formatLabel, va_list vl);
static void prvTraceUserEventHelper2(UserEventChannel channel, uint32_t* data, uint32_t noOfSlots);
#endif

static void prvTraceTaskInstanceFinish(int8_t direct);


/*******************************************************************************
 * vTraceInitTraceData
 *
 * Allocates, if necessary, and initializes the recorder data structure, based
 * on the constants in trcConfig.h.
 ******************************************************************************/
void vTraceInitTraceData(void)
{
	prvTraceInitTraceData();
}

/*******************************************************************************
 * vTraceSetRecorderData
 *
 * If custom allocation is used, this function must be called so the recorder
 * library knows where to save the trace data.
 ******************************************************************************/
#if TRACE_DATA_ALLOCATION == TRACE_DATA_ALLOCATION_CUSTOM
void vTraceSetRecorderData(void* pRecorderData)
{
	TRACE_ASSERT(pRecorderData != NULL, "vTraceSetTraceData, pRecorderData == NULL", );
	RecorderDataPtr = pRecorderData;
}
#endif

/*******************************************************************************
 * vTraceSetStopHook
 *
 * Sets a function to be called when the recorder is stopped.
 ******************************************************************************/
void vTraceSetStopHook(TRACE_STOP_HOOK stopHookFunction)
{
	vTraceStopHookPtr = stopHookFunction;
}

/*******************************************************************************
 * vTraceClear
 *
 * Resets the recorder. Only necessary if a restart is desired - this is not
 * needed in the startup initialization.
 ******************************************************************************/
void vTraceClear(void)
{
	TRACE_SR_ALLOC_CRITICAL_SECTION();
	trcCRITICAL_SECTION_BEGIN();

	RecorderDataPtr->absTimeLastEventSecond = 0;

	RecorderDataPtr->absTimeLastEvent = 0;
	RecorderDataPtr->nextFreeIndex = 0;
	RecorderDataPtr->numEvents = 0;
	RecorderDataPtr->bufferIsFull = 0;
	traceErrorMessage = NULL;
	RecorderDataPtr->internalErrorOccured = 0;

	memset(RecorderDataPtr->eventData, 0, RecorderDataPtr->maxEvents * 4);

	handle_of_last_logged_task = 0;
	
	trcCRITICAL_SECTION_END();

}

/*******************************************************************************
 * uiTraceStart
 *
 * Starts the recorder. The recorder will not be started if an error has been
 * indicated using vTraceError, e.g. if any of the Nx constants in trcConfig.h
 * has a too small value (NTASK, NQUEUE, etc).
 *
 * Returns 1 if the recorder was started successfully.
 * Returns 0 if the recorder start was prevented due to a previous internal
 * error. In that case, check vTraceGetLastError to get the error message.
 * Any error message is also presented when opening a trace file.
 ******************************************************************************/

uint32_t uiTraceStart(void)
{
	objectHandleType handle;
	TRACE_SR_ALLOC_CRITICAL_SECTION();

	handle = 0;

	if (RecorderDataPtr == NULL)
	{
		vTraceError("RecorderDataPtr is NULL. Call vTraceInitTraceData() before starting trace.");
		return 0;
	}

	if (traceErrorMessage == NULL)
	{
		trcCRITICAL_SECTION_BEGIN();
		RecorderDataPtr->recorderActive = 1;

		handle = TRACE_GET_TASK_NUMBER(TRACE_GET_CURRENT_TASK());
		if (handle == 0)
		{
			/* This occurs if the scheduler is not yet started.
			This creates a dummy "(startup)" task entry internally in the
			recorder */
			handle = xTraceGetObjectHandle(TRACE_CLASS_TASK);
			vTraceSetObjectName(TRACE_CLASS_TASK, handle, "(startup)");

			vTraceSetPriorityProperty(TRACE_CLASS_TASK, handle, 0);
		}

		vTraceStoreTaskswitch(handle); /* Register the currently running task */
		trcCRITICAL_SECTION_END();
	}

	return RecorderDataPtr->recorderActive;
}

/*******************************************************************************
 * vTraceStart
 *
 * Starts the recorder. The recorder will not be started if an error has been
 * indicated using vTraceError, e.g. if any of the Nx constants in trcConfig.h
 * has a too small value (NTASK, NQUEUE, etc).
 *
 * This function is obsolete, but has been saved for backwards compatibility.
 * We recommend using uiTraceStart instead.
 ******************************************************************************/
void vTraceStart(void)
{
	(void)uiTraceStart();
}

/*******************************************************************************
 * vTraceStop
 *
 * Stops the recorder. The recording can be resumed by calling vTraceStart.
 * This does not reset the recorder. Use vTraceClear if that is desired.
 ******************************************************************************/
void vTraceStop(void)
{
	RecorderDataPtr->recorderActive = 0;

	if (vTraceStopHookPtr != (TRACE_STOP_HOOK)0)
	{
		(*vTraceStopHookPtr)();			/* An application call-back function. */
	}
}

/*******************************************************************************
 * xTraceGetLastError
 *
 * Gives the last error message, if any. NULL if no error message is stored.
 * Any error message is also presented when opening a trace file.
 ******************************************************************************/
char* xTraceGetLastError(void)
{
	return traceErrorMessage;
}

/*******************************************************************************
* vTraceClearError
*
* Removes any previous error message generated by recorder calling vTraceError.
* By calling this function, it may be possible to start/restart the trace
* despite errors in the recorder, but there is no guarantee that the trace
* recorder will work correctly in that case, depending on the type of error.
******************************************************************************/
void vTraceClearError(int resetErrorMessage)
{
	( void ) resetErrorMessage;
	traceErrorMessage = NULL;
	RecorderDataPtr->internalErrorOccured = 0;
}

/*******************************************************************************
 * vTraceGetTraceBuffer
 *
 * Returns a pointer to the recorder data structure. Use this together with
 * uiTraceGetTraceBufferSize if you wish to implement an own store/upload
 * solution, e.g., in case a debugger connection is not available for uploading
 * the data.
 ******************************************************************************/
void* vTraceGetTraceBuffer(void)
{
	return RecorderDataPtr;
}

/*******************************************************************************
 * uiTraceGetTraceBufferSize
 *
 * Gets the size of the recorder data structure. For use together with
 * vTraceGetTraceBuffer if you wish to implement an own store/upload solution,
 * e.g., in case a debugger connection is not available for uploading the data.
 ******************************************************************************/
uint32_t uiTraceGetTraceBufferSize(void)
{
	return sizeof(RecorderDataType);
}

/******************************************************************************
 * prvTraceTaskInstanceFinish.
 *
 * Private common function for the vTraceTaskInstanceFinishXXX functions.
 * 
 *****************************************************************************/
void prvTraceTaskInstanceFinish(int8_t direct)
{
	TaskInstanceStatusEvent* tis;
	uint8_t dts45;

	TRACE_SR_ALLOC_CRITICAL_SECTION();

	trcCRITICAL_SECTION_BEGIN();
	if (RecorderDataPtr->recorderActive && (! inExcludedTask || nISRactive) && handle_of_last_logged_task)
	{
		dts45 = (uint8_t)prvTraceGetDTS(0xFF);
		tis = (TaskInstanceStatusEvent*) xTraceNextFreeEventBufferSlot();
		if (tis != NULL)
		{
			if (direct == 0)
				tis->type = TASK_INSTANCE_FINISHED_NEXT_KSE;
			else
				tis->type = TASK_INSTANCE_FINISHED_DIRECT;

			tis->dts = dts45;
			prvTraceUpdateCounters();
		}
	}
	trcCRITICAL_SECTION_END();
}

/******************************************************************************
 * vTraceTaskInstanceFinish(void)
 *
 * Marks the current task instance as finished on the next kernel call.
 *
 * If that kernel call is blocking, the instance ends after the blocking event
 * and the corresponding return event is then the start of the next instance.
 * If the kernel call is not blocking, the viewer instead splits the current
 * fragment right before the kernel call, which makes this call the first event
 * of the next instance.
 *
 * See also USE_IMPLICIT_IFE_RULES in trcConfig.h
 *
 * Example:
 *
 *		while(1)
 *		{
 *			xQueueReceive(CommandQueue, &command, timeoutDuration);
 *			processCommand(command);
 *          vTraceInstanceFinish();
 *		}
 *
 * Note: This is only supported in Tracealyzer tools v2.7 or later
 *
 *****************************************************************************/
void vTraceTaskInstanceFinish(void)
{
    prvTraceTaskInstanceFinish(0);
}

/******************************************************************************
 * vTraceTaskInstanceFinishDirect(void)
 *
 * Marks the current task instance as finished at this very instant.
 * This makes the viewer to splits the current fragment at this point and begin
 * a new actor instance.
 *
 * See also USE_IMPLICIT_IFE_RULES in trcConfig.h
 *
 * Example:
 *
 *		This example will generate two instances for each loop iteration.
 *		The first instance ends at vTraceInstanceFinishDirect(), while the second
 *      instance ends at the next xQueueReceive call.
 *
 *		while (1)
 *		{
 *          xQueueReceive(CommandQueue, &command, timeoutDuration);
 *			ProcessCommand(command);
 *			vTraceInstanceFinishDirect();
 *			DoSometingElse();
 *          vTraceInstanceFinish();
 *      }
 *
 * Note: This is only supported in Tracealyzer tools v2.7 or later
 *
 *****************************************************************************/
void vTraceTaskInstanceFinishDirect(void)
{
	prvTraceTaskInstanceFinish(1);
}

/*******************************************************************************
 * Interrupt recording functions
 ******************************************************************************/

#if (INCLUDE_ISR_TRACING == 1)

#define MAX_ISR_NESTING 16
static uint8_t isrstack[MAX_ISR_NESTING];
int32_t isPendingContextSwitch = 0;

/*******************************************************************************
 * vTraceSetISRProperties
 *
 * Registers an Interrupt Service Routine in the recorder library, This must be
 * called before using vTraceStoreISRBegin to store ISR events. This is
 * typically called in the startup of the system, before the scheduler is
 * started.
 *
 * Example:
 *	 #define ID_ISR_TIMER1 1		// lowest valid ID is 1
 *	 #define PRIO_OF_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	 ...
 *	 vTraceSetISRProperties(ID_ISR_TIMER1, "ISRTimer1", PRIO_OF_ISR_TIMER1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin(ID_OF_ISR_TIMER1);
 *		 ...
 *		 vTraceStoreISREnd(0);
 *	 }
 *
 * NOTE: To safely record ISRs, you need to make sure that all traced
 * interrupts actually are disabled by trcCRITICAL_SECTION_BEGIN(). However,
 * in some ports this does not disable high priority interrupts!
 * If an ISR calls vTraceStoreISRBegin while the recorder is busy, it will
 * stop the recording and give an error message.
 ******************************************************************************/
void vTraceSetISRProperties(objectHandleType handle, const char* name, char priority)
{
	TRACE_ASSERT(handle <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[TRACE_CLASS_ISR], "vTraceSetISRProperties: Invalid value for handle", );
	TRACE_ASSERT(name != NULL, "vTraceSetISRProperties: name == NULL", );

	vTraceSetObjectName(TRACE_CLASS_ISR, handle, name);
	vTraceSetPriorityProperty(TRACE_CLASS_ISR, handle, priority);
}

#if (SELECTED_PORT == PORT_ARM_CortexM)
/******************************************************************************
 * (Advanced...)
 *
 * ISR_TAILCHAINING_THRESHOLD (For Cortex-M devices only)
 *
 * ARM Cortex-M devices may execute ISRs back-to-back (tail-chained) without
 * resuming the previous context in between. Since this is decided in
 * hardware, we can only detect this indirectly, in the following manner:
 *
 * When entering vTraceStoreISRBegin, we check the number of CPU cycles since
 * the last return of vTraceStoreISREnd. If less or equal to the constant
 * ISR_TAILCHAINING_THRESHOLD it is assumed that the ISRs executed back-to-back
 * (tail-chained). In that case, the previously stored RESUME event
 * (pointed to by ptrLastISRExitEvent) is then deleted to avoid showing a
 * fragment of the previous context in between the ISR events. The delete is
 * made by replacing the event code with a XTS16L event, that serves to keep
 * the differential timestamp from the earlier event.
 *
 * The value of ISR_TAILCHAINING_THRESHOLD depends on the interrupt latency of
 * the processor, on the compiler and on the compiler settings, but should be
 * around 70 cycles. The default value is 66 cycles, which should be correct when
 * using GCC with optimizations disabled (-O0) and Cortex-M3/M4.
 *
 * To measure this value, see MEASURE_ISR_TAILCHAINING_THRESHOLD below.
 *
 * If this value set too low, tail-chained ISRs will incorrectly be shown
 * separated, with a short fragment of the previous task or ISR in between.
 * If this value is set too high, you get the opposite effect - separate ISRs
 * will appear to execute tail-chained and will appear to have higher execution
 * time and response time (maximum ISR_TAILCHAINING_THRESHOLD cycles more).
 *
 * Read the blog post explaining this on our website:
 * http://percepio.com/2014/05/06/sw-based-exc-tracing-arm-cortex-m/
 *
 *****************************************************************************/
#define ISR_TAILCHAINING_THRESHOLD 66

uint8_t* ptrLastISRExitEvent = NULL;
uint32_t DWTCycleCountAtLastISRExit = 0;

/******************************************************************************
 * (Advanced...)
 *
 * MEASURE_ISR_TAILCHAINING_THRESHOLD (For Cortex-M devices only)
 *
 * Allows for calibrating the value of ISR_TAILCHAINING_THRESHOLD (see above).
 *
 * This is intended to measure the minimum number of clock cycles from the end
 * of vTraceStoreISREnd to the beginning of the following vTraceStoreISRBegin.
 * For this purpose, we assume a test setup using the SysTick interrupt, which
 * is available on most Cortex-M devices and typically used by the RTOS kernel.
 * To do the measurement, follow these steps:
 *
 * 1. Make sure MEASURE_ISR_TAILCHAINING_THRESHOLD is enabled (defined as 1)
 *
 * 2. Temporarily replace your SysTick handler with the following:
 *
 *	void xPortSysTickHandler( void )
 *	{
 *		vTraceStoreISRBegin(1);
 *		vTraceStoreISREnd(0);
 *	}
 *
 * 3. To make sure that the ISRs execute back-to-back, increase the OS tick
 *	frequency to a very high level so that the OS tick interrupt execute
 *	continuously with no application tasks in between, e.g. 10 MHz.
 *
 * 4. Put a breakpoint in the highest priority task and make sure it is not
 *	reached. This means that the SysTick handler is executing at maximum rate
 *	and thereby tail-chained, where the interrupt latency is 6 cycles.
 *
 * 5. Let the system run without breakpoints and inspect the value of
 *	threshold_low_watermark. This is the minimum total latency observed.
 *	The hardware latency is 6 clock cycles due to the tail-chaining, so the
 *	software latency (SL) is then SL = threshold_low_watermark - 6.
 *
 * The threshold value ISR_TAILCHAINING_THRESHOLD should be SL + 2 * HL, where
 * HL is the normal hardware interrupt latency, i.e., the number of CPU
 * cycles to enter or exit the exception handler for an exception in task
 * context. The HL value is 12-16 depending on core, as shown below.
 *
 * Values for ISR_TAILCHAINING_THRESHOLD, assuming SL = 42
 *	Cortex-M3 and M4 (HL = 12):	66 cycles
 *	Cortex-M0 (HL = 16):		74 cycles
 *	Cortex-M0+ (HL = 15):		72 cycles
 *
 * If the ISR_TAILCHAINING_THRESHOLD value is set too low, some tail-chained
 * ISRs be shown separated, with a short fragment of the previous context
 * in between. On the other hand, if the value is set too high, ISRs that 
 * actually are separated may appear to execute back-to-back (tail-chained).
 *
 * Read the blog post explaining this on our website:
 * http://percepio.com/2014/05/06/sw-based-exc-tracing-arm-cortex-m/
 *
 *****************************************************************************/
#define MEASURE_ISR_TAILCHAINING_THRESHOLD 1

#if (MEASURE_ISR_TAILCHAINING_THRESHOLD == 1)
volatile uint32_t threshold_low_watermark = 2000000000;
#endif

#endif

/*******************************************************************************
 * vTraceStoreISRBegin
 *
 * Registers the beginning of an Interrupt Service Routine.
 *
 * Example:
 *	 #define ID_ISR_TIMER1 1		// lowest valid ID is 1
 *	 #define PRIO_OF_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	 ...
 *	 vTraceSetISRProperties(ID_ISR_TIMER1, "ISRTimer1", PRIO_OF_ISR_TIMER1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin(ID_OF_ISR_TIMER1);
 *		 ...
 *		 vTraceStoreISREnd(0);
 *	 }
 *
 ******************************************************************************/
void vTraceStoreISRBegin(objectHandleType handle)
{
	uint16_t dts4;
	#if (SELECTED_PORT == PORT_ARM_CortexM)
	uint32_t CPUCyclesSinceLastISRExit = REG_DWT_CYCCNT - DWTCycleCountAtLastISRExit;
	#endif
	TSEvent* ts;
	TRACE_SR_ALLOC_CRITICAL_SECTION();

	ts = NULL;

#if (SELECTED_PORT == PORT_ARM_CortexM)
	if (DWTCycleCountAtLastISRExit > 0)
	{
		#if (MEASURE_ISR_TAILCHAINING_THRESHOLD == 1)
		/* Allows for verifying the value of ISR_TAILCHAINING_THRESHOLD */
		if (CPUCyclesSinceLastISRExit < threshold_low_watermark)
		{
			threshold_low_watermark = CPUCyclesSinceLastISRExit;
		}
		#endif

		if (CPUCyclesSinceLastISRExit <= ISR_TAILCHAINING_THRESHOLD)
		{
			/* This is judged to be a case of ISR tail-chaining since the
			number of cycles since the last vTraceStoreISREnd is shorter or equal to
			the threshold (ISR_TAILCHAINING_THRESHOLD) */

			if (ptrLastISRExitEvent != NULL)
			{
				/* Overwrite the last ISR exit event with a "neutral" event that only
					accounts for the time passed */
				*ptrLastISRExitEvent = XTS16L;
			}
		}

	}
#endif

	if (recorder_busy)
	{
	 vTraceError("Illegal call to vTraceStoreISRBegin, recorder busy!");
	 return;
	}
	trcCRITICAL_SECTION_BEGIN();
	
	if (nISRactive == 0)
		isPendingContextSwitch = 0;	/* We are at the start of a possible ISR chain. No context switches should have been triggered now. */
	
	if (RecorderDataPtr->recorderActive && handle_of_last_logged_task)
	{

		TRACE_ASSERT(handle <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[TRACE_CLASS_ISR], "vTraceStoreISRBegin: Invalid value for handle", );
		
		dts4 = (uint16_t)prvTraceGetDTS(0xFFFF);

		if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
		{
			if (nISRactive < MAX_ISR_NESTING)
			{
				uint8_t hnd8 = prvTraceGet8BitHandle(handle);
				isrstack[nISRactive] = handle;
				nISRactive++;
				ts = (TSEvent*)xTraceNextFreeEventBufferSlot();
				if (ts != NULL)
				{
					ts->type = TS_ISR_BEGIN;
					ts->dts = dts4;
					ts->objHandle = hnd8;
					prvTraceUpdateCounters();
				}
			}
			else
			{
				/* This should not occur unless something is very wrong */
				vTraceError("Too many nested interrupts!");
			}
		}
	}
	trcCRITICAL_SECTION_END();
}

/*******************************************************************************
 * vTraceStoreISREnd
 *
 * Registers the end of an Interrupt Service Routine.
 *
 * The parameter pendingISR indicates if the interrupt has requested a
 * task-switch (= 1) or if the interrupt returns to the earlier context (= 0)
 *
 * Example:
 *
 *	 #define ID_ISR_TIMER1 1		// lowest valid ID is 1
 *	 #define PRIO_OF_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	 ...
 *	 vTraceSetISRProperties(ID_ISR_TIMER1, "ISRTimer1", PRIO_OF_ISR_TIMER1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin(ID_OF_ISR_TIMER1);
 *		 ...
 *		 vTraceStoreISREnd(0);
 *	 }
 *
 ******************************************************************************/
void vTraceStoreISREnd(int pendingISR)
{
	TSEvent* ts;
	uint16_t dts5;
	uint8_t hnd8 = 0, type = 0;
	
	TRACE_SR_ALLOC_CRITICAL_SECTION();

	if (! RecorderDataPtr->recorderActive ||  ! handle_of_last_logged_task)
	{
		return;
	}

	if (recorder_busy)
	{
		vTraceError("Illegal call to vTraceStoreISREnd, recorder busy!");
		return;
	}
	
	if (nISRactive == 0)
	{
		vTraceError("Unmatched call to vTraceStoreISREnd (nISRactive == 0, expected > 0)");
		return;
	}

	trcCRITICAL_SECTION_BEGIN();
	isPendingContextSwitch |= pendingISR;	/* Is there a pending context switch right now? */
	nISRactive--;
	if (nISRactive > 0)
	{
		/* Return to another isr */
		type = TS_ISR_RESUME;
		hnd8 = prvTraceGet8BitHandle(isrstack[nISRactive - 1]); /* isrstack[nISRactive] is the handle of the ISR we're currently exiting. isrstack[nISRactive - 1] is the handle of the ISR that was executing previously. */
	}
	else if (isPendingContextSwitch == 0)
	{
		/* No context switch has been triggered by any ISR in the chain. Return to task */
		type = TS_TASK_RESUME;
		hnd8 = prvTraceGet8BitHandle(handle_of_last_logged_task);
	}
	else
	{
		/* Context switch has been triggered by some ISR. We expect a proper context switch event shortly so we do nothing. */
	}

	if (type != 0)
	{
		dts5 = (uint16_t)prvTraceGetDTS(0xFFFF);
		ts = (TSEvent*)xTraceNextFreeEventBufferSlot();
		if (ts != NULL)
		{
			ts->type = type;
			ts->objHandle = hnd8;
			ts->dts = dts5;
			prvTraceUpdateCounters();
		}

		#if (SELECTED_PORT == PORT_ARM_CortexM)
		/* Remember the last ISR exit event, as the event needs to be modified in case of a following ISR entry (if tail-chained ISRs) */
		ptrLastISRExitEvent = (uint8_t*)ts;
		#endif		
	}

	#if (SELECTED_PORT == PORT_ARM_CortexM)
	DWTCycleCountAtLastISRExit = REG_DWT_CYCCNT;
	#endif

	trcCRITICAL_SECTION_END();
}

#else

/* ISR tracing is turned off */
void vTraceIncreaseISRActive(void)
{
	if (RecorderDataPtr->recorderActive && handle_of_last_logged_task)
		nISRactive++;
}

void vTraceDecreaseISRActive(void)
{
	if (RecorderDataPtr->recorderActive && handle_of_last_logged_task)
		nISRactive--;
}
#endif


/********************************************************************************/
/* User Event functions															*/
/********************************************************************************/

#if (INCLUDE_USER_EVENTS == 1)

#define MAX_ARG_SIZE (4+32)
/*** Locally used in vTracePrintF ***/
static uint8_t writeInt8(void * buffer, uint8_t i, uint8_t value)
{
	TRACE_ASSERT(buffer != NULL, "writeInt8: buffer == NULL", 0);

	if (i >= MAX_ARG_SIZE)
	{
		return 255;
	}

	((uint8_t*)buffer)[i] = value;

	if (i + 1 > MAX_ARG_SIZE)
	{
		return 255;
	}

	return i + 1;
}

/*** Locally used in vTracePrintF ***/
static uint8_t writeInt16(void * buffer, uint8_t i, uint16_t value)
{
	TRACE_ASSERT(buffer != NULL, "writeInt16: buffer == NULL", 0);

	/* Align to multiple of 2 */
	while ((i % 2) != 0)
	{
		if (i >= MAX_ARG_SIZE)
		{
			return 255;
		}

		((uint8_t*)buffer)[i] = 0;
		i++;
	}

	if (i + 2 > MAX_ARG_SIZE)
	{
		return 255;
	}

	((uint16_t*)buffer)[i/2] = value;

	return i + 2;
}

/*** Locally used in vTracePrintF ***/
static uint8_t writeInt32(void * buffer, uint8_t i, uint32_t value)
{
	TRACE_ASSERT(buffer != NULL, "writeInt32: buffer == NULL", 0);

	/* A 32 bit value should begin at an even 4-byte address */
	while ((i % 4) != 0)
	{
		if (i >= MAX_ARG_SIZE)
		{
			return 255;
		}

		((uint8_t*)buffer)[i] = 0;
		i++;
	}

	if (i + 4 > MAX_ARG_SIZE)
	{
		return 255;
	}

	((uint32_t*)buffer)[i/4] = value;

	return i + 4;
}

#if (INCLUDE_FLOAT_SUPPORT)

/*** Locally used in vTracePrintF ***/
static uint8_t writeFloat(void * buffer, uint8_t i, float value)
{
	TRACE_ASSERT(buffer != NULL, "writeFloat: buffer == NULL", 0);

	/* A 32 bit value should begin at an even 4-byte address */
	while ((i % 4) != 0)
	{
		if (i >= MAX_ARG_SIZE)
		{
			return 255;
		}

		((uint8_t*)buffer)[i] = 0;
		i++;
	}

	if (i + 4 > MAX_ARG_SIZE)
	{
		return 255;
	}

	((float*)buffer)[i/4] = value;

	return i + 4;
}

/*** Locally used in vTracePrintF ***/
static uint8_t writeDouble(void * buffer, uint8_t i, double value)
{
	uint32_t * dest;
	uint32_t * src = (uint32_t*)&value;

	TRACE_ASSERT(buffer != NULL, "writeDouble: buffer == NULL", 0);

	/* The double is written as two 32 bit values, and should begin at an even
	4-byte address (to avoid having to align with 8 byte) */
	while (i % 4 != 0)
	{
		if (i >= MAX_ARG_SIZE)
		{
			return 255;
		}

		((uint8_t*)buffer)[i] = 0;
		i++;
	}

	if (i + 8 > MAX_ARG_SIZE)
	{
		return 255;
	}

	dest = &(((uint32_t *)buffer)[i/4]);

	dest[0] = src[0];
	dest[1] = src[1];

	return i + 8;
}

#endif

/*******************************************************************************
 * prvTraceUserEventFormat
 *
 * Parses the format string and stores the arguments in the buffer.
 ******************************************************************************/
static uint8_t prvTraceUserEventFormat(const char* formatStr, va_list vl, uint8_t* buffer, uint8_t byteOffset)
{
	uint16_t formatStrIndex = 0;
	uint8_t argCounter = 0;
	uint8_t i = byteOffset;

	while (formatStr[formatStrIndex] != '\0')
	{
		if (formatStr[formatStrIndex] == '%')
		{
			argCounter++;

			if (argCounter > 15)
			{
				vTraceError("vTracePrintF - Too many arguments, max 15 allowed!");
				return 0;
			}

			/*******************************************************************************
			* These below code writes raw data (primitive datatypes) in the event buffer,
			* instead of the normal event structs (where byte 0 is event type).
			* These data entries must never be interpreted as real event data, as the type
			* field would be misleading since used for payload data.
			*
			* The correctness of this encoding depends on two mechanisms:
			*
			* 1. An initial USER_EVENT, which type code tells the number of 32-bit data
			* entires that follows. (code - USER_EVENT = number of data entries).
			* Note that a data entry corresponds to the slots that normally corresponds to
			* one (1) event, i.e., 32 bits. vTracePrintF may encode several pieces of data
			* in one data entry, e.g., two 16-bit values or four 8-bit values, one 16-bit
			* value followed by two 8-bit values, etc.
			*
			* 2. A two-phase commit procedure, where the USER_EVENT and data entries are
			* written to a local buffer at first, and when all checks are OK then copied to
			* the main event buffer using a fast memcpy. The event code is finalized as the
			* very last step. Before that step, the event code indicates an unfinished
			* event, which causes it to be ignored and stop the loading of the file (since
			* an unfinished event is the last event in the trace).
			*******************************************************************************/
			formatStrIndex++;

			while ((formatStr[formatStrIndex] >= '0' && formatStr[formatStrIndex] <= '9') || formatStr[formatStrIndex] == '#' || formatStr[formatStrIndex] == '.')
				formatStrIndex++;

			if (formatStr[formatStrIndex] != '\0')
			{
				switch (formatStr[formatStrIndex])
				{
					case 'd':	i = writeInt32(	buffer,
												i,
												(uint32_t)va_arg(vl, uint32_t));
								break;
					case 'x':
					case 'X':
					case 'u':	i = writeInt32(	buffer,
												i,
												(uint32_t)va_arg(vl, uint32_t));
								break;
					case 's':	i = writeInt16(	buffer,
												i,
												(uint16_t)xTraceOpenLabel((char*)va_arg(vl, char*)));
								break;

#if (INCLUDE_FLOAT_SUPPORT)
					/* Yes, "double" as type also in the float
					case. This since "float" is promoted into "double"
					by the va_arg stuff. */
					case 'f':	i = writeFloat(	buffer,
												i,
												(float)va_arg(vl, double));
								break;
#else
					/* No support for floats, but attempt to store a float user event
					avoid a possible crash due to float reference. Instead store the
					data on uint_32 format (will not be displayed anyway). This is just
					to keep va_arg and i consistent. */

					case 'f':	i = writeInt32(	buffer,
												i,
												(uint32_t)va_arg(vl, double));
								break;
#endif
					case 'l':
								formatStrIndex++;
								switch (formatStr[formatStrIndex])
								{
#if (INCLUDE_FLOAT_SUPPORT)
									case 'f':	i = writeDouble(buffer,
																i,
																(double)va_arg(vl, double));
												break;
#else
									/* No support for floats, but attempt to store a float user event
									avoid a possible crash due to float reference. Instead store the
									data on uint_32 format (will not be displayed anyway). This is just
									to keep va_arg and i consistent. */
									case 'f':	i = writeInt32(	buffer, /* In this case, the value will not be shown anyway */
																i,
																(uint32_t)va_arg(vl, double));

												i = writeInt32(	buffer, /* Do it twice, to write in total 8 bytes */
																i,
																(uint32_t)va_arg(vl, double));
										break;
#endif

								}
								break;
					case 'h':
								formatStrIndex++;
								switch (formatStr[formatStrIndex])
								{
									case 'd':	i = writeInt16(	buffer,
																i,
																(uint16_t)va_arg(vl, uint32_t));
												break;
									case 'u':	i = writeInt16(	buffer,
																i,
																(uint16_t)va_arg(vl, uint32_t));
												break;
								}
								break;
					case 'b':
								formatStrIndex++;
								switch (formatStr[formatStrIndex])
								{
									case 'd':	i = writeInt8(	buffer,
																i,
																(uint8_t)va_arg(vl, uint32_t));
												break;

									case 'u':	i = writeInt8(	buffer,
																i,
																(uint8_t)va_arg(vl, uint32_t));
												break;
								}
								break;
				}
			}
			else
				break;
		}
		formatStrIndex++;
		if (i == 255)
		{
			vTraceError("vTracePrintF - Too large arguments, max 32 byte allowed!");
			return 0;
		}
	}
	return (i+3)/4;
}

#if (USE_SEPARATE_USER_EVENT_BUFFER == 1)

/*******************************************************************************
 * prvTraceClearChannelBuffer
 *
 * Clears a number of items in the channel buffer, starting from nextSlotToWrite.
 ******************************************************************************/
static void prvTraceClearChannelBuffer(uint32_t count)
{
	uint32_t slots;

	TRACE_ASSERT(USER_EVENT_BUFFER_SIZE >= count,
		"prvTraceClearChannelBuffer: USER_EVENT_BUFFER_SIZE is too small to handle this event.", );

	/* Check if we're close to the end of the buffer */
	if (RecorderDataPtr->userEventBuffer.nextSlotToWrite + count > USER_EVENT_BUFFER_SIZE)
	{
		slots = USER_EVENT_BUFFER_SIZE - RecorderDataPtr->userEventBuffer.nextSlotToWrite; /* Number of slots before end of buffer */
		(void)memset(&RecorderDataPtr->userEventBuffer.channelBuffer[RecorderDataPtr->userEventBuffer.nextSlotToWrite], 0, slots);
		(void)memset(&RecorderDataPtr->userEventBuffer.channelBuffer[0], 0, (count - slots));
	}
	else
		(void)memset(&RecorderDataPtr->userEventBuffer.channelBuffer[RecorderDataPtr->userEventBuffer.nextSlotToWrite], 0, count);
}

/*******************************************************************************
 * prvTraceCopyToDataBuffer
 *
 * Copies a number of items to the data buffer, starting from nextSlotToWrite.
 ******************************************************************************/
static void prvTraceCopyToDataBuffer(uint32_t* data, uint32_t count)
{
	TRACE_ASSERT(data != NULL,
		"prvTraceCopyToDataBuffer: data == NULL.", );
	TRACE_ASSERT(count <= USER_EVENT_BUFFER_SIZE,
		"prvTraceCopyToDataBuffer: USER_EVENT_BUFFER_SIZE is too small to handle this event.", );

	uint32_t slots;
	/* Check if we're close to the end of the buffer */
	if (RecorderDataPtr->userEventBuffer.nextSlotToWrite + count > USER_EVENT_BUFFER_SIZE)
	{
		slots = USER_EVENT_BUFFER_SIZE - RecorderDataPtr->userEventBuffer.nextSlotToWrite; /* Number of slots before end of buffer */
		(void)memcpy(&RecorderDataPtr->userEventBuffer.dataBuffer[RecorderDataPtr->userEventBuffer.nextSlotToWrite * 4], data, slots * 4);
		(void)memcpy(&RecorderDataPtr->userEventBuffer.dataBuffer[0], data + slots, (count - slots) * 4);
	}
	else
	{
		(void)memcpy(&RecorderDataPtr->userEventBuffer.dataBuffer[RecorderDataPtr->userEventBuffer.nextSlotToWrite * 4], data, count * 4);
	}
}

/*******************************************************************************
 * prvTraceUserEventHelper1
 *
 * Calls on prvTraceUserEventFormat() to do the actual formatting, then goes on
 * to the next helper function.
 ******************************************************************************/
static void prvTraceUserEventHelper1(UserEventChannel channel, traceLabel eventLabel, traceLabel formatLabel, va_list vl)
{
	uint32_t data[(3 + MAX_ARG_SIZE) / 4];
	uint8_t byteOffset = 4; /* Need room for timestamp */
	uint8_t noOfSlots;

	if (channel == 0)
	{
		/* We are dealing with an unknown channel format pair */
		byteOffset += 4; /* Also need room for channel and format */
		((uint16_t*)data)[2] = eventLabel;
		((uint16_t*)data)[3] = formatLabel;
	}

	noOfSlots = prvTraceUserEventFormat((char*)&(RecorderDataPtr->SymbolTable.symbytes[formatLabel+4]), vl, (uint8_t*)data, byteOffset);

	prvTraceUserEventHelper2(channel, data, noOfSlots);
}

/*******************************************************************************
 * prvTraceUserEventHelper2
 *
 * This function simply copies the data buffer to the actual user event buffer.
 ******************************************************************************/
static void prvTraceUserEventHelper2(UserEventChannel channel, uint32_t* data, uint32_t noOfSlots)
{
	static uint32_t old_timestamp = 0;
	uint32_t old_nextSlotToWrite = 0;

	TRACE_ASSERT(USER_EVENT_BUFFER_SIZE >= noOfSlots, "vTracePrintF: USER_EVENT_BUFFER_SIZE is too small to handle this event.", );

	trcCRITICAL_SECTION_BEGIN();
	/* Store the timestamp */
	vTracePortGetTimeStamp(data);

	if (*data < old_timestamp)
	{
		RecorderDataPtr->userEventBuffer.wraparoundCounter++;
	}

	old_timestamp = *data;

	/* Start by erasing any information in the channel buffer */
	prvTraceClearChannelBuffer(noOfSlots);

	prvTraceCopyToDataBuffer(data, noOfSlots); /* Will wrap around the data if necessary */

	old_nextSlotToWrite = RecorderDataPtr->userEventBuffer.nextSlotToWrite; /* Save the index that we want to write the channel data at when we're done */
	RecorderDataPtr->userEventBuffer.nextSlotToWrite = (RecorderDataPtr->userEventBuffer.nextSlotToWrite + noOfSlots) % USER_EVENT_BUFFER_SIZE; /* Make sure we never end up outside the buffer */

	/* Write to the channel buffer to indicate that this user event is ready to be used */
	if (channel != 0)
	{
		RecorderDataPtr->userEventBuffer.channelBuffer[old_nextSlotToWrite] = channel;
	}
	else
	{
		/* 0xFF indicates that this is not a normal channel id */
		RecorderDataPtr->userEventBuffer.channelBuffer[old_nextSlotToWrite] = (UserEventChannel)0xFF;
	}
	trcCRITICAL_SECTION_END();
}

/*******************************************************************************
 * xTraceRegisterChannelFormat
 *
 * Attempts to create a pair of the channel and format string.
 *
 * Note: This is only available if USE_SEPARATE_USER_EVENT_BUFFER is enabled in
 * trcConfig.h
 ******************************************************************************/
UserEventChannel xTraceRegisterChannelFormat(traceLabel channel, traceLabel formatStr)
{
	uint8_t i;
	UserEventChannel retVal = 0;

	TRACE_ASSERT(formatStr != 0, "vTraceRegisterChannelFormat: formatStr == 0", (UserEventChannel)0);

	trcCRITICAL_SECTION_BEGIN();
	for (i = 1; i <= CHANNEL_FORMAT_PAIRS; i++) /* Size of the channels buffer is CHANNEL_FORMAT_PAIRS + 1. Index 0 is unused. */
	{
		if(RecorderDataPtr->userEventBuffer.channels[i].name == 0 && RecorderDataPtr->userEventBuffer.channels[i].defaultFormat == 0)
		{
			/* Found empty slot */
			RecorderDataPtr->userEventBuffer.channels[i].name = channel;
			RecorderDataPtr->userEventBuffer.channels[i].defaultFormat = formatStr;
			retVal = (UserEventChannel)i;
			break;
		}

		if (RecorderDataPtr->userEventBuffer.channels[i].name == channel && RecorderDataPtr->userEventBuffer.channels[i].defaultFormat == formatStr)
		{
			/* Found a match */
			retVal = (UserEventChannel)i;
			break;
		}
	}
	trcCRITICAL_SECTION_END();
	return retVal;
}

/******************************************************************************
 * vTraceChannelPrintF
 *
 * Slightly faster version of vTracePrintF() due to no lookups.
 *
 * Note: This is only available if USE_SEPARATE_USER_EVENT_BUFFER is enabled in
 * trcConfig.h
 *
 ******************************************************************************/
void vTraceChannelPrintF(UserEventChannel channelPair, ...)
{
#if (TRACE_SCHEDULING_ONLY == 0)
	va_list vl;

	va_start(vl, channelPair);
	vTraceChannelPrintF_Helper(channelPair, vl);
	va_end(vl);
#endif /* TRACE_SCHEDULING_ONLY */
}

void vTraceChannelPrintF_Helper(UserEventChannel channelPair, va_list vl)
{
	traceLabel channel;
	traceLabel formatStr;

	TRACE_ASSERT(channelPair != 0, "vTraceChannelPrintF: channelPair == 0", );
	TRACE_ASSERT(channelPair <= CHANNEL_FORMAT_PAIRS, "vTraceChannelPrintF: ", );

	channel = RecorderDataPtr->userEventBuffer.channels[channelPair].name;
	formatStr = RecorderDataPtr->userEventBuffer.channels[channelPair].defaultFormat;

	prvTraceUserEventHelper1(channelPair, channel, formatStr, vl);
}

/******************************************************************************
 * vTraceChannelUserEvent
 *
 * Slightly faster version of vTraceUserEvent() due to no lookups.
 ******************************************************************************/
void vTraceChannelUserEvent(UserEventChannel channelPair)
{
#if (TRACE_SCHEDULING_ONLY == 0)
	uint32_t data[(3 + MAX_ARG_SIZE) / 4];

	TRACE_ASSERT(channelPair != 0, "vTraceChannelPrintF: channelPair == 0", );
	TRACE_ASSERT(channelPair <= CHANNEL_FORMAT_PAIRS, "vTraceChannelPrintF: ", );

	prvTraceUserEventHelper2(channelPair, data, 1); /* Only need one slot for timestamp */
#endif /* TRACE_SCHEDULING_ONLY */
}
#endif /* USE_SEPARATE_USER_EVENT_BUFFER == 1 */

/******************************************************************************
 * vTracePrintF
 *
 * Advanced user events (Professional Edition only)
 *
 * Generates User Event with formatted text and data, similar to a "printf".
 * It is very fast compared to a normal "printf" since this function only
 * stores the arguments. The actual formatting is done
 * on the host PC when the trace is displayed in the viewer tool.
 *
 * User Event labels are created using xTraceOpenLabel.
 * Example:
 *
 *	 traceLabel adc_uechannel = xTraceOpenLabel("ADC User Events");
 *	 ...
 *	 vTracePrint(adc_uechannel,
 *				 "ADC channel %d: %lf volts",
 *				 ch, (double)adc_reading/(double)scale);
 *
 * This can be combined into one line, if desired, but this is slower:
 *
 *	 vTracePrint(xTraceOpenLabel("ADC User Events"),
 *				 "ADC channel %d: %lf volts",
 *				 ch, (double)adc_reading/(double)scale);
 *
 * Calling xTraceOpenLabel multiple times will not create duplicate entries, but
 * it is of course faster to just do it once, and then keep the handle for later
 * use. If you don�t have any data arguments, only a text label/string, it is
 * better to use vTraceUserEvent - it is faster.
 *
 * Format specifiers supported:
 * %d - 32 bit signed integer
 * %u - 32 bit unsigned integer
 * %f - 32 bit float
 * %s - string (is copied to the recorder symbol table)
 * %hd - 16 bit signed integer
 * %hu - 16 bit unsigned integer
 * %bd - 8 bit signed integer
 * %bu - 8 bit unsigned integer
 * %lf - double-precision float (Note! See below...)
 *
 * Up to 15 data arguments are allowed, with a total size of maximum 32 byte.
 * In case this is exceeded, the user event is changed into an error message.
 *
 * The data is stored in trace buffer, and is packed to allow storing multiple
 * smaller data entries in the same 4-byte record, e.g., four 8-bit values.
 * A string requires two bytes, as the symbol table is limited to 64K. Storing
 * a double (%lf) uses two records, so this is quite costly. Use float (%f)
 * unless the higher precision is really necessary.
 *
 * Note that the double-precision float (%lf) assumes a 64 bit double
 * representation. This does not seem to be the case on e.g. PIC24 and PIC32.
 * Before using a %lf argument on a 16-bit MCU, please verify that
 * "sizeof(double)" actually gives 8 as expected. If not, use %f instead.
 ******************************************************************************/

void vTracePrintF(traceLabel eventLabel, const char* formatStr, ...)
{
#if (TRACE_SCHEDULING_ONLY == 0)
	va_list vl;

	va_start(vl, formatStr);
	vTracePrintF_Helper(eventLabel, formatStr, vl);
	va_end(vl);
#endif /* TRACE_SCHEDULING_ONLY */
}

void vTracePrintF_Helper(traceLabel eventLabel, const char* formatStr, va_list vl)
{
#if (USE_SEPARATE_USER_EVENT_BUFFER == 0)
	uint32_t noOfSlots;
	UserEvent* ue1;
	uint32_t tempDataBuffer[(3 + MAX_ARG_SIZE) / 4];
	TRACE_SR_ALLOC_CRITICAL_SECTION();

	/**************************************************************************
	* The array tempDataBuffer is a local buffer used in a two-phase commit of
	* the event data, since a vTracePrintF may span over multiple slots in the
	* buffer.
	* This buffer can be made larger, of course, but remember the risk for
	* stack overflow. Note: This should be a LOCAL buffer, must not be made
	* global. That would cause data corruption when two calls to vTracePrintF
	* from different tasks overlaps (interrupts are only disabled in a small
	* part of this function, otherwise enabled)
	***************************************************************************/

	TRACE_ASSERT(formatStr != NULL, "vTracePrintF: formatStr == NULL", );

	trcCRITICAL_SECTION_BEGIN();

	if (RecorderDataPtr->recorderActive && (! inExcludedTask || nISRactive) && handle_of_last_logged_task)
	{
		/* First, write the "primary" user event entry in the local buffer, but
		let the event type be "EVENT_BEING_WRITTEN" for now...*/

		ue1 = (UserEvent*)(&tempDataBuffer[0]);

		ue1->type = EVENT_BEING_WRITTEN;	 /* Update this as the last step */

		noOfSlots = prvTraceUserEventFormat(formatStr, vl, (uint8_t*)tempDataBuffer, 4);

		/* Store the format string, with a reference to the channel symbol */
		ue1->payload = prvTraceOpenSymbol(formatStr, eventLabel);

		ue1->dts = (uint8_t)prvTraceGetDTS(0xFF);

		 /* prvTraceGetDTS might stop the recorder in some cases... */
		if (RecorderDataPtr->recorderActive)
		{

			/* If the data does not fit in the remaining main buffer, wrap around to
			0 if allowed, otherwise stop the recorder and quit). */
			if (RecorderDataPtr->nextFreeIndex + noOfSlots > RecorderDataPtr->maxEvents)
			{
				#if (TRACE_RECORDER_STORE_MODE == TRACE_STORE_MODE_RING_BUFFER)
				(void)memset(& RecorderDataPtr->eventData[RecorderDataPtr->nextFreeIndex * 4],
						0,
						(RecorderDataPtr->maxEvents - RecorderDataPtr->nextFreeIndex)*4);
				RecorderDataPtr->nextFreeIndex = 0;
				RecorderDataPtr->bufferIsFull = 1;
				#else

				/* Stop recorder, since the event data will not fit in the
				buffer and not circular buffer in this case... */
				vTraceStop();
				#endif
			}

			/* Check if recorder has been stopped (i.e., vTraceStop above) */
			if (RecorderDataPtr->recorderActive)
			{
				/* Check that the buffer to be overwritten does not contain any user
				events that would be partially overwritten. If so, they must be "killed"
				by replacing the user event and following data with NULL events (i.e.,
				using a memset to zero).*/
				#if (TRACE_RECORDER_STORE_MODE == TRACE_STORE_MODE_RING_BUFFER)
				prvCheckDataToBeOverwrittenForMultiEntryEvents((uint8_t)noOfSlots);
				#endif
				/* Copy the local buffer to the main buffer */
				(void)memcpy(& RecorderDataPtr->eventData[RecorderDataPtr->nextFreeIndex * 4],
						tempDataBuffer,
						noOfSlots * 4);

				/* Update the event type, i.e., number of data entries following the
				main USER_EVENT entry (Note: important that this is after the memcpy,
				but within the critical section!)*/
				RecorderDataPtr->eventData[RecorderDataPtr->nextFreeIndex * 4] =
				 (uint8_t) ( USER_EVENT + noOfSlots - 1 );

				/* Update the main buffer event index (already checked that it fits in
				the buffer, so no need to check for wrapping)*/

				RecorderDataPtr->nextFreeIndex += noOfSlots;
				RecorderDataPtr->numEvents += noOfSlots;

				if (RecorderDataPtr->nextFreeIndex >= EVENT_BUFFER_SIZE)
				{
					#if (TRACE_RECORDER_STORE_MODE == TRACE_STORE_MODE_RING_BUFFER)
					/* We have reached the end, but this is a ring buffer. Start from the beginning again. */
					RecorderDataPtr->bufferIsFull = 1;
					RecorderDataPtr->nextFreeIndex = 0;
					#else
					/* We have reached the end so we stop. */
					vTraceStop();
					#endif
				}
			}

			#if (TRACE_RECORDER_STORE_MODE == TRACE_STORE_MODE_RING_BUFFER)
			/* Make sure the next entry is cleared correctly */
			prvCheckDataToBeOverwrittenForMultiEntryEvents(1);
			#endif

		}
	}
	trcCRITICAL_SECTION_END();

#elif (USE_SEPARATE_USER_EVENT_BUFFER == 1)
	/* Use the separate user event buffer */
	traceLabel formatLabel;
	UserEventChannel channel;

	if (RecorderDataPtr->recorderActive && (! inExcludedTask || nISRactive) && handle_of_last_logged_task)
	{
		formatLabel = xTraceOpenLabel(formatStr);

		channel = xTraceRegisterChannelFormat(eventLabel, formatLabel);

		prvTraceUserEventHelper1(channel, eventLabel, formatLabel, vl);
	}
#endif
}

/******************************************************************************
 * vTraceUserEvent
 *
 * Basic user event (Standard and Professional Edition only)
 *
 * Generates a User Event with a text label. The label is created/looked up
 * in the symbol table using xTraceOpenLabel.
 ******************************************************************************/
void vTraceUserEvent(traceLabel eventLabel)
{
#if (TRACE_SCHEDULING_ONLY == 0)
#if (USE_SEPARATE_USER_EVENT_BUFFER == 0)
	UserEvent* ue;
	uint8_t dts1;
	TRACE_SR_ALLOC_CRITICAL_SECTION();

	TRACE_ASSERT(eventLabel > 0, "vTraceUserEvent: Invalid value for eventLabel", );

	trcCRITICAL_SECTION_BEGIN();
	if (RecorderDataPtr->recorderActive && (! inExcludedTask || nISRactive) && handle_of_last_logged_task)
	{
		dts1 = (uint8_t)prvTraceGetDTS(0xFF);
		ue = (UserEvent*) xTraceNextFreeEventBufferSlot();
		if (ue != NULL)
		{
			ue->dts = dts1;
			ue->type = USER_EVENT;
			ue->payload = eventLabel;
			prvTraceUpdateCounters();
		}
	}
	trcCRITICAL_SECTION_END();

#elif (USE_SEPARATE_USER_EVENT_BUFFER == 1)
	UserEventChannel channel;
	uint32_t noOfSlots = 1;
	uint32_t tempDataBuffer[(3 + MAX_ARG_SIZE) / 4];
	if (RecorderDataPtr->recorderActive && (! inExcludedTask || nISRactive) && handle_of_last_logged_task)
	{
		channel = xTraceRegisterChannelFormat(0, eventLabel);

		if (channel == 0)
		{
			/* We are dealing with an unknown channel format pair */
			noOfSlots++; /* Also need room for channel and format */
			((uint16_t*)tempDataBuffer)[2] = 0;
			((uint16_t*)tempDataBuffer)[3] = eventLabel;
		}

		prvTraceUserEventHelper2(channel, tempDataBuffer, noOfSlots);
	}
#endif
#endif /* TRACE_SCHEDULING_ONLY */
}

/*******************************************************************************
 * xTraceOpenLabel
 *
 * Creates user event labels for user event channels or for individual events.
 * User events can be used to log application events and data for display in
 * the visualization tool. A user event is identified by a label, i.e., a string,
 * which is stored in the recorder's symbol table.
 * When logging a user event, a numeric handle (reference) to this string is
 * used to identify the event. This is obtained by calling
 *
 *	 xTraceOpenLabel()
 *
 * which adds the string to the symbol table (if not already present)
 * and returns the corresponding handle.
 *
 * This can be used in two ways:
 *
 * 1. The handle is looked up every time, when storing the user event.
 *
 * Example:
 *	 vTraceUserEvent(xTraceOpenLabel("MyUserEvent"));
 *
 * 2. The label is registered just once, with the handle stored in an
 * application variable - much like using a file handle.
 *
 * Example:
 *	 myEventHandle = xTraceOpenLabel("MyUserEvent");
 *	 ...
 *	 vTraceUserEvent(myEventHandle);
 *
 * The second option is faster since no lookup is required on each event, and
 * therefore recommended for user events that are frequently
 * executed and/or located in time-critical code. The lookup operation is
 * however fairly fast due to the design of the symbol table.
 ******************************************************************************/
traceLabel xTraceOpenLabel(const char* label)
{
	TRACE_ASSERT(label != NULL, "xTraceOpenLabel: label == NULL", (traceLabel)0);

	return prvTraceOpenSymbol(label, 0);
}

#endif

#endif
