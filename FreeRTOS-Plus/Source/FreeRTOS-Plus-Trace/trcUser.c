/*******************************************************************************
 * Tracealyzer v2.4.1 Recorder Library
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
 * Copyright Percepio AB, 2013.
 * www.percepio.com
 ******************************************************************************/

#include "trcUser.h"

#if (USE_TRACEALYZER_RECORDER == 1)

#include <string.h>
#include <stdarg.h>
#include <stdint.h>

TRACE_STOP_HOOK vTraceStopHookPtr = (TRACE_STOP_HOOK)0;

extern uint8_t inExcludedTask;
extern uint8_t nISRactive;
extern uint8_t handle_of_last_logged_task;
extern uint32_t dts_min;
extern uint32_t hwtc_count_max_after_tick;
extern uint32_t hwtc_count_sum_after_tick;
extern uint32_t hwtc_count_sum_after_tick_counter;
extern char* traceErrorMessage;

/*** private functions *******************************************************/
void vTracePrintF_Helper(traceLabel eventLabel, const char* formatStr, va_list vl);

#if (USE_SEPARATE_USER_EVENT_BUFFER == 1)
void vTraceChannelPrintF_Helper(UserEventChannel channelPair, va_list vl);
static void prvTraceUserEventHelper1(UserEventChannel channel, traceLabel eventLabel, traceLabel formatLabel, va_list vl);
static void prvTraceUserEventHelper2(UserEventChannel channel, uint32_t* data, uint32_t noOfSlots);
#endif
/*****************************************************************************/



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
 * vTraceClear
 *
 * Resets the recorder. Only necessary if a restart is desired - this is not
 * needed in the startup initialization.
 ******************************************************************************/
void vTraceClear(void)
{
    trcCRITICAL_SECTION_BEGIN();

    RecorderDataPtr->absTimeLastEvent = 0;
    RecorderDataPtr->nextFreeIndex = 0;
    RecorderDataPtr->numEvents = 0;
    RecorderDataPtr->bufferIsFull = 0;

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
	objectHandleType handle = 0;

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
		(*vTraceStopHookPtr)();                      /* Call an application level call back function. */
	}
}

/*******************************************************************************
 * xTraceGetLastError
 *
 * Gives the last error message, if any. NULL if no error message is stored.
 * The message is cleared on read.
 * Any error message is also presented when opening a trace file.
 ******************************************************************************/
char* xTraceGetLastError(void)
{
	return traceErrorMessage;
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
 * vTraceTaskInstanceIsFinished
 *
 * This defines an explicit Instance Finish Event for the current task. It tells
 * the recorder that the current instance of this task is finished at the 
 * context-switch. This function should be called right before the API function 
 * call considered to be the Instance Finish Event.
 *****************************************************************************/
void vTraceTaskInstanceIsFinished()
{
    if (handle_of_last_logged_task)
    {
		TRACE_PROPERTY_OBJECT_STATE(TRACE_CLASS_TASK, handle_of_last_logged_task) = 0;
    }
}

/*******************************************************************************
 * Interrupt recording functions
 ******************************************************************************/

#if (INCLUDE_ISR_TRACING == 1)

#define MAX_ISR_NESTING 16
static uint8_t isrstack[MAX_ISR_NESTING];

/*******************************************************************************
 * vTraceSetISRProperties
 *
 * Registers an Interrupt Service Routine in the recorder library, This must be
 * called before using vTraceStoreISRBegin to store ISR events. This is
 * typically called in the startup of the system, before the scheduler is
 * started.
 *
 * Example:
 *     #define ID_ISR_TIMER1 1       // lowest valid ID is 1
 *     #define PRIO_OF_ISR_TIMER1 3  // the hardware priority of the interrupt
 *     ...
 *     vTraceSetISRProperties(ID_ISR_TIMER1, "ISRTimer1", PRIO_OF_ISR_TIMER1);
 *     ...
 *     void ISR_handler()
 *     {
 *         vTraceStoreISRBegin(ID_OF_ISR_TIMER1);
 *         ...
 *         vTraceStoreISREnd();
 *     }
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
	TRACE_ASSERT(priority >= 0, "vTraceSetISRProperties: Invalid value for priority", );

    vTraceSetObjectName(TRACE_CLASS_ISR, handle, name);
    vTraceSetPriorityProperty(TRACE_CLASS_ISR, handle, priority);
}

/*******************************************************************************
 * vTraceStoreISRBegin
 *
 * Registers the beginning of an Interrupt Service Routine.
 *
 * Example:
 *     #define ID_ISR_TIMER1 1       // lowest valid ID is 1
 *     #define PRIO_OF_ISR_TIMER1 3  // the hardware priority of the interrupt
 *     ...
 *     vTraceSetISRProperties(ID_ISR_TIMER1, "ISRTimer1", PRIO_OF_ISR_TIMER1);
 *     ...
 *     void ISR_handler()
 *     {
 *         vTraceStoreISRBegin(ID_OF_ISR_TIMER1);
 *         ...
 *         vTraceStoreISREnd();
 *     }
 *
 * NOTE: You need to make sure that any traced interrupts actually are
 * disabled by trcCRITICAL_SECTION_BEGIN().
 * If an invalid call to vTraceStoreISRBegin is detected (i.e., that preempted
 * a critical section of the recorder) this will generate a recorder error
 * using vTraceError.
 ******************************************************************************/
void vTraceStoreISRBegin(objectHandleType handle)
{
    uint16_t dts4;
    TSEvent* ts = NULL;

    TRACE_ASSERT(handle <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[TRACE_CLASS_ISR], "vTraceStoreISRBegin: Invalid value for handle", );

    if (recorder_busy)
    {
      vTraceError("Illegal call to vTraceStoreISRBegin, recorder busy!");
      return;
    }
    if (RecorderDataPtr->recorderActive && handle_of_last_logged_task)
    {
        trcCRITICAL_SECTION_BEGIN();
        dts4 = (uint16_t)prvTraceGetDTS(0xFFFF);

        if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
        {

            if (nISRactive < MAX_ISR_NESTING)
            {
                isrstack[nISRactive] = handle;
                nISRactive++;
                ts = (TSEvent*)xTraceNextFreeEventBufferSlot();
                if (ts != NULL)
                {
                    ts->type = TS_ISR_BEGIN;
                    ts->dts = dts4;
                    ts->objHandle = handle;
                    prvTraceUpdateCounters();
                }
            }
            else
            {
                /* This should not occur unless something is very wrong */
                vTraceError("Too many nested interrupts!");
            }
        }
        trcCRITICAL_SECTION_END();
    }
}


#if (SELECTED_PORT == PORT_ARM_CortexM)

static int tailchain_irq_pending(void);

/*******************************************************************************
 * tailchain_irq_pending
 *
 * For Cortex-M chips only. Returns 1 if an interrupt is pending, by checking
 * the 8 NVIC IRQ pend registers at 0xE000E200 to 0xE000E21C. Returns 0 if no
 * interrupt is pending. This is used to predict tailchaining of ISRs.
 ******************************************************************************/
static int tailchain_irq_pending(void)
{
  uint32_t* pend_reg = ((uint32_t*)0xE000E200);
  int i;

  for (i=0; i<8; i++)
  {
    if (pend_reg[i] != 0)
    {
      return 1;
    }
  }
  return 0;
}

#endif

/*******************************************************************************
 * vTraceStoreISREnd
 *
 * Registers the end of an Interrupt Service Routine.
 *
 * Example:
 *     #define ID_ISR_TIMER1 1       // lowest valid ID is 1
 *     #define PRIO_OF_ISR_TIMER1 3  // the hardware priority of the interrupt
 *     ...
 *     vTraceSetISRProperties(ID_ISR_TIMER1, "ISRTimer1", PRIO_OF_ISR_TIMER1);
 *     ...
 *     void ISR_handler()
 *     {
 *         vTraceStoreISRBegin(ID_OF_ISR_TIMER1);
 *         ...
 *         vTraceStoreISREnd();
 *     }
 *
 * NOTE: You need to make sure that any traced interrupts actually are
 * disabled by trcCRITICAL_SECTION_BEGIN().
 * If an invalid call to vTraceStoreISREnd is detected (i.e., that preempted
 * a critical section of the recorder) this will generate a recorder error
 * using vTraceError.
 ******************************************************************************/
void vTraceStoreISREnd(void)
{
    TSEvent* ts;
    uint16_t dts5;

    if (recorder_busy)
    {
      vTraceError("Illegal call to vTraceStoreISREnd, recorder busy!");
      return;
    }

    if (RecorderDataPtr->recorderActive && handle_of_last_logged_task)
    {
        #if (SELECTED_PORT == PORT_ARM_CortexM)
        if (tailchain_irq_pending() > 0)
        {
            nISRactive--; /* If an IRQ strikes exactly here, the resulting
            ISR tailchaining is not detected. The trace instead shows a very
            short fragment of the earlier preempted task/ISR, and then the new
            ISR begins. */
            return;
        }
        #endif

        trcCRITICAL_SECTION_BEGIN();
        dts5 = (uint16_t)prvTraceGetDTS(0xFFFF);

        if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
        {
            ts = (TSEvent*)xTraceNextFreeEventBufferSlot();
            if (ts != NULL)
            {
                if (nISRactive > 1)
                {
                    /* return to another isr */
                    ts->type = TS_ISR_RESUME;
                    ts->objHandle = isrstack[nISRactive];
                }
                else
                {
                    /* return to task */
                    ts->type = TS_TASK_RESUME;
                    ts->objHandle = handle_of_last_logged_task;
                }
                ts->dts = dts5;
                nISRactive--;
                prvTraceUpdateCounters();
            }
        }
        trcCRITICAL_SECTION_END();
    }
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


/*******************************************************************************
 * User Event functions
 ******************************************************************************/

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
	TRACE_ASSERT(buffer != NULL, "writeDouble: buffer == NULL", 0);

    uint32_t * dest = buffer;
    uint32_t * src = (void*)&value;
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

    dest[i/4+0] = src[0];
    dest[i/4+1] = src[1];

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
				case 'd':    i = writeInt32(buffer,
												i,
												(uint32_t)va_arg(vl, uint32_t));
								break;
				case 'x':
				case 'X':
				case 'u':    i = writeInt32(buffer,
												i,
												(uint32_t)va_arg(vl, uint32_t));
								break;
				case 's':    i = writeInt16(buffer,
												i,
												(uint16_t)xTraceOpenLabel((char*)va_arg(vl, char*)));
								break;

#if (INCLUDE_FLOAT_SUPPORT)
								/* Yes, "double" as type also in the float
								case. This since "float" is promoted into "double"
								by the va_arg stuff. */
				case 'f':    i = writeFloat(buffer,
												i,
												(float)va_arg(vl, double));
								break;
#else
	/* No support for floats, but attempt to store a float user event
	avoid a possible crash due to float reference. Instead store the
	data on uint_32 format (will not be displayed anyway). This is just
	to keep va_arg and i consistent. */

				case 'f':    i = writeInt32(buffer,
												i,
												(uint32_t)va_arg(vl, double));
								break;
#endif
				case 'l':
					formatStrIndex++;
					switch (formatStr[formatStrIndex])
					{
#if (INCLUDE_FLOAT_SUPPORT)
					case 'f':     i = writeDouble(buffer,
														i,
														(double)va_arg(vl, double));
								break;
#else
	/* No support for floats, but attempt to store a float user event
	avoid a possible crash due to float reference. Instead store the
	data on uint_32 format (will not be displayed anyway). This is just
	to keep va_arg and i consistent. */
					case 'f':    i = writeInt32(buffer, /* In this case, the value will not be shown anyway */
													i,
													(uint32_t)va_arg(vl, double));
									i = writeInt32(buffer, /* Do it twice, to write in total 8 bytes */
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
					case 'd':    i = writeInt16(buffer,
													i,
													(uint16_t)va_arg(vl, uint32_t));
									break;
					case 'u':    i = writeInt16(buffer,
													i,
													(uint16_t)va_arg(vl, uint32_t));
									break;
					}
					break;
				case 'b':
					formatStrIndex++;
					switch (formatStr[formatStrIndex])
					{
					case 'd':    i = writeInt8(buffer,
													i,
													(uint8_t)va_arg(vl, uint32_t));
									break;
					case 'u':    i = writeInt8(buffer,
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

	TRACE_ASSERT(USER_EVENT_BUFFER_SIZE >= count, "prvTraceClearChannelBuffer: USER_EVENT_BUFFER_SIZE is too small to handle this event.", );

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
	TRACE_ASSERT(data != NULL, "prvTraceCopyToDataBuffer: data == NULL.", );
	TRACE_ASSERT(count <= USER_EVENT_BUFFER_SIZE, "prvTraceCopyToDataBuffer: USER_EVENT_BUFFER_SIZE is too small to handle this event.", );

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
 * Calls on prvTraceUserEventFormat() to do the actual formatting, then goes on to the next helper function.
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
		RecorderDataPtr->userEventBuffer.wraparoundCounter++;
	old_timestamp = *data;

	/* Start by erasing any information in the channel buffer */
	prvTraceClearChannelBuffer(noOfSlots);

	prvTraceCopyToDataBuffer(data, noOfSlots); /* Will wrap around the data if necessary */

	old_nextSlotToWrite = RecorderDataPtr->userEventBuffer.nextSlotToWrite; /* Save the index that we want to write the channel data at when we're done */
	RecorderDataPtr->userEventBuffer.nextSlotToWrite = (RecorderDataPtr->userEventBuffer.nextSlotToWrite + noOfSlots) % USER_EVENT_BUFFER_SIZE; /* Make sure we never end up outside the buffer */

	/* Write to the channel buffer to indicate that this user event is ready to be used */
	if (channel != 0)
		RecorderDataPtr->userEventBuffer.channelBuffer[old_nextSlotToWrite] = channel;
	else
		RecorderDataPtr->userEventBuffer.channelBuffer[old_nextSlotToWrite] = (UserEventChannel)0xFF;	/* 0xFF indicates that this is not a normal channel id */
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
	va_list vl;

	va_start(vl, channelPair);
	vTraceChannelPrintF_Helper(channelPair, vl);
	va_end(vl);
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
	uint32_t data[(3 + MAX_ARG_SIZE) / 4];

	TRACE_ASSERT(channelPair != 0, "vTraceChannelPrintF: channelPair == 0", );
	TRACE_ASSERT(channelPair <= CHANNEL_FORMAT_PAIRS, "vTraceChannelPrintF: ", );

	prvTraceUserEventHelper2(channelPair, data, 1); /* Only need one slot for timestamp */
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
 *     traceLabel adc_uechannel = xTraceOpenLabel("ADC User Events");
 *     ...
 *     vTracePrint(adc_uechannel,
 *                 "ADC channel %d: %lf volts",
 *                 ch, (double)adc_reading/(double)scale);
 *
 * This can be combined into one line, if desired, but this is slower:
 *
 *     vTracePrint(xTraceOpenLabel("ADC User Events"),
 *                 "ADC channel %d: %lf volts",
 *                 ch, (double)adc_reading/(double)scale);
 *
 * Calling xTraceOpenLabel multiple times will not create duplicate entries, but
 * it is of course faster to just do it once, and then keep the handle for later
 * use. If you don´t have any data arguments, only a text label/string, it is
 * better to use vTraceUserEvent - it is faster.
 *
 * Format specifiers supported:
 *  %d - 32 bit signed integer
 *  %u - 32 bit unsigned integer
 *  %f - 32 bit float
 *  %s - string (is copied to the recorder symbol table)
 *  %hd - 16 bit signed integer
 *  %hu - 16 bit unsigned integer
 *  %bd - 8 bit signed integer
 *  %bu - 8 bit unsigned integer
 *  %lf - double-precision float
 *
 * Up to 15 data arguments are allowed, with a total size of maximum 32 byte.
 * In case this is exceeded, the user event is changed into an error message.
 *
 * The data is stored in trace buffer, and is packed to allow storing multiple
 * smaller data entries in the same 4-byte record, e.g., four 8-bit values.
 * A string requires two bytes, as the symbol table is limited to 64K. Storing a
 * double (%lf) uses two records, so this is quite costly. Use float (%f) unless
 * the higher precision is really necessary.
 ******************************************************************************/

void vTracePrintF(traceLabel eventLabel, const char* formatStr, ...)
{
	va_list vl;

	va_start(vl, formatStr);
	vTracePrintF_Helper(eventLabel, formatStr, vl);
	va_end(vl);
}

void vTracePrintF_Helper(traceLabel eventLabel, const char* formatStr, va_list vl)
{
#if (USE_SEPARATE_USER_EVENT_BUFFER == 0)
	uint32_t noOfSlots;
    UserEvent* ue1;
    uint32_t tempDataBuffer[(3 + MAX_ARG_SIZE) / 4];

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

    if (RecorderDataPtr->recorderActive && (! inExcludedTask || nISRactive) && handle_of_last_logged_task)
    {
        /* First, write the "primary" user event entry in the local buffer, but
        let the event type be "EVENT_BEING_WRITTEN" for now...*/

        ue1 = (UserEvent*)(&tempDataBuffer[0]);
        ue1->type = EVENT_BEING_WRITTEN;      /* Update this as the last step */

        noOfSlots = prvTraceUserEventFormat(formatStr, vl, (uint8_t*)tempDataBuffer, 4);

        /* Store the format string, with a reference to the channel symbol */
        ue1->payload = prvTraceOpenSymbol(formatStr, eventLabel);

        trcCRITICAL_SECTION_BEGIN();

        ue1->dts = (uint8_t)prvTraceGetDTS(0xFF);
        if (! RecorderDataPtr->recorderActive)
        {

            /* Abort, since an XTS event (created by prvTraceGetDTS) filled the
            buffer, and the recorder stopped since not circular buffer. */
            trcCRITICAL_SECTION_END();

            return;
        }

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
            /* Abort and stop recorder, since the event data will not fit in the
            buffer and not circular buffer in this case... */
            trcCRITICAL_SECTION_END();
            vTraceStop();


            return;
#endif
        }

#if (TRACE_RECORDER_STORE_MODE == TRACE_STORE_MODE_RING_BUFFER)
        /* Check that the buffer to be overwritten does not contain any user
        events that would be partially overwritten. If so, they must be "killed"
        by replacing the user event and following data with NULL events (i.e.,
        using a memset to zero).*/
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

#if (TRACE_RECORDER_STORE_MODE == TRACE_STORE_MODE_RING_BUFFER)
		/* Make sure the next entry is cleared correctly */
		prvCheckDataToBeOverwrittenForMultiEntryEvents(1);
#endif

#ifdef STOP_AFTER_N_EVENTS
#if (STOP_AFTER_N_EVENTS > -1)
		/* Check if we have reached the desired number of events */
		if (RecorderDataPtr->numEvents >= STOP_AFTER_N_EVENTS)
		{
			vTraceStop();
		}
#endif
#endif

        trcCRITICAL_SECTION_END();
    }

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
#if (USE_SEPARATE_USER_EVENT_BUFFER == 0)
    UserEvent* ue;
    uint8_t dts1;

	TRACE_ASSERT(eventLabel > 0, "vTraceUserEvent: Invalid value for eventLabel", );

    if (RecorderDataPtr->recorderActive && (! inExcludedTask || nISRactive) && handle_of_last_logged_task)
    {
        trcCRITICAL_SECTION_BEGIN();

        dts1 = (uint8_t)prvTraceGetDTS(0xFF);

        if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
        {
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
    }
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
 *     xTraceOpenLabel()
 *
 * which adds the string to the symbol table (if not already present)
 * and returns the corresponding handle.
 *
 * This can be used in two ways:
 *
 * 1. The handle is looked up every time, when storing the user event.
 *
 * Example:
 *     vTraceUserEvent(xTraceOpenLabel("MyUserEvent"));
 *
 * 2. The label is registered just once, with the handle stored in an
 *  application variable - much like using a file handle.
 *
 * Example:
 *     myEventHandle = xTraceOpenLabel("MyUserEvent");
 *     ...
 *     vTraceUserEvent(myEventHandle);
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