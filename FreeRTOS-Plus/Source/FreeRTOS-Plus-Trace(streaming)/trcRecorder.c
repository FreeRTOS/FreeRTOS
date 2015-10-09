/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v3.0.2
 * Percepio AB, www.percepio.com
 *
 * trcRecorder.c
 *
 * The trace recorder core functions (portable).
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

#include <stdarg.h>
#include <stdint.h>

#include "trcRecorder.h"
#include "trcStreamPort.h"

#if (USE_TRACEALYZER_RECORDER == 1)

uint32_t uiTraceTickCount = 0;

typedef struct{
	int16_t EventID;
	uint16_t EventCount;
	uint32_t TS;
} BaseEvent;

typedef struct{
  BaseEvent base;
  uint32_t param1;
} EventWithParam_1;

typedef struct{
  BaseEvent base;
  uint32_t param1;
  uint32_t param2;
} EventWithParam_2;

typedef struct{
  BaseEvent base;
  uint32_t param1;
  uint32_t param2;
  uint32_t param3;
} EventWithParam_3;

/* Used in event functions with variable number of parameters. */
typedef struct
{
  BaseEvent base;
  char data[60]; /* maximum payload size */
} largestEventType;

typedef struct{
  uint32_t psf;
  uint16_t version;
  uint16_t platform;
  uint32_t options;
  uint16_t symbolSize;
  uint16_t symbolCount;
  uint16_t objectDataSize;
  uint16_t objectDataCount;
} PSFHeaderInfo;

/* The size of each slot in the Symbol Table */
#define SYMBOL_TABLE_SLOT_SIZE (sizeof(uint32_t) + (((TRC_SYMBOL_MAX_LENGTH)+(sizeof(uint32_t)-1))/sizeof(uint32_t))*sizeof(uint32_t))

#define OBJECT_DATA_SLOT_SIZE (sizeof(uint32_t) + sizeof(uint32_t))

/* The total size of the Symbol Table */
#define SYMBOL_TABLE_BUFFER_SIZE (TRC_SYMBOL_TABLE_SLOTS * SYMBOL_TABLE_SLOT_SIZE)

/* The total size of the Object Data Table */
#define OBJECT_DATA_TABLE_BUFFER_SIZE (TRC_OBJECT_DATA_SLOTS * OBJECT_DATA_SLOT_SIZE)

/* The Symbol Table type - just a byte array */
typedef struct{
  uint8_t pSymbolTableBuffer[SYMBOL_TABLE_BUFFER_SIZE];
} SymbolTable;

/* The Object Data Table type - just a byte array */
typedef struct{
  uint8_t pObjectDataTableBuffer[OBJECT_DATA_TABLE_BUFFER_SIZE];
} ObjectDataTable;

/* The Symbol Table instance - keeps names of tasks and other named objects. */
static SymbolTable symbolTable = { { 0 } };

/* The Object Data Table instance - keeps initial priorities of tasks. */
static ObjectDataTable objectDataTable = { { 0 } };

/* Code used for "task address" when no task has started. (NULL = idle task) */
#define HANDLE_NO_TASK 2

/* The maximum number of nested ISRs */
#define MAX_ISR_NESTING 8

/* Keeps track of ISR nesting */
static uint32_t ISR_stack[MAX_ISR_NESTING];

/* Keeps track of ISR nesting */
static int8_t ISR_stack_index = -1;

/* Any error that occured in the recorder (also creates User Event) */
static int errorCode = 0;

/* The user event channel for recorder warnings, defined in trcKernelPort.c */
extern char* trcWarningChannel;

/* Performs timestamping using definitions in trcHardwarePort.h */
static uint32_t prvGetTimestamp32(void);

/* Counts the number of trace sessions (not yet used) */
static uint32_t SessionCounter = 0;

/* Master switch for recording (0 => Disabled, 1 => Enabled) */
static uint32_t RecorderEnabled = 0;

/* Used to determine endian of data (big/little) */
static uint32_t PSFEndianessIdentifier = 0x50534600;

/* Used to interpret the data format */
static uint16_t FormatVersion = 0x0002;

/* The number of events stored. Used as event sequence number. */
static uint32_t eventCounter = 0;

/* Keeps track of if the current ISR chain has triggered a context switch that will be performed once all ISRs have returned. */
int32_t isPendingContextSwitch = 0;

/*******************************************************************************
 * NoRoomForSymbol
 *
 * Incremented on vTraceSaveSymbol if no room for saving the symbol name. This
 * is used for storing the names of:
 * - Tasks
 * - Named ISRs (vTraceSetISRProperties)
 * - Named kernel objects (vTraceStoreKernelObjectName)
 * - User event channels (vTraceStoreUserEventChannelName)
 *
 * This variable should be zero. If not, it shows the number of missing slots so
 * far. In that case, increment SYMBOL_TABLE_SLOTS with (at least) this value.
 ******************************************************************************/
volatile uint32_t NoRoomForSymbol = 0;

/*******************************************************************************
 * NoRoomForObjectData
 *
 * Incremented on vTraceSaveObjectData if no room for saving the object data,
 * i.e., the base priorities of tasks. There must be one slot for each task.
 * If not, this variable will show the difference.
 *
 * This variable should be zero. If not, it shows the number of missing slots so
 * far. In that case, increment OBJECT_DATA_SLOTS with (at least) this value.
 ******************************************************************************/
volatile uint32_t NoRoomForObjectData = 0;

/*******************************************************************************
 * LongestSymbolName
 *
 * Updated in vTraceSaveSymbol. Should not exceed SYMBOL_MAX_LENGTH, otherwise
 * symbol names will be truncated. In that case, set SYMBOL_MAX_LENGTH to (at
 * least) this value.
 ******************************************************************************/
volatile uint32_t LongestSymbolName = 0;

/*******************************************************************************
 * MaxBytesTruncated
 *
 * Set in prvTraceStoreStringEvent if the total data payload exceeds 60 bytes,
 * including data arguments and the string. For user events, that is 52 bytes
 * for string and data arguments. In that is exceeded, the event is  truncated
 * (usually only the string, unless more than 15 parameters) and this variable
 * holds the maximum number of truncated bytes, from any event.
 ******************************************************************************/
volatile uint32_t MaxBytesTruncated = 0;

/* Internal common function for storing string events */
static void prvTraceStoreStringEvent(	int nArgs,
										uint16_t eventID,
										const char* userEvtChannel,
										const char* str,
										va_list vl);

/* Stores the header information on Start */
static void vTraceStoreHeader(void);

/* Stores the symbol table on Start */
static void vTraceStoreSymbolTable(void);

/* Stores the object table on Start */
static void vTraceStoreObjectDataTable(void);

/* Store the Timestamp Config on Start */
static void vTraceStoreTSConfig(void);

/* Internal function for starting/stopping the recorder. */
static void intSetRecorderEnabled(int isEnabled);

/* Command codes for TzCtrl task (sent on Start/Stop). */
#define CMD_SET_ACTIVE 1

/* The final command code, used to validate commands. Only one command yet. */
#define CMD_LAST_COMMAND 1

/* Part of the PSF format - encodes the number of 32-bit params in an event */
#define PARAM_COUNT(n) ((n & 0xF) << 12)

/* Temporary fix since embOS sources aren't yet updated to contain them */
#ifndef OS_TRACE_ID_IFE
#define OS_TRACE_ID_IFE (4000u)
#endif

#ifndef OS_TRACE_ID_IFE_NEXT
#define OS_TRACE_ID_IFE_NEXT (4001u)
#endif

/******************************************************************************
 * vTraceInstanceFinishNow
 *
 * Creates an event that ends the current task instance at this very instant.
 * This makes the viewer to splits the current fragment at this point and begin
 * a new actor instance, even if no task-switch has occurred.
 *****************************************************************************/
void vTraceInstanceFinishedNow(void)
{
	vTraceStoreEvent0(PSF_EVENT_IFE_DIRECT);
}

/******************************************************************************
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
void vTraceInstanceFinishedNext(void)
{
	vTraceStoreEvent0(PSF_EVENT_IFE_NEXT);
}

/*******************************************************************************
 * vTraceStoreUserEventChannelName
 *
 * Stores a name for a user event channel, returns the handle (just a pointer
 * to the const char*.
 * The returned channel handle
 ******************************************************************************/
char* vTraceStoreUserEventChannelName(const char* name)
{
    vTraceSaveSymbol((void*)name, name);

	/* Always save in symbol table, if the recording has not yet started */
	vTraceStoreStringEvent(1, PSF_EVENT_OBJ_NAME, name, (uint32_t)name);

	return (char*)name;
}

/*******************************************************************************
 * vTraceStoreKernelObjectName
 *
 * Stores a name for kernel objects (Semaphore, Mailbox, etc.).
 ******************************************************************************/
void vTraceStoreKernelObjectName(void* object, const char* name)
{
    vTraceSaveSymbol(object, name);

	/* Always save in symbol table, if the recording has not yet started */
	vTraceStoreStringEvent(1, PSF_EVENT_OBJ_NAME, name, (uint32_t)object);
}

/******************************************************************************
 * vTracePrint
 *
 * Generates "User Events", with unformatted text.
 *
 * User Events can be used for very efficient application logging, and are shown
 * as yellow labels in the main trace view.
 *
 * You may group User Events into User Event Channels. The yellow User Event 
 * labels shows the logged string, preceeded by the channel  name within 
 * brackets. For example:
 *
 *  "[MyChannel] Hello World!"
 *
 * The User Event Channels are shown in the View Filter, which makes it easy to
 * select what User Events you wish to display. User Event Channels are created
 * using vTraceStoreUserEventChannelName().
 *
 * Example:
 *
 *	 char* error_uechannel = vTraceStoreUserEventChannelName("Errors");
 *	 ...
 *	 vTracePrint(error_uechannel, "Shouldn't reach this code!");
 *
 ******************************************************************************/
void vTracePrint(const char* chn, const char* str)
{
  va_list vl = { 0 };
  
  if (chn != NULL)
  {
    prvTraceStoreStringEvent(0, PSF_EVENT_USER_EVENT + 1, chn, str, vl);
  }
  else
  {
    prvTraceStoreStringEvent(0, PSF_EVENT_USER_EVENT, chn, str, vl);
  }
}

/******************************************************************************
 * vTracePrintF
 *
 * Generates "User Events", with formatted text and data, similar to a "printf".
 * It is very fast since the actual formatting is done on the host side when the
 * trace is displayed.
 *
 * User Events can be used for very efficient application logging, and are shown
 * as yellow labels in the main trace view.
 * An advantage of User Events is that data can be plotted in the "User Event
 * Signal Plot" view, visualizing any data you log as User Events, discrete
 * states or control system signals (e.g. system inputs or outputs).
 *
 * You may group User Events into User Event Channels. The yellow User Event 
 * labels show the logged string, preceeded by the channel name within brackets.
 * 
 * Example:
 *
 *  "[MyChannel] Hello World!"
 *
 * The User Event Channels are shown in the View Filter, which makes it easy to
 * select what User Events you wish to display. User Event Channels are created
 * using vTraceStoreUserEventChannelName().
 *
 * Example:
 *
 *	 char* adc_uechannel = vTraceStoreUserEventChannelName("ADC User Events");
 *	 ...
 *	 vTracePrint(adc_uechannel,
 *				 "ADC channel %d: %lf volts",
 *				 ch, (double)adc_reading/(double)scale);
 *
 * All data arguments are assumed to be 32 bt wide. The following formats are
 * supported in v2.8:
 * %d - signed integer. The following width and padding format is supported: "%05d" -> "-0042" and "%5d" -> "  -42"
 * %u - unsigned integer. The following width and padding format is supported: "%05u" -> "00042" and "%5u" -> "   42"
 * %X - hexadecimal (uppercase). The following width and padding format is supported: "%04X" -> "002A" and "%4X" -> "  2A"
 * %x - hexadecimal (lowercase). The following width and padding format is supported: "%04x" -> "002a" and "%4x" -> "  2a"
 * %s - string (currently, this must be an earlier stored symbol name)
 *
 * Up to 15 data arguments are allowed, with a total size of maximum 60 byte
 * including 8 byte for the base event fields and the format string. So with
 * one data argument, the maximum string length is 48 chars. If this is exceeded
 * the string is truncated (4 bytes at a time).
 *
 ******************************************************************************/
void vTracePrintF(const char* chn, const char* fmt, ...)
{
  int i = 0;
  va_list vl;

  int nArgs = 0;

  int len = 0;
  for (len = 0; fmt[len] != 0; len++)
  {
	  // Empty
  }
  if (len > 52)
    len = 52;
  
  while (i < len)
  {
    if (fmt[i] == '%')
    {
      if (fmt[i+1] != '%')
        nArgs++;        /* Found an argument */
      
      i++;      /* Move past format specifier or non-argument '%' */
    }
    
    i++;
  }

  va_start(vl, fmt);
  if (chn != NULL)
  {
    prvTraceStoreStringEvent(nArgs, PSF_EVENT_USER_EVENT + nArgs + 1, chn, fmt, vl);
  }
  else
  {
    prvTraceStoreStringEvent(nArgs, PSF_EVENT_USER_EVENT + nArgs, chn, fmt, vl);
  }
  va_end(vl);
}

/*******************************************************************************
 * vTraceSetISRProperties
 *
 * Stores a name and priority level for an Interrupt Service Routine, to allow
 * for better visualization. The string address is used as a unique handle.
 *
 * Example:
 *	 #define PRIO_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	 ...
 *	 vTraceSetISRProperties("ISRTimer1", PRIO_ISR_TIMER1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin("ISRTimer1");
 *		 ...
 *		 vTraceStoreISREnd(0);
 *	 }
 *
 ******************************************************************************/
void vTraceSetISRProperties(const char* name, char priority)
{
	/* Save object data in object data table */
	vTraceSaveObjectData((void*)name, priority);
        
	/* Note: "name" is used both as a string argument, and the address as ID */
	vTraceStoreStringEvent(2, PSF_EVENT_DEFINE_ISR, name, name, priority);
        
	/* Always save in symbol table, if the recording has not yet started */
	vTraceSaveSymbol((void*)name, name);
}

/*******************************************************************************
 * vTraceStoreISRBegin
 *
 * Registers the beginning of an Interrupt Service Routine.
 *
 * Example:
 *	 #define PRIO_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	 ...
 *	 vTraceSetISRProperties("ISRTimer1", PRIO_ISR_TIMER1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin("ISRTimer1");
 *		 ...
 *		 vTraceStoreISREnd(0);
 *	 }
 *
 ******************************************************************************/
void vTraceStoreISRBegin(void* handle)
{
	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_ENTER_CRITICAL_SECTION();

	if (ISR_stack_index == -1)
		isPendingContextSwitch = 0; /* We are at the start of a possible ISR chain. No context switches should have been triggered now. */

	if (ISR_stack_index < MAX_ISR_NESTING - 1)
	{
		ISR_stack_index++;
		ISR_stack[ISR_stack_index] = (uint32_t)handle;
		vTraceStoreEvent1(PSF_EVENT_ISR_BEGIN, (uint32_t)handle);
		TRACE_EXIT_CRITICAL_SECTION();
	}
	else
	{
		TRACE_EXIT_CRITICAL_SECTION();
		psfError(PSF_ERROR_ISR_NESTING_OVERFLOW);
	}
}

/*******************************************************************************
 * vTraceStoreISREnd
 *
 * Registers the end of an Interrupt Service Routine.
 *
 * This function will automatically detect if a task switch will take place 
 * when interrupt ends. If this is possible depends on the kernel port.
 *
 * Example:
 *	 #define PRIO_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	 ...
 *	 vTraceSetISRProperties("ISRTimer1", PRIO_ISR_TIMER1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin("ISRTimer1");
 *		 ...
 *		 vTraceStoreISREnd();
 *	 }
 *
 ******************************************************************************/
void vTraceStoreISREnd()
{
	vTraceStoreISREndManual(OS_IS_SWITCH_FROM_INT_REQUIRED());
}

/*******************************************************************************
 * vTraceStoreISREndManual
 *
 * Registers the end of an Interrupt Service Routine.
 *
 * The parameter taskSwitchRequested indicates if the interrupt has requested a
 * task-switch (= 1) or if the interrupt returns to the earlier context (= 0)
 *
 * Example:
 *	 #define PRIO_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	 ...
 *	 vTraceSetISRProperties("ISRTimer1", PRIO_ISR_TIMER1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin("ISRTimer1");
 *		 ...
 *		 vTraceStoreISREndManual(0);
 *	 }
 *
 ******************************************************************************/
void vTraceStoreISREndManual(int isTaskSwitchRequired)
{
	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_ENTER_CRITICAL_SECTION();

	isPendingContextSwitch |= isTaskSwitchRequired;	/* Is there a pending context switch right now? */
	if (ISR_stack_index > 0)
	{
		ISR_stack_index--;

		/* Store return to interrupted ISR (if nested ISRs)*/
		vTraceStoreEvent1(PSF_EVENT_ISR_RESUME, (uint32_t)ISR_stack[ISR_stack_index]);
	}
	else
	{
		ISR_stack_index--;
		
		/* Store return to interrupted task, if a task switch has not been triggered by any interrupt */
		if (isPendingContextSwitch == 0)
		{
			vTraceStoreEvent1(PSF_EVENT_TS_RESUME, (uint32_t)TRACE_GET_CURRENT_TASK());
		}
	}

	TRACE_EXIT_CRITICAL_SECTION();
}


/******************************************************************************/
/*** INTERNAL FUNCTIONS *******************************************************/
/******************************************************************************/

/* Internal function for starting/stopping the recorder. */
static void intSetRecorderEnabled(int isEnabled)
{
	TRACE_ALLOC_CRITICAL_SECTION();

  	void* currentTask = TRACE_GET_CURRENT_TASK();

	TRACE_ENTER_CRITICAL_SECTION();

    RecorderEnabled = isEnabled;

    if (currentTask == NULL)
    {
		currentTask = (void*)HANDLE_NO_TASK;
	}

	if (RecorderEnabled)
	{
        vTraceOnTraceBegin();
        
     	eventCounter = 0;
        ISR_stack_index = -1;
        vTraceStoreHeader();
		vTraceStoreSymbolTable();
    	vTraceStoreObjectDataTable();
        vTraceStoreEvent3(	PSF_EVENT_TRACE_START,
							(uint32_t)TRACE_GET_OS_TICKS(),
							(uint32_t)currentTask,
							SessionCounter++);
        vTraceStoreTSConfig();
	}
    else
    {
        vTraceOnTraceEnd();
    }

	TRACE_EXIT_CRITICAL_SECTION();
}

/* Stores the symbol table on Start */
static void vTraceStoreSymbolTable()
{
	uint32_t i = 0;
        uint32_t j = 0;
  	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_ENTER_CRITICAL_SECTION();

	if (RecorderEnabled)
	{
		for (i = 0; i < sizeof(SymbolTable); i += SYMBOL_TABLE_SLOT_SIZE)
		{
            TRC_STREAM_PORT_ALLOCATE_EVENT(uint8_t, data, SYMBOL_TABLE_SLOT_SIZE);
            for (j = 0; j < SYMBOL_TABLE_SLOT_SIZE; j++)
            {
                    data[j] = symbolTable.pSymbolTableBuffer[i+j];
            }
			TRC_STREAM_PORT_COMMIT_EVENT(data, SYMBOL_TABLE_SLOT_SIZE);
		}
	}
	TRACE_EXIT_CRITICAL_SECTION();
}

/* Stores the object table on Start */
static void vTraceStoreObjectDataTable()
{
	uint32_t i = 0;
        uint32_t j = 0;
  	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_ENTER_CRITICAL_SECTION();

	if (RecorderEnabled)
	{
		for (i = 0; i < sizeof(ObjectDataTable); i += OBJECT_DATA_SLOT_SIZE)
        {
            TRC_STREAM_PORT_ALLOCATE_EVENT(uint8_t, data, OBJECT_DATA_SLOT_SIZE);
            for (j = 0; j < OBJECT_DATA_SLOT_SIZE; j++)
            {
                    data[j] = objectDataTable.pObjectDataTableBuffer[i+j];
            }
            TRC_STREAM_PORT_COMMIT_EVENT(data, OBJECT_DATA_SLOT_SIZE);
        }
	}
	TRACE_EXIT_CRITICAL_SECTION();
}

/* Stores the header information on Start */
static void vTraceStoreHeader()
{
  	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_ENTER_CRITICAL_SECTION();

	if (RecorderEnabled)
	{
	  	TRC_STREAM_PORT_ALLOCATE_EVENT(PSFHeaderInfo, header, sizeof(PSFHeaderInfo));
		if (header != NULL)
		{
			header->psf = PSFEndianessIdentifier;
			header->version = FormatVersion;
			header->platform = KERNEL_ID;
            header->options = 0;
            /* Lowest bit used for IRQ_PRIORITY_ORDER */
            header->options = header->options | (IRQ_PRIORITY_ORDER << 0);
			header->symbolSize = SYMBOL_TABLE_SLOT_SIZE;
			header->symbolCount = TRC_SYMBOL_TABLE_SLOTS;
			header->objectDataSize = 8;
			header->objectDataCount = TRC_OBJECT_DATA_SLOTS;
			TRC_STREAM_PORT_COMMIT_EVENT(header, sizeof(PSFHeaderInfo));
		}
	}
	TRACE_EXIT_CRITICAL_SECTION();
}

/* Store an event with zero parameters (event ID only) */
void vTraceStoreEvent0(uint16_t eventID)
{
  	TRACE_ALLOC_CRITICAL_SECTION();

	PSF_ASSERT(eventID < 4096, PSF_ERROR_EVENT_CODE_TOO_LARGE);

	TRACE_ENTER_CRITICAL_SECTION();

	if (RecorderEnabled)
	{
		eventCounter++;

  		TRC_STREAM_PORT_ALLOCATE_EVENT(BaseEvent, event, sizeof(BaseEvent));
		if (event != NULL)
		{
			event->EventID = eventID | PARAM_COUNT(0);
			event->EventCount = eventCounter;
			event->TS = prvGetTimestamp32();
			TRC_STREAM_PORT_COMMIT_EVENT(event, sizeof(BaseEvent));
		}

	}
	TRACE_EXIT_CRITICAL_SECTION();
}

/* Store an event with one 32-bit parameter (pointer address or an int) */
void vTraceStoreEvent1(uint16_t eventID, uint32_t param1)
{
  	TRACE_ALLOC_CRITICAL_SECTION();

	PSF_ASSERT(eventID < 4096, PSF_ERROR_EVENT_CODE_TOO_LARGE);

	TRACE_ENTER_CRITICAL_SECTION();

	if (RecorderEnabled)
	{
		eventCounter++;
  		TRC_STREAM_PORT_ALLOCATE_EVENT(EventWithParam_1, event, sizeof(EventWithParam_1));
		if (event != NULL)
		{
			event->base.EventID = eventID | PARAM_COUNT(1);
			event->base.EventCount = eventCounter;
			event->base.TS = prvGetTimestamp32();
			event->param1 = (uint32_t)param1;
			TRC_STREAM_PORT_COMMIT_EVENT(event, sizeof(EventWithParam_1));
		}
	}
	TRACE_EXIT_CRITICAL_SECTION();
}

/* Store an event with two 32-bit parameters */
void vTraceStoreEvent2(uint16_t eventID, uint32_t param1, uint32_t param2)
{
  	TRACE_ALLOC_CRITICAL_SECTION();

	PSF_ASSERT(eventID < 4096, PSF_ERROR_EVENT_CODE_TOO_LARGE);

	TRACE_ENTER_CRITICAL_SECTION();

	if (RecorderEnabled)
	{
		eventCounter++;

	  	TRC_STREAM_PORT_ALLOCATE_EVENT(EventWithParam_2, event, sizeof(EventWithParam_2));
		if (event != NULL)
		{
		  	event->base.EventID = eventID | PARAM_COUNT(2);
			event->base.EventCount = eventCounter;
			event->base.TS = prvGetTimestamp32();
			event->param1 = (uint32_t)param1;
			event->param2 = param2;
			TRC_STREAM_PORT_COMMIT_EVENT(event, sizeof(EventWithParam_2));
		}
	}
	TRACE_EXIT_CRITICAL_SECTION();
}

/* Store an event with three 32-bit parameters */
void vTraceStoreEvent3(	uint16_t eventID,
						uint32_t param1,
						uint32_t param2,
						uint32_t param3)
{
  	TRACE_ALLOC_CRITICAL_SECTION();

	PSF_ASSERT(eventID < 4096, PSF_ERROR_EVENT_CODE_TOO_LARGE);

	TRACE_ENTER_CRITICAL_SECTION();

	if (RecorderEnabled)
	{
  		eventCounter++;

	  	TRC_STREAM_PORT_ALLOCATE_EVENT(EventWithParam_3, event, sizeof(EventWithParam_3));
		if (event != NULL)
		{
			event->base.EventID = eventID | PARAM_COUNT(3);
			event->base.EventCount = eventCounter;
			event->base.TS = prvGetTimestamp32();
			event->param1 = (uint32_t)param1;
			event->param2 = param2;
			event->param3 = param3;
			TRC_STREAM_PORT_COMMIT_EVENT(event, sizeof(EventWithParam_3));
		}
	}
	TRACE_EXIT_CRITICAL_SECTION();
}

/* Stores an event with <nParam> 32-bit integer parameters */
void vTraceStoreEvent(int nParam, uint16_t eventID, ...)
{
    TRACE_ALLOC_CRITICAL_SECTION();
	va_list vl;
	int i;

	PSF_ASSERT(eventID < 4096, PSF_ERROR_EVENT_CODE_TOO_LARGE);

	TRACE_ENTER_CRITICAL_SECTION();

	if (RecorderEnabled)
	{
	  	int eventSize = sizeof(BaseEvent) + nParam * sizeof(uint32_t);

		eventCounter++;

	  	TRC_STREAM_PORT_ALLOCATE_EVENT(largestEventType, event, eventSize);
		if (event != NULL)
		{
			event->base.EventID = eventID | PARAM_COUNT(nParam);
			event->base.EventCount = eventCounter;
			event->base.TS = prvGetTimestamp32();

			va_start(vl, eventID);
  			for (i = 0; i < nParam; i++)
			{
		  		uint32_t* tmp = (uint32_t*) &(event->data[i * 4]);
	  			*tmp = va_arg(vl, uint32_t);
			}
			va_end(vl);

			TRC_STREAM_PORT_COMMIT_EVENT(event, eventSize);
		}
	}
	TRACE_EXIT_CRITICAL_SECTION();
}

/* Stories an event with a string and <nParam> 32-bit integer parameters */
void vTraceStoreStringEvent(int nArgs, uint16_t eventID, const char* str, ...)
{
  	va_list vl;

	va_start(vl, str);
	prvTraceStoreStringEvent(nArgs, eventID, NULL, str, vl);
	va_end(vl);
}

/* Internal common function for storing string events */
static void prvTraceStoreStringEvent(	int nArgs,
										uint16_t eventID,
										const char* userEvtChannel,
										const char* str, va_list vl)
{
  	TRACE_ALLOC_CRITICAL_SECTION();
	int len;
  	int nParam;
	int strParam;
	int i;

	PSF_ASSERT(eventID < 4096, PSF_ERROR_EVENT_CODE_TOO_LARGE);

	len = 0;
	for (len = 0; str[len] != 0; len++)
	{
		// Empty
	}
  
	/* The string length in multiples of 32 bit words (+1 for null character) */
	strParam = (len+1+3)/4;

	/* If a user event channel is specified, add in the list */
	if (userEvtChannel) nArgs++;

	/* The total number of 32-bit words needed for the whole payload */
	nParam = strParam + nArgs;

	if (nParam > 15) /* if attempting to store more than 60 byte (= max) */
	{
		/* Truncate event if too large. The	string characters are stored
		last, so usually only the string is truncated, unless there a lot
		of parameters... */

		/* Diagnostics ... */
		uint32_t bytesTrucated = (nParam - 15) * 4;

		if (bytesTrucated > MaxBytesTruncated)
		{
			MaxBytesTruncated = bytesTrucated;
		}

		nParam = 15;
	}

	TRACE_ENTER_CRITICAL_SECTION();

	if (RecorderEnabled)
	{
		int eventSize = sizeof(BaseEvent) + nParam * sizeof(uint32_t);

		eventCounter++;

	  	TRC_STREAM_PORT_ALLOCATE_EVENT(largestEventType, event, eventSize);
		if (event != NULL)
		{
			event->base.EventID = (eventID) | PARAM_COUNT(nParam);
			event->base.EventCount = eventCounter;
			event->base.TS = prvGetTimestamp32();

			/* 32-bit write-pointer for the data argument */
			uint32_t* data32 = (uint32_t*) &(event->data[0]);

			for (i = 0; i < nArgs; i++)
			{
				if ((userEvtChannel != NULL) && (i == 0))
				{
					/* First, add the User Event Channel if not NULL */
					data32[i] = (uint32_t)userEvtChannel;
				}
				else
				{
					/* Add data arguments... */
					data32[i] = va_arg(vl, uint32_t);
				}
			}

			for (i = 0; i < len; i++)
			{
		  		event->data[nArgs * 4 + i] = str[i];
			}

			event->data[nArgs * 4 + len] = 0;
			TRC_STREAM_PORT_COMMIT_EVENT(event, eventSize);
		}
	}
	TRACE_EXIT_CRITICAL_SECTION();
}

/* Saves a symbol name (task name etc.) in symbol table */
void vTraceSaveSymbol(void *address, const char *name)
{
	uint32_t i = 0;
	uint32_t foundSlot = SYMBOL_TABLE_BUFFER_SIZE;
	void *ptr;

	for (i = 0; i < SYMBOL_TABLE_BUFFER_SIZE; i += SYMBOL_TABLE_SLOT_SIZE)
	{
		ptr = *((void**)&symbolTable.pSymbolTableBuffer[i]);
		if (ptr == 0 && foundSlot == SYMBOL_TABLE_BUFFER_SIZE)
		{
			foundSlot = i;
		}
		else if (ptr == address)
		{
			foundSlot = i;
			break;
		}
	}

	if (foundSlot != SYMBOL_TABLE_BUFFER_SIZE)
	{
		*((uint32_t*)&symbolTable.pSymbolTableBuffer[foundSlot]) =
			(uint32_t)address;

		for (i = 0; i < TRC_SYMBOL_MAX_LENGTH; i++)
        {
			if (name[i] == 0)
				break;

			symbolTable.pSymbolTableBuffer[foundSlot + sizeof(uint32_t) + i] =
				name[i];
		}

		/* Check the length of "name", if longer than SYMBOL_MAX_LENGTH */
		while ((name[i] != 0) && i < 128)
		{
			i++;
		}

		/* Remember the longest symbol name, for diagnostic purposes */
		if (i > LongestSymbolName)
		{
			LongestSymbolName = i;
		}
	}
	else
	{
		NoRoomForSymbol++;
	}
}

/* Deletes a symbol name (task name etc.) from symbol table */
void vTraceDeleteSymbol(void *address)
{
	uint32_t i = 0;
	void **ptr;

	for (i = 0; i < SYMBOL_TABLE_BUFFER_SIZE; i += SYMBOL_TABLE_SLOT_SIZE)
	{
		ptr = ((void**)&symbolTable.pSymbolTableBuffer[i]);
		if (*ptr == address)
		{
			*ptr = 0;
			break;
		}
	}
}

/* Saves an object data entry (task base priority) in object data table */
void vTraceSaveObjectData(void *address, uint32_t data)
{
	uint32_t i = 0;
	uint32_t foundSlot = OBJECT_DATA_TABLE_BUFFER_SIZE;
	void *ptr;

	for (i = 0; i < OBJECT_DATA_TABLE_BUFFER_SIZE; i += OBJECT_DATA_SLOT_SIZE)
	{
		ptr = *((void**)&objectDataTable.pObjectDataTableBuffer[i]);
		if (ptr == 0 && foundSlot == OBJECT_DATA_TABLE_BUFFER_SIZE)
		{
			foundSlot = i;
		}
		else if (ptr == address)
		{
			foundSlot = i;
			break;
		}
	}

	if (foundSlot != OBJECT_DATA_TABLE_BUFFER_SIZE)
	{
		*(uint32_t*)&objectDataTable.pObjectDataTableBuffer[foundSlot] = (uint32_t)address;
		*(uint32_t*)&objectDataTable.pObjectDataTableBuffer[foundSlot + sizeof(uint32_t)] = data;
	}
	else
	{
		NoRoomForObjectData++;
	}
}

/* Removes an object data entry (task base priority) from object data table */
void vTraceDeleteObjectData(void *address)
{
	uint32_t i = 0;
	void **ptr;

	for (i = 0; i < OBJECT_DATA_TABLE_BUFFER_SIZE; i += OBJECT_DATA_SLOT_SIZE)
	{
		ptr = (void**)&objectDataTable.pObjectDataTableBuffer[i];
		if (*ptr == address)
		{
			*ptr = 0;
			break;
		}
	}
}

/* Checks if the provided command is a valid command */
int isValidCommand(TracealyzerCommandType* cmd)
{
  	uint16_t checksum = (uint16_t)(0xFFFF - (	cmd->cmdCode +
												cmd->param1 +
												cmd->param2 +
												cmd->param3 +
												cmd->param4 +
												cmd->param5));

	if (cmd->checksumMSB != (unsigned char)(checksum >> 8))
		return 0;

	if (cmd->checksumLSB != (unsigned char)(checksum & 0xFF))
		return 0;

	if (cmd->cmdCode > CMD_LAST_COMMAND)
		return 0;

	return 1;
}

/* Executed the received command (Start or Stop) */
void processCommand(TracealyzerCommandType* cmd)
{
  	switch(cmd->cmdCode)
	{
		case CMD_SET_ACTIVE:
		  	intSetRecorderEnabled(cmd->param1);
		  	break;

		default:
		  	break;
	}
}

/* Called on critical errors in the recorder. Stops the recorder! */
void psfError(int errCode)
{
	if (! errorCode)
	{
		errorCode = errCode;
		vTracePrintF(trcWarningChannel, "Error %d. Stopped recorder.", errorCode);

		intSetRecorderEnabled(0);
	}
}

/* Performs timestamping using definitions in trcHardwarePort.h */
static uint32_t prvGetTimestamp32(void)
{
	int ticks = TRACE_GET_OS_TICKS();
	return (HWTC_COUNT & 0x00FFFFFF) + ((ticks & 0x000000FF) << 24);
}

/* Store the Timestamp Config event */
static void vTraceStoreTSConfig(void)
{
	vTraceStoreEvent3(	PSF_EVENT_TS_CONFIG,
						(uint32_t)TRACE_CPU_CLOCK_HZ,
						(uint32_t)TRACE_TICK_RATE_HZ,
						(int32_t)HWTC_TYPE);
}

#endif
