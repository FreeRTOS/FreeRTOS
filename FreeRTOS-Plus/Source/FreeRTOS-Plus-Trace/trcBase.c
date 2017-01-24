/*******************************************************************************
 * Tracealyzer v3.0.2 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcBase.c
 *
 * Core functionality of the trace recorder library.
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

#include "trcBase.h"

#if (USE_TRACEALYZER_RECORDER == 1)

#include <stdint.h>

/*******************************************************************************
 * Static data initializations
 ******************************************************************************/

/* Tasks and kernel objects can be explicitly excluded from the trace to reduce
buffer usage. This structure handles the exclude flags for all objects and tasks.
Note that slot 0 is not used, since not a valid handle. */
uint8_t excludedObjects[(TRACE_KERNEL_OBJECT_COUNT + TRACE_NCLASSES) / 8 + 1] = { 0 };

/* Specific events can also be excluded, i.e., by the event code. This can be
used to exclude kernel calls that don't refer to a kernel object, like a delay.
This structure handle the exclude flags for all event codes */
uint8_t excludedEventCodes[NEventCodes / 8 + 1] = { 0 };

/* A set of stacks that keeps track of available object handles for each class.
The stacks are empty initially, meaning that allocation of new handles will be
based on a counter (for each object class). Any delete operation will
return the handle to the corresponding stack, for reuse on the next allocate.*/
objectHandleStackType objectHandleStacks = { { 0 }, { 0 }, { 0 }, { 0 }, { 0 } };

/* Initial HWTC_COUNT value, for detecting if the time-stamping source is
enabled. If using the OS periodic timer for time-stamping, this might not
have been configured on the earliest events during the startup. */
uint32_t init_hwtc_count;

/*******************************************************************************
 * RecorderData
 *
 * The main data structure. This is the data read by the Tracealyzer tools,
 * typically through a debugger RAM dump. The recorder uses the pointer
 * RecorderDataPtr for accessing this, to allow for dynamic allocation.
 *
 * On the NXP LPC17xx you may use the secondary RAM bank (AHB RAM) for this
 * purpose. For instance, the LPC1766 has 32 KB AHB RAM which allows for
 * allocating a buffer size of at least 7500 events without affecting the main
 * RAM. To place RecorderData in this RAM bank using IAR Embedded Workbench
 * for ARM, use this pragma right before the declaration:
 *
 *	 #pragma location="AHB_RAM_MEMORY"
 *
 * This of course works for other hardware architectures with additional RAM
 * banks as well, just replace "AHB_RAM_MEMORY" with the section name from the
 * linker .map file, or simply the desired address.
 *
 * For portability reasons, we don't add the pragma directly in trcBase.c, but
 * in a header file included below. To include this header, you need to enable
 * USE_LINKER_PRAGMA, defined in trcConfig.h.
 *
 * If using GCC, you need to modify the declaration as follows:
 *
 *	 RecorderDataType RecorderData __attribute__ ((section ("name"))) = ...
 *
 * Remember to replace "name" with the correct section name.
 ******************************************************************************/

static void vInitStartMarkers(void);

#if (TRACE_DATA_ALLOCATION == TRACE_DATA_ALLOCATION_STATIC)
#if (USE_LINKER_PRAGMA == 1)
#include "recorderdata_linker_pragma.h"
#endif

RecorderDataType RecorderData;

#endif

RecorderDataType* RecorderDataPtr = NULL;

/* This version of the function dynamically allocates the trace data */
void prvTraceInitTraceData()
{
	init_hwtc_count = HWTC_COUNT;

#if TRACE_DATA_ALLOCATION == TRACE_DATA_ALLOCATION_STATIC
	RecorderDataPtr = &RecorderData;
#elif TRACE_DATA_ALLOCATION == TRACE_DATA_ALLOCATION_DYNAMIC
	RecorderDataPtr = (RecorderDataType*)TRACE_MALLOC(sizeof(RecorderDataType));
#elif TRACE_DATA_ALLOCATION == TRACE_DATA_ALLOCATION_CUSTOM
	/* DO NOTHING */
#endif


	TRACE_ASSERT(RecorderDataPtr != NULL, "prvTraceInitTraceData, RecorderDataPtr == NULL", );

	if (! RecorderDataPtr)
	{
		vTraceError("No recorder data structure allocated!");
		return;
	}

	(void)memset(RecorderDataPtr, 0, sizeof(RecorderDataType));

	RecorderDataPtr->startmarker0 = 0x00;
	RecorderDataPtr->startmarker1 = 0x01;
	RecorderDataPtr->startmarker2 = 0x02;
	RecorderDataPtr->startmarker3 = 0x03;
	RecorderDataPtr->startmarker4 = 0x70;
	RecorderDataPtr->startmarker5 = 0x71;
	RecorderDataPtr->startmarker6 = 0x72;
	RecorderDataPtr->startmarker7 = 0x73;
	RecorderDataPtr->startmarker8 = 0xF0;
	RecorderDataPtr->startmarker9 = 0xF1;
	RecorderDataPtr->startmarker10 = 0xF2;
	RecorderDataPtr->startmarker11 = 0xF3;

	RecorderDataPtr->version = TRACE_KERNEL_VERSION;
	RecorderDataPtr->minor_version = TRACE_MINOR_VERSION;
	RecorderDataPtr->irq_priority_order = IRQ_PRIORITY_ORDER;
	RecorderDataPtr->filesize = sizeof(RecorderDataType);

	RecorderDataPtr->maxEvents = EVENT_BUFFER_SIZE;

	RecorderDataPtr->debugMarker0 = 0xF0F0F0F0;

	RecorderDataPtr->isUsing16bitHandles = USE_16BIT_OBJECT_HANDLES;

	/* This function is kernel specific */
	vTraceInitObjectPropertyTable();

	RecorderDataPtr->debugMarker1 = 0xF1F1F1F1;
	RecorderDataPtr->SymbolTable.symTableSize = SYMBOL_TABLE_SIZE;
	RecorderDataPtr->SymbolTable.nextFreeSymbolIndex = 1;
#if (INCLUDE_FLOAT_SUPPORT == 1)
	RecorderDataPtr->exampleFloatEncoding = 1.0f; /* otherwise already zero */
#endif
	RecorderDataPtr->debugMarker2 = 0xF2F2F2F2;
	(void)strncpy(RecorderDataPtr->systemInfo, "Trace Recorder Demo", 80);
	RecorderDataPtr->debugMarker3 = 0xF3F3F3F3;
	RecorderDataPtr->endmarker0 = 0x0A;
	RecorderDataPtr->endmarker1 = 0x0B;
	RecorderDataPtr->endmarker2 = 0x0C;
	RecorderDataPtr->endmarker3 = 0x0D;
	RecorderDataPtr->endmarker4 = 0x71;
	RecorderDataPtr->endmarker5 = 0x72;
	RecorderDataPtr->endmarker6 = 0x73;
	RecorderDataPtr->endmarker7 = 0x74;
	RecorderDataPtr->endmarker8 = 0xF1;
	RecorderDataPtr->endmarker9 = 0xF2;
	RecorderDataPtr->endmarker10 = 0xF3;
	RecorderDataPtr->endmarker11 = 0xF4;

#if USE_SEPARATE_USER_EVENT_BUFFER
	RecorderDataPtr->userEventBuffer.bufferID = 1;
	RecorderDataPtr->userEventBuffer.version = 0;
	RecorderDataPtr->userEventBuffer.numberOfSlots = USER_EVENT_BUFFER_SIZE;
	RecorderDataPtr->userEventBuffer.numberOfChannels = CHANNEL_FORMAT_PAIRS + 1;
#endif

	/* Kernel specific initialization of the objectHandleStacks variable */
	vTraceInitObjectHandleStack();

	/* Fix the start markers of the trace data structure */
	vInitStartMarkers();

	#ifdef PORT_SPECIFIC_INIT
	PORT_SPECIFIC_INIT();
	#endif
}

static void vInitStartMarkers()
{
	uint32_t i;
	uint8_t *ptr = (uint8_t*)&(RecorderDataPtr->startmarker0);
	if ((*ptr) == 0)
	{
		for (i = 0; i < 12; i++)
		{
			ptr[i] += 1;
		}
	}
	else
	{
		vTraceError("Trace start markers already initialized!");
	}
}

volatile int recorder_busy = 0;

/* Gives the last error message of the recorder. NULL if no error message. */
const char* traceErrorMessage = NULL;

void* xTraceNextFreeEventBufferSlot(void)
{
	if (! RecorderDataPtr->recorderActive)
	{
		// If the associated XTS or XPS event prio to the main event has filled the buffer and store mode "stop when full".
		return NULL;
	}

	if (RecorderDataPtr->nextFreeIndex >= EVENT_BUFFER_SIZE)
	{
		vTraceError("Attempt to index outside event buffer!");
		return NULL;
	}
	return (void*)(&RecorderDataPtr->eventData[RecorderDataPtr->nextFreeIndex*4]);
}

uint16_t uiIndexOfObject(objectHandleType objecthandle, uint8_t objectclass)
{
	TRACE_ASSERT(objectclass < TRACE_NCLASSES,
		"uiIndexOfObject: Invalid value for objectclass", 0);
	TRACE_ASSERT(objecthandle > 0 && objecthandle <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectclass],
		"uiIndexOfObject: Invalid value for objecthandle", 0);

	if ((objectclass < TRACE_NCLASSES) && (objecthandle > 0) &&
		(objecthandle <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectclass]))
	{
		return (uint16_t)(RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[objectclass] +
			(RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[objectclass] * (objecthandle-1)));
	}

	vTraceError("Object table lookup with invalid object handle or object class!");
	return 0;
}

/*******************************************************************************
 * Object handle system
 * This provides a mechanism to assign each kernel object (tasks, queues, etc)
 * with a 1-byte handle, that is used to identify the object in the trace.
 * This way, only one byte instead of four is necessary to identify the object.
 * This allows for maximum 255 objects, of each object class, active at any
 * moment.
 * Note that zero is reserved as an error code and is not a valid handle.
 *
 * In order to allow for fast dynamic allocation and release of object handles,
 * the handles of each object class (e.g., TASK) are stored in a stack. When a
 * handle is needed, e.g., on task creation, the next free handle is popped from
 * the stack. When an object (e.g., task) is deleted, its handle is pushed back
 * on the stack and can thereby be reused for other objects.
 *
 * Since this allows for reuse of object handles, a specific handle (e.g, "8")
 * may refer to TASK_X at one point, and later mean "TASK_Y". To resolve this,
 * the recorder uses "Close events", which are stored in the main event buffer
 * when objects are deleted and their handles are released. The close event
 * contains the mapping between object handle and object name which was valid up
 * to this point in time. The object name is stored as a symbol table entry.
 ******************************************************************************/

objectHandleType xTraceGetObjectHandle(traceObjectClass objectclass)
{
	objectHandleType handle;
	static int indexOfHandle;

	TRACE_ASSERT(objectclass < TRACE_NCLASSES,
		"xTraceGetObjectHandle: Invalid value for objectclass", (objectHandleType)0);

	indexOfHandle = objectHandleStacks.indexOfNextAvailableHandle[objectclass];
	if (objectHandleStacks.objectHandles[indexOfHandle] == 0)
	{
		/* Zero is used to indicate a never before used handle, i.e.,
			new slots in the handle stack. The handle slot needs to
			be initialized here (starts at 1). */
		objectHandleStacks.objectHandles[indexOfHandle] =
			(objectHandleType)(1 + indexOfHandle -
			objectHandleStacks.lowestIndexOfClass[objectclass]);
	}

	handle = objectHandleStacks.objectHandles[indexOfHandle];

	if (objectHandleStacks.indexOfNextAvailableHandle[objectclass]
		> objectHandleStacks.highestIndexOfClass[objectclass])
	{
		/* ERROR */
		vTraceError(pszTraceGetErrorNotEnoughHandles(objectclass));

		handle = 0; /* an invalid/anonymous handle - but the recorder is stopped now... */
	}
	else
	{
		int hndCount;
		objectHandleStacks.indexOfNextAvailableHandle[objectclass]++;

		hndCount = objectHandleStacks.indexOfNextAvailableHandle[objectclass] -
			objectHandleStacks.lowestIndexOfClass[objectclass];

		if (hndCount >
			objectHandleStacks.handleCountWaterMarksOfClass[objectclass])
		{
			objectHandleStacks.handleCountWaterMarksOfClass[objectclass] =
				(objectHandleType)hndCount;
		}

		TRACE_CLEAR_OBJECT_FLAG_ISEXCLUDED(objectclass, handle);
	}

	return handle;
}

void vTraceFreeObjectHandle(traceObjectClass objectclass, objectHandleType handle)
{
	int indexOfHandle;

	TRACE_ASSERT(objectclass < TRACE_NCLASSES,
		"vTraceFreeObjectHandle: Invalid value for objectclass", );
	TRACE_ASSERT(handle > 0 && handle <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectclass],
		"vTraceFreeObjectHandle: Invalid value for handle", );

	/* Check that there is room to push the handle on the stack */
	if ((objectHandleStacks.indexOfNextAvailableHandle[objectclass] - 1) <
		objectHandleStacks.lowestIndexOfClass[objectclass])
	{
		/* Error */
		vTraceError("Attempt to free more handles than allocated!");
	}
	else
	{
		objectHandleStacks.indexOfNextAvailableHandle[objectclass]--;
		indexOfHandle = objectHandleStacks.indexOfNextAvailableHandle[objectclass];
		objectHandleStacks.objectHandles[indexOfHandle] = handle;
	}

}

/*******************************************************************************
 * Objects Property Table
 *
 * This holds the names and properties of the currently active objects, such as
 * tasks and queues. This is developed to support "dynamic" objects which might
 * be deleted during runtime. Their handles are only valid during their
 * lifetime, i.e., from create to delete, as they might be reused on later
 * create operations. When an object is deleted from the OPT, its data is moved
 * to the trace buffer and/or the symbol table.
 * When an object (task, queue, etc.) is created, it receives a handle, which
 * together with the object class specifies its location in the OPT. Thus,
 * objects of different types may share the same name and/or handle, but still
 * be independent objects.
 ******************************************************************************/

/*******************************************************************************
 * vTraceSetObjectName
 *
 * Registers the names of queues, semaphores and other kernel objects in the
 * recorder's Object Property Table, at the given handle and object class.
 ******************************************************************************/
void vTraceSetObjectName(traceObjectClass objectclass,
						 objectHandleType handle,
						 const char* name)
{
	static uint16_t idx;

	TRACE_ASSERT(name != NULL, "vTraceSetObjectName: name == NULL", );

	if (objectclass >= TRACE_NCLASSES)
	{
		vTraceError("Illegal object class in vTraceSetObjectName");
		return;
	}

	if (handle == 0)
	{
		vTraceError("Illegal handle (0) in vTraceSetObjectName.");
		return;
	}

	if (handle > RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectclass])
	{
		/* ERROR */
		vTraceError(pszTraceGetErrorNotEnoughHandles(objectclass));
	}
	else
	{
		idx = uiIndexOfObject(handle, objectclass);

		if (traceErrorMessage == NULL)
		{
			(void)strncpy((char*)&(RecorderDataPtr->ObjectPropertyTable.objbytes[idx]),
				name,
				RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[ objectclass ]);
		}
	}
}

traceLabel prvTraceOpenSymbol(const char* name, traceLabel userEventChannel)
{
	uint16_t result;
	uint8_t len;
	uint8_t crc;
	TRACE_SR_ALLOC_CRITICAL_SECTION();

	len = 0;
	crc = 0;

	TRACE_ASSERT(name != NULL, "prvTraceOpenSymbol: name == NULL", (traceLabel)0);

	prvTraceGetChecksum(name, &crc, &len);

	trcCRITICAL_SECTION_BEGIN();
	result = prvTraceLookupSymbolTableEntry(name, crc, len, userEventChannel);
	if (!result)
	{
		result = prvTraceCreateSymbolTableEntry(name, crc, len, userEventChannel);
	}
	trcCRITICAL_SECTION_END();

	return result;
}

/*******************************************************************************
 * Supporting functions
 ******************************************************************************/

/*******************************************************************************
 * vTraceError
 *
 * Called by various parts in the recorder. Stops the recorder and stores a
 * pointer to an error message, which is printed by the monitor task.
 * If you are not using the monitor task, you may use xTraceGetLastError()
 * from your application to check if the recorder is OK.
 *
 * Note: If a recorder error is registered before vTraceStart is called, the
 * trace start will be aborted. This can occur if any of the Nxxxx constants
 * (e.g., NTask) in trcConfig.h is too small.
 ******************************************************************************/
void vTraceError(const char* msg)
{
	TRACE_ASSERT(msg != NULL, "vTraceError: msg == NULL", );
	TRACE_ASSERT(RecorderDataPtr != NULL, "vTraceError: RecorderDataPtr == NULL", );

	/* Stop the recorder. Note: We do not call vTraceStop, since that adds a weird
	and unnecessary dependency to trcUser.c */

	RecorderDataPtr->recorderActive = 0;

	if (traceErrorMessage == NULL)
	{
		traceErrorMessage = msg;
		(void)strncpy(RecorderDataPtr->systemInfo, traceErrorMessage, 80);
		RecorderDataPtr->internalErrorOccured = 1;
	}

}

/******************************************************************************
 * prvCheckDataToBeOverwrittenForMultiEntryEvents
 *
 * This checks if the next event to be overwritten is a multi-entry user event,
 * i.e., a USER_EVENT followed by data entries.
 * Such data entries do not have an event code at byte 0, as other events.
 * All 4 bytes are user data, so the first byte of such data events must
 * not be interpreted as type field. The number of data entries following
 * a USER_EVENT is given in the event code of the USER_EVENT.
 * Therefore, when overwriting a USER_EVENT (when using in ringbuffer mode)
 * any data entries following must be replaced with NULL events (code 0).
 *
 * This is assumed to execute within a critical section...
 *****************************************************************************/

void prvCheckDataToBeOverwrittenForMultiEntryEvents(uint8_t nofEntriesToCheck)
{
	/* Generic "int" type is desired - should be 16 bit variable on 16 bit HW */
	unsigned int i = 0;
	unsigned int e = 0;

	TRACE_ASSERT(nofEntriesToCheck != 0,
		"prvCheckDataToBeOverwrittenForMultiEntryEvents: nofEntriesToCheck == 0", );

	while (i < nofEntriesToCheck)
	{
		e = RecorderDataPtr->nextFreeIndex + i;
		if ((RecorderDataPtr->eventData[e*4] > USER_EVENT) &&
			(RecorderDataPtr->eventData[e*4] < USER_EVENT + 16))
		{
			uint8_t nDataEvents = (uint8_t)(RecorderDataPtr->eventData[e*4] - USER_EVENT);
			if ((e + nDataEvents) < RecorderDataPtr->maxEvents)
			{
				(void)memset(& RecorderDataPtr->eventData[e*4], 0, 4 + 4 * nDataEvents);
			}
		}
		else if (RecorderDataPtr->eventData[e*4] == DIV_XPS)
		{
			if ((e + 1) < RecorderDataPtr->maxEvents)
			{
				/* Clear 8 bytes */
				(void)memset(& RecorderDataPtr->eventData[e*4], 0, 4 + 4);
			}
			else
			{
				/* Clear 8 bytes, 4 first and 4 last */
				(void)memset(& RecorderDataPtr->eventData[0], 0, 4);
				(void)memset(& RecorderDataPtr->eventData[e*4], 0, 4);
			}
		}
		i++;
	}
}

/*******************************************************************************
 * prvTraceUpdateCounters
 *
 * Updates the index of the event buffer.
 ******************************************************************************/
void prvTraceUpdateCounters(void)
{
	if (RecorderDataPtr->recorderActive == 0)
	{
		return;
	}

	RecorderDataPtr->numEvents++;

	RecorderDataPtr->nextFreeIndex++;

	if (RecorderDataPtr->nextFreeIndex >= EVENT_BUFFER_SIZE)
	{
#if (TRACE_RECORDER_STORE_MODE == TRACE_STORE_MODE_RING_BUFFER)
		RecorderDataPtr->bufferIsFull = 1;
		RecorderDataPtr->nextFreeIndex = 0;
#else
		vTraceStop();
#endif
	}

#if (TRACE_RECORDER_STORE_MODE == TRACE_STORE_MODE_RING_BUFFER)
	prvCheckDataToBeOverwrittenForMultiEntryEvents(1);
#endif
}

/******************************************************************************
 * prvTraceGetDTS
 *
 * Returns a differential timestamp (DTS), i.e., the time since
 * last event, and creates an XTS event if the DTS does not fit in the
 * number of bits given. The XTS event holds the MSB bytes of the DTS.
 *
 * The parameter param_maxDTS should be 0xFF for 8-bit dts or 0xFFFF for
 * events with 16-bit dts fields.
 *****************************************************************************/
uint16_t prvTraceGetDTS(uint16_t param_maxDTS)
{
	static uint32_t old_timestamp = 0;
	XTSEvent* xts = 0;
	uint32_t dts = 0;
	uint32_t timestamp = 0;

	TRACE_ASSERT(param_maxDTS == 0xFF || param_maxDTS == 0xFFFF, "prvTraceGetDTS: Invalid value for param_maxDTS", 0);

#if (SELECTED_PORT != PORT_ARM_CortexM)

	if (RecorderDataPtr->frequency == 0 && init_hwtc_count != HWTC_COUNT)
	{
		/* If HWTC_PERIOD is mapped to the timer reload register,
		it might not be initialized	before the scheduler has been started.
		We therefore store the frequency of the timer when the counter
		register has changed from its initial value.
		(Note that this function is called also by vTraceStart and
		uiTraceStart, which might be called before the scheduler
		has been started.) */

#if (SELECTED_PORT == PORT_Win32)
		RecorderDataPtr->frequency = 100000;
#elif (SELECTED_PORT == PORT_HWIndependent)
		RecorderDataPtr->frequency = TRACE_TICK_RATE_HZ;
#else
		RecorderDataPtr->frequency = (HWTC_PERIOD * TRACE_TICK_RATE_HZ) / (uint32_t)HWTC_DIVISOR;
#endif
	}
#endif
	/**************************************************************************
	* The below statements read the timestamp from the timer port module.
	* If necessary, whole seconds are extracted using division while the rest
	* comes from the modulo operation.
	**************************************************************************/

	vTracePortGetTimeStamp(&timestamp);

	/***************************************************************************
	* Since dts is unsigned the result will be correct even if timestamp has
	* wrapped around.
	***************************************************************************/
	dts = timestamp - old_timestamp;
	old_timestamp = timestamp;

	if (RecorderDataPtr->frequency > 0)
	{
		/* Check if dts > 1 second */
		if (dts > RecorderDataPtr->frequency)
		{
			/* More than 1 second has passed */
			RecorderDataPtr->absTimeLastEventSecond += dts / RecorderDataPtr->frequency;
			/* The part that is not an entire second is added to absTimeLastEvent */
			RecorderDataPtr->absTimeLastEvent += dts % RecorderDataPtr->frequency;
		}
		else
		{
			RecorderDataPtr->absTimeLastEvent += dts;
		}

		/* Check if absTimeLastEvent >= 1 second */
		if (RecorderDataPtr->absTimeLastEvent >= RecorderDataPtr->frequency)
		{
			/* RecorderDataPtr->absTimeLastEvent is more than or equal to 1 second, but always less than 2 seconds */
			RecorderDataPtr->absTimeLastEventSecond++;
			RecorderDataPtr->absTimeLastEvent -= RecorderDataPtr->frequency;
			/* RecorderDataPtr->absTimeLastEvent is now less than 1 second */
		}
	}
	else
	{
		/* Special case if the recorder has not yet started (frequency may be uninitialized, i.e., zero) */
		RecorderDataPtr->absTimeLastEvent = timestamp;
	}

	/* If the dts (time since last event) does not fit in event->dts (only 8 or 16 bits) */
	if (dts > param_maxDTS)
	{
		/* Create an XTS event (eXtended TimeStamp) containing the higher dts bits*/
		xts = (XTSEvent*) xTraceNextFreeEventBufferSlot();

		if (xts != NULL)
		{
			if (param_maxDTS == 0xFFFF)
			{
				xts->type = XTS16;
				xts->xts_16 = (uint16_t)((dts / 0x10000) & 0xFFFF);
				xts->xts_8 = 0;
			}
			else if (param_maxDTS == 0xFF)
			{
				xts->type = XTS8;
				xts->xts_16 = (uint16_t)((dts / 0x100) & 0xFFFF);
				xts->xts_8 = (uint8_t)((dts / 0x1000000) & 0xFF);
			}
			else
			{
				vTraceError("Bad param_maxDTS in prvTraceGetDTS");
			}
			prvTraceUpdateCounters();
		}
	}

	return (uint16_t)dts & param_maxDTS;
}

/*******************************************************************************
 * prvTraceLookupSymbolTableEntry
 *
 * Find an entry in the symbol table, return 0 if not present.
 *
 * The strings are stored in a byte pool, with four bytes of "meta-data" for
 * every string.
 * byte 0-1: index of next entry with same checksum (for fast lookup).
 * byte 2-3: reference to a symbol table entry, a label for vTracePrintF
 * format strings only (the handle of the destination channel).
 * byte 4..(4 + length): the string (object name or user event label), with
 * zero-termination
 ******************************************************************************/
traceLabel prvTraceLookupSymbolTableEntry(const char* name,
										 uint8_t crc6,
										 uint8_t len,
										 traceLabel chn)
{
	uint16_t i = RecorderDataPtr->SymbolTable.latestEntryOfChecksum[ crc6 ];

	TRACE_ASSERT(name != NULL, "prvTraceLookupSymbolTableEntry: name == NULL", (traceLabel)0);
	TRACE_ASSERT(len != 0, "prvTraceLookupSymbolTableEntry: len == 0", (traceLabel)0);

	while (i != 0)
	{
		if (RecorderDataPtr->SymbolTable.symbytes[i + 2] == (chn & 0x00FF))
		{
			if (RecorderDataPtr->SymbolTable.symbytes[i + 3] == (chn / 0x100))
			{
				if (RecorderDataPtr->SymbolTable.symbytes[i + 4 + len] == '\0')
				{
					if (strncmp((char*)(& RecorderDataPtr->SymbolTable.symbytes[i + 4]), name, len) == 0)
					{
						break; /* found */
					}
				}
			}
		}
		i = (uint16_t)(RecorderDataPtr->SymbolTable.symbytes[i] + (RecorderDataPtr->SymbolTable.symbytes[i + 1] * 0x100));
	}
	return i;
}

/*******************************************************************************
 * prvTraceCreateSymbolTableEntry
 *
 * Creates an entry in the symbol table, independent if it exists already.
 *
 * The strings are stored in a byte pool, with four bytes of "meta-data" for
 * every string.
 * byte 0-1: index of next entry with same checksum (for fast lookup).
 * byte 2-3: reference to a symbol table entry, a label for vTracePrintF
 * format strings only (the handle of the destination channel).
 * byte 4..(4 + length): the string (object name or user event label), with
 * zero-termination
 ******************************************************************************/
uint16_t prvTraceCreateSymbolTableEntry(const char* name,
										uint8_t crc6,
										uint8_t len,
										traceLabel channel)
{
	uint16_t ret = 0;

	TRACE_ASSERT(name != NULL, "prvTraceCreateSymbolTableEntry: name == NULL", 0);
	TRACE_ASSERT(len != 0, "prvTraceCreateSymbolTableEntry: len == 0", 0);

	if (RecorderDataPtr->SymbolTable.nextFreeSymbolIndex + len + 4 >= SYMBOL_TABLE_SIZE)
	{
		vTraceError("Symbol table full. Increase SYMBOL_TABLE_SIZE in trcConfig.h");
		ret = 0;
	}
	else
	{

		RecorderDataPtr->SymbolTable.symbytes
			[ RecorderDataPtr->SymbolTable.nextFreeSymbolIndex] =
			(uint8_t)(RecorderDataPtr->SymbolTable.latestEntryOfChecksum[ crc6 ] & 0x00FF);

		RecorderDataPtr->SymbolTable.symbytes
			[ RecorderDataPtr->SymbolTable.nextFreeSymbolIndex + 1] =
			(uint8_t)(RecorderDataPtr->SymbolTable.latestEntryOfChecksum[ crc6 ] / 0x100);

		RecorderDataPtr->SymbolTable.symbytes
			[ RecorderDataPtr->SymbolTable.nextFreeSymbolIndex + 2] =
			(uint8_t)(channel & 0x00FF);

		RecorderDataPtr->SymbolTable.symbytes
			[ RecorderDataPtr->SymbolTable.nextFreeSymbolIndex + 3] =
			(uint8_t)(channel / 0x100);

		/* set name (bytes 4...4+len-1) */
		(void)strncpy((char*)&(RecorderDataPtr->SymbolTable.symbytes
			[ RecorderDataPtr->SymbolTable.nextFreeSymbolIndex + 4]), name, len);

		/* Set zero termination (at offset 4+len) */
		RecorderDataPtr->SymbolTable.symbytes
			[RecorderDataPtr->SymbolTable.nextFreeSymbolIndex + 4 + len] = '\0';

		/* store index of entry (for return value, and as head of LL[crc6]) */
		RecorderDataPtr->SymbolTable.latestEntryOfChecksum
			[ crc6 ] = (uint16_t)RecorderDataPtr->SymbolTable.nextFreeSymbolIndex;

		RecorderDataPtr->SymbolTable.nextFreeSymbolIndex += (len + 5);

		ret = (uint16_t)(RecorderDataPtr->SymbolTable.nextFreeSymbolIndex -
			(len + 5));
	}

	return ret;
}


/*******************************************************************************
 * prvTraceGetChecksum
 *
 * Calculates a simple 6-bit checksum from a string, used to index the string
 * for fast symbol table lookup.
 ******************************************************************************/
void prvTraceGetChecksum(const char *pname, uint8_t* pcrc, uint8_t* plength)
{
	unsigned char c;
	int length = 1;		/* Should be 1 to account for '\0' */
	int crc = 0;

	TRACE_ASSERT(pname != NULL, "prvTraceGetChecksum: pname == NULL", );
	TRACE_ASSERT(pcrc != NULL, "prvTraceGetChecksum: pcrc == NULL", );
	TRACE_ASSERT(plength != NULL, "prvTraceGetChecksum: plength == NULL", );

	if (pname != (const char *) 0)
	{
		for (; (c = *pname++) != '\0';)
		{
			crc += c;
			length++;
		}
	}
	*pcrc = (uint8_t)(crc & 0x3F);
	*plength = (uint8_t)length;
}

#if (USE_16BIT_OBJECT_HANDLES == 1)

void prvTraceStoreXID(objectHandleType handle);

/******************************************************************************
 * prvTraceStoreXID
 *
 * Stores an XID (eXtended IDentifier) event.
 * This is used if an object/task handle is larger than 255.
 * The parameter "handle" is the full (16 bit) handle, assumed to be 256 or
 * larger. Handles below 256 should not use this function.
 *
 * NOTE: this function MUST be called from within a critical section.
 *****************************************************************************/

void prvTraceStoreXID(objectHandleType handle)
{
	XPSEvent* xid;

	TRACE_ASSERT(handle >= 256, "prvTraceStoreXID: Handle < 256", );

	xid = (XPSEvent*)xTraceNextFreeEventBufferSlot();

	if (xid != NULL)
	{
		xid->type = XID;

		/* This function is (only) used when objectHandleType is 16 bit... */
		xid->xps_16 = handle;

		prvTraceUpdateCounters();
	}
}

unsigned char prvTraceGet8BitHandle(objectHandleType handle)
{
	if (handle > 255)
	{
		prvTraceStoreXID(handle);
		/* The full handle (16 bit) is stored in the XID event.
		This code (255) is used instead of zero (which is an error code).*/
		return 255;
	}
	return (unsigned char)(handle & 0xFF);
}

#endif

#endif
