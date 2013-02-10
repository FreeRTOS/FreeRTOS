/*******************************************************************************
 * FreeRTOS+Trace v2.3.0 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcBase.c
 *
 * Core functionality of the trace recorder library.
 *
 * Terms of Use
 * This software is copyright Percepio AB. The recorder library is free for
 * use together with Percepio products. You may distribute the recorder library
 * in its original form, including modifications in trcPort.c and trcPort.h
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
 * FreeRTOS+Trace is available as Free Edition and in two premium editions.
 * You may use the premium features during 30 days for evaluation.
 * Download FreeRTOS+Trace at http://www.percepio.com/products/downloads/
 *
 * Copyright Percepio AB, 2012.
 * www.percepio.com
 ******************************************************************************/

#include "trcUser.h"
#include "task.h"

#if (configUSE_TRACE_FACILITY == 1)

/*******************************************************************************
 * Static data initializations
 ******************************************************************************/


/*******************************************************************************
 * RecorderData
 *
 * The main data structure. This is the data read by FreeRTOS+Trace, typically
 * through a debugger RAM dump. The recorder access this through the pointer
 * RecorderDataPtr, to allow for dynamic memory allocation as well.
 *
 * On the NXP LPC17xx you may use the secondary RAM bank (AHB RAM) for this
 * purpose. For instance, the LPC1766 has 32 KB AHB RAM which allows for 
 * allocating a buffer size of at least 7500 events without affecting the main
 * RAM. To place RecorderData in this RAM bank, use the below declaration.
 * 
 *     #pragma location="AHB_RAM_MEMORY"
 *     RecorderDataType RecorderData = ...
 * 
 * This of course works for other hardware architectures with additional RAM 
 * banks as well, just replace "AHB_RAM_MEMORY" with the name of the right 
 * address section from the linker file.
 *
 * However, to keep trcBase.c portable and still have a preconfigured IAR demo
 * using AHB RAM, we don't add the pragma directly in trcBase.c but in a header 
 * included where the pragma should go. This is used depending on the setting
 * USE_LINKER_PRAGMA, defined in trcConfig.h.
 * 
 * If using GCC, this is instead done by adding a "section" attribute:
 *
 *     RecorderDataType RecorderData __attribute__ ((section ("name"))) = ...
 *
 * Remember to replace "name" with the correct section name.
 ******************************************************************************/

#if (TRACE_DATA_ALLOCATION == TRACE_DATA_ALLOCATION_STATIC)
#if (USE_LINKER_PRAGMA == 1)
#include "recorderdata_linker_pragma.h"
#endif
RecorderDataType RecorderData =
{
    /* start marker, 12 chars */
    0x01, 0x02, 0x03, 0x04,
    0x71, 0x72, 0x73, 0x74,
    0xF1, 0xF2, 0xF3, 0xF4,

    /* version code - also used to determine endianness */
    VERSION,

    /* minor file format version */
    MINOR_VERSION,
    
    /* irq priority order */
    IRQ_PRIORITY_ORDER,

    /* file size (for control) */
    sizeof(RecorderDataType),

    /* number of events stored so far */
    0,

    /* size of events buffer (in event records, each 4 bytes) */
    EVENT_BUFFER_SIZE,

    /* next free event index (event index, not byte address) */
    0,

    /* buffer is full */ 
    0,

    /* frequency of clock user for timestamps, in Hz - should be 0 here
    as this is used to indicate "not yet initialized" - this is instead
    initialized on the first taskswitch event. */
    0,

    /* the absolute timestamp of the last stored event, modulo frequency */
    0,

    /* the number of seconds so far */
    0,

    /* is recorder active (yes = 1) - note that "close" events are always 
        stored to keep the name-handle mapping updated!*/
    0,

    /* Generated by FreeRTOS+Trace in Team Admin mode. Otherwise this should be "". */
    TEAM_LICENSE_CODE,

    /* debug marker 0 */
    0xF0F0F0F0,

    /* The Object Property Table - holds info of all active objects */ 
    {
        /* Number of object classes, also those not used */
        NCLASSES,

        /* The size in bytes of the object table byte pool */
        DynObjTableSize,

        /* The number of slots/handles available for each class */
        {
            NQueue,
            NSemaphore,
            NMutex,
            NTask,
            NISR
        },

        /* The maximum name length for each object class */
        {
            NameLenQueue,
            NameLenSemaphore,
            NameLenMutex,
            NameLenTask,
            NameLenISR
        },

        /* The total length a property table entry of the class */
        {
            PropertyTableSizeQueue,
            PropertyTableSizeSemaphore,
            PropertyTableSizeMutex,
            PropertyTableSizeTask,
            PropertyTableSizeISR
        },

        /* The start index of each class in the object property table */
        {
            StartIndexQueue,
            StartIndexSemaphore,
            StartIndexMutex,
            StartIndexTask,
            StartIndexISR
        },

        /* the object property table - encoded in a byte array using above 
        definitions */
        {0}
    },

    /* debug marker 1 */
    0xF1F1F1F1,

    /* The Symbol Table - holds all object names used since system 
       startup. Every string is unique, so objects with same name will share 
       an entry. Each name entry has four extra bytes: byte 0-1 is a link 
       reference in an internal linked list, used for fast lookups, byte 2-3 
       holds a reference to a channel label used for vTracePrintF format 
       strings, and byte 4.. holds the object name, followed by a 
       zero-termination.*/
    {
        SYMBOL_TABLE_SIZE,

        /* next free index (0 is reserved to mean NULL) */
        1,

        /* the symbol table byte pool */
        {0},

        /* this is a 64 entry array holding 16-bit references (indexes) 
           to the most recent entry of each checksum - i.e., list heads.*/
        {0},

    },

#if (INCLUDE_FLOAT_SUPPORT == 1)
    /* example float, for float endian detection */
    (float)1.0,
#else
    /* This code signals that no float support is included */
    (uint32_t)0, 
#endif

    /* internalErrorOccured */
    0,
    
    /* debug marker 2 */
    0xF2F2F2F2,
    
    /* The trace description string, can hold any information about the system, 
        e.g., version, configuration. Error messages from the recorder are
        copied to this buffer. Also used for internal error messages.*/
    TRACE_DESCRIPTION,
        
    /* debug marker 3 */
    0xF3F3F3F3,

    /* the event data buffer, size EVENT_BUFFER_SIZE*4 */
    {0},

    /* end markers, used to extract the trace from a RAM dump image */
    0x0A, 0x0B, 0x0C, 0x0D,
    0x71, 0x72, 0x73, 0x74,
    0xF1, 0xF2, 0xF3, 0xF4
};

RecorderDataType* RecorderDataPtr = &RecorderData;

/* This version of the function does nothing as the trace data is statically allocated */
RecorderDataType* xTraceInitTraceData(void)
{
    return 0;
}

#elif (TRACE_DATA_ALLOCATION == TRACE_DATA_ALLOCATION_DYNAMIC)

RecorderDataType* RecorderDataPtr = NULL;

/* This version of the function dynamically allocates the trace data */
RecorderDataType* xTraceInitTraceData(void)
{
    RecorderDataType* tmp = (RecorderDataType*)pvPortMalloc(sizeof(RecorderDataType));

    if (! tmp)
    {
        vTraceError("Malloc failed in xTraceInitTraceData! Reduce size constants in trcConfig.h");
        return NULL;
    }
    
    (void)memset(tmp, 0, sizeof(RecorderDataType));

    tmp->startmarker0 = 0x01;
    tmp->startmarker1 = 0x02;
    tmp->startmarker2 = 0x03;
    tmp->startmarker3 = 0x04;
    tmp->startmarker4 = 0x71;
    tmp->startmarker5 = 0x72;
    tmp->startmarker6 = 0x73;
    tmp->startmarker7 = 0x74;
    tmp->startmarker8 = 0xF1;
    tmp->startmarker9 = 0xF2;
    tmp->startmarker10 = 0xF3;
    tmp->startmarker11 = 0xF4;
    tmp->version = VERSION;
    tmp->minor_version = MINOR_VERSION;
    tmp->irq_priority_order = IRQ_PRIORITY_ORDER;
    tmp->filesize = sizeof(RecorderDataType);
    
    tmp->maxEvents = EVENT_BUFFER_SIZE;
    
    tmp->debugMarker0 = 0xF0F0F0F0;
    tmp->ObjectPropertyTable.NumberOfObjectClasses = NCLASSES;
    tmp->ObjectPropertyTable.ObjectPropertyTableSizeInBytes = DynObjTableSize;
    tmp->ObjectPropertyTable.NumberOfObjectsPerClass[0] = NQueue;
    tmp->ObjectPropertyTable.NumberOfObjectsPerClass[1] = NSemaphore;
    tmp->ObjectPropertyTable.NumberOfObjectsPerClass[2] = NMutex;
    tmp->ObjectPropertyTable.NumberOfObjectsPerClass[3] = NTask;
    tmp->ObjectPropertyTable.NumberOfObjectsPerClass[4] = NISR;
    tmp->ObjectPropertyTable.NameLengthPerClass[0] = NameLenQueue;
    tmp->ObjectPropertyTable.NameLengthPerClass[1] = NameLenSemaphore;
    tmp->ObjectPropertyTable.NameLengthPerClass[2] = NameLenMutex;
    tmp->ObjectPropertyTable.NameLengthPerClass[3] = NameLenTask;
    tmp->ObjectPropertyTable.NameLengthPerClass[4] = NameLenISR;
    tmp->ObjectPropertyTable.TotalPropertyBytesPerClass[0] = PropertyTableSizeQueue;
    tmp->ObjectPropertyTable.TotalPropertyBytesPerClass[1] = PropertyTableSizeSemaphore;
    tmp->ObjectPropertyTable.TotalPropertyBytesPerClass[2] = PropertyTableSizeMutex;
    tmp->ObjectPropertyTable.TotalPropertyBytesPerClass[3] = PropertyTableSizeTask;
    tmp->ObjectPropertyTable.TotalPropertyBytesPerClass[4] = PropertyTableSizeISR;
    tmp->ObjectPropertyTable.StartIndexOfClass[0] = StartIndexQueue;
    tmp->ObjectPropertyTable.StartIndexOfClass[1] = StartIndexSemaphore;
    tmp->ObjectPropertyTable.StartIndexOfClass[2] = StartIndexMutex;
    tmp->ObjectPropertyTable.StartIndexOfClass[3] = StartIndexTask;
    tmp->ObjectPropertyTable.StartIndexOfClass[4] = StartIndexISR;    
    tmp->debugMarker1 = 0xF1F1F1F1;
    tmp->SymbolTable.symTableSize = SYMBOL_TABLE_SIZE;
    tmp->SymbolTable.nextFreeSymbolIndex = 1;
#if (INCLUDE_FLOAT_SUPPORT == 1)
    tmp->exampleFloatEncoding = (float)1.0; /* otherwize already zero */
#endif
    tmp->debugMarker2 = 0xF2F2F2F2;    
    (void)strncpy(tmp->systemInfo, TRACE_DESCRIPTION, TRACE_DESCRIPTION_MAX_LENGTH);
    tmp->debugMarker3 = 0xF3F3F3F3;
    tmp->endmarker0 = 0x0A;
    tmp->endmarker1 = 0x0B;
    tmp->endmarker2 = 0x0C;
    tmp->endmarker3 = 0x0D;
    tmp->endmarker4 = 0x71;
    tmp->endmarker5 = 0x72;
    tmp->endmarker6 = 0x73;
    tmp->endmarker7 = 0x74;
    tmp->endmarker8 = 0xF1;
    tmp->endmarker9 = 0xF2;
    tmp->endmarker10 = 0xF3;
    tmp->endmarker11 = 0xF4;
    
    RecorderDataPtr = tmp;

    return (RecorderDataType*)RecorderDataPtr;
}

#endif

volatile int recorder_busy = 0;

char sprintfBuffer[150];

/* For debug printouts - the names of the object classes */
char OBJECTCLASSNAME[NCLASSES][10] =
{
        "QUEUE",
        "SEMAPHORE",
        "MUTEX",
        "TASK",
        "ISR"
};

/* Initialization of the handle mechanism, see e.g, xTraceGetObjectHandle */
objectHandleStackType objectHandleStacks =
{
        /* indexOfNextAvailableHandle */
        {
                0,
                NQueue,
                NQueue + NSemaphore,
                NQueue + NSemaphore + NMutex,
                NQueue + NSemaphore + NMutex + NTask
        },

        /* lowestIndexOfClass */
        {
                0,
                NQueue,
                NQueue + NSemaphore,
                NQueue + NSemaphore + NMutex,
                NQueue + NSemaphore + NMutex + NTask
        },

        /* highestIndexOfClass */
        {
                NQueue - 1,
                NQueue + NSemaphore - 1,
                NQueue + NSemaphore + NMutex - 1,
                NQueue + NSemaphore + NMutex + NTask - 1,
                NQueue + NSemaphore + NMutex + NTask + NISR - 1
        },
        {0},
        {0}
};


/* Used for internal state flags of objects */
uint8_t excludedFlags[(NEventCodes+NQueue+NSemaphore+NMutex+NTask) / 8 + 1];
uint8_t ifeFlags[NTask / 8 + 1];

/* Gives the last error message of the recorder. NULL if no error message. */
char* traceErrorMessage = NULL;

void* xTraceNextFreeEventBufferSlot(void)
{
    if (RecorderDataPtr->nextFreeIndex >= EVENT_BUFFER_SIZE)
    {
        vTraceError("Attempt to index outside event buffer!");
        return NULL;
    }
    return (void*)(&RecorderDataPtr->
                   eventData[RecorderDataPtr->nextFreeIndex*4]);
}

uint16_t uiIndexOfObject(objectHandleType objecthandle, uint8_t objectclass)
{
    if ((objectclass < NCLASSES) && (objecthandle > 0) && (objecthandle <= 
    RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectclass]))
    {
        return (uint16_t)(RecorderDataPtr->
            ObjectPropertyTable.StartIndexOfClass[objectclass] + 
            (RecorderDataPtr->
            ObjectPropertyTable.TotalPropertyBytesPerClass[objectclass] * 
            (objecthandle-1)));
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
    static objectHandleType handle;
    static int indexOfHandle;

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
    
    if ( objectHandleStacks.indexOfNextAvailableHandle[objectclass] 
        > objectHandleStacks.highestIndexOfClass[objectclass] )
    {
        /* ERROR */
        switch(objectclass)
        {
        case TRACE_CLASS_TASK:
            vTraceError("Not enough TASK handles - increase NTask in trcConfig.h");         
            break;
        case TRACE_CLASS_ISR:
            vTraceError("Not enough ISR handles - increase NISR in trcConfig.h");         
            break;
        case TRACE_CLASS_SEMAPHORE:
            vTraceError("Not enough SEMAPHORE handles - increase NSemaphore in trcConfig.h");         
            break;
        case TRACE_CLASS_MUTEX:
            vTraceError("Not enough MUTEX handles - increase NMutex in trcConfig.h");         
            break;
        case TRACE_CLASS_QUEUE:
            vTraceError("Not enough QUEUE handles - increase NQueue in trcConfig.h");         
            break;
        default:
            vTraceError("Invalid object class.");
            break;
        }
        
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
    }

    return handle;
}

void vTraceFreeObjectHandle(traceObjectClass objectclass, objectHandleType handle)
{
    int indexOfHandle;

    /* Check that there is room to push the handle on the stack */
    if ( (objectHandleStacks.indexOfNextAvailableHandle[objectclass] - 1) < 
        objectHandleStacks.lowestIndexOfClass[objectclass] )
    {
        /* Error */
        vTraceError("Attempt to free more handles than allocated! (duplicate xTaskDelete or xQueueDelete?)");
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

    if (handle == 0)
    {
        vTraceError("Illegal handle (0) in vTraceSetObjectName.");   
        return;
    }
    
    switch(objectclass)
    {
        case TRACE_CLASS_TASK:
        case TRACE_CLASS_ISR:
        case TRACE_CLASS_SEMAPHORE:
        case TRACE_CLASS_MUTEX:
        case TRACE_CLASS_QUEUE:
        break;
    default:
        vTraceError("Illegal object class in vTraceSetObjectName");   
        break;            
    }

    if (handle > 
        RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectclass])
    {
        switch(objectclass)
        {
            case TRACE_CLASS_TASK:
            vTraceError("Not enough TASK handles - increase NTask in trcConfig.h");         
            break;
            case TRACE_CLASS_ISR:
            vTraceError("Not enough ISR handles - increase NISR in trcConfig.h");       
            break;
            case TRACE_CLASS_SEMAPHORE:
            vTraceError("Not enough SEMAPHORE handles - increase NSemaphore in trcConfig.h");
            break;
            case TRACE_CLASS_MUTEX:
            vTraceError("Not enough MUTEX handles - increase NMutex in trcConfig.h");
            break;
            case TRACE_CLASS_QUEUE:
            vTraceError("Not enough QUEUE handles - increase NQueue in trcConfig.h");
            break;
        }
    }
    else
    {
        idx = uiIndexOfObject(handle, objectclass);

        if (traceErrorMessage == NULL)
        {
            (void)strncpy((char*)&(RecorderDataPtr->ObjectPropertyTable.objbytes[idx]),
                    name,
                    RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[ objectclass ] );
#ifdef WIN32
            printf("vTraceSetObjectName(%d, %d, %s)\n", objectclass, handle, name);
#endif
        }
    }
}

traceLabel prvTraceOpenSymbol(const char* name, traceLabel userEventChannel)
{
    static uint16_t result;
    static uint8_t len;
    static uint8_t crc;
    len = 0;
    crc = 0;
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
    vTraceStop();
    if (traceErrorMessage == NULL)
    {
      traceErrorMessage = (char*)msg;
      (void)strncpy(RecorderDataPtr->systemInfo, 
          traceErrorMessage, 
          TRACE_DESCRIPTION_MAX_LENGTH);
      RecorderDataPtr->internalErrorOccured = 1;
    }
}

/******************************************************************************
 * prvCheckDataToBeOverwrittenForMultiEntryUserEvents
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

void prvCheckDataToBeOverwrittenForMultiEntryUserEvents(
    uint8_t nofEntriesToCheck)
{
    /* Generic "int" type is desired - should be 16 bit variable on 16 bit HW */
    unsigned int i = 0; 
    unsigned int e = 0;
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
#if (RECORDER_STORE_MODE == STORE_MODE_RING_BUFFER)       
        RecorderDataPtr->bufferIsFull = 1;
        RecorderDataPtr->nextFreeIndex = 0;
#else
        vTraceStop();
#endif
    }

#if (RECORDER_STORE_MODE == STORE_MODE_RING_BUFFER)
    prvCheckDataToBeOverwrittenForMultiEntryUserEvents(1);
#endif
    
#ifdef STOP_AFTER_N_EVENTS
#if (STOP_AFTER_N_EVENTS > -1)
    if (RecorderDataPtr->numEvents >= STOP_AFTER_N_EVENTS)
    {
        vTraceStop();
    }
#endif
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

    if (RecorderDataPtr->frequency == 0)
    {
        /* If HWTC_PERIOD is mapped to the timer reload register,
        such as in the Cortex M port, it is not initialized before
        FreeRTOS has been started. We therefore store the frequency
        of the timer at the first timestamped event after the 
        scheduler has started. (Note that this function is called
        also by vTraceStart and uiTraceStart, which might be
        called before the scheduler has been started.) */

#if (SELECTED_PORT == PORT_Win32)    
        RecorderDataPtr->frequency = 100000;
#elif (SELECTED_PORT == PORT_HWIndependent)    
        RecorderDataPtr->frequency = configTICK_RATE_HZ;
#else        
        if (xTaskGetSchedulerState() != 0) /* Has the scheduler started? */
        {            
            RecorderDataPtr->frequency = 
                 (uint32_t)HWTC_PERIOD * (uint32_t)configTICK_RATE_HZ / (uint32_t)HWTC_DIVISOR; 
        }
#endif
    }

    /**************************************************************************
    * The below statements read the timestamp from the timer port module.
    * If necessary, whole seconds are extracted using division while the rest
    * comes from the modulo operation.
    **************************************************************************/
    
    uiTracePortGetTimeStamp(&timestamp);

    /***************************************************************************
    * This condition is only for the Win32 port, since it does not use the tick
    * count but instead only HWTC_COUNT (from the performance counter).
    * Without this condition, you sometimes get a negative dts value (converted
    * into a very large unsiged value) when the performance counter wraps 
    * around. In other "normal" ports also using the FreeRTOS tick counter, this 
    * condition can not occur and therefore has no impact.
    ***************************************************************************/
    if (timestamp < old_timestamp)
    {
        timestamp += RecorderDataPtr->frequency;
    }


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
            RecorderDataPtr->absTimeLastEvent += dts;
        
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

    return (uint16_t)(dts % (param_maxDTS + 1));
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
        (void)strncpy((char*)&( RecorderDataPtr->SymbolTable.symbytes
            [ RecorderDataPtr->SymbolTable.nextFreeSymbolIndex + 4] ), name, len);

        /* Set zero termination (at offest 4+len) */
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
   int length = 0;
   int crc = 0;
   if ( pname != (const char *) 0 )
   {
      for ( ; (c = *pname++) != '\0'; )
      {
         crc += c;
         length++;
      }
   }
   *pcrc = (uint8_t)(crc % 64);
   *plength = (uint8_t)length;
}

#endif
