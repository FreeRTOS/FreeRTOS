/*******************************************************************************
 * FreeRTOS+Trace v2.3.0 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcBase.h
 *
 * Core functionallity of the FreeRTOS+Trace recorder library.
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

#ifndef TRCBASE_H
#define TRCBASE_H

#include <stdio.h>
#include <string.h>

#include "FreeRTOS.h"
#include "trcConfig.h"
#include "trcTypes.h"
#include "trcPort.h"

extern volatile int recorder_busy;

#define trcCRITICAL_SECTION_BEGIN() {taskENTER_CRITICAL(); recorder_busy++;}
#define trcCRITICAL_SECTION_END() {recorder_busy--; taskEXIT_CRITICAL();}

#define NCLASSES 5
#define VERSION 0x1AA1
#define MINOR_VERSION 1
#define STORE_MODE_STOP_WHEN_FULL 1
#define STORE_MODE_RING_BUFFER 2
#define TRACE_DATA_ALLOCATION_STATIC 1
#define TRACE_DATA_ALLOCATION_DYNAMIC 2

/******************************************************************************
 * Object Property Table
 * The Object Table contains name and other properties of the objects (tasks,
 * queues, mutexes, etc). The below data structures defines the properties of
 * each object class and are used to cast the byte buffer into a cleaner format.
 *
 * The values in the object table are continously overwritten and always 
 * represent the current state. If a property is changed during runtime, the OLD 
 * value should be stored in the trace buffer, not the new value (since the new 
 * value is found in the Object Property Table).
 * For close events this mechanism is the old names are stored in the symbol
 * table), for "priority set" (the old priority is stored in the event data)
 * and for "isActive", where the value decides is the taskswitch event type
 * should be "new" or "resume".
 ******************************************************************************/

/* The size of the Object Property Table entries, in bytes, per object */

/* Queue properties (except name):     current number of message in queue */
#define PropertyTableSizeQueue         (NameLenQueue + 1)      

/* Semaphore properties (except name): state (signaled = 1, cleared = 0) */
#define PropertyTableSizeSemaphore     (NameLenSemaphore + 1) 

/* Mutex properties (except name):     owner (task handle, 0 = free) */
#define PropertyTableSizeMutex         (NameLenMutex + 1)         

/* Task properties (except name):      Byte 0: Current priority
                                       Byte 1: state (if already active) 
                                       Byte 2: InstanceFinishEvent_ServiceCode
                                       Byte 3: InstanceFinishEvent_ObjHandle */
#define PropertyTableSizeTask         (NameLenTask + 4)

/* ISR properties:                     Byte 0: priority
                                       Byte 1: state (if already active) */
#define PropertyTableSizeISR          (NameLenISR + 2)

/* The layout of the byte array representing the Object Property Table */
#define StartIndexQueue            0
#define StartIndexSemaphore        StartIndexQueue     + NQueue * PropertyTableSizeQueue
#define StartIndexMutex            StartIndexSemaphore + NSemaphore * PropertyTableSizeSemaphore
#define StartIndexTask             StartIndexMutex     + NMutex * PropertyTableSizeMutex
#define StartIndexISR              StartIndexTask      + NTask * PropertyTableSizeTask
#define DynObjTableSize            StartIndexISR       + NISR * PropertyTableSizeISR

typedef struct
{
    /* = NCLASSES */
    uint32_t NumberOfObjectClasses;
    
    uint32_t ObjectPropertyTableSizeInBytes;
        
    /* This is used to calculate the index in the dynamic object table 
    (handle - 1 - nofStaticObjects = index)*/
    uint8_t NumberOfObjectsPerClass[ 4*((NCLASSES+3)/4)];      

    /* Allocation size rounded up to the closest multiple of 4 */    
    uint8_t NameLengthPerClass[ 4*((NCLASSES+3)/4) ];
    
    uint8_t TotalPropertyBytesPerClass[ 4*((NCLASSES+3)/4) ];
    
    /* Allocation size rounded up to the closest multiple of 2 */
    uint16_t StartIndexOfClass[ 2*((NCLASSES+1)/2) ];

    /* The actual handles issued, should be Initiated to all zeros */     
    uint8_t objbytes[ 4*((DynObjTableSize+3)/4) ];
} ObjectPropertyTableType;

/* Symbol table data structure */
typedef struct
{
    /* = SYMBOL_HISTORY_TABLE_SIZE_IN_BYTES */
    uint32_t symTableSize;                       
        
    /* Entry 0 is reserved. Any reference to entry 0 implies NULL*/
    uint32_t nextFreeSymbolIndex;         
        
    /* Size rounded up to closest multiple of 4, to avoid alignment issues*/
    uint8_t symbytes[4*((SYMBOL_TABLE_SIZE+3)/4)];           
        
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
    objectHandleType objHandle;
    uint16_t dts;    /* differential timestamp - time since last event */            
} TSEvent, TREvent;

typedef struct
{
    uint8_t type;
    uint8_t objHandle;
    uint16_t dts;
} KernelCall;

typedef struct
{
    uint8_t type;
    objectHandleType objHandle;
    uint8_t param;
    uint8_t dts;                
} KernelCallWithParamAndHandle;

typedef struct
{
    uint8_t type;
    uint8_t dts;                
    uint16_t param;
} KernelCallWithParam16;

typedef struct
{
    uint8_t type;
    objectHandleType objHandle;    /* the handle of the closed object */
    uint16_t symbolIndex;          /* the name of the closed object */
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
    uint8_t dts;                
    uint16_t payload;         /* the name of the user event */
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


/*******************************************************************************
 * The main datastructure, read by FreeRTOS+Trace from the RAM dump
 ******************************************************************************/

typedef struct
{    
    uint8_t startmarker0;
    uint8_t startmarker1;
    uint8_t startmarker2;
    uint8_t startmarker3;
    uint8_t startmarker4;
    uint8_t startmarker5;
    uint8_t startmarker6;
    uint8_t startmarker7;
    uint8_t startmarker8;
    uint8_t startmarker9;
    uint8_t startmarker10;
    uint8_t startmarker11;

    /* For FreeRTOS: 0x1AA1 */
    uint16_t version;     
    
    /* Currently 1 for v2.2.2 (0 earlier)*/
    uint8_t minor_version;
    
    /* This should be 0 if lower irq priority values implies higher priority 
    levels, such as on ARM Cortex M. If the opposite scheme is used, i.e., 
    if higher irq priority values means higher priority, this should be 1. */ 
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

    /* For storing a Team License key */
    uint8_t teamLicenceKey[32];

    /* 0xF0F0F0F0 - for control only */
    int32_t debugMarker0;                    

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

    /* For includsion of float support, and for endian detection of floats. 
    The value should be (float)1 or (uint32_t)0 */    
#if (INCLUDE_FLOAT_SUPPORT == 1)
    float exampleFloatEncoding;              
#else
    uint32_t exampleFloatEncoding;              
#endif
    /* This is non-zero if an internal error occured in the recorder, e.g., if
    one of the Nxxx constants was too small. The systemInfo string will then 
    contain an error message that is displayed when attempting to view the 
    trace file. */
    uint32_t internalErrorOccured;
    
    /* 0xF2F2F2F2 - for control only */ 
    int32_t debugMarker2;                    
      
    /* Generic system information string, presented in the tool. Note that this 
    is also used for storing any internal error messages from the recorder, so
    do not make TRACE_DESCRIPTION_MAX_LENGTH too small. 80 is recommended. */
    char systemInfo[TRACE_DESCRIPTION_MAX_LENGTH];                   

    /* 0xF3F3F3F3 - for control only */
    int32_t debugMarker3;                    

    /* The event data, in 4-byte records */
    uint8_t eventData[ EVENT_BUFFER_SIZE * 4 ];

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

/******************************************************************************
 * ObjectHandleStack
 * This data-structure is used to provide a mechanism for 1-byte trace object
 * handles. This way, only 1 byte is necessary instead of 4 bytes (a pointer)
 * when storing a reference to an object. This allows for up to 255 objects of
 * each object class - Task, ISR, Semaphore, CountingSemaphore, Mutex and Queue,
 * active at any given moment. There can be more "historic" objects, that have
 * been deleted - that number is only limited by the size of the symbol table.
 * Note that handle zero (0) is not used, it is a code for an invalid handle.
 *
 * This data structure keeps track of the FREE handles, not the handles in use.
 * This datastructure contains one stack per object class. When a handle is
 * allocated to an object, the next free handle is popped from the stack. When
 * a handle is released (on object delete), it is pushed back on the stack.
 * Note that there is no initialization code that pushed the free handles
 * initially, that is not necessary due to the following optimization:
 *
 * The stack of handles (objectHandles) is initially all zeros. Since zero
 * is not a valid handle, that is a signal of additional handles needed.
 * If a zero is received when popping a new handle, it is replaced by the
 * index of the popped handle instead.
 *
 *****************************************************************************/
typedef struct
{
    /* For each object class, the index of the next handle to allocate */
    int16_t indexOfNextAvailableHandle[ NCLASSES ];              

    /* The lowest index of this class (constant) */        
    int16_t lowestIndexOfClass[ NCLASSES ];                    
        
    /* The highest index of this class (constant) */
    int16_t highestIndexOfClass[ NCLASSES ];    
        
    /* The highest use count for this class (for statistics) */
    int16_t handleCountWaterMarksOfClass[ NCLASSES ];                
        
    /* The free object handles - a set of stacks within this array */
    objectHandleType objectHandles[ NTask+NISR+NSemaphore+NMutex+NQueue ];

} objectHandleStackType;

/* Internal data */

extern objectHandleStackType objectHandleStacks;

/* Structures to handle the exclude flags for all objects, tasks and event codes */
#define NEventCodes 0x100
extern uint8_t excludedFlags[(NEventCodes+NQueue+NSemaphore+NMutex+NTask) / 8 + 1];
extern uint8_t ifeFlags[NTask / 8 + 1];

/* Internal functions */

uint16_t prvTraceGetDTS(uint16_t param_maxDTS);

void prvTraceGetChecksum(const char *pname, uint8_t* pcrc, uint8_t* plength);

traceLabel prvTraceCreateSymbolTableEntry(const char* name, 
                                          uint8_t crc6, 
                                          uint8_t len, 
                                          traceLabel channel);

traceLabel prvTraceLookupSymbolTableEntry(const char* name, 
                                          uint8_t crc6, 
                                          uint8_t len, 
                                          traceLabel channel);

traceLabel prvTraceOpenSymbol(const char* name, traceLabel userEventChannel);

void prvTraceUpdateCounters(void);

void prvCheckDataToBeOverwrittenForMultiEntryUserEvents(uint8_t nEntries);

objectHandleType xTraceGetObjectHandle(traceObjectClass objectclass);

void vTraceFreeObjectHandle(traceObjectClass objectclass, 
                            objectHandleType handle);

void vTraceSetObjectName(traceObjectClass objectclass, 
                         objectHandleType handle, 
                         const char* name);

void* xTraceNextFreeEventBufferSlot(void);

uint16_t uiIndexOfObject(objectHandleType objecthandle, 
    uint8_t objectclass);


/*******************************************************************************
 * vTraceError
 *
 * Called by various parts in the recorder. Stops the recorder and stores a 
 * pointer to an error message, which is printed by the monitor task.
 ******************************************************************************/
void vTraceError(const char* msg);

/*******************************************************************************
 * xTraceGetLastError
 *
 * Gives the last error message, if any. NULL if no error message is stored.
 * The message is cleared on read.
 ******************************************************************************/
char* xTraceGetLastError(void);

/*******************************************************************************
 * xTraceInitTraceData
 *
 * Allocates and initializes the recorder datastructure, based on the constants
 * in trcConfig.h. This allows for allocating the data on the heap, instead of
 * using a static declaration.
 ******************************************************************************/
RecorderDataType* xTraceInitTraceData(void);

/* Internal macros */

#define PROPERTY_NAME_GET(objectclass, objecthandle) \
(const char*)(& RecorderDataPtr->ObjectPropertyTable.objbytes \
[uiIndexOfObject(objecthandle, objectclass)])

#define PROPERTY_OBJECT_STATE(objectclass, handle) \
RecorderDataPtr->ObjectPropertyTable.objbytes[uiIndexOfObject(handle, objectclass) \
+ RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[objectclass]]

#define PROPERTY_ACTOR_PRIORITY(objectclass, handle) \
RecorderDataPtr->ObjectPropertyTable.objbytes[uiIndexOfObject(handle, objectclass) \
+ RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[objectclass] + 1]

#define PROPERTY_TASK_IFE_SERVICECODE(handle) \
RecorderDataPtr->ObjectPropertyTable.objbytes \
[uiIndexOfObject(handle, TRACE_CLASS_TASK) \
+ RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[TRACE_CLASS_TASK]+2]

#define PROPERTY_TASK_IFE_OBJHANDLE(handle) \
RecorderDataPtr->ObjectPropertyTable.objbytes \
[uiIndexOfObject(handle, TRACE_CLASS_TASK) \
+  RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[TRACE_CLASS_TASK]+3]

#define SET_FLAG_ISEXCLUDED(bitIndex) excludedFlags[(bitIndex) >> 3] |= (1 << ((bitIndex) & 7))
#define CLEAR_FLAG_ISEXCLUDED(bitIndex) excludedFlags[(bitIndex) >> 3] &= ~(1 << ((bitIndex) & 7))
#define GET_FLAG_ISEXCLUDED(bitIndex) (excludedFlags[(bitIndex) >> 3] & (1 << ((bitIndex) & 7)))

#define SET_FLAG_MARKIFE(bitIndex) ifeFlags[(bitIndex) >> 3] |= (1 << ((bitIndex) & 7))
#define CLEAR_FLAG_MARKIFE(bitIndex) ifeFlags[(bitIndex) >> 3] &= ~(1 << ((bitIndex) & 7))
#define GET_FLAG_MARKIFE(bitIndex) (ifeFlags[(bitIndex) >> 3] & (1 << ((bitIndex) & 7)))

#define SET_EVENT_CODE_FLAG_ISEXCLUDED(eventCode) SET_FLAG_ISEXCLUDED(eventCode)
#define CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(eventCode) CLEAR_FLAG_ISEXCLUDED(eventCode)
#define GET_EVENT_CODE_FLAG_ISEXCLUDED(eventCode) GET_FLAG_ISEXCLUDED(eventCode)

#define SET_QUEUE_FLAG_ISEXCLUDED(queueHandle) SET_FLAG_ISEXCLUDED(NEventCodes+queueHandle-1)
#define CLEAR_QUEUE_FLAG_ISEXCLUDED(queueHandle) CLEAR_FLAG_ISEXCLUDED(NEventCodes+queueHandle-1)
#define GET_QUEUE_FLAG_ISEXCLUDED(queueHandle) GET_FLAG_ISEXCLUDED(NEventCodes+queueHandle-1)

#define SET_SEMAPHORE_FLAG_ISEXCLUDED(semaphoreHandle) SET_FLAG_ISEXCLUDED(NEventCodes+NQueue+semaphoreHandle-1)
#define CLEAR_SEMAPHORE_FLAG_ISEXCLUDED(semaphoreHandle) CLEAR_FLAG_ISEXCLUDED(NEventCodes+NQueue+semaphoreHandle-1)
#define GET_SEMAPHORE_FLAG_ISEXCLUDED(semaphoreHandle) GET_FLAG_ISEXCLUDED(NEventCodes+NQueue+semaphoreHandle-1)

#define SET_MUTEX_FLAG_ISEXCLUDED(mutexHandle) SET_FLAG_ISEXCLUDED(NEventCodes+NQueue+NSemaphore+mutexHandle-1)
#define CLEAR_MUTEX_FLAG_ISEXCLUDED(mutexHandle) CLEAR_FLAG_ISEXCLUDED(NEventCodes+NQueue+NSemaphore+mutexHandle-1)
#define GET_MUTEX_FLAG_ISEXCLUDED(mutexHandle) GET_FLAG_ISEXCLUDED(NEventCodes+NQueue+NSemaphore+mutexHandle-1)

#define SET_TASK_FLAG_ISEXCLUDED(taskHandle) SET_FLAG_ISEXCLUDED(NEventCodes+NQueue+NSemaphore+NMutex+taskHandle-1)
#define CLEAR_TASK_FLAG_ISEXCLUDED(taskHandle) CLEAR_FLAG_ISEXCLUDED(NEventCodes+NQueue+NSemaphore+NMutex+taskHandle-1)
#define GET_TASK_FLAG_ISEXCLUDED(taskHandle) GET_FLAG_ISEXCLUDED(NEventCodes+NQueue+NSemaphore+NMutex+taskHandle-1)

#define SET_TASK_FLAG_MARKIFE(bitIndex) SET_FLAG_MARKIFE(bitIndex-1)
#define CLEAR_TASK_FLAG_MARKIFE(bitIndex) CLEAR_FLAG_MARKIFE(bitIndex-1)
#define GET_TASK_FLAG_MARKIFE(bitIndex) GET_FLAG_MARKIFE(bitIndex-1)

/* For debug printouts - the names of the object classes */
extern char OBJECTCLASSNAME[NCLASSES][10];
/*=
{
        "QUEUE"
        "SEMAPHORE",
        "MUTEX",
        "TASK",
        "ISR"
};*/

#endif

