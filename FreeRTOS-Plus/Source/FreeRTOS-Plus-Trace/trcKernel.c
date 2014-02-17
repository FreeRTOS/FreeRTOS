/*******************************************************************************
 * Tracealyzer v2.6.0 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcKernel.c
 *
 * Functions used by trcKernelHooks.h.
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

#include "trcKernel.h"

#if (USE_TRACEALYZER_RECORDER == 1)

#include <stdint.h>

/* Internal variables */
uint8_t nISRactive = 0;
objectHandleType handle_of_last_logged_task = 0;
uint8_t inExcludedTask = 0;

static uint32_t prvTraceGetParam(uint32_t, uint32_t);

#if !defined INCLUDE_READY_EVENTS || INCLUDE_READY_EVENTS == 1
/*******************************************************************************
 * vTraceStoreTaskReady
 *
 * This function stores a ready state for the task handle sent in as parameter.
 ******************************************************************************/
void vTraceStoreTaskReady(objectHandleType handle)
{
    uint16_t dts3;
    TREvent* tr;
	TRACE_SR_ALLOC_CRITICAL_SECTION();
	
	TRACE_ASSERT(handle > 0 && handle <= NTask, "vTraceStoreTaskReady: Invalid value for handle", );

    if (recorder_busy)
    {
      /***********************************************************************
      * This should never occur, as the tick- and kernel call ISR is on lowest
      * interrupt priority and always are disabled during the critical sections
      * of the recorder.
      ***********************************************************************/

      vTraceError("Recorder busy - high priority ISR using syscall? (1)");
      return;
    }

	trcCRITICAL_SECTION_BEGIN();
    if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
	{
		if (!TRACE_GET_TASK_FLAG_ISEXCLUDED(handle))
		{
			dts3 = (uint16_t)prvTraceGetDTS(0xFFFF);
			if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
			{
				uint8_t hnd8 = prvTraceGet8BitHandle(handle);

				tr = (TREvent*)xTraceNextFreeEventBufferSlot();

				if (tr != NULL)
				{
					tr->type = DIV_TASK_READY;
					tr->dts = dts3;
					tr->objHandle = hnd8;

					prvTraceUpdateCounters();
				}
			}
		}
	}
	trcCRITICAL_SECTION_END();
}
#endif

/*******************************************************************************
 * vTraceStoreLowPower
 *
 * This function stores a low power state.
 ******************************************************************************/
void vTraceStoreLowPower(uint32_t flag)
{
    uint16_t dts;
    LPEvent* lp;
	TRACE_SR_ALLOC_CRITICAL_SECTION();
	
	TRACE_ASSERT(flag <= 1, "vTraceStoreLowPower: Invalid flag value", );

    if (recorder_busy)
    {
		/***********************************************************************
		* This should never occur, as the tick- and kernel call ISR is on lowest
		* interrupt priority and always are disabled during the critical sections
		* of the recorder.
		***********************************************************************/
	  
		vTraceError("Recorder busy - high priority ISR using syscall? (1)");
		return;
    }
	
	trcCRITICAL_SECTION_BEGIN();
    if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
	{
		dts = (uint16_t)prvTraceGetDTS(0xFFFF);
		if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
		{
			lp = (LPEvent*)xTraceNextFreeEventBufferSlot();
			if (lp != NULL)
			{
				lp->type = LOW_POWER_BEGIN + ( uint8_t ) flag; /* BEGIN or END depending on flag */
				lp->dts = dts;

				prvTraceUpdateCounters();
			}
		}
	}
	trcCRITICAL_SECTION_END();
}

/*******************************************************************************
 * vTraceStoreMemMangEvent
 *
 * This function stores malloc and free events. Each call requires two records,
 * for size and address respectively. The event code parameter (ecode) is applied 
 * to the first record (size) and the following address record gets event 
 * code "ecode + 1", so make sure this is respected in the event code table.
 ******************************************************************************/
#if (INCLUDE_MEMMANG_EVENTS == 1)
void vTraceStoreMemMangEvent(uint32_t ecode, uint32_t address, uint32_t size)
{
	uint8_t dts1;
	MemEventSize * ms;
	MemEventAddr * ma;
	uint16_t size_low;
	uint16_t addr_low;
	uint8_t addr_high;
	
	TRACE_SR_ALLOC_CRITICAL_SECTION();

	trcCRITICAL_SECTION_BEGIN();
	if (RecorderDataPtr->recorderActive)
	{
		/* If it is an ISR or NOT an excluded task, this kernel call will be stored in the trace */
		if (nISRactive || !inExcludedTask)
		{
			dts1 = (uint8_t)prvTraceGetDTS(0xFF);
			
			size_low = (uint16_t)prvTraceGetParam(0xFFFF, size);
			
			ms = (MemEventSize *)xTraceNextFreeEventBufferSlot();
			if (ms != NULL)
			{
				ms->dts = dts1;
				ms->type = (uint8_t)ecode;
				ms->size = size_low;
				prvTraceUpdateCounters();
				
				/* Storing a second record with address (signals "failed" if null) */
				#if (HEAP_SIZE_BELOW_16M)
					addr_low = address & 0xFFFF;
					addr_high = (address >> 16) & 0xFF;
				#else
					addr_low = (uint16_t)prvTraceGetParam(0xFFFF, address);
					addr_high = 0;
				#endif
				
				ma = (MemEventAddr *) xTraceNextFreeEventBufferSlot();
				
				if (ma != NULL)
				{
					ma->addr_low = addr_low;
					ma->addr_high = addr_high;
					ma->type = ( ( uint8_t) ecode ) + 1;  /* Note this! */
					prvTraceUpdateCounters();				
				}
			}
		}
	}
	trcCRITICAL_SECTION_END();	
}
#endif

/*******************************************************************************
 * vTraceStoreKernelCall
 *
 * This is the main integration point for storing kernel calls, and
 * is called by the hooks in trcKernelHooks.h (see trcKernelPort.h for event codes).
 ******************************************************************************/
void vTraceStoreKernelCall(uint32_t ecode, traceObjectClass objectClass, uint32_t objectNumber)
{
    KernelCall * kse;
    uint16_t dts1;
    TRACE_SR_ALLOC_CRITICAL_SECTION();

    TRACE_ASSERT(ecode < 0xFF, "vTraceStoreKernelCall: ecode >= 0xFF", );
    TRACE_ASSERT(objectClass < TRACE_NCLASSES, "vTraceStoreKernelCall: objectClass >= TRACE_NCLASSES", );
    TRACE_ASSERT(objectNumber <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectClass], "vTraceStoreKernelCall: Invalid value for objectNumber", );

    if (recorder_busy)
    {
        /*************************************************************************
        * This may occur if a high-priority ISR is illegally using a system call,
        * or creates a user event.
        * Only ISRs that are disabled by TRACE_ENTER_CRITICAL_SECTION may use system calls
        * or user events (see TRACE_MAX_SYSCALL_INTERRUPT_PRIORITY).
        *************************************************************************/

        vTraceError("Recorder busy - high priority ISR using syscall? (2)");
        return;
    }

    if (handle_of_last_logged_task == 0)
    {
        return;
    }

	trcCRITICAL_SECTION_BEGIN();
    if (RecorderDataPtr->recorderActive)
    {
        /* If it is an ISR or NOT an excluded task, this kernel call will be stored in the trace */
        if (nISRactive || !inExcludedTask)
        {
            /* Check if the referenced object or the event code is excluded */
            if (!uiTraceIsObjectExcluded(objectClass, (objectHandleType)objectNumber) && !TRACE_GET_EVENT_CODE_FLAG_ISEXCLUDED(ecode))
            {                
                dts1 = (uint16_t)prvTraceGetDTS(0xFFFF);

                if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
                {
					uint8_t hnd8 = prvTraceGet8BitHandle(objectNumber);

                    kse = (KernelCall*) xTraceNextFreeEventBufferSlot();
                    if (kse != NULL)
                    {
                        kse->dts = dts1;
                        kse->type = (uint8_t)ecode;
                        kse->objHandle = hnd8;
                        prvTraceUpdateCounters();
                    }
                }                
            }
        }
    }
	trcCRITICAL_SECTION_END();
}

/*******************************************************************************
 * vTraceStoreKernelCallWithParam
 *
 * Used for storing kernel calls with a handle and a numeric parameter. If the 
 * numeric parameter does not fit in one byte, and extra XPS event is inserted
 * before the kernel call event containing the three upper bytes.
 ******************************************************************************/
void vTraceStoreKernelCallWithParam(uint32_t evtcode,
                                    traceObjectClass objectClass,
                                    uint32_t objectNumber,
                                    uint32_t param)
{
    KernelCallWithParamAndHandle * kse;
    uint8_t dts2;	
    TRACE_SR_ALLOC_CRITICAL_SECTION();

	TRACE_ASSERT(evtcode < 0xFF, "vTraceStoreKernelCall: evtcode >= 0xFF", );
	TRACE_ASSERT(objectClass < TRACE_NCLASSES, "vTraceStoreKernelCallWithParam: objectClass >= TRACE_NCLASSES", );
	TRACE_ASSERT(objectNumber <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectClass], "vTraceStoreKernelCallWithParam: Invalid value for objectNumber", );

	if (recorder_busy)
    {
        /*************************************************************************
        * This may occur if a high-priority ISR is illegally using a system call,
        * or creates a user event.
        * Only ISRs that are disabled by TRACE_ENTER_CRITICAL_SECTION may use system calls
        * or user events (see TRACE_MAX_SYSCALL_INTERRUPT_PRIORITY).
        *************************************************************************/

        vTraceError("Recorder busy - high priority ISR using syscall? (3)");
        return;
    }

	trcCRITICAL_SECTION_BEGIN();
    if (RecorderDataPtr->recorderActive && handle_of_last_logged_task &&
        (! inExcludedTask || nISRactive))
    {
        
        /* Check if the referenced object or the event code is excluded */
        if (!uiTraceIsObjectExcluded(objectClass, (objectHandleType)objectNumber) && !TRACE_GET_EVENT_CODE_FLAG_ISEXCLUDED(evtcode))
        {            
            dts2 = (uint8_t)prvTraceGetDTS(0xFF);

            if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
            {
				uint8_t p8 = (uint8_t) prvTraceGetParam(0xFF, param);
				
				uint8_t hnd8 = prvTraceGet8BitHandle((objectHandleType)objectNumber);

                kse = (KernelCallWithParamAndHandle*) xTraceNextFreeEventBufferSlot();
                if (kse != NULL)
                {
                    kse->dts = dts2;
                    kse->type = (uint8_t)evtcode;
                    kse->objHandle = hnd8; 
                    kse->param = p8;
                    prvTraceUpdateCounters();
                }
            }            
        }
    }
	trcCRITICAL_SECTION_END();
}

/*******************************************************************************
 * prvTraceGetParam
 *
 * Used for storing extra bytes for kernel calls with numeric parameters.
 *
 * May only be called within a critical section!
 ******************************************************************************/
static uint32_t prvTraceGetParam(uint32_t param_max, uint32_t param)
{
	XPSEvent* xps;
	
	TRACE_ASSERT(param_max == 0xFF || param_max == 0xFFFF, "prvTraceGetParam: Invalid value for param_max", param);
	
	if (param <= param_max)
	{
		return param;
	}
	else
	{
		xps = (XPSEvent*) xTraceNextFreeEventBufferSlot();
		if (xps != NULL)
		{
			xps->type = DIV_XPS;
			xps->xps_8 = (param & (0xFF00 & ~param_max)) >> 8;
			xps->xps_16 = (param & (0xFFFF0000 & ~param_max)) >> 16;
			prvTraceUpdateCounters();
		}

		return param & param_max;
	}
}

/*******************************************************************************
 * vTraceStoreKernelCallWithNumericParamOnly
 *
 * Used for storing kernel calls with numeric parameters only. This is
 * only used for traceTASK_DELAY and traceDELAY_UNTIL at the moment.
 ******************************************************************************/
void vTraceStoreKernelCallWithNumericParamOnly(uint32_t evtcode, uint32_t param)
{
    KernelCallWithParam16 * kse;
    uint8_t dts6;
	uint16_t restParam;
    TRACE_SR_ALLOC_CRITICAL_SECTION();

	restParam = 0;

	TRACE_ASSERT(evtcode < 0xFF, "vTraceStoreKernelCallWithNumericParamOnly: Invalid value for evtcode", );
	
	if (recorder_busy)
    {
        /*************************************************************************
        * This may occur if a high-priority ISR is illegally using a system call,
        * or creates a user event.
        * Only ISRs that are disabled by TRACE_ENTER_CRITICAL_SECTION may use system calls
        * or user events (see TRACE_MAX_SYSCALL_INTERRUPT_PRIORITY).
        *************************************************************************/

        vTraceError("Recorder busy - high priority ISR using syscall? (4)");
        return;
    }
	
	trcCRITICAL_SECTION_BEGIN();
    if (RecorderDataPtr->recorderActive && handle_of_last_logged_task
        && (! inExcludedTask || nISRactive))
    {
        /* Check if the event code is excluded */
        if (!TRACE_GET_EVENT_CODE_FLAG_ISEXCLUDED(evtcode))
        {            
            dts6 = (uint8_t)prvTraceGetDTS(0xFF);

            if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
            {
				restParam = (uint16_t)prvTraceGetParam(0xFFFF, param);

				if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
				{
					kse = (KernelCallWithParam16*) xTraceNextFreeEventBufferSlot();
					if (kse != NULL)
					{
						kse->dts = dts6;
						kse->type = (uint8_t)evtcode;
						kse->param = restParam;
						prvTraceUpdateCounters();
					}
				}
            }            
        }
    }
	trcCRITICAL_SECTION_END();
}

/*******************************************************************************
 * vTraceStoreTaskswitch
 * Called by the scheduler from the SWITCHED_OUT hook, and by uiTraceStart.
 * At this point interrupts are assumed to be disabled!
 ******************************************************************************/
void vTraceStoreTaskswitch(objectHandleType task_handle)
{
    uint16_t dts3;
    TSEvent* ts;
    int8_t skipEvent;
	TRACE_SR_ALLOC_CRITICAL_SECTION();
		
	skipEvent = 0;

	TRACE_ASSERT(task_handle <= NTask, "vTraceStoreTaskswitch: Invalid value for task_handle", );
	
    /***************************************************************************
    This is used to detect if a high-priority ISRs is illegally using the
    recorder ISR trace functions (vTraceStoreISRBegin and ...End) while the
    recorder is busy with a task-level event or lower priority ISR event.

    If this is detected, it triggers a call to vTraceError with the error
    "Illegal call to vTraceStoreISRBegin/End". If you get this error, it means
    that the macro trcCRITICAL_SECTION_BEGIN does not disable this ISR, as required.

    Note: Setting recorder_busy is normally handled in our macros
    trcCRITICAL_SECTION_BEGIN and _END, but is needed explicitly in this
    function since critical sections should not be used in the context switch
    event...)
    ***************************************************************************/
    
    /* Skip the event if the task has been excluded, using vTraceExcludeTask */
    if (TRACE_GET_TASK_FLAG_ISEXCLUDED(task_handle))
    {
        skipEvent = 1;
        inExcludedTask = 1;
    }
    else
	{
        inExcludedTask = 0;
	}

	trcCRITICAL_SECTION_BEGIN_ON_CORTEX_M_ONLY();

	/* Skip the event if the same task is scheduled */
	if (task_handle == handle_of_last_logged_task)
	{
		skipEvent = 1;
	}
	
    if (!RecorderDataPtr->recorderActive)
    {
        skipEvent = 1;
    }

    /* If this event should be logged, log it! */
    if (skipEvent == 0)
    {
        dts3 = (uint16_t)prvTraceGetDTS(0xFFFF);

        if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */
        {
			uint8_t hnd8;
            handle_of_last_logged_task = task_handle;
			hnd8 = prvTraceGet8BitHandle(handle_of_last_logged_task);

            ts = (TSEvent*)xTraceNextFreeEventBufferSlot();

            if (ts != NULL)
            {
                if (uiTraceGetObjectState(TRACE_CLASS_TASK,
                    handle_of_last_logged_task) == TASK_STATE_INSTANCE_ACTIVE)
                {
                    ts->type = TS_TASK_RESUME;
                }
                else
                {
                    ts->type = TS_TASK_BEGIN;
                }

                ts->dts = dts3;
                ts->objHandle = hnd8;

                vTraceSetObjectState(TRACE_CLASS_TASK,
                                     handle_of_last_logged_task,
                                     TASK_STATE_INSTANCE_ACTIVE);

                prvTraceUpdateCounters();
            }
        }
    }

	trcCRITICAL_SECTION_END_ON_CORTEX_M_ONLY();
}

/*******************************************************************************
 * vTraceStoreNameCloseEvent
 *
 * Updates the symbol table with the name of this object from the dynamic
 * objects table and stores a "close" event, holding the mapping between handle
 * and name (a symbol table handle). The stored name-handle mapping is thus the
 * "old" one, valid up until this point.
 ******************************************************************************/
#if (INCLUDE_OBJECT_DELETE == 1)
void vTraceStoreObjectNameOnCloseEvent(objectHandleType handle,
                                       traceObjectClass objectclass)
{
    ObjCloseNameEvent * ce;
    const char * name;
    traceLabel idx;

	TRACE_ASSERT(objectclass < TRACE_NCLASSES, "vTraceStoreObjectNameOnCloseEvent: objectclass >= TRACE_NCLASSES", );
	TRACE_ASSERT(handle <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectclass], "vTraceStoreObjectNameOnCloseEvent: Invalid value for handle", );

    if (RecorderDataPtr->recorderActive)
	{
		uint8_t hnd8 = prvTraceGet8BitHandle(handle);

		name = TRACE_PROPERTY_NAME_GET(objectclass, handle);

		idx = prvTraceOpenSymbol(name, 0);

		// Interrupt disable not necessary, already done in trcHooks.h macro
		ce = (ObjCloseNameEvent*) xTraceNextFreeEventBufferSlot();
		if (ce != NULL)
		{
			ce->type = EVENTGROUP_OBJCLOSE_NAME + objectclass;
			ce->objHandle = hnd8; 
			ce->symbolIndex = idx;
			prvTraceUpdateCounters();
		}
	}
}

void vTraceStoreObjectPropertiesOnCloseEvent(objectHandleType handle,
                                             traceObjectClass objectclass)
{
    ObjClosePropEvent * pe;
	
    TRACE_ASSERT(objectclass < TRACE_NCLASSES, "vTraceStoreObjectPropertiesOnCloseEvent: objectclass >= TRACE_NCLASSES", );
    TRACE_ASSERT(handle <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectclass], "vTraceStoreObjectPropertiesOnCloseEvent: Invalid value for handle", );

    if (RecorderDataPtr->recorderActive)
	{
		// Interrupt disable not necessary, already done in trcHooks.h macro
		pe = (ObjClosePropEvent*) xTraceNextFreeEventBufferSlot();
		if (pe != NULL)
		{
			if (objectclass == TRACE_CLASS_TASK)
			{
				pe->arg1 = TRACE_PROPERTY_ACTOR_PRIORITY(objectclass, handle);
				pe->arg2 = 0; // Legacy - IFE info removed.
				pe->arg3 = 0; // Legacy - IFE info removed.
			}else{
				pe->arg1 = TRACE_PROPERTY_OBJECT_STATE(objectclass, handle);
			}
			pe->type = EVENTGROUP_OBJCLOSE_PROP + objectclass;
			prvTraceUpdateCounters();
		}
	}
}
#endif

void vTraceSetPriorityProperty(uint8_t objectclass, objectHandleType id, uint8_t value)
{
	TRACE_ASSERT(objectclass < TRACE_NCLASSES, "vTraceSetPriorityProperty: objectclass >= TRACE_NCLASSES", );
	TRACE_ASSERT(id <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectclass], "vTraceSetPriorityProperty: Invalid value for id", );

    TRACE_PROPERTY_ACTOR_PRIORITY(objectclass, id) = value;
}

uint8_t uiTraceGetPriorityProperty(uint8_t objectclass, objectHandleType id)
{
	TRACE_ASSERT(objectclass < TRACE_NCLASSES, "uiTraceGetPriorityProperty: objectclass >= TRACE_NCLASSES", 0);
	TRACE_ASSERT(id <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectclass], "uiTraceGetPriorityProperty: Invalid value for id", 0);

    return TRACE_PROPERTY_ACTOR_PRIORITY(objectclass, id);
}

void vTraceSetObjectState(uint8_t objectclass, objectHandleType id, uint8_t value)
{
	TRACE_ASSERT(objectclass < TRACE_NCLASSES, "vTraceSetObjectState: objectclass >= TRACE_NCLASSES", );
	TRACE_ASSERT(id <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectclass], "vTraceSetObjectState: Invalid value for id", );
	
    TRACE_PROPERTY_OBJECT_STATE(objectclass, id) = value;
}

uint8_t uiTraceGetObjectState(uint8_t objectclass, objectHandleType id)
{
	TRACE_ASSERT(objectclass < TRACE_NCLASSES, "uiTraceGetObjectState: objectclass >= TRACE_NCLASSES", 0);
	TRACE_ASSERT(id <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[objectclass], "uiTraceGetObjectState: Invalid value for id", 0);
	
    return TRACE_PROPERTY_OBJECT_STATE(objectclass, id);
}

void vTraceSetTaskInstanceFinished(objectHandleType handle)
{
	TRACE_ASSERT(handle <= RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[TRACE_CLASS_TASK], "vTraceSetTaskInstanceFinished: Invalid value for handle", );
	
#if (USE_IMPLICIT_IFE_RULES == 1)
    TRACE_PROPERTY_OBJECT_STATE(TRACE_CLASS_TASK, handle) = 0;    
#endif
}

#endif