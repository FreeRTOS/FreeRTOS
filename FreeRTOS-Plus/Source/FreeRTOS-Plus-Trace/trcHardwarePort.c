/******************************************************************************* 
 * Tracealyzer v2.6.0 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcHardwarePort.c
 *
 * Contains together with trcHardwarePort.h all hardware portability issues of 
 * the trace recorder library.
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
 * Copyright Percepio AB, 2013.
 * www.percepio.com
 ******************************************************************************/

#include "trcHardwarePort.h"
#include "trcKernelPort.h"

#if (USE_TRACEALYZER_RECORDER == 1)

#include <stdint.h>

uint32_t trace_disable_timestamp = 0;
uint32_t last_timestamp = 0;

/*******************************************************************************
 * uiTraceTickCount
 *
 * This variable is should be updated by the Kernel tick interrupt. This does 
 * not need to be modified when developing a new timer port. It is preferred to 
 * keep any timer port changes in the HWTC macro definitions, which typically 
 * give sufficient flexibility.
 ******************************************************************************/
uint32_t uiTraceTickCount = 0;

uint32_t DWT_CYCLES_ADDED = 0;

#if (SELECTED_PORT == PORT_ARM_CortexM)

void prvTraceEnableIRQ(void)
{
	asm volatile ("cpsie i");
}

void prvTraceDisableIRQ(void)
{
	asm volatile ("cpsid i");
}

void prvTraceSetIRQMask(uint32_t priMask)
{
	asm volatile ("MSR primask, %0" : : "r" (priMask) );
}

uint32_t prvTraceGetIRQMask(void)
{
	uint32_t result;
	asm volatile ("MRS %0, primask" : "=r" (result) );
	return result;
}

void prvTraceInitCortexM()
{
	DWT_CTRL_REG |= 1;     /* Enable the cycle counter */
	DWT_CYCLE_COUNTER = 0;
	
	if (RecorderDataPtr->frequency == 0)
	{		
		RecorderDataPtr->frequency = TRACE_CPU_CLOCK_HZ / HWTC_DIVISOR;
	}
}

#endif

/******************************************************************************
 * vTracePortGetTimeStamp
 *
 * Returns the current time based on the HWTC macros which provide a hardware
 * isolation layer towards the hardware timer/counter.
 *
 * The HWTC macros and vTracePortGetTimeStamp is the main porting issue
 * or the trace recorder library. Typically you should not need to change
 * the code of vTracePortGetTimeStamp if using the HWTC macros.
 *
 ******************************************************************************/
void vTracePortGetTimeStamp(uint32_t *pTimestamp)
{
	static uint32_t last_traceTickCount = 0;
    static uint32_t last_hwtc_count = 0;
    uint32_t traceTickCount = 0;
    uint32_t hwtc_count = 0;
    
	if (trace_disable_timestamp == 1)
	{
		if (pTimestamp)
			*pTimestamp = last_timestamp;
		return;
	}
			
    /* Retrieve HWTC_COUNT only once since the same value should be used all throughout this function. */
#if (HWTC_COUNT_DIRECTION == DIRECTION_INCREMENTING)
    hwtc_count = HWTC_COUNT;
#elif (HWTC_COUNT_DIRECTION == DIRECTION_DECREMENTING)
    hwtc_count = HWTC_PERIOD - HWTC_COUNT;
#else
    Junk text to cause compiler error - HWTC_COUNT_DIRECTION is not set correctly!
    Should be DIRECTION_INCREMENTING or DIRECTION_DECREMENTING
#endif
    
    if (last_traceTickCount - uiTraceTickCount - 1 < 0x80000000)
    {
        /* This means last_traceTickCount is higher than uiTraceTickCount,
        so we have previously compensated for a missed tick.
        Therefore we use the last stored value because that is more accurate. */
        traceTickCount = last_traceTickCount;
    }
    else
    {
        /* Business as usual */
        traceTickCount = uiTraceTickCount;
    }

    /* Check for overflow. May occur if the update of uiTraceTickCount has been 
    delayed due to disabled interrupts. */
    if (traceTickCount == last_traceTickCount && hwtc_count < last_hwtc_count)
    {
        /* A trace tick has occurred but not been executed by the kernel, so we compensate manually. */
        traceTickCount++;
    }
    
    /* Check if the return address is OK, then we perform the calculation. */
    if (pTimestamp)
    {
        /* Get timestamp from trace ticks. Scale down the period to avoid unwanted overflows. */
        *pTimestamp = traceTickCount * (HWTC_PERIOD / HWTC_DIVISOR);
        /* Increase timestamp by (hwtc_count + "lost hardware ticks from scaling down period") / HWTC_DIVISOR. */
        *pTimestamp += (hwtc_count + traceTickCount * (HWTC_PERIOD % HWTC_DIVISOR)) / HWTC_DIVISOR;
		
		last_timestamp = *pTimestamp;
    }
    
    /* Store the previous values. */
    last_traceTickCount = traceTickCount;
    last_hwtc_count = hwtc_count;
}

#endif