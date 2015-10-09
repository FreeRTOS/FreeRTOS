/*******************************************************************************
 * Tracealyzer v3.0.2 Recorder Library
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
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2014.
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

uint32_t DWT_CYCLES_ADDED = 0; /* Used on ARM Cortex-M only */

#if (SELECTED_PORT == PORT_ARM_CortexM)

void prvTraceInitCortexM()
{
	/* Make sure DWT is enabled is enabled, if supported */
	REG_DEMCR |= DEMCR_TRCENA;

	do{
		/* Verify that DWT is supported */
		if (REG_DEMCR == 0)
		{
			vTraceError("DWT not supported by this chip!");
			break;
		}

		/* Verify that DWT_CYCCNT is supported */
		if (REG_DWT_CTRL & DWT_CTRL_NOCYCCNT)
		{
			vTraceError("DWT_CYCCNT not supported by this chip!");
			break;
		}

		/* Reset the cycle counter */
		REG_DWT_CYCCNT = 0;

		/* Enable the cycle counter */
		REG_DWT_CTRL |= DWT_CTRL_CYCCNTENA;

	}while(0);	/* breaks above jump here */

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

#if (SELECTED_PORT == PORT_Win32)
	/* The Win32 port uses ulGetRunTimeCounterValue for timestamping, which in turn
	uses QueryPerformanceCounter. That function is not always reliable when used over
	multiple threads. We must therefore handle rare cases where the timestamp is less
	than the previous. In practice, the Win32 should "never" roll over since the
	performance counter is 64 bit wide. */

	if (last_hwtc_count > hwtc_count)
	{
		hwtc_count = last_hwtc_count;
	}
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
