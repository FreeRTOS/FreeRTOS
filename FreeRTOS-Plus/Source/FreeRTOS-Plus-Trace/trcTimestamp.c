/*
* Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of timestamps.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

TraceTimestamp_t *pxTraceTimestamp;

traceResult xTraceTimestampInitialize(TraceTimestampBuffer_t *pxBuffer)
{
	TRC_ASSERT_EQUAL_SIZE(TraceTimestampBuffer_t, TraceTimestamp_t);

	/* This should never fail */
	TRC_ASSERT(pxBuffer != 0);

	pxTraceTimestamp = (TraceTimestamp_t*)pxBuffer;
	pxTraceTimestamp->frequency = 0;
	pxTraceTimestamp->period = TRC_HWTC_PERIOD;
	pxTraceTimestamp->osTickHz = TRC_TICK_RATE_HZ;
	pxTraceTimestamp->osTickCount = 0;
	pxTraceTimestamp->wraparounds = 0;
	pxTraceTimestamp->type = TRC_HWTC_TYPE;

#if (TRC_HWTC_TYPE == TRC_FREE_RUNNING_32BIT_INCR || TRC_HWTC_TYPE == TRC_CUSTOM_TIMER_INCR || TRC_HWTC_TYPE == TRC_OS_TIMER_INCR)
	pxTraceTimestamp->latestTimestamp = 0;
#elif (TRC_HWTC_TYPE == TRC_FREE_RUNNING_32BIT_DECR || TRC_HWTC_TYPE == TRC_CUSTOM_TIMER_DECR || TRC_HWTC_TYPE == TRC_OS_TIMER_DECR)
	pxTraceTimestamp->latestTimestamp = pxTraceTimestamp->period - 1;
#endif

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_TIMESTAMP);

	return TRC_SUCCESS;
}

#if ((TRC_CFG_USE_TRACE_ASSERT) == 1)

traceResult xTraceTimestampGet(uint32_t *puiTimestamp)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_TIMESTAMP));

	/* This should never fail */
	TRC_ASSERT(puiTimestamp != 0);

	switch (pxTraceTimestamp->type)
	{
	case TRC_FREE_RUNNING_32BIT_INCR:
	case TRC_CUSTOM_TIMER_INCR:
		*puiTimestamp = TRC_HWTC_COUNT;
		if (*puiTimestamp < pxTraceTimestamp->latestTimestamp)
		{
			pxTraceTimestamp->wraparounds++;
		}
		break;
	case TRC_FREE_RUNNING_32BIT_DECR:
	case TRC_CUSTOM_TIMER_DECR:
		*puiTimestamp = TRC_HWTC_COUNT;
		if (*puiTimestamp > pxTraceTimestamp->latestTimestamp)
		{
			pxTraceTimestamp->wraparounds++;
		}
		break;
	case TRC_OS_TIMER_INCR:
	case TRC_OS_TIMER_DECR:
		*puiTimestamp = ((TRC_HWTC_COUNT) & 0x00FFFFFFU) + ((pxTraceTimestamp->osTickCount & 0x000000FFU) << 24);
		pxTraceTimestamp->wraparounds = pxTraceTimestamp->osTickCount;
		break;
	default:
		return TRC_FAIL;
	}

	pxTraceTimestamp->latestTimestamp = *puiTimestamp;
	
	return TRC_SUCCESS;
}

traceResult xTraceTimestampGetWraparounds(uint32_t* puiTimerWraparounds)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_TIMESTAMP));

	/* This should never fail */
	TRC_ASSERT(puiTimerWraparounds != 0);

	*puiTimerWraparounds = pxTraceTimestamp->wraparounds;

	return TRC_SUCCESS;
}

traceResult xTraceTimestampSetFrequency(TraceUnsignedBaseType_t uxFrequency)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_TIMESTAMP));

	pxTraceTimestamp->frequency = uxFrequency;

	return TRC_SUCCESS;
}

traceResult xTraceTimestampSetPeriod(uint32_t uiPeriod)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_TIMESTAMP));

	pxTraceTimestamp->period = uiPeriod;

	return TRC_SUCCESS;
}

traceResult xTraceTimestampSetOsTickCount(uint32_t uiOsTickCount)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_TIMESTAMP));

	pxTraceTimestamp->osTickCount = uiOsTickCount;

	return TRC_SUCCESS;
}

traceResult xTraceTimestampGetFrequency(TraceUnsignedBaseType_t *puxFrequency)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_TIMESTAMP));

	/* This should never fail */
	TRC_ASSERT(puxFrequency != 0);

	*puxFrequency = pxTraceTimestamp->frequency;

	return TRC_SUCCESS;
}

traceResult xTraceTimestampGetPeriod(uint32_t *puiPeriod)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_TIMESTAMP));

	/* This should never fail */
	TRC_ASSERT(puiPeriod != 0);

	*puiPeriod = pxTraceTimestamp->period;

	return TRC_SUCCESS;
}

traceResult xTraceTimestampGetOsTickCount(uint32_t* puiOsTickCount)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_TIMESTAMP));

	/* This should never fail */
	TRC_ASSERT(puiOsTickCount != 0);

	*puiOsTickCount = pxTraceTimestamp->osTickCount;

	return TRC_SUCCESS;
}

#endif /* ((TRC_CFG_USE_TRACE_ASSERT) == 1) */

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
