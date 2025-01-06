/*
* Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of timestamps.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

TraceTimestampData_t *pxTraceTimestamp TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTraceTimestampInitialize(TraceTimestampData_t *pxBuffer)
{
	/* This should never fail */
	TRC_ASSERT(pxBuffer != (void*)0);

	pxTraceTimestamp = pxBuffer;

	/* These will be set when tracing is enabled */
	pxTraceTimestamp->frequency = 0u;
	pxTraceTimestamp->period = 0u;

	pxTraceTimestamp->osTickHz = TRC_TICK_RATE_HZ;
	pxTraceTimestamp->osTickCount = 0u;
	pxTraceTimestamp->wraparounds = 0u;
	pxTraceTimestamp->type = TRC_HWTC_TYPE;

#if (TRC_HWTC_TYPE == TRC_FREE_RUNNING_32BIT_INCR || TRC_HWTC_TYPE == TRC_CUSTOM_TIMER_INCR || TRC_HWTC_TYPE == TRC_OS_TIMER_INCR)
	pxTraceTimestamp->latestTimestamp = 0u;
#elif (TRC_HWTC_TYPE == TRC_FREE_RUNNING_32BIT_DECR || TRC_HWTC_TYPE == TRC_CUSTOM_TIMER_DECR || TRC_HWTC_TYPE == TRC_OS_TIMER_DECR)
	pxTraceTimestamp->latestTimestamp = pxTraceTimestamp->period - 1u;
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
	TRC_ASSERT(puiTimestamp != (void*)0);

	switch (pxTraceTimestamp->type)
	{
	case TRC_FREE_RUNNING_32BIT_INCR:
	case TRC_CUSTOM_TIMER_INCR:
		*puiTimestamp = (uint32_t)(TRC_HWTC_COUNT);
		if (*puiTimestamp < pxTraceTimestamp->latestTimestamp)
		{
			pxTraceTimestamp->wraparounds++;
		}
		break;
	case TRC_FREE_RUNNING_32BIT_DECR:
	case TRC_CUSTOM_TIMER_DECR:
		*puiTimestamp = (uint32_t)(TRC_HWTC_COUNT);
		if (*puiTimestamp > pxTraceTimestamp->latestTimestamp)
		{
			pxTraceTimestamp->wraparounds++;
		}
		break;
	case TRC_OS_TIMER_INCR:
	case TRC_OS_TIMER_DECR:
		*puiTimestamp = (((uint32_t)(TRC_HWTC_COUNT)) & 0x00FFFFFFUL) + ((pxTraceTimestamp->osTickCount & 0x000000FFUL) << 24);
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
	TRC_ASSERT(puiTimerWraparounds != (void*)0);

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
	TRC_ASSERT(puxFrequency != (void*)0);

	*puxFrequency = pxTraceTimestamp->frequency;

	return TRC_SUCCESS;
}

traceResult xTraceTimestampGetPeriod(uint32_t *puiPeriod)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_TIMESTAMP));

	/* This should never fail */
	TRC_ASSERT(puiPeriod != (void*)0);

	*puiPeriod = pxTraceTimestamp->period;

	return TRC_SUCCESS;
}

traceResult xTraceTimestampGetOsTickCount(uint32_t* puiOsTickCount)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_TIMESTAMP));

	/* This should never fail */
	TRC_ASSERT(puiOsTickCount != (void*)0);

	*puiOsTickCount = pxTraceTimestamp->osTickCount;

	return TRC_SUCCESS;
}

#endif

#endif
