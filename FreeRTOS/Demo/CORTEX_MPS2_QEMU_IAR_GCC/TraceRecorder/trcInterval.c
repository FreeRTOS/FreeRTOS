/*
* Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of intervals.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceIntervalChannelSetCreate(const char* szName, TraceIntervalChannelSetHandle_t* pxIntervalChannelSetHandle)
{
	TraceObjectHandle_t xObjectHandle;

	/* This should never fail */
	TRC_ASSERT(pxIntervalChannelSetHandle != (void*)0);

	/* We need to check this */
	if (xTraceObjectRegister(PSF_EVENT_INTERVAL_CHANNEL_SET_CREATE, (void*)0, szName, 0u, &xObjectHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetOptions((TraceEntryHandle_t)xObjectHandle, TRC_ENTRY_OPTION_INTERVAL_CHANNEL_SET) == TRC_SUCCESS);

	*pxIntervalChannelSetHandle = (TraceIntervalChannelSetHandle_t)xObjectHandle;

	return TRC_SUCCESS;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceIntervalChannelCreate(const char *szName, TraceIntervalChannelSetHandle_t xIntervalChannelSetHandle, TraceIntervalChannelHandle_t *pxIntervalChannelHandle)
{
	TraceObjectHandle_t xObjectHandle;

	/* This should never fail */
	TRC_ASSERT(pxIntervalChannelHandle != (void*)0);

	/* This should never fail */
	TRC_ASSERT(xIntervalChannelSetHandle != 0);

	/* We need to check this */
	if (xTraceObjectRegister(PSF_EVENT_INTERVAL_CHANNEL_CREATE, (void*)0, szName, (TraceUnsignedBaseType_t)xIntervalChannelSetHandle, &xObjectHandle) == TRC_FAIL) /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 Suppress conversion from pointer to integer check*/
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetOptions((TraceEntryHandle_t)xObjectHandle, TRC_ENTRY_OPTION_INTERVAL_CHANNEL) == TRC_SUCCESS);

	*pxIntervalChannelHandle = (TraceIntervalChannelHandle_t)xObjectHandle;
	
	return TRC_SUCCESS;
}

traceResult xTraceIntervalStart(TraceIntervalChannelHandle_t xIntervalChannelHandle, TraceUnsignedBaseType_t uxValue, TraceIntervalInstanceHandle_t *pxIntervalInstanceHandle)
{
	TRC_ASSERT(xIntervalChannelHandle != 0);
	
	TRC_ASSERT(pxIntervalInstanceHandle != (void*)0);
	
	/* We null all of it first in case it's 64-bit and we only write 32-bit */
	*pxIntervalInstanceHandle = 0;

	TRC_ASSERT_ALWAYS_EVALUATE(xTraceTimestampGet((uint32_t*)pxIntervalInstanceHandle) == TRC_SUCCESS); /*cstat !MISRAC2004-11.4 !MISRAC2012-Rule-11.3 Suppress conversion between pointer types checks*/

	(void)xTraceEventCreate3(PSF_EVENT_INTERVAL_START, (TraceUnsignedBaseType_t)xIntervalChannelHandle, (TraceUnsignedBaseType_t)*pxIntervalInstanceHandle, uxValue); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 Suppress conversion from pointer to integer check*/
	
	return TRC_SUCCESS;
}

traceResult xTraceIntervalStop(TraceIntervalChannelHandle_t xIntervalChannelHandle, TraceIntervalInstanceHandle_t xIntervalInstanceHandle)
{
	TRC_ASSERT(xIntervalChannelHandle != 0);

	(void)xTraceEventCreate2(PSF_EVENT_INTERVAL_STOP, (TraceUnsignedBaseType_t)xIntervalChannelHandle, (TraceUnsignedBaseType_t)xIntervalInstanceHandle); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 Suppress conversion from pointer to integer check*/

	return TRC_SUCCESS;
}

#endif
