/*
* Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of dependencies.
*/
#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#define TRC_DEPENDENCY_STATE_INDEX_TYPE 0UL

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceDependencyRegister(const char* szName, TraceUnsignedBaseType_t uxDependencyType)
{
	TraceObjectHandle_t xObjectHandle;
	TraceUnsignedBaseType_t auxStates[TRC_ENTRY_TABLE_STATE_COUNT] = { 0UL };

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_CORE));

	/* This should never fail */
	TRC_ASSERT(szName != (void*)0);

	/* This should never fail */
	TRC_ASSERT(szName[0] != (char)0); /*cstat !MISRAC2004-17.4_b Checking first character*/ /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/

	switch (uxDependencyType)
	{
	case TRC_DEPENDENCY_TYPE_ELF:
		auxStates[TRC_DEPENDENCY_STATE_INDEX_TYPE] = uxDependencyType;
		break;
	default:
		return TRC_FAIL;
	}
	
	return xTraceObjectRegisterInternal(PSF_EVENT_DEPENDENCY_REGISTER, (void*)0, szName, 1u, auxStates, TRC_ENTRY_OPTION_DEPENDENCY, &xObjectHandle);
}

#endif
