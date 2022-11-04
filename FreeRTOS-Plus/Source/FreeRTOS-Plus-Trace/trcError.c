/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for errors.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

/* We skip the slot for TRC_ERROR_NONE so error code 1 is the first bit */
#define GET_ERROR_WARNING_FLAG(errorCode) (pxErrorInfo->uiErrorAndWarningFlags & (1 << ((errorCode) - 1)))
#define SET_ERROR_WARNING_FLAG(errorCode) (pxErrorInfo->uiErrorAndWarningFlags |= (1 << ((errorCode) - 1)))

traceResult prvTraceErrorPrint(uint32_t uiErrorCode);
traceResult prvTraceErrorGetDescription(uint32_t uiErrorCode, const char** pszDesc);

typedef struct TraceErrorInfo
{
	uint32_t uiErrorAndWarningFlags;
	uint32_t uiErrorCode;
	TraceStringHandle_t xWarningChannel;
} TraceErrorInfo_t;

static TraceErrorInfo_t* pxErrorInfo;

traceResult xTraceErrorInitialize(TraceErrorBuffer_t* pxBuffer)
{
	TRC_ASSERT_EQUAL_SIZE(TraceErrorBuffer_t, TraceErrorInfo_t);

	/* This should never fail */
	TRC_ASSERT(pxBuffer != 0);

	pxErrorInfo = (TraceErrorInfo_t*)pxBuffer;

	pxErrorInfo->uiErrorAndWarningFlags = 0;
	pxErrorInfo->uiErrorCode = 0;
	pxErrorInfo->xWarningChannel = 0;

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_ERROR);

	return TRC_SUCCESS;
}

/* Called on warnings, when the recording can continue. */
traceResult xTraceWarning(uint32_t uiErrorCode)
{
	/* Probably good to verify this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ERROR))
	{
		/* If not initialized */
		return TRC_FAIL;
	}
	
	if (GET_ERROR_WARNING_FLAG(uiErrorCode) == 0)
	{
		/* Will never reach this point more than once per warning type, since we verify if uiErrorAndWarningFlags[uiErrorCode] has already been set */
		SET_ERROR_WARNING_FLAG(uiErrorCode);

		prvTraceErrorPrint(uiErrorCode);
	}

	return TRC_SUCCESS;
}

/* Called on critical errors in the recorder. Stops the recorder! */
traceResult xTraceError(uint32_t uiErrorCode)
{
	/* Probably good to verify this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ERROR))
	{
		return TRC_FAIL;
	}

	if (pxErrorInfo->uiErrorCode == TRC_ERROR_NONE)
	{
		/* Will never reach this point more than once, since we verify if uiErrorCode has already been set */
		SET_ERROR_WARNING_FLAG(uiErrorCode);
		pxErrorInfo->uiErrorCode = uiErrorCode;

		if (prvTraceErrorPrint(uiErrorCode) == TRC_FAIL)
		{
			xTraceDisable();
			
			return TRC_FAIL;
		}
		
		xTracePrint(pxErrorInfo->xWarningChannel, "Recorder stopped in xTraceError(...)!");
		xTraceDisable();
	}

	return TRC_SUCCESS;
}

/*******************************************************************************
 * xTraceErrorGetLast
 *
 * Returns the last error or warning, as a string, or NULL if none.
 *****************************************************************************/
traceResult xTraceErrorGetLast(const char **pszError)
{
	/* Probably good to verify this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ERROR))
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT(pszError != 0);
	
	return prvTraceErrorGetDescription(pxErrorInfo->uiErrorCode, pszError);
}

/*******************************************************************************
 * xTraceErrorClear
 *
 * Clears any errors.
 *****************************************************************************/
traceResult xTraceErrorClear(void)
{
	/* Probably good to verify this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ERROR))
	{
		/* If not initialized */
		return TRC_FAIL;
	}
	
	pxErrorInfo->uiErrorCode = TRC_ERROR_NONE;

	return TRC_SUCCESS;
}

/* Returns the error or warning, as a string, or NULL if none. */
traceResult prvTraceErrorPrint(uint32_t uiErrorCode)
{
	const char* szDesc;
	/* Note: the error messages are short, in order to fit in a User Event.
	Instead, the users can read more in the below comments.*/

	if (pxErrorInfo->xWarningChannel == 0)
	{
		/* The #WFR channel means "Warnings from Recorder" and
		* is used to store warnings and errors from the recorder.
		* The abbreviation #WFR is used instead of the longer full name,
		* to avoid truncation by small slots in the symbol table.
		* This is translated in Tracealyzer and shown as the full name,
		* "Warnings from Recorder".
		 */
		if (xTraceStringRegister("#WFR", &pxErrorInfo->xWarningChannel) == TRC_FAIL)
		{
			return TRC_FAIL;
		}
	}

	prvTraceErrorGetDescription(uiErrorCode, &szDesc);

	switch (uiErrorCode)
	{
	case TRC_WARNING_ENTRY_TABLE_SLOTS:
	case TRC_WARNING_ENTRY_SYMBOL_MAX_LENGTH:
	case TRC_WARNING_EVENT_SIZE_TRUNCATED:
	case TRC_WARNING_STREAM_PORT_READ:
	case TRC_WARNING_STREAM_PORT_WRITE:
	case TRC_WARNING_STREAM_PORT_INITIAL_BLOCKING:
	case TRC_WARNING_STACKMON_NO_SLOTS:
	case TRC_ERROR_STREAM_PORT_WRITE:
	case TRC_ERROR_EVENT_CODE_TOO_LARGE:
	case TRC_ERROR_ISR_NESTING_OVERFLOW:
	case TRC_ERROR_DWT_NOT_SUPPORTED:
	case TRC_ERROR_DWT_CYCCNT_NOT_SUPPORTED:
	case TRC_ERROR_TZCTRLTASK_NOT_CREATED:
		xTracePrint(pxErrorInfo->xWarningChannel, szDesc);
		break;

	case TRC_ERROR_ASSERT:
		/* A TRC_ASSERT has triggered */
		{
			TraceUnsignedBaseType_t uxLineNumber;
			TraceStringHandle_t xFileName;

			if (xTraceAssertGet(&xFileName, &uxLineNumber) == TRC_FAIL)
			{
				return TRC_FAIL;
			}

			xTracePrintF(pxErrorInfo->xWarningChannel, szDesc, xFileName, (uint32_t)uxLineNumber);

			return TRC_SUCCESS;
		}
		
	default:
		/* No error, or an unknown error occurred */
		xTracePrintF(pxErrorInfo->xWarningChannel, "Unknown error code: 0x%08X", uiErrorCode);
		
		return TRC_FAIL;
	}

	return TRC_SUCCESS;
}

/* Returns the error or warning, as a string, or NULL if none. */
traceResult prvTraceErrorGetDescription(uint32_t uiErrorCode, const char** pszDesc)
{
	/* Note: the error messages are short, in order to fit in a User Event.
	Instead, the users can read more in the below comments.*/

	switch (uiErrorCode)
	{
	case TRC_ERROR_NONE:
		return TRC_FAIL;

	case TRC_WARNING_ENTRY_TABLE_SLOTS:
		/* There was not enough symbol table slots for storing symbol names.
		The number of missing slots is counted by NoRoomForSymbol. Inspect this
		variable and increase TRC_CFG_ENTRY_TABLE_SLOTS by at least that value. */

		*pszDesc = "Exceeded TRC_CFG_ENTRY_TABLE_SLOTS";
		break;

	case TRC_WARNING_ENTRY_SYMBOL_MAX_LENGTH:
		/* A symbol name exceeded TRC_CFG_ENTRY_SYMBOL_MAX_LENGTH in length.
		Make sure the symbol names are at most TRC_CFG_SYMBOL_MAX_LENGTH,
		or inspect uiLongestSymbolName in trcEntryTable and increase
		TRC_CFG_ENTRY_SYMBOL_MAX_LENGTH to at least this value. */

		*pszDesc = "Exceeded TRC_CFG_ENTRY_SYMBOL_MAX_LENGTH";
		break;

	case TRC_WARNING_EVENT_SIZE_TRUNCATED:
		/* Some arguments was longer than the maximum payload size
		and has been truncated by "uiMaxBytesTruncated" bytes.

		This usually happens for the following functions:
		- xTracePrint
		- xTracePrintF
		- xTraceStringRegister

		A trace event may store a maximum of 56 bytes payload, including
		data arguments and string characters. */

		*pszDesc = "Event size exceeded";
		break;

	case TRC_WARNING_STREAM_PORT_READ:
		/* TRC_STREAM_PORT_READ_DATA is expected to return 0 when completed successfully.
		This means there is an error in the communication with host/Tracealyzer. */

		*pszDesc = "TRC_STREAM_PORT_READ_DATA returned error";
		break;

	case TRC_WARNING_STREAM_PORT_WRITE:
		/* TRC_STREAM_PORT_WRITE_DATA is expected to return 0 when completed successfully.
		This means there is an error in the communication with host/Tracealyzer. */

		*pszDesc = "TRC_STREAM_PORT_WRITE_DATA returned error";
		break;

	case TRC_WARNING_STREAM_PORT_INITIAL_BLOCKING:
		/* Blocking occurred during xTraceEnable. This happens if the trace buffer is
		smaller than the initial transmission (trace header, object table, and symbol table). */

		*pszDesc = "Blocking in xTraceEnable";
		break;

	case TRC_WARNING_STACKMON_NO_SLOTS:
		/* Some tasks did not fit in the stack monitor. Increase the slot count. */

		*pszDesc = "No slots left in Stack Monitor";
		break;

	case TRC_ERROR_STREAM_PORT_WRITE:
		/* TRC_STREAM_PORT_WRITE_DATA is expected to return 0 when completed successfully.
		This means there is an error in the communication with host/Tracealyzer. */

		*pszDesc = "TRC_STREAM_PORT_WRITE_DATA returned error";
		break;

	case TRC_ERROR_EVENT_CODE_TOO_LARGE:
		/* The highest allowed event code is 4095, anything higher is an unexpected error.
		Please contact support@percepio.com for assistance.*/

		*pszDesc = "Invalid event code";
		break;

	case TRC_ERROR_ISR_NESTING_OVERFLOW:
		/* Nesting of ISR trace calls exceeded the limit (TRC_CFG_MAX_ISR_NESTING).
		If this is unlikely, make sure that you call vTraceStoreISRExit in the end
		of all ISR handlers. Or increase TRC_CFG_MAX_ISR_NESTING. */

		*pszDesc = "Exceeded ISR nesting";
		break;

	case TRC_ERROR_DWT_NOT_SUPPORTED:
		/* On ARM Cortex-M only - failed to initialize DWT Cycle Counter since not supported by this chip.
		DWT timestamping is selected automatically for ART Cortex-M3, M4 and higher, based on the __CORTEX_M
		macro normally set by ARM's CMSIS library, since typically available. You can however select
		SysTick timestamping instead by defining adding "#define TRC_CFG_ARM_CM_USE_SYSTICK".*/

		*pszDesc = "DWT not supported";
		break;

	case TRC_ERROR_DWT_CYCCNT_NOT_SUPPORTED:
		/* On ARM Cortex-M only - failed to initialize DWT Cycle Counter since not supported by this chip.
		DWT timestamping is selected automatically for ART Cortex-M3, M4 and higher, based on the __CORTEX_M
		macro normally set by ARM's CMSIS library, since typically available. You can however select
		SysTick timestamping instead by defining adding "#define TRC_CFG_ARM_CM_USE_SYSTICK".*/

		*pszDesc = "DWT_CYCCNT not supported";
		break;

	case TRC_ERROR_TZCTRLTASK_NOT_CREATED:
		/* xTraceEnable failed creating the trace control task (TzCtrl) - incorrect parameters (priority?)
		or insufficient heap size? */
		*pszDesc = "Could not create TzCtrl";
		break;

	case TRC_ERROR_ASSERT:
		/* A TRC_ASSERT has triggered */
		*pszDesc = "ASSERT: %s (%d)";
		break;

	default:
		/* An unknown error occurred */
		*pszDesc = "Unknown error code: 0x%08X";
		break;
	}

	return TRC_SUCCESS;
}

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
