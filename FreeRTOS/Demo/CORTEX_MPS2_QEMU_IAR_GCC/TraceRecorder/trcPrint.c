/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for print.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) && (TRC_CFG_INCLUDE_USER_EVENTS == 1)

#include <stdarg.h>

static traceResult prvTraceVPrintF(const TraceStringHandle_t xChannel, const char* szFormat, uint32_t uiLength, uint32_t uiArgs, va_list* pxVariableList);

static TracePrintData_t *pxPrintData TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTracePrintInitialize(TracePrintData_t *pxBuffer)
{
	/* This should never fail */
	TRC_ASSERT(pxBuffer != (void*)0);

	pxPrintData = pxBuffer;

	pxPrintData->defaultChannel = 0;
	pxPrintData->consoleChannel = 0;

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_PRINT);
	
	return TRC_SUCCESS;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTracePrint(TraceStringHandle_t xChannel, const char* szString)
{
	uint32_t uiLength;
	uint32_t i;
	
	/* We need to check this */
	if (xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_PRINT) == 0U)
	{
		return TRC_FAIL;
	}

	if (szString == (void*)0)
	{
		szString = ""; /*cstat !MISRAC2012-Rule-17.8 Suppress modified function parameter check*/
	}

	for (i = 0u; (szString[i] != (char)0) && (i < 128u); i++) {} /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress char base type usage checks*/ /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/

	uiLength = i + 1u; /* Null termination */

	return prvTraceVPrintF(xChannel, szString, uiLength, 0u, (va_list*)0);  /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 Suppress conversion of pointer to integer check*/ /*cstat !MISRAC2012-Rule-11.9 Suppress NULL recommendation*/
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-16.1 Suppress variable parameter count check*/
traceResult xTraceConsoleChannelPrintF(const char* szFormat, ...)
{
	traceResult xResult;
	va_list xVariableList; /*cstat !MISRAC2012-Rule-17.1 Suppress stdarg usage check*/

	/* We need to check this */
	if (xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_PRINT) == 0U)
	{
		return TRC_FAIL;
	}

	if (pxPrintData->consoleChannel == 0)
	{
		if (xTraceStringRegister("Debug Console", &pxPrintData->consoleChannel) == TRC_FAIL)
		{
			return TRC_FAIL;
		}
	}

	va_start(xVariableList, szFormat);
	xResult = xTraceVPrintF(pxPrintData->consoleChannel, szFormat, &xVariableList);
	va_end(xVariableList);

	return xResult;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-16.1 Suppress variable parameter count check*/
traceResult xTracePrintCompactF(const char* szChannel, const char* szFormat, ...)
{
	uint32_t i;
	uint32_t uiArgs = 0u;
	traceResult xResult;
	va_list xVariableList; /*cstat !MISRAC2012-Rule-17.1 Suppress stdarg usage check*/
	TraceUnsignedBaseType_t uxArg1, uxArg2, uxArg3, uxArg4;

	/* We need to check this */
	if (xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_PRINT) == 0U)
	{
		return TRC_FAIL;
	}

	if (szFormat == (void*)0)
	{
		szFormat = ""; /*cstat !MISRAC2012-Rule-17.8 Suppress modified function parameter check*/
	}

	/* Count the number of arguments in the format string (e.g., %d) */
	for (i = 0u; (szFormat[i] != (char)0) && (i < 128u); i++) /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress char base type usage checks*/ /*cstat !MISRAC2012-Rule-14.2 Suppress malformed for loop due to i being incremented inside*/ /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/
	{
		if (szFormat[i] == '%') /*cstat !MISRAC2004-17.4_b We need to access a specific character in the string*/
		{
			if (szFormat[i + 1u] == (char)0) /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-17.4_b We need to access a specific character in the string*/
			{
				/* Found end of string, let for loop detect it */
				continue; /*cstat !MISRAC2004-14.5 Suppress continue usage check*/
			}

			if (szFormat[i + 1u] != '%') /*cstat !MISRAC2004-17.4_b We need to access a specific character in the string*/
			{
				uiArgs++;        /* Found an argument */
			}

			/* Move past format specifier or non-argument '%' */
			i++; /*cstat !MISRAC2004-13.6 Suppress i increment inside for loop check*/
		}
	}

	va_start(xVariableList, szFormat);
	switch(uiArgs)
	{
	case 0:
		xResult = xTraceEventCreate2(PSF_EVENT_USER_EVENT_FIXED, (TraceUnsignedBaseType_t)szChannel, (TraceUnsignedBaseType_t)szFormat); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 We need the addresses*/
		break;
	case 1:
		uxArg1 = va_arg(xVariableList, TraceUnsignedBaseType_t);
		xResult = xTraceEventCreate3(PSF_EVENT_USER_EVENT_FIXED + 1UL, (TraceUnsignedBaseType_t)szChannel, (TraceUnsignedBaseType_t)szFormat, uxArg1); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 We need the addresses*/
		break;
	case 2:
		uxArg1 = va_arg(xVariableList, TraceUnsignedBaseType_t);
		uxArg2 = va_arg(xVariableList, TraceUnsignedBaseType_t);
		xResult = xTraceEventCreate4(PSF_EVENT_USER_EVENT_FIXED + 2UL, (TraceUnsignedBaseType_t)szChannel, (TraceUnsignedBaseType_t)szFormat, uxArg1, uxArg2); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 We need the addresses*/
		break;
	case 3:
		uxArg1 = va_arg(xVariableList, TraceUnsignedBaseType_t);
		uxArg2 = va_arg(xVariableList, TraceUnsignedBaseType_t);
		uxArg3 = va_arg(xVariableList, TraceUnsignedBaseType_t);
		xResult = xTraceEventCreate5(PSF_EVENT_USER_EVENT_FIXED + 3UL, (TraceUnsignedBaseType_t)szChannel, (TraceUnsignedBaseType_t)szFormat, uxArg1, uxArg2, uxArg3); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 We need the addresses*/
		break;
	case 4:
		uxArg1 = va_arg(xVariableList, TraceUnsignedBaseType_t);
		uxArg2 = va_arg(xVariableList, TraceUnsignedBaseType_t);
		uxArg3 = va_arg(xVariableList, TraceUnsignedBaseType_t);
		uxArg4 = va_arg(xVariableList, TraceUnsignedBaseType_t);
		xResult = xTraceEventCreate6(PSF_EVENT_USER_EVENT_FIXED + 4UL, (TraceUnsignedBaseType_t)szChannel, (TraceUnsignedBaseType_t)szFormat, uxArg1, uxArg2, uxArg3, uxArg4); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 We need the addresses*/
		break;
	default:
		xResult = TRC_FAIL;
		break;
	}
	va_end(xVariableList);

	return xResult;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-16.1 Suppress variable parameter count check*/
traceResult xTracePrintF(TraceStringHandle_t xChannel, const char* szFormat, ...)
{
	traceResult xResult;
	va_list xVariableList; /*cstat !MISRAC2012-Rule-17.1 Suppress stdarg usage check*/

	/* We need to check this */
	if (xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_PRINT) == 0U)
	{
		return TRC_FAIL;
	}

	va_start(xVariableList, szFormat);
	xResult = xTraceVPrintF(xChannel, szFormat, &xVariableList);
	va_end(xVariableList);

	return xResult;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2012-Rule-17.1 Suppress stdarg usage check*/
traceResult xTraceVPrintF(TraceStringHandle_t xChannel, const char* szFormat, va_list* pxVariableList)
{
	uint32_t i;
	uint32_t uiArgs = 0u;
	uint32_t uiLength;

	/* We need to check this */
	if (xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_PRINT) == 0U)
	{
		return TRC_FAIL;
	}

	if (szFormat == (void*)0)
	{
		szFormat = ""; /*cstat !MISRAC2012-Rule-17.8 Suppress modified function parameter check*/
	}

	/* Count the number of arguments in the format string (e.g., %d) */
	for (i = 0u; (szFormat[i] != (char)0) && (i < 128u); i++) /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress char base type usage checks*/ /*cstat !MISRAC2012-Rule-14.2 Suppress malformed for loop due to i being incremented inside*/ /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/
	{
		if (szFormat[i] == '%') /*cstat !MISRAC2004-17.4_b We need to access a specific character in the string*/
		{
			if (szFormat[i + 1u] == (char)0) /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-17.4_b We need to access a specific character in the string*/
			{
				/* Found end of string, let for loop detect it */
				continue; /*cstat !MISRAC2004-14.5 Suppress continue usage check*/
			}

			if (szFormat[i + 1u] != '%') /*cstat !MISRAC2004-17.4_b We need to access a specific character in the string*/
			{
				uiArgs++;        /* Found an argument */
			}

			/* Move past format specifier or non-argument '%' */
			i++; /*cstat !MISRAC2004-13.6 Suppress i increment inside for loop check*/
		}
	}

	uiLength = i + 1u; /* Null termination */

	return prvTraceVPrintF(xChannel, szFormat, uiLength, uiArgs, pxVariableList);
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2012-Rule-17.1 Suppress stdarg usage check*/
static traceResult prvTraceVPrintF(TraceStringHandle_t xChannel, const char* szFormat, uint32_t uiLength, uint32_t uiArgs, va_list* pxVariableList)
{
	const uint32_t uiEventCode = PSF_EVENT_USER_EVENT + 1u + uiArgs; /* Add channel (1) */
	traceResult xResult;
	TraceUnsignedBaseType_t uxParam1;
	TraceUnsignedBaseType_t uxParam2;
	TraceUnsignedBaseType_t uxParam3;
	TraceUnsignedBaseType_t uxParam4;
	TraceUnsignedBaseType_t uxParam5;

	if (xChannel == 0)
	{
		if (pxPrintData->defaultChannel == 0)
		{
			/* Channel is not present */
			if (xTraceStringRegister("Default", &pxPrintData->defaultChannel) == TRC_FAIL)
			{
				return TRC_FAIL;
			}
		}

		xChannel = pxPrintData->defaultChannel; /*cstat !MISRAC2012-Rule-17.8 Suppress modified function parameter check*/
	}

	switch (uiArgs)
	{
		case 0:
			xResult = xTraceEventCreateData1(uiEventCode, (TraceUnsignedBaseType_t)xChannel, (TraceUnsignedBaseType_t*)szFormat, uiLength);
			break;
		case 1:
			uxParam1 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			xResult = xTraceEventCreateData2(
				uiEventCode,
				(TraceUnsignedBaseType_t)xChannel,
				uxParam1,
				(TraceUnsignedBaseType_t*)szFormat,
				uiLength
			);
			break;
		case 2:
			uxParam1 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			uxParam2 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			xResult = xTraceEventCreateData3(
				uiEventCode,
				(TraceUnsignedBaseType_t)xChannel,
				uxParam1,
				uxParam2,
				(TraceUnsignedBaseType_t*)szFormat,
				uiLength
			);
			break;
		case 3:
			uxParam1 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			uxParam2 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			uxParam3 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			xResult = xTraceEventCreateData4(
				uiEventCode,
				(TraceUnsignedBaseType_t)xChannel,
				uxParam1,
				uxParam2,
				uxParam3,
				(TraceUnsignedBaseType_t*)szFormat,
				uiLength
			);
			break;
		case 4:
			uxParam1 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			uxParam2 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			uxParam3 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			uxParam4 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			xResult = xTraceEventCreateData5(
				uiEventCode,
				(TraceUnsignedBaseType_t)xChannel,
				uxParam1,
				uxParam2,
				uxParam3,
				uxParam4,
				(TraceUnsignedBaseType_t*)szFormat,
				uiLength
			);
			break;
		case 5:
			uxParam1 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			uxParam2 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			uxParam3 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			uxParam4 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			uxParam5 = va_arg(*pxVariableList, TraceUnsignedBaseType_t);
			xResult = xTraceEventCreateData6(
				uiEventCode,
				(TraceUnsignedBaseType_t)xChannel,
				uxParam1,
				uxParam2,
				uxParam3,
				uxParam4,
				uxParam5,
				(TraceUnsignedBaseType_t*)szFormat,
				uiLength
			);
			break;
		default:
			xResult = TRC_FAIL;
			break;
	}

	return xResult;
}

#endif
