/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for print.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#if (TRC_CFG_SCHEDULING_ONLY == 0) && (TRC_CFG_INCLUDE_USER_EVENTS == 1)

#include <stdarg.h>

static traceResult prvTraceVPrintF(TraceStringHandle_t xChannel, const char* szFormat, uint32_t uiLength, uint32_t uiArgs, va_list *pxVL);

typedef struct TracePrintInfo
{
	TraceStringHandle_t defaultChannel;
	TraceStringHandle_t consoleChannel;
} TracePrintInfo_t;

static TracePrintInfo_t *pxPrintInfo;

traceResult xTracePrintInitialize(TracePrintBuffer_t *pxBuffer)
{
	TRC_ASSERT_EQUAL_SIZE(TracePrintBuffer_t, TracePrintInfo_t);
	
	/* This should never fail */
	TRC_ASSERT(pxBuffer != 0);

	pxPrintInfo = (TracePrintInfo_t*)pxBuffer;
	pxPrintInfo->defaultChannel = 0;
	pxPrintInfo->consoleChannel = 0;

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_PRINT);
	
	return TRC_SUCCESS;
}

/******************************************************************************
 * xTracePrint
 *
 * Generates "User Events", with unformatted text.
 *
 * User Events can be used for very efficient application logging, and are shown
 * as yellow labels in the main trace view.
 *
 * You may group User Events into User Event Channels. The yellow User Event
 * labels shows the logged string, preceded by the channel  name within
 * brackets. For example:
 *
 *  "[MyChannel] Hello World!"
 *
 * The User Event Channels are shown in the View Filter, which makes it easy to
 * select what User Events you wish to display. User Event Channels are created
 * using xTraceStringRegister().
 *
 * Example:
 *
 *	 TraceStringHandle_t xChannel = xTraceStringRegister("MyChannel");
 *	 ...
 *	 xTracePrint(xChannel, "Hello World!");
 *
 ******************************************************************************/
traceResult xTracePrint(TraceStringHandle_t xChannel, const char* szString)
{
	uint32_t uiLength = 0;
	uint32_t i = 0;
	
	/* We need to check this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_PRINT))
	{
		return TRC_FAIL;
	}

	if (szString == 0)
	{
		szString = "";
	}
	
	while ((szString[i] != 0) && (i < 128))
	{
		i++;
	}

	uiLength = i + 1; /* Null termination */

	return prvTraceVPrintF(xChannel, szString, uiLength, 0, (va_list*)0);
}

/*******************************************************************************
* xTraceConsoleChannelPrintF
*
* Wrapper for vTracePrint, using the default channel. Can be used as a drop-in
* replacement for printf and similar functions, e.g. in a debug logging macro.
*
* Example:
*
*	 // Old: #define LogString debug_console_printf
*
*    // New, log to Tracealyzer instead:
*	 #define LogString xTraceConsoleChannelPrintF
*	 ...
*	 LogString("My value is: %d", myValue);
******************************************************************************/
traceResult xTraceConsoleChannelPrintF(const char* szFormat, ...)
{
	traceResult xResult;
	va_list xVL;

	/* We need to check this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_PRINT))
	{
		return TRC_FAIL;
	}

	if (pxPrintInfo->consoleChannel == 0)
	{
		if (xTraceStringRegister("Debug Console", &pxPrintInfo->consoleChannel) == TRC_FAIL)
		{
			return TRC_FAIL;
		}
	}

	va_start(xVL, szFormat);
	xResult = xTraceVPrintF(pxPrintInfo->consoleChannel, szFormat, xVL);
	va_end(xVL);

	return xResult;
}

/******************************************************************************
 * xTracePrintF
 *
 * Generates "User Events", with formatted text and data, similar to a "printf".
 * It is very fast since the actual formatting is done on the host side when the
 * trace is displayed.
 *
 * User Events can be used for very efficient application logging, and are shown
 * as yellow labels in the main trace view.
 * An advantage of User Events is that data can be plotted in the "User Event
 * Signal Plot" view, visualizing any data you log as User Events, discrete
 * states or control system signals (e.g. system inputs or outputs).
 *
 * You may group User Events into User Event Channels. The yellow User Event
 * labels show the logged string, preceded by the channel name within brackets.
 *
 * Example:
 *
 *  "[MyChannel] Hello World!"
 *
 * The User Event Channels are shown in the View Filter, which makes it easy to
 * select what User Events you wish to display. User Event Channels are created
 * using xTraceStringRegister().
 *
 * Example:
 *
 *	 TraceStringHandle_t adc_uechannel = xTraceStringRegister("ADC User Events");
 *	 ...
 *	 xTracePrintF(adc_uechannel,
 *				 "ADC channel %d: %d volts",
 *				 ch, adc_reading);
 *
 * All data arguments are assumed to be 32 bit wide. The following formats are
 * supported:
 * %d - signed integer. The following width and padding format is supported: "%05d" -> "-0042" and "%5d" -> "  -42"
 * %u - unsigned integer. The following width and padding format is supported: "%05u" -> "00042" and "%5u" -> "   42"
 * %X - hexadecimal (uppercase). The following width and padding format is supported: "%04X" -> "002A" and "%4X" -> "  2A"
 * %x - hexadecimal (lowercase). The following width and padding format is supported: "%04x" -> "002a" and "%4x" -> "  2a"
 * %s - string (currently, this must be an earlier stored symbol name)
 *
 * Up to 15 data arguments are allowed, with a total size of maximum 60 byte
 * including 8 byte for the base event fields and the format string. So with
 * one data argument, the maximum string length is 48 chars. If this is exceeded
 * the string is truncated (4 bytes at a time).
 *
 ******************************************************************************/
traceResult xTracePrintF(TraceStringHandle_t xChannel, const char* szFormat, ...)
{
	traceResult xResult;
	va_list xVL;

	/* We need to check this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_PRINT))
	{
		return TRC_FAIL;
	}

	va_start(xVL, szFormat);
	xResult = xTraceVPrintF(xChannel, szFormat, xVL);
	va_end(xVL);

	return xResult;
}

/******************************************************************************
 * xTraceVPrintF
 *
 * xTracePrintF variant that accepts a va_list.
 * See xTraceVPrintF documentation for further details.
 *
 ******************************************************************************/
traceResult xTraceVPrintF(TraceStringHandle_t xChannel, const char* szFormat, va_list xVL)
{
	uint32_t i = 0;
	uint32_t uiArgs = 0;
	uint32_t uiLength;

	/* We need to check this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_PRINT))
	{
		return TRC_FAIL;
	}

	if (szFormat == 0)
	{
		szFormat = "";
	}

	/* Count the number of arguments in the format string (e.g., %d) */
	for (i = 0; (szFormat[i] != 0) && (i < 128); i++)
	{
		if (szFormat[i] == '%')
		{
			if (szFormat[i + 1] == 0)
			{
				/* Found end of string, let for loop detect it */
				continue;
			}

			if (szFormat[i + 1] != '%')
			{
				uiArgs++;        /* Found an argument */
			}

			i++;      /* Move past format specifier or non-argument '%' */
		}
	}

	uiLength = i + 1; /* Null termination */

	return prvTraceVPrintF(xChannel, szFormat, uiLength, uiArgs, &xVL);
}

static traceResult prvTraceVPrintF(TraceStringHandle_t xChannel, const char* szFormat, uint32_t uiLength, uint32_t uiArgs, va_list *pxVL)
{
	TraceEventHandle_t xEventHandle = 0;
	uint32_t i, uiRemaining;
	uint32_t uiValue;
	uint32_t uiEventCode = PSF_EVENT_USER_EVENT + 1 + uiArgs; /* Add channel (1) */
	uint32_t uiSize = sizeof(void*) + uiArgs * sizeof(TraceUnsignedBaseType_t) + uiLength; /* Add channel (sizeof(void*)) */

	if (xChannel == 0)
	{
		if (pxPrintInfo->defaultChannel == 0)
		{
			/* Channel is not present */
			if (xTraceStringRegister("Default", &pxPrintInfo->defaultChannel) == TRC_FAIL)
			{
				return TRC_FAIL;
			}
		}

		xChannel = pxPrintInfo->defaultChannel;
	}

	/* Added channel to uiEventCode and uiSize */
	if (xTraceEventBegin(uiEventCode, uiSize , &xEventHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/* Add xChannel */
	xTraceEventAddPointer(xEventHandle, (void*)xChannel);

	/* Add all arguments */
	for (i = 0; i < uiArgs; i++)
	{
		xTraceEventAddUnsignedBaseType(xEventHandle, va_arg(*pxVL, TraceUnsignedBaseType_t));
	}

	xTraceEventPayloadRemaining(xEventHandle, &uiRemaining);
	if (uiRemaining < uiLength)
	{
		uiLength = uiRemaining - 1; /* Make room for null termination */
	}

	/* Add format string */
	xTraceEventAddData(xEventHandle, (void*)szFormat, uiLength);

	/* Check if we can truncate */
	xTraceEventPayloadRemaining(xEventHandle, &uiValue);
	if (uiValue > 0)
	{
		xTraceEventAdd8(xEventHandle, 0);
	}

	xTraceEventEnd(xEventHandle);

	return TRC_SUCCESS;
}

#endif /* (TRC_CFG_SCHEDULING_ONLY == 0) && (TRC_CFG_INCLUDE_USER_EVENTS == 1) */

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
