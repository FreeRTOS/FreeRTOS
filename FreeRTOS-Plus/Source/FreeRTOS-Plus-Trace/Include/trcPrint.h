/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*/

/**
 * @file 
 * 
 * @brief Public trace print APIs.
 */

#ifndef TRC_PRINT_H
#define TRC_PRINT_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <stdarg.h>
#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_print_apis Trace Print APIs
 * @ingroup trace_recorder_apis
 * @{
 */

#if (TRC_CFG_SCHEDULING_ONLY == 0) && (TRC_CFG_INCLUDE_USER_EVENTS == 1)

/** @internal */
#define TRC_PRINT_BUFFER_SIZE (sizeof(TraceStringHandle_t) + sizeof(TraceStringHandle_t))

/**
 * @internal Trace Print Buffer Structure
 */
typedef struct TracePrintBuffer
{
	uint32_t buffer[(TRC_PRINT_BUFFER_SIZE) / sizeof(uint32_t)];
} TracePrintBuffer_t;

/**
 * @internal Initialize print trace system.
 * 
 * @param[in] pxBuffer Pointer to memory that will be used by the print
 * trace system.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTracePrintInitialize(TracePrintBuffer_t* pxBuffer);

/**
 * @brief Generate "User Events" with unformatted text.
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
 * @param[in] xChannel Channel.
 * @param[in] szString String.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTracePrint(TraceStringHandle_t xChannel, const char* szString);

/**
 * @brief Wrapper for vTracePrintF for printing to default channel.
 * 
 * Wrapper for vTracePrintF, using the default channel. Can be used as a drop-in
 * replacement for printf and similar functions, e.g. in a debug logging macro.
 * 
 * Example:
 * 	// Old: #define LogString debug_console_printf
 * 	
 *  // New, log to Tracealyzer instead:
 *  #define LogString xTraceConsoleChannelPrintF
 *  ...
 *  LogString("My value is: %d", myValue);
 * 
 * @param[in] szFormat Format
 * @param[in] ... 
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceConsoleChannelPrintF(const char* szFormat, ...);

/**
 * @brief Generates "User Events" with formatted text and data.
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
 * @param[in] xChannel Channel.
 * @param[in] szFormat Format.
 * @param[in] ... 
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTracePrintF(TraceStringHandle_t xChannel, const char* szFormat, ...);

/**
 * @brief Generates "User Events" with formatted text and data.
 * 
 * @param[in] xChannel Channel.
 * @param[in] szFormat Format.
 * @param[in] xVL Variable list arguments.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceVPrintF(TraceStringHandle_t xChannel, const char* szFormat, va_list xVL);

#else /* (TRC_CFG_SCHEDULING_ONLY == 0) && (TRC_CFG_INCLUDE_USER_EVENTS == 1) */

typedef struct TracePrintBuffer
{
	uint32_t buffer[1];
} TracePrintBuffer_t;

#define xTracePrintInitialize(p) ((void)p, p != 0 ? TRC_SUCCESS : TRC_FAIL)

#define xTracePrint(c, s) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)c, (void)s, TRC_SUCCESS)

#define xTracePrintF(c, s, ...) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)c, (void)s, TRC_SUCCESS)

#define xTraceConsoleChannelPrintF(s, ...) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)s, TRC_SUCCESS)

#define xTraceVPrintF(c, s, v) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)c, (void)s, (void)v, TRC_SUCCESS)

#endif /* (TRC_CFG_SCHEDULING_ONLY == 0) && (TRC_CFG_INCLUDE_USER_EVENTS == 1) */

/** @} */

#ifdef __cplusplus
}
#endif

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */


#endif /* TRC_PRINT_H */
