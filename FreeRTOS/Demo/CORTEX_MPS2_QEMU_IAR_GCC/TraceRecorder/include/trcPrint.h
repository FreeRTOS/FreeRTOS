/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
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

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) && (TRC_CFG_INCLUDE_USER_EVENTS == 1)

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

typedef struct TracePrintData	/* Aligned */
{
	TraceStringHandle_t defaultChannel;
	TraceStringHandle_t consoleChannel;
} TracePrintData_t;

/**
 * @internal Initialize print trace system.
 * 
 * @param[in] pxBuffer Pointer to memory that will be used by the print
 * trace system.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTracePrintInitialize(TracePrintData_t* pxBuffer);

/**
 * @brief Generate a "User Event". Channel and format string are only stored in ELF.
 *
 * This is a compact version of xTracePrintF(). Only addresses to channel and format strings are stored and an ELF file must be provided to interpret the trace.
 * NOTE! All parameters must be cast to TraceUnsignedBaseType_t/TraceBaseType_t!
 *
 * Example:
 *	xTracePrintCompact("MyChannel", "MyFormat %d", 1);
 *
 * @param[in] szChannel Channel string.
 * @param[in] szFormat Format string.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTracePrintCompactF(const char* szChannel, const char* szFormat, ...);

/**
 * @brief Generate a "User Event" with 0 parameters. Channel and format string are only stored in ELF.
 *
 * This is a compact and fixed version of xTracePrintF(). Only addresses to channel and format strings are stored and an ELF file must be provided to interpret the trace.
 *
 * Example:
 *	xTraceDependencyRegister("my_project.elf", TRC_DEPENDENCY_TYPE_ELF);
 *	...
 *	xTracePrintCompactF0("MyChannel", "MyText");
 *
 * @param[in] szChannel Channel string.
 * @param[in] szFormat Format string.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTracePrintCompactF0(szChannel, szFormat) xTraceEventCreate2(PSF_EVENT_USER_EVENT_FIXED, (TraceUnsignedBaseType_t)(szChannel), (TraceUnsignedBaseType_t)(szFormat))

/**
 * @brief Generate a "User Event" with 1 parameter. Channel and format string are only stored in ELF.
 *
 * This is a compact and fixed version of xTracePrintF(). Only addresses to channel and format strings are stored and an ELF file must be provided to interpret the trace.
 *
 * Example:
 *	xTraceDependencyRegister("my_project.elf", TRC_DEPENDENCY_TYPE_ELF);
 *	...
 *	xTracePrintCompactF1("MyChannel", "MyFormat %u", 1);
 *
 * @param[in] szChannel Channel string.
 * @param[in] szFormat Format string.
 * @param[in] uxParam1 First parameter.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTracePrintCompactF1(szChannel, szFormat, uxParam1) xTraceEventCreate3(PSF_EVENT_USER_EVENT_FIXED + 1, (TraceUnsignedBaseType_t)(szChannel), (TraceUnsignedBaseType_t)(szFormat), uxParam1)

/**
 * @brief Generate a "User Event" with 2 parameters. Channel and format string are only stored in ELF.
 *
 * This is a compact and fixed version of xTracePrintF(). Only addresses to channel and format strings are stored and an ELF file must be provided to interpret the trace.
 *
 * Example
 *	xTraceDependencyRegister("my_project.elf", TRC_DEPENDENCY_TYPE_ELF);
 *	...
 *	xTracePrintCompactF2("MyChannel", "MyFormat %u %u", 1, 2);
 *
 * @param[in] szChannel Channel string.
 * @param[in] szFormat Format string.
 * @param[in] uxParam1 First parameter.
 * @param[in] uxParam2 Second parameter.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTracePrintCompactF2(szChannel, szFormat, uxParam1, uxParam2) xTraceEventCreate4(PSF_EVENT_USER_EVENT_FIXED + 2, (TraceUnsignedBaseType_t)(szChannel), (TraceUnsignedBaseType_t)(szFormat), uxParam1, uxParam2)

/**
 * @brief Generate a "User Event" with 3 parameters. Channel and format string are only stored in ELF.
 *
 * This is a compact and fixed version of xTracePrintF(). Only addresses to channel and format strings are stored and an ELF file must be provided to interpret the trace.
 *
 * Example:
 *	xTraceDependencyRegister("my_project.elf", TRC_DEPENDENCY_TYPE_ELF);
 *	...
 *	xTracePrintCompactF3("MyChannel", "MyFormat %u %u %u", 1, 2, 3);
 *
 * @param[in] szChannel Channel string.
 * @param[in] szFormat Format string.
 * @param[in] uxParam1 First parameter.
 * @param[in] uxParam2 Second parameter.
 * @param[in] uxParam3 Third parameter.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTracePrintCompactF3(szChannel, szFormat, uxParam1, uxParam2, uxParam3) xTraceEventCreate5(PSF_EVENT_USER_EVENT_FIXED + 3, (TraceUnsignedBaseType_t)(szChannel), (TraceUnsignedBaseType_t)(szFormat), uxParam1, uxParam2, uxParam3)

/**
 * @brief Generate a "User Event" with 4 parameters. Channel and format string are only stored in ELF.
 *
 * This is a compact and fixed version of xTracePrintF(). Only addresses to channel and format strings are stored and an ELF file must be provided to interpret the trace.
 *
 * Example:
 *	xTraceDependencyRegister("my_project.elf", TRC_DEPENDENCY_TYPE_ELF);
 *	...
 *	xTracePrintCompactF4("MyChannel", "MyFormat %u %u %u %u", 1, 2, 3, 4);
 *
 * @param[in] szChannel Channel string.
 * @param[in] szFormat Format string.
 * @param[in] uxParam1 First parameter.
 * @param[in] uxParam2 Second parameter.
 * @param[in] uxParam3 Third parameter.
 * @param[in] uxParam4 Fourth parameter.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTracePrintCompactF4(szChannel, szFormat, uxParam1, uxParam2, uxParam3, uxParam4) xTraceEventCreate6(PSF_EVENT_USER_EVENT_FIXED + 4, (TraceUnsignedBaseType_t)(szChannel), (TraceUnsignedBaseType_t)(szFormat), uxParam1, uxParam2, uxParam3, uxParam4)

/**
 * @brief Generate a "User Event" with 0 parameters.
 *
 * This is a highly optimized version of xTracePrintF().
 * The channel and format string must be registered using xTraceStringRegister().
 *
 * Example:
 * 	TraceStringHandle_t xChannel;
 * 	TraceStringHandle_t xHelloWorld;
 *
 *	xTraceStringRegister("MyChannel", &xChannel);
 *	xTraceStringRegister("Hello world!", &xHelloWorld);
 *	...
 *	xTracePrintFormat0(xChannel, xHelloWorld);
 *
 * @param[in] xChannel Channel handle.
 * @param[in] xFormatStringHandle Format string handle.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTracePrintF0(xChannelStringHandle, xFormatStringHandle) xTraceEventCreate2(PSF_EVENT_USER_EVENT_FIXED, (TraceUnsignedBaseType_t)(xChannelStringHandle), (TraceUnsignedBaseType_t)(xFormatStringHandle))

/**
 * @brief Generate a "User Event" with 1 parameter.
 *
 * This is a highly optimized version of xTracePrintF().
 * The channel and format string must be registered using xTraceStringRegister().
 *
 * Example:
 * 	TraceStringHandle_t xChannel;
 * 	TraceStringHandle_t xHelloWorld;
 *
 *	xTraceStringRegister("MyChannel", &xChannel);
 *	xTraceStringRegister("Hello world! %d", &xHelloWorld);
 *	...
 *	xTracePrintFormat1(xChannel, xHelloWorld, 1);
 *
 * @param[in] xChannel Channel handle.
 * @param[in] xFormatStringHandle Format string handle.
 * @param[in] uxParam1 First parameter.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTracePrintF1(xChannelStringHandle, xFormatStringHandle, uxParam1) xTraceEventCreate3(PSF_EVENT_USER_EVENT_FIXED + 1, (TraceUnsignedBaseType_t)(xChannelStringHandle), (TraceUnsignedBaseType_t)(xFormatStringHandle), uxParam1)

/**
 * @brief Generate a "User Event" with 2 parameters.
 *
 * This is a highly optimized version of xTracePrintF().
 * The channel and format string must be registered using xTraceStringRegister().
 *
 * Example:
 * 	TraceStringHandle_t xChannel;
 * 	TraceStringHandle_t xHelloWorld;
 *
 *	xTraceStringRegister("MyChannel", &xChannel);
 *	xTraceStringRegister("Hello world! %d %d", &xHelloWorld);
 *	...
 *	xTracePrintFormat2(xChannel, xHelloWorld, 1, 2);
 *
 * @param[in] xChannel Channel handle.
 * @param[in] xFormatStringHandle Format string handle.
 * @param[in] uxParam1 First parameter.
 * @param[in] uxParam2 Second parameter.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTracePrintF2(xChannelStringHandle, xFormatStringHandle, uxParam1, uxParam2) xTraceEventCreate4(PSF_EVENT_USER_EVENT_FIXED + 2, (TraceUnsignedBaseType_t)(xChannelStringHandle), (TraceUnsignedBaseType_t)(xFormatStringHandle), uxParam1, uxParam2)

/**
 * @brief Generate a "User Event" with 3 parameters.
 *
 * This is a highly optimized version of xTracePrintF().
 * The channel and format string must be registered using xTraceStringRegister().
 *
 * Example:
 * 	TraceStringHandle_t xChannel;
 * 	TraceStringHandle_t xHelloWorld;
 *
 *	xTraceStringRegister("MyChannel", &xChannel);
 *	xTraceStringRegister("Hello world! %d %d %d", &xHelloWorld);
 *	...
 *	xTracePrintFormat3(xChannel, xHelloWorld, 1, 2, 3);
 *
 * @param[in] xChannel Channel handle.
 * @param[in] xFormatStringHandle Format string handle.
 * @param[in] uxParam1 First parameter.
 * @param[in] uxParam2 Second parameter.
 * @param[in] uxParam3 Third parameter.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTracePrintF3(xChannelStringHandle, xFormatStringHandle, uxParam1, uxParam2, uxParam3) xTraceEventCreate5(PSF_EVENT_USER_EVENT_FIXED + 3, (TraceUnsignedBaseType_t)(xChannelStringHandle), (TraceUnsignedBaseType_t)(xFormatStringHandle), uxParam1, uxParam2, uxParam3)

/**
 * @brief Generate a "User Event" with 4 parameters.
 *
 * This is a highly optimized version of xTracePrintF().
 * The channel and format string must be registered using xTraceStringRegister().
 *
 * Example:
 * 	TraceStringHandle_t xChannel;
 * 	TraceStringHandle_t xHelloWorld;
 *
 *	xTraceStringRegister("MyChannel", &xChannel);
 *	xTraceStringRegister("Hello world! %d %d %d %d", &xHelloWorld);
 *	...
 *	xTracePrintFormat4(xChannel, xHelloWorld, 1, 2, 3, 4);
 *
 * @param[in] xChannel Channel handle.
 * @param[in] xFormatStringHandle Format string handle.
 * @param[in] uxParam1 First parameter.
 * @param[in] uxParam2 Second parameter.
 * @param[in] uxParam3 Third parameter.
 * @param[in] uxParam4 Fourth parameter.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTracePrintF4(xChannelStringHandle, xFormatStringHandle, uxParam1, uxParam2, uxParam3, uxParam4) xTraceEventCreate6(PSF_EVENT_USER_EVENT_FIXED + 4, (TraceUnsignedBaseType_t)(xChannelStringHandle), (TraceUnsignedBaseType_t)(xFormatStringHandle), uxParam1, uxParam2, uxParam3, uxParam4)

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
 *	 TraceStringHandle_t xChannel;
 *	 xTraceStringRegister("MyChannel", &xChannel);
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
 * @brief Wrapper for xTracePrintF for printing to default channel.
 * 
 * Wrapper for vTracePrintF, using the default channel. Can be used as a drop-in
 * replacement for printf and similar functions, e.g. in a debug logging macro.
 * NOTE! All parameters must be cast to TraceUnsignedBaseType_t/TraceBaseType_t!
 * 
 * Example:
 * 	// Old: #define LogString debug_console_printf
 * 	
 *  // New, log to Tracealyzer instead:
 *  #define LogString xTraceConsoleChannelPrintF
 *  ...
 *  LogString("My value is: %d", myValue);
 * 
 * @param[in] szFormat Format.
 * @param[in] ... Parameters.
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
 *	 TraceStringHandle_t adc_uechannel;
 *	 xTraceStringRegister("ADC User Events", &adc_uechannel);
 *	 ...
 *	 xTracePrintF(adc_uechannel,
 *				 "ADC channel %d: %d volts",
 *				 ch, (TraceBaseType_t)adc_reading);
 *
 * NOTE! All data arguments must be TraceUnsignedBaseType_t or TraceBaseType_t.
 *
 * The following formats are supported:
 * %d - signed integer. The following width and padding format is supported: "%05d" -> "-0042" and "%5d" -> "  -42"
 * %u - unsigned integer. The following width and padding format is supported: "%05u" -> "00042" and "%5u" -> "   42"
 * %X - hexadecimal (uppercase). The following width and padding format is supported: "%04X" -> "002A" and "%4X" -> "  2A"
 * %x - hexadecimal (lowercase). The following width and padding format is supported: "%04x" -> "002a" and "%4x" -> "  2a"
 * %s - string. A TraceStringHandle_t from a string that was stored using xTraceStringRegister(...).
 *
 * A maximum of 5 parameters will be stored in the event along with the format string.
 * On a 32-bit system; a maximum size of 52 bytes is allowed for the parameters and format string combined. Each parameter takes 4 bytes.
 * On a 64-bit system; a maximum size of 112 bytes is allowed for the parameters and format string combined. Each parameter takes 8 bytes.
 * The format string will be truncated if maximum size is exceeded.
 * 
 * @param[in] xChannel Channel.
 * @param[in] szFormat Format.
 * @param[in] ... Parameters.
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
 * @param[in] pxVariableList Pointer to variable list arguments.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceVPrintF(TraceStringHandle_t xChannel, const char* szFormat, va_list* pxVariableList);

/** @} */

#ifdef __cplusplus
}
#endif

#else

typedef struct TracePrintData
{
	TraceUnsignedBaseType_t buffer[1];
} TracePrintData_t;

#define xTracePrintInitialize(__pvBuffer) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(__pvBuffer), TRC_SUCCESS)

#define xTracePrint(_c, _s) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_c), (void)(_s), TRC_SUCCESS)

#define xTracePrintF(_c, _s, ...) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_c), (void)(_s), TRC_SUCCESS)

#define xTraceConsoleChannelPrintF(_s, ...) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(_s), TRC_SUCCESS)

#define xTraceVPrintF(_c, _s, _v) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(_c), (void)(_s), (void)(_v), TRC_SUCCESS)

#define xTracePrintF0(_c, _f) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_c), (void)(_f), TRC_SUCCESS)
#define xTracePrintF1(_c, _f, _p1) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(_c), (void)(_f), (void)(_p1), TRC_SUCCESS)
#define xTracePrintF2(_c, _f, _p1, _p2) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_5((void)(_c), (void)(_f), (void)(_p1), (void)(_p2), TRC_SUCCESS)
#define xTracePrintF3(_c, _f, _p1, _p2, _p3) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_6((void)(_c), (void)(_f), (void)(_p1), (void)(_p2), (void)(_p3), TRC_SUCCESS)
#define xTracePrintF4(_c, _f, _p1, _p2, _p3, _p4) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_7((void)(_c), (void)(_f), (void)(_p1), (void)(_p2), (void)(_p3), (void)(_p4), TRC_SUCCESS)

#define xTracePrintCompactF xTracePrintF
#define xTracePrintCompactF0 xTracePrintF0
#define xTracePrintCompactF1 xTracePrintF1
#define xTracePrintCompactF2 xTracePrintF2
#define xTracePrintCompactF3 xTracePrintF3
#define xTracePrintCompactF4 xTracePrintF4

#endif

#endif
