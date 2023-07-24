// Copyright 2019-2021 XMOS LIMITED.
// This Software is subject to the terms of the XMOS Public Licence: Version 1.

#ifndef _rtos_printf_h_
#define _rtos_printf_h_

/**
Debug Printing Module
=====================

This module provides a lightweight RTOS safe printf function that can
be enabled or disabled via configuration macros. Code can be declared
to be within a "debug unit" (usually a module) and prints can be
enabled/disabled per debug unit.

This uses the same DEBUG macros as lib_logging to control "debug units",
but implements a slightly more capable and RTOS safe printf function.
It also provides sprintf and snprintf functions.

**/

#include "rtos_support_rtos_config.h"

#ifdef __rtos_support_conf_h_exists__
#include "rtos_support_conf.h"
#endif

#ifndef RTOS_DEBUG_PRINTF_REMAP
#define RTOS_DEBUG_PRINTF_REMAP 0
#endif

/* remap calls to debug_printf to rtos_printf */
#if RTOS_DEBUG_PRINTF_REMAP

    #ifdef _debug_printf_h_
    #error Do not include debug_print.h when using rtos_printf
    #endif

    /* Ensure that if debug_print.h is included later that it is ignored */
    #define _debug_printf_h_

    #define debug_printf rtos_printf

#endif /* RTOS_DEBUG_PRINTF_REMAP */

#ifndef DEBUG_UNIT
#define DEBUG_UNIT APPLICATION
#endif

#ifndef DEBUG_PRINT_ENABLE_ALL
#define DEBUG_PRINT_ENABLE_ALL 0
#endif

#ifndef DEBUG_PRINT_ENABLE
#define DEBUG_PRINT_ENABLE 0
#endif

#if !defined(DEBUG_PRINT_ENABLE_APPLICATION) && !defined(DEBUG_PRINT_DISABLE_APPLICATION)
#define DEBUG_PRINT_ENABLE_APPLICATION DEBUG_PRINT_ENABLE
#endif

#define DEBUG_UTILS_JOIN0(x,y) x ## y
#define DEBUG_UTILS_JOIN(x,y) DEBUG_UTILS_JOIN0(x,y)

#if DEBUG_UTILS_JOIN(DEBUG_PRINT_ENABLE_,DEBUG_UNIT)
#define DEBUG_PRINT_ENABLE0 1
#endif

#if DEBUG_UTILS_JOIN(DEBUG_PRINT_DISABLE_,DEBUG_UNIT)
#define DEBUG_PRINT_ENABLE0 0
#endif

#if !defined(DEBUG_PRINT_ENABLE0)
#define DEBUG_PRINT_ENABLE0 DEBUG_PRINT_ENABLE_ALL
#endif

#if defined(__cplusplus) || defined(__XC__)
extern "C" {
#endif

#include <stddef.h>
#include <stdarg.h>

/**
 * Just like snprintf, but not all of the
 * standard C format control are supported.
 */
int rtos_snprintf(char *str, size_t size, const char *fmt, ...);

/**
 * Just like sprintf, but not all of the
 * standard C format control are supported.
 */
int rtos_sprintf(char *str, const char *fmt, ...);

/**
 * Just like vprintf, but not all of the
 * standard C format control are supported.
 */
#ifndef __XC__
int rtos_vprintf(const char *fmt, va_list ap);
#endif

/**
 * Just like printf, but not all of the
 * standard C format control are supported.
 */
int rtos_printf(const char *fmt, ...);

#if defined(__cplusplus) || defined(__XC__)
}
#endif

#if DEBUG_PRINT_ENABLE0
#define rtos_vprintf(...) rtos_vprintf(__VA_ARGS__)
#define rtos_printf(...) rtos_printf(__VA_ARGS__)
#else
#define rtos_vprintf(...)
#define rtos_printf(...)
#endif

#endif // _rtos_printf_h_
