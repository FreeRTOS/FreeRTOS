/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/*
    Title: Trace

    About: Purpose
        Standard output methods for reporting debug information, warnings and
        errors, which can be turned on/off.

    About: Usage
        1 - Initialize the DBGU using <trace_CONFIGURE>.
        2 - Uses the <trace_LOG> macro to output traces throughout the program.
        3 - Turn off all traces by defining the NOTRACE symbol during
            compilation.
        4 - Disable a group of trace by changing the value of <trace_LEVEL>
            during compilation; traces with a level below <trace_LEVEL> are not
            generated.
*/

#ifndef TRACE_H
#define TRACE_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#if !defined(NOTRACE)
    #include <board.h>
    #include <dbgu/dbgu.h>
    #include <pio/pio.h>
    #include <stdio.h>
#endif

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------
/*
    Constants: Trace levels
        trace_FATAL - Indicates a major error which prevents the program from
            going any further.
        trace_ERROR - Indicates an error which may not stop the program
            execution, but which indicates there is a problem with the code.
        trace_WARNING - Indicates that a minor error has happened. In most case
            it can be discarded safely; it may even be expected.
        trace_INFO - Informational trace about the program execution. Should
            enable the user to see the execution flow.
        trace_DEBUG - Traces whose only purpose is for debugging the program,
            and which do not produce meaningful information otherwise.
*/
#define trace_DEBUG                     0
#define trace_INFO                      1
#define trace_WARNING                   2
#define trace_ERROR                     3
#define trace_FATAL                     4

/*
    Constant: trace_LEVEL
        Minimum level of traces that are output. By default, all traces are
        output; change the value of this symbol during compilation for a more
        restrictive behavior.
*/
#if !defined(trace_LEVEL)
    #define trace_LEVEL                     0
#endif

/*
    Macro: trace_CONFIGURE
        Initializes the DBGU unless the NOTRACE symbol has been defined.

    Parameters:
        mode - DBGU mode.
        baudrate - DBGU baudrate.
        mck - Master clock frequency.
*/
#if !defined(NOTRACE)
    #define trace_CONFIGURE(mode, baudrate, mck) { \
        const Pin pinsDbgu[] = {PINS_DBGU}; \
        PIO_Configure(pinsDbgu, PIO_LISTSIZE(pinsDbgu)); \
        DBGU_Configure(mode, baudrate, mck); \
    }
#else
    #define trace_CONFIGURE(...)
#endif

/*
    Macro: trace_LOG
        Outputs a formatted string using <printf> if the log level is high
        enough. Can be disabled by defining the NOTRACE symbol during
        compilation.

    Parameters:
        level - Trace level (see <Trace levels>).
        format - Formatted string to output.
        ... - Additional parameters, depending on the formatted string.
*/
#if !defined(NOTRACE)
    #define trace_LOG(level, ...) { \
        if (level >= trace_LEVEL) { \
            printf(__VA_ARGS__); \
        } \
    }
#else
    #define trace_LOG(...)
#endif

#endif //#ifndef TRACE_H

