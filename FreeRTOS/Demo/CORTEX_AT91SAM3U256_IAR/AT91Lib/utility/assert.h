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

//------------------------------------------------------------------------------
/// \unit
///
/// !Purpose
///
/// Definition of the ASSERT() and SANITY_CHECK() macros, which are used for
/// runtime condition & parameter verifying.
///
/// !Usage
///
/// -# Use ASSERT() in your code to check the value of function parameters,
///    return values, etc. *Warning:* the ASSERT() condition must not have
///    any side-effect; otherwise, the program may not work properly
///    anymore when assertions are disabled.
/// -# Use SANITY_CHECK() to perform checks with a default error message
///    (outputs the file and line number where the error occured). This 
///    reduces memory overhead caused by assertion error strings.
/// -# Initialize the dbgu to see failed assertions at run-time.
/// -# Assertions can be entirely disabled by defining the NOASSERT symbol
///    at compilation time.
//------------------------------------------------------------------------------

#ifndef ASSERT_H
#define ASSERT_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include <stdio.h>
#include "trace.h"

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------
#if defined(NOASSERT)
    #define ASSERT(...)
    #define SANITY_CHECK(...)
#else

    #if (TRACE_LEVEL == 0)
        /// Checks that the given condition is true, 
        /// otherwise stops the program execution.
        /// \param condition  Condition to verify.
        #define ASSERT(condition, ...)  { \
            if (!(condition)) { \
                while (1); \
            } \
        }

        /// Performs the same duty as the ASSERT() macro
        /// \param condition  Condition to verify.
        #define SANITY_CHECK(condition) ASSERT(condition, ...)

    #else
        /// Checks that the given condition is true, otherwise displays an error
        /// message and stops the program execution.
        /// \param condition  Condition to verify.
        #define ASSERT(condition, ...)  { \
            if (!(condition)) { \
                printf("-F- ASSERT: "); \
                printf(__VA_ARGS__); \
                while (1); \
            } \
        }
        #define SANITY_ERROR            "Sanity check failed at %s:%d\n\r"
    
        /// Performs the same duty as the ASSERT() macro, except a default error
        /// message is output if the condition is false.
        /// \param condition  Condition to verify.
        #define SANITY_CHECK(condition) ASSERT(condition, SANITY_ERROR, __FILE__, __LINE__)
    #endif
#endif










#endif //#ifndef ASSERT_H

