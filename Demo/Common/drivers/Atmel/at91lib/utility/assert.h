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
    Title: Assert

    About: Purpose
        Definition of the ASSERT() macro, which is used for runtime condition
        verifying.

    About: Usage
        1 - Use <ASSERT> in your code to check the value of function parameters,
            return values, etc. *Warning:* the ASSERT condition must not have
            any side-effect; otherwise, the program may not work properly
            anymore when assertions are disabled.
        2 - Use SANITY_CHECK to perform checks with a default error message
            (outputs the file and line number where the error occured). This 
            reduces memory overhead caused by assertion error strings.
        3 - Initialize the <DBGU> to see failed assertions at run-time.
        4 - Disable assertions by defining the NOASSERT symbol at compilation
            time.
*/

#ifndef ASSERT_H
#define ASSERT_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include <stdio.h>

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------
/*
    Macro: ASSERT
        Check that the given condition is true, otherwise displays an error
        message and stops the program execution.

    Parameters:
        condition - Condition to verify.
        string - Formatted string to output if the condition fails.
        ... - Additional arguments depending on the formatted string.
*/
#if !defined(NOASSERT) && !defined(NOTRACE)

    //char sanityError[] = "Sanity check failed at %s:%d\n\r";

    #define ASSERT(condition, ...)  { \
        if (!(condition)) { \
            printf(__VA_ARGS__); \
            while (1); \
        } \
    }
    #define SANITY_ERROR            "Sanity check failed at %s:%d\n\r"
    #define SANITY_CHECK(condition) ASSERT(condition, SANITY_ERROR, __FILE__, __LINE__)
#else
    #define ASSERT(...)
    #define SANITY_CHECK(...)
#endif

#endif //#ifndef ASSERT_H

