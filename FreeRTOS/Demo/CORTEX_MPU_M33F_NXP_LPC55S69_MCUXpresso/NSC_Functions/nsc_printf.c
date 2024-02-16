/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/* ARM includes. */
#include <arm_cmse.h>

/* Interface includes. */
#include "nsc_printf.h"

/* FreeRTOS includes. */
#include "secure_port_macros.h"

/* Device includes. */
#include "fsl_debug_console.h"
/*-----------------------------------------------------------*/

/* Maximum length of the string that the non-secure code
 * can print. */
#define MAX_ALLOWED_STRING_LENGTH   0x400
/*-----------------------------------------------------------*/

secureportNON_SECURE_CALLABLE void NSC_Printf( char const *str )
{
    uint32_t isInvalidSting = 0;
    size_t stringLength;

    /* Check whether the string is null terminated. */
    stringLength = strnlen( str, MAX_ALLOWED_STRING_LENGTH );

    if( ( stringLength == MAX_ALLOWED_STRING_LENGTH ) &&
        ( str[ stringLength ] != '\0') )
    {
        PRINTF( "[ERROR] [NSC_Printf] String too long or not null terminated!\r\n" );
        isInvalidSting = 1;
    }

    if( isInvalidSting == 0 )
    {
        /* Check whether the string is located in non-secure memory. */
        if( cmse_check_address_range( ( void * ) str,
                                      stringLength,
                                      ( CMSE_NONSECURE | CMSE_MPU_READ ) ) == NULL )
        {
            PRINTF( "[ERROR] [NSC_Printf] String is not located in non-secure memory!\r\n" );
            isInvalidSting = 1;
        }
    }

    /* Print the string if it is a valid string. */
    if( isInvalidSting == 0 )
    {
        PRINTF( str );
    }
}
/*-----------------------------------------------------------*/
