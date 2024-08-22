/*             ----> DO NOT REMOVE THE FOLLOWING NOTICE <----
 *
 *                 Copyright (c) 2014-2015 Datalight, Inc.
 *                     All Rights Reserved Worldwide.
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; use version 2 of the License.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but "AS-IS," WITHOUT ANY WARRANTY; without even the implied warranty
 *  of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

/*  Businesses and individuals that for commercial or other reasons cannot
 *  comply with the terms of the GPLv2 license may obtain a commercial license
 *  before incorporating Reliance Edge into proprietary software for
 *  distribution in any form.  Visit http://www.datalight.com/reliance-edge for
 *  more information.
 */

/** @file
 *  @brief Implements utilities that convert strings to numbers.
 */
#include <redfs.h>
#include <redtestutils.h>


#define ISHEXDIGITU( c )    ( ( ( c ) >= 'A' ) && ( ( c ) <= 'F' ) )
#define ISHEXDIGITL( c )    ( ( ( c ) >= 'a' ) && ( ( c ) <= 'f' ) )
#define ISHEXDIGIT( c )     ( ISHEXDIGITL( c ) || ISHEXDIGITU( c ) )


/** @brief Converts an ASCII number into an int32_t.
 *
 *  Converts all decimal digit numbers up to the end of the string or to the
 *  first non-numerical character.
 *
 *  @note This function does *not* ignore leading white space.
 *
 *  @param pszNum   Pointer to a constant array of characters.
 *
 *  @return The integer represented in the string.
 */
int32_t RedAtoI( const char * pszNum )
{
    int32_t lValue = 0;
    int32_t lNegative = 1;
    uint32_t ulIdx = 0U;

    if( pszNum[ ulIdx ] == '+' )
    {
        ulIdx++;
    }
    else if( pszNum[ ulIdx ] == '-' )
    {
        ulIdx++;
        lNegative = -1;
    }
    else
    {
        /*  No sign, implicitly positive.
         */
    }

    while( ISDIGIT( pszNum[ ulIdx ] ) )
    {
        lValue *= 10;
        lValue += pszNum[ ulIdx ] - '0';
        ulIdx++;
    }

    lValue *= lNegative;

    return lValue;
}


/** @brief Convert a hexadecimal ASCII number into a uint32_t value.
 *
 *  The function processes all hex digits up to a NUL-terminator, or to the
 *  first non-hex character.  Only hexadecimal digits are processed, so leading
 *  white space, or a leading "0x" prefix are not allowed.
 *
 *  If pszNum points to an empty string (points to a NUL), this function will
 *  return NULL, and the value at *pulNum will not be modified.
 *
 *  @note This function does not check for overflow.  If there are more
 *        significant digits than can be represented in a uint32_t variable, the
 *        output is unspecified.
 *
 *  @param pszNum   A pointer to a constant array of hex characters.
 *  @param pulNum   A pointer to the location in which to store the uint32_t
 *                  result.  Upon return, this value will be modified ONLY if
 *                  the function succeeds and the returned pointer is valid (not
 *                  NULL).
 *
 *  @return A pointer to the byte following the converted number or NULL to
 *          indicate failure.
 */
const char * RedHtoUL( const char * pszNum,
                       uint32_t * pulNum )
{
    uint64_t ullValue;
    const char * pszReturn;

    pszReturn = RedHtoULL( pszNum, &ullValue );

    if( pszReturn != NULL )
    {
        if( ullValue < UINT32_MAX )
        {
            *pulNum = ( uint32_t ) ullValue;
        }
        else
        {
            pszReturn = NULL;
        }
    }

    return pszReturn;
}


/** @brief Convert a hexadecimal ASCII number into a D_UINT64 value.
 *
 *  The function processes all hex digits up to a NUL-terminator, or to the
 *  first non-hex character.  Only hexadecimal digits are processed, so leading
 *  white space, or a leading "0x" prefix are not allowed.
 *
 *  If pszNum points to an empty string (points to a NUL), this function will
 *  return NULL, and the value at *pulNum will not be modified.
 *
 *  @note This function does not check for overflow.  If there are more
 *        significant digits than can be represented in a uint64_t variable, the
 *        output is unspecified.
 *
 *  @param pszNum   A pointer to a constant array of hex characters.
 *  @param pullNum  A pointer to the location in which to store the uint64_t
 *                  result.  Upon return, this value will be modified ONLY if
 *                  the function succeeds and the returned pointer is valid (not
 *                  NULL).
 *
 *  @return A pointer to the byte following the converted number, or NULL to
 *          indicate failure.
 */
const char * RedHtoULL( const char * pszNum,
                        uint64_t * pullNum )
{
    uint64_t ullValue = 0U;
    const char * pszReturn = NULL;
    uint32_t ulIdx = 0U;

    REDASSERT( pszNum != NULL );
    REDASSERT( pullNum != NULL );

    while( pszNum[ ulIdx ] != '\0' )
    {
        char cDigit = pszNum[ ulIdx ];

        if( ISDIGIT( cDigit ) )
        {
            cDigit -= '0';
        }
        else if( ISHEXDIGITU( cDigit ) )
        {
            cDigit -= ( 'A' - 10 );
        }
        else if( ISHEXDIGITL( cDigit ) )
        {
            cDigit -= ( 'a' - 10 );
        }
        else
        {
            break;
        }

        REDASSERT( ( ullValue & UINT64_SUFFIX( 0xF000000000000000 ) ) == 0U );

        ullValue <<= 4U;
        ullValue += cDigit;

        ulIdx++;
        pszReturn = &pszNum[ ulIdx ];
    }

    /*  Modify the number returned only if we found one or more valid hex
     *  digits.
     */
    if( pszReturn != NULL )
    {
        *pullNum = ullValue;
    }

    return pszReturn;
}


/** @brief Convert the ASCII number to a uint32_t  value.
 *
 *  The number may be hex or decimal.  Hex numbers must be prefixed by '0x', and
 *  they may be upper or lower case.  The conversion process will stop with the
 *  first non hex or decimal digit.
 *
 *  If the number is negative (the first character is a '-' sign), the value
 *  will be range checked and returned as the equivalent unsigned value.
 *
 *  @note   This function will NOT fail for numbers which exceed the size of a
 *          uint32_t value.
 *
 *  @param pszNum   A pointer to the ASCII number to convert
 *  @param pulNum   A pointer to the uint32_t location to store the result.
 *                  This value will be modified on return only if the function
 *                  succeeds and the returned pointer is valid (not NULL).
 *
 *  @return A pointer to the byte following the converted number, or NULL to
 *          indicate failure.
 */
const char * RedNtoUL( const char * pszNum,
                       uint32_t * pulNum )
{
    bool fNegative = false;
    uint32_t ulIdx = 0U;
    const char * pszReturn;

    REDASSERT( pszNum != NULL );
    REDASSERT( pulNum != NULL );

    if( pszNum[ ulIdx ] == '-' )
    {
        fNegative = true;
        ulIdx++;
    }

    /*  Hex numbers must be prefixed with '0x'.
     */
    if( ( pszNum[ ulIdx ] == '0' ) && ( ( pszNum[ ulIdx + 1U ] == 'x' ) || ( pszNum[ ulIdx + 1U ] == 'X' ) ) )
    {
        ulIdx += 2U;

        if( ISDIGIT( pszNum[ ulIdx ] ) || ISHEXDIGIT( pszNum[ ulIdx ] ) )
        {
            pszReturn = RedHtoUL( &pszNum[ ulIdx ], pulNum );
        }
        else
        {
            pszReturn = NULL;
        }
    }
    else if( ISDIGIT( pszNum[ ulIdx ] ) )
    {
        uint32_t ulTemp;

        ulTemp = RedAtoI( &pszNum[ ulIdx ] );

        while( ISDIGIT( pszNum[ ulIdx ] ) )
        {
            ulIdx++;
        }

        if( fNegative )
        {
            /*  Fail if the number is out of range.
             */
            if( ulTemp > INT32_MAX )
            {
                pszReturn = NULL;
            }
            else
            {
                *pulNum = -( ( int32_t ) ulTemp );
                pszReturn = &pszNum[ ulIdx ];
            }
        }
        else
        {
            *pulNum = ulTemp;
            pszReturn = &pszNum[ ulIdx ];
        }
    }
    else
    {
        /*  Return an error if there is not at least one hex or decimal digit.
         */
        pszReturn = NULL;
    }

    return pszReturn;
}


/** @brief Convert the ASCII number pointed to by pszNum to a uint64_t value.
 *
 *  The number may be hex or decimal.  Hex numbers must be prefixed by '0x', and
 *  they may be upper or lower case.  The conversion process will stop with the
 *  first non hex or decimal digit.
 *
 *  If the number is negative (the first character is a '-' sign), the value
 *  will be range checked and returned as the equivalent unsigned value.
 *
 *  @param pszNum   A pointer to the ASCII number to convert.
 *  @param pullNum  A pointer to the uint64_t location to store the result.
 *                  This value will be modified on return only if the function
 *                  succeeds and the returned pointer is valid (not NULL).
 *
 *  @return A pointer to the byte following the converted number, or NULL to
 *          indicate failure.
 */
const char * RedNtoULL( const char * pszNum,
                        uint64_t * pullNum )
{
    bool fNegative = false;
    uint32_t ulIdx = 0U;
    const char * pszReturn;

    REDASSERT( pszNum != NULL );
    REDASSERT( pullNum != NULL );

    if( pszNum[ ulIdx ] == '-' )
    {
        fNegative = true;
        ulIdx++;
    }

    /*  Hex numbers must be prefixed with '0x'.
     */
    if( ( pszNum[ ulIdx ] == '0' ) && ( ( pszNum[ ulIdx + 1U ] == 'x' ) || ( pszNum[ ulIdx + 1U ] == 'X' ) ) )
    {
        ulIdx += 2U;

        if( ISDIGIT( pszNum[ ulIdx ] ) || ISHEXDIGIT( pszNum[ ulIdx ] ) )
        {
            pszReturn = RedHtoULL( &pszNum[ ulIdx ], pullNum );
        }
        else
        {
            pszReturn = NULL;
        }
    }
    else if( ISDIGIT( pszNum[ ulIdx ] ) )
    {
        uint64_t ullTemp = 0U;

        while( ISDIGIT( pszNum[ ulIdx ] ) )
        {
            ullTemp *= 10U;
            ullTemp += pszNum[ ulIdx ] - '0';
            ulIdx++;
        }

        if( fNegative )
        {
            /*  Fail if the number is out of range.
             */
            if( ullTemp > INT64_MAX )
            {
                pszReturn = NULL;
            }
            else
            {
                *pullNum = ( uint64_t ) ( -( ( int64_t ) ullTemp ) );
                pszReturn = &pszNum[ ulIdx ];
            }
        }
        else
        {
            *pullNum = ullTemp;
            pszReturn = &pszNum[ ulIdx ];
        }
    }
    else
    {
        /*  Return an error if there is not at least one hex or decimal digit.
         */
        pszReturn = NULL;
    }

    return pszReturn;
}


/** @brief Convert an ASCII hex or decimal number, which may may have a "B",
 *         "KB", or "MB" suffix (case insensitive), to a binary value.
 *
 *  Hex numbers must be prefixed with "0x".
 *
 *  @note If there is no postfix, KB is assumed!
 *
 *  May fail due to bad formatting or overflow.
 *
 *  @param pszNum       A pointer to the ASCII number to convert.
 *  @param pulResult    A pointer to a uint32_t in which to place the result.
 *
 *  @return A pointer to the byte following the string, or NULL to indicate an
 *          error.  In the event of an error, *pulResult will not be modified.
 */
const char * RedSizeToUL( const char * pszNum,
                          uint32_t * pulResult )
{
    uint32_t ulResult;
    const char * pszSuffix;
    const char * pszReturn;
    uint32_t ulIdx = 0U;

    REDASSERT( pszNum != NULL );
    REDASSERT( pulResult != NULL );

    /*  Do the basic hex/decimal conversion
     */
    pszSuffix = RedNtoUL( pszNum, &ulResult );

    if( pszSuffix != NULL )
    {
        if( ( pszSuffix[ ulIdx ] == 'B' ) || ( pszSuffix[ ulIdx ] == 'b' ) )
        {
            ulIdx++;
            pszReturn = &pszSuffix[ ulIdx ];
        }
        else if( ( ( pszSuffix[ ulIdx ] == 'M' ) || ( pszSuffix[ ulIdx ] == 'm' ) ) &&
                 ( ( pszSuffix[ ulIdx + 1U ] == 'B' ) || ( pszSuffix[ ulIdx + 1U ] == 'b' ) ) )
        {
            ulIdx += 2U;

            if( ulResult > ( UINT32_MAX / ( 1024U * 1024U ) ) )
            {
                pszReturn = NULL;
            }
            else
            {
                ulResult *= 1024U * 1024U;
                pszReturn = &pszSuffix[ ulIdx ];
            }
        }
        else
        {
            /*  The number is either postfixed with "KB" or something
             *  else (we don't care), but we must increment the pointer
             *  if it is something recognize.
             */
            if( ( ( pszSuffix[ ulIdx ] == 'K' ) || ( pszSuffix[ ulIdx ] == 'k' ) ) &&
                ( ( pszSuffix[ ulIdx + 1U ] == 'B' ) || ( pszSuffix[ ulIdx + 1U ] == 'b' ) ) )
            {
                ulIdx += 2U;
            }

            /*  "B" or "MB" were not specified, so it must be "KB"
             */
            if( ulResult > ( UINT32_MAX / 1024U ) )
            {
                pszReturn = NULL;
            }
            else
            {
                ulResult *= 1024UL;
                pszReturn = &pszSuffix[ ulIdx ];
            }
        }

        if( pszReturn != NULL )
        {
            *pulResult = ulResult;
        }
    }
    else
    {
        pszReturn = NULL;
    }

    return pszReturn;
}
