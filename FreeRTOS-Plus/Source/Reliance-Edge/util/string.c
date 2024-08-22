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
 *  @brief Default implementations of string manipulation functions.
 *
 *  These implementations are intended to be small and simple, and thus forego
 *  all optimizations.  If the C library is available, or if there are better
 *  third-party implementations available in the system, those can be used
 *  instead by defining the appropriate macros in redconf.h.
 *
 *  These functions are not intended to be completely 100% ANSI C compatible
 *  implementations, but rather are designed to meet the needs of Reliance Edge.
 *  The compatibility is close enough that ANSI C compatible implementations
 *  can be "dropped in" as replacements without difficulty.
 */
#include <redfs.h>


#ifndef RedStrLenUnchecked
    static uint32_t RedStrLenUnchecked( const char * pszStr );
#endif
#ifndef RedStrCmpUnchecked
    static int32_t RedStrCmpUnchecked( const char * pszStr1,
                                       const char * pszStr2 );
#endif
#ifndef RedStrNCmpUnchecked
    static int32_t RedStrNCmpUnchecked( const char * pszStr1,
                                        const char * pszStr2,
                                        uint32_t ulLen );
#endif
#ifndef RedStrNCpyUnchecked
    static void RedStrNCpyUnchecked( char * pszDst,
                                     const char * pszSrc,
                                     uint32_t ulLen );
#endif


/** @brief Determine the length (in bytes) of a null terminated string.
 *
 *  The length does not include the null terminator byte.
 *
 *  @param pszStr   The null terminated string whose length is to be determined.
 *
 *  @return The length of the @p pszStr string.
 */
uint32_t RedStrLen( const char * pszStr )
{
    uint32_t ulLen;

    if( pszStr == NULL )
    {
        REDERROR();
        ulLen = 0U;
    }
    else
    {
        /*  Cast the result to uint32_t, since RedStrLenUnchecked() might be
         *  strlen(), which returns size_t, which is possibly a 64-bit value.
         */
        ulLen = ( uint32_t ) RedStrLenUnchecked( pszStr );
    }

    return ulLen;
}


#ifndef RedStrLenUnchecked

/** @brief Determine the length (in bytes) of a null terminated string.
 *
 *  @param pszStr   The null terminated string whose length is to be determined.
 *
 *  @return The length of the @p pszStr string.
 */
    static uint32_t RedStrLenUnchecked( const char * pszStr )
    {
        uint32_t ulLen = 0U;

        while( pszStr[ ulLen ] != '\0' )
        {
            ulLen++;
        }

        return ulLen;
    }
#endif /* ifndef RedStrLenUnchecked */


/** @brief Compare two null terminated strings.
 *
 *  @param pszStr1  The first string to compare.
 *  @param pszStr2  The second string to compare.
 *
 *  @return Zero if the two strings are the same, otherwise nonzero.
 *
 *  @retval 0   @p pszStr1 and @p pszStr2 are the same.
 *  @retval 1   @p pszStr1 is greater than @p pszStr2, as determined by the
 *              values of the first differing bytes.
 *  @retval -1  @p pszStr2 is greater than @p pszStr1, as determined by the
 *              values of the first differing bytes.
 */
int32_t RedStrCmp( const char * pszStr1,
                   const char * pszStr2 )
{
    int32_t lResult;

    if( ( pszStr1 == NULL ) || ( pszStr2 == NULL ) )
    {
        REDERROR();
        lResult = 0;
    }
    else
    {
        lResult = RedStrCmpUnchecked( pszStr1, pszStr2 );
    }

    return lResult;
}


#ifndef RedStrCmpUnchecked

/** @brief Compare two null terminated strings.
 *
 *  @param pszStr1  The first string to compare.
 *  @param pszStr2  The second string to compare.
 *
 *  @return Zero if the two strings are the same, otherwise nonzero.
 */
    static int32_t RedStrCmpUnchecked( const char * pszStr1,
                                       const char * pszStr2 )
    {
        int32_t lResult;
        uint32_t ulIdx = 0U;

        while( ( pszStr1[ ulIdx ] == pszStr2[ ulIdx ] ) && ( pszStr1[ ulIdx ] != '\0' ) )
        {
            ulIdx++;
        }

        /*  "The sign of a non-zero return value is determined by the sign of the
         *  difference between the values of the first pair of bytes (both
         *  interpreted as type unsigned char) that differ in the strings being
         *  compared."  Use uint8_t instead of unsigned char to avoid MISRA C
         *  deviations.
         */
        if( ( uint8_t ) pszStr1[ ulIdx ] > ( uint8_t ) pszStr2[ ulIdx ] )
        {
            lResult = 1;
        }
        else if( ( uint8_t ) pszStr1[ ulIdx ] < ( uint8_t ) pszStr2[ ulIdx ] )
        {
            lResult = -1;
        }
        else
        {
            lResult = 0;
        }

        return lResult;
    }
#endif /* ifndef RedStrCmpUnchecked */


/** @brief Compare the first @p ulLen characters of two null terminated strings.
 *
 *  @param pszStr1  The first string to compare.
 *  @param pszStr2  The second string to compare.
 *  @param ulLen    The maximum length to compare.  The comparison stops when
 *                  either of the strings end or when @p ulLen bytes have been
 *                  compared.
 *
 *  @return Zero if the two strings are the same, otherwise nonzero.
 *
 *  @retval 0   @p pszStr1 and @p pszStr2 are the same.
 *  @retval 1   @p pszStr1 is greater than @p pszStr2, as determined by the
 *              values of the first differing bytes.
 *  @retval -1  @p pszStr2 is greater than @p pszStr1, as determined by the
 *              values of the first differing bytes.
 */
int32_t RedStrNCmp( const char * pszStr1,
                    const char * pszStr2,
                    uint32_t ulLen )
{
    int32_t lResult;

    if( ( pszStr1 == NULL ) || ( pszStr2 == NULL ) )
    {
        REDERROR();
        lResult = 0;
    }
    else
    {
        lResult = RedStrNCmpUnchecked( pszStr1, pszStr2, ulLen );
    }

    return lResult;
}


#ifndef RedStrNCmpUnchecked

/** @brief Compare the first @p ulLen characters of two null terminated strings.
 *
 *  @param pszStr1  The first string to compare.
 *  @param pszStr2  The second string to compare.
 *  @param ulLen    The maximum length to compare.  The comparison stops when
 *                  either of the strings end or when @p ulLen bytes have been
 *                  compared.
 *
 *  @return Zero if the two strings are the same, otherwise nonzero.
 */
    static int32_t RedStrNCmpUnchecked( const char * pszStr1,
                                        const char * pszStr2,
                                        uint32_t ulLen )
    {
        int32_t lResult = 0;
        uint32_t ulIdx;

        for( ulIdx = 0U; ulIdx < ulLen; ulIdx++ )
        {
            if( pszStr1[ ulIdx ] != pszStr2[ ulIdx ] )
            {
                /*  "The sign of a non-zero return value is determined by the sign
                 *  of the difference between the values of the first pair of bytes
                 *  (both interpreted as type unsigned char) that differ in the
                 *  strings being compared."  Use uint8_t instead of unsigned char
                 *  to avoid MISRA C deviations.
                 */
                if( ( uint8_t ) pszStr1[ ulIdx ] > ( uint8_t ) pszStr2[ ulIdx ] )
                {
                    lResult = 1;
                }
                else
                {
                    lResult = -1;
                }
            }

            if( ( lResult != 0 ) || ( pszStr1[ ulIdx ] == '\0' ) )
            {
                break;
            }
        }

        return lResult;
    }
#endif /* ifndef RedStrNCmpUnchecked */


/** @brief Copy a string.
 *
 *  Copy up to @p ulLen bytes of a null-terminated string (@p pszSrc) to a
 *  destination buffer (@p pszDst).  The result will not be null-terminated if
 *  @p pszSrc is longer than @p ulLen - 1 bytes.
 *
 *  If @p pszSrc is shorter than @p ulLen - 1 bytes, the remainder of @p pszDst
 *  will be filled with null bytes.
 *
 *  @param pszDst   The destination buffer, which is at least @p ulLen bytes
 *                  in size.
 *  @param pszSrc   The null-terminated string to copy.
 *  @param ulLen    The maximum number of characters to copy.
 */
void RedStrNCpy( char * pszDst,
                 const char * pszSrc,
                 uint32_t ulLen )
{
    if( ( pszDst == NULL ) || ( pszSrc == NULL ) )
    {
        REDERROR();
    }
    else
    {
        RedStrNCpyUnchecked( pszDst, pszSrc, ulLen );
    }
}


#ifndef RedStrNCpyUnchecked

/** @brief Copy a string.
 *
 *  @param pszDst   The destination buffer, which is at least @p ulLen bytes
 *                  in size.
 *  @param pszSrc   The null-terminated string to copy.
 *  @param ulLen    The maximum number of characters to copy.
 */
    static void RedStrNCpyUnchecked( char * pszDst,
                                     const char * pszSrc,
                                     uint32_t ulLen )
    {
        uint32_t ulIdx = 0U;

        while( ( ulIdx < ulLen ) && ( pszSrc[ ulIdx ] != '\0' ) )
        {
            pszDst[ ulIdx ] = pszSrc[ ulIdx ];
            ulIdx++;
        }

        while( ulIdx < ulLen )
        {
            pszDst[ ulIdx ] = '\0';
            ulIdx++;
        }
    }
#endif /* ifndef RedStrNCpyUnchecked */
