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
 *  @brief Implements functions for printing.
 *
 *  These functions are intended to be used in portable test code, which cannot
 *  assume the standard I/O functions will be available.  Similar to their ANSI
 *  C counterparts, these functions allow formatting text strings and (if the
 *  configuration allows it) outputing formatted text.  The latter ability
 *  relies on the RedOsOutputString() OS service function.
 *
 *  Do *not* use these functions in code which can safely assume the standard
 *  I/O functions are available (e.g., in host tools code).
 *
 *  Do *not* use these functions from within the file system driver.  These
 *  functions use variable arguments and thus are not MISRA-C:2012 compliant.
 */
#include <redfs.h>
#include <redtestutils.h>
#include <limits.h>
#include <stdarg.h>


/** @brief Maximum number of bytes of output supported by RedPrintf().
 *
 *  Typically only Datalight code uses these functions, and that could should be
 *  written to respect this limit, so it should not normally be necessary to
 *  adjust this value.
 */
#define OUTPUT_BUFFER_SIZE    256U


typedef enum
{
    PRFMT_UNKNOWN = 0,
    PRFMT_CHAR,
    PRFMT_ANSISTRING,
    PRFMT_SIGNED8BIT,
    PRFMT_UNSIGNED8BIT,
    PRFMT_SIGNED16BIT,
    PRFMT_UNSIGNED16BIT,
    PRFMT_SIGNED32BIT,
    PRFMT_UNSIGNED32BIT,
    PRFMT_SIGNED64BIT,
    PRFMT_UNSIGNED64BIT,
    PRFMT_HEX8BIT,
    PRFMT_HEX16BIT,
    PRFMT_HEX32BIT,
    PRFMT_HEX64BIT,
    PRFMT_POINTER,
    PRFMT_DOUBLEPERCENT
} PRINTTYPE;

typedef struct
{
    PRINTTYPE type;          /* The PRFMT_* type found */
    uint32_t ulSpecifierIdx; /* Returns a pointer to the % sign */
    uint32_t ulFillLen;
    char cFillChar;
    bool fLeftJustified;
    bool fHasIllegalType; /* TRUE if an illegal sequence was skipped over */
    bool fHasVarWidth;
} PRINTFORMAT;


/*  Our output handlers are written for standard fixed width data types.  Map
 *  the standard ANSI C data types onto our handlers.  Currently this code has
 *  the following requirements:
 *
 *  1) shorts must be either 16 or 32 bits
 *  2) ints must be either 16 or 32 bits
 *  3) longs must be between 32 or 64 bits
 *  4) long longs must be 64 bits
 */
#if ( USHRT_MAX == 0xFFFFU )
    #define MAPSHORT        PRFMT_SIGNED16BIT
    #define MAPUSHORT       PRFMT_UNSIGNED16BIT
    #define MAPHEXUSHORT    PRFMT_HEX16BIT
#elif ( USHRT_MAX == 0xFFFFFFFFU )
    #define MAPSHORT        PRFMT_SIGNED32BIT
    #define MAPUSHORT       PRFMT_UNSIGNED32BIT
    #define MAPHEXUSHORT    PRFMT_HEX32BIT
#else
    #error "The 'short' data type does not have a 16 or 32-bit width"
#endif

#if ( UINT_MAX == 0xFFFFU )
    #define MAPINT        PRFMT_SIGNED16BIT
    #define MAPUINT       PRFMT_UNSIGNED16BIT
    #define MAPHEXUINT    PRFMT_HEX16BIT
#elif ( UINT_MAX == 0xFFFFFFFFU )
    #define MAPINT        PRFMT_SIGNED32BIT
    #define MAPUINT       PRFMT_UNSIGNED32BIT
    #define MAPHEXUINT    PRFMT_HEX32BIT
#else
    #error "The 'int' data type does not have a 16 or 32-bit width"
#endif

#if ( ULONG_MAX == 0xFFFFFFFFU )
    #define MAPLONG        PRFMT_SIGNED32BIT
    #define MAPULONG       PRFMT_UNSIGNED32BIT
    #define MAPHEXULONG    PRFMT_HEX32BIT
#elif ( ULONG_MAX <= UINT64_SUFFIX( 0xFFFFFFFFFFFFFFFF ) )

/*  We've run into unusual environments where "longs" are 40-bits wide.
 *  In this event, map them to 64-bit types so no data is lost.
 */
    #define MAPLONG        PRFMT_SIGNED64BIT
    #define MAPULONG       PRFMT_UNSIGNED64BIT
    #define MAPHEXULONG    PRFMT_HEX64BIT
#else
    #error "The 'long' data type is not between 32 and 64 bits wide"
#endif /* if ( ULONG_MAX == 0xFFFFFFFFU ) */

#if defined( ULLONG_MAX ) && ( ULLONG_MAX != UINT64_SUFFIX( 0xFFFFFFFFFFFFFFFF ) )
    #error "The 'long long' data type is not 64 bits wide"
#else
    #define MAPLONGLONG        PRFMT_SIGNED64BIT
    #define MAPULONGLONG       PRFMT_UNSIGNED64BIT
    #define MAPHEXULONGLONG    PRFMT_HEX64BIT
#endif


static uint32_t ProcessFormatSegment( char * pcBuffer,
                                      uint32_t ulBufferLen,
                                      const char * pszFormat,
                                      PRINTFORMAT * pFormat,
                                      uint32_t * pulSpecifierLen );
static uint32_t ParseFormatSpecifier( char const * pszFormat,
                                      PRINTFORMAT * pFormatType );
static PRINTTYPE ParseFormatType( const char * pszFormat,
                                  uint32_t * pulTypeLen );
static uint32_t LtoA( char * pcBuffer,
                      uint32_t ulBufferLen,
                      int32_t lNum,
                      uint32_t ulFillLen,
                      char cFill );
static uint32_t LLtoA( char * pcBuffer,
                       uint32_t ulBufferLen,
                       int64_t llNum,
                       uint32_t ulFillLen,
                       char cFill );
static uint32_t ULtoA( char * pcBuffer,
                       uint32_t ulBufferLen,
                       uint32_t ulNum,
                       bool fHex,
                       uint32_t ulFillLen,
                       char cFill );
static uint32_t ULLtoA( char * pcBuffer,
                        uint32_t ulBufferLen,
                        uint64_t ullNum,
                        bool fHex,
                        uint32_t ulFillLen,
                        char cFill );
static uint32_t FinishToA( const char * pcDigits,
                           uint32_t ulDigits,
                           char * pcOutBuffer,
                           uint32_t ulBufferLen,
                           uint32_t ulFillLen,
                           char cFill );


/*  Digits for the *LtoA() routines.
 */
static const char gacDigits[] = "0123456789ABCDEF";


#if REDCONF_OUTPUT == 1

/** @brief Print formatted data with a variable length argument list.
 *
 *  This function provides a subset of the ANSI C printf() functionality with
 *  several extensions to support fixed size data types.
 *
 *  See RedVSNPrintf() for the list of supported types.
 *
 *  @param pszFormat    A pointer to the null-terminated format string.
 *  @param ...          The variable length argument list.
 */
    void RedPrintf( const char * pszFormat,
                    ... )
    {
        va_list arglist;

        va_start( arglist, pszFormat );

        RedVPrintf( pszFormat, arglist );

        va_end( arglist );
    }


/** @brief Print formatted data using a pointer to a variable length argument
 *         list.
 *
 *  This function provides a subset of the ANSI C vprintf() functionality.
 *
 *  See RedVSNPrintf() for the list of supported types.
 *
 *  This function accommodates a maximum output length of #OUTPUT_BUFFER_SIZE.
 *  If this function must truncate the output, and the original string was
 *  \n terminated, the truncated output will be \n terminated as well.
 *
 *  @param pszFormat    A pointer to the null-terminated format string.
 *  @param arglist      The variable length argument list.
 */
    void RedVPrintf( const char * pszFormat,
                     va_list arglist )
    {
        char achBuffer[ OUTPUT_BUFFER_SIZE ];

        if( RedVSNPrintf( achBuffer, sizeof( achBuffer ), pszFormat, arglist ) == -1 )
        {
            /*  Ensure the buffer is null terminated.
             */
            achBuffer[ sizeof( achBuffer ) - 1U ] = '\0';

            /*  If the original string was \n terminated and the new one is not, due to
             *  truncation, stuff a \n into the new one.
             */
            if( pszFormat[ RedStrLen( pszFormat ) - 1U ] == '\n' )
            {
                achBuffer[ sizeof( achBuffer ) - 2U ] = '\n';
            }
        }

        RedOsOutputString( achBuffer );
    }
#endif /* #if REDCONF_OUTPUT == 1 */


/** @brief Format arguments into a string using a subset of the ANSI C
 *         vsprintf() functionality.
 *
 *  This function is modeled after the Microsoft _snprint() extension to the
 *  ANSI C sprintf() function, and allows a buffer length to be specified so
 *  that overflow is avoided.
 *
 *  See RedVSNPrintf() for the list of supported types.
 *
 *  @param pcBuffer     A pointer to the output buffer
 *  @param ulBufferLen  The output buffer length
 *  @param pszFormat    A pointer to the null terminated format string
 *  @param ...          Variable argument list
 *
 *  @return The length output, or -1 if the buffer filled up.  If -1 is
 *          returned, the output buffer may not be null-terminated.
 */
int32_t RedSNPrintf( char * pcBuffer,
                     uint32_t ulBufferLen,
                     const char * pszFormat,
                     ... )
{
    int32_t iLen;
    va_list arglist;

    va_start( arglist, pszFormat );

    iLen = RedVSNPrintf( pcBuffer, ulBufferLen, pszFormat, arglist );

    va_end( arglist );

    return iLen;
}


/** @brief Format arguments into a string using a subset of the ANSI C
 *         vsprintf() functionality.
 *
 *  This function is modeled after the Microsoft _vsnprint() extension to the
 *  ANSI C vsprintf() function, and requires a buffer length to be specified so
 *  that overflow is avoided.
 *
 *  The following ANSI C standard formatting codes are supported:
 *
 | Code | Meaning                            |
 | ---- | ---------------------------------- |
 | %c   | Format a character                 |
 | %s   | Format a null-terminated C string  |
 | %hd  | Format a signed short              |
 | %hu  | Format an unsigned short           |
 | %d   | Format a signed integer            |
 | %u   | Format an unsigned integer         |
 | %ld  | Format a signed long               |
 | %lu  | Format an unsigned long            |
 | %lld | Format a signed long long          |
 | %llu | Format an unsigned long long       |
 | %hx  | Format a short in hex              |
 | %x   | Format an integer in hex           |
 | %lx  | Format a long in hex               |
 | %llx | Format a long long in hex          |
 | %p   | Format a pointer (hex value)       |
 |
 |  @note All formatting codes are case-sensitive.
 |
 |  Fill characters and field widths are supported per the ANSI standard, as is
 |  left justification with the '-' character.
 |
 |  The only supported fill characters are '0', ' ', and '_'.
 |
 |  '*' is supported to specify variable length field widths.
 |
 |  Hexidecimal numbers are always displayed in upper case.  Formatting codes
 |  which specifically request upper case (e.g., "%lX") are not supported.
 |
 |  Unsupported behaviors:
 |    - Precision is not supported.
 |    - Floating point is not supported.
 |
 |  Errata:
 |  - There is a subtle difference in the return value for this function versus
 |    the Microsoft implementation.  In the Microsoft version, if the buffer
 |    exactly fills up, but there is no room for a null-terminator, the return
 |    value will be the length of the buffer.  In this code, -1 will be returned
 |    when this happens.
 |  - When using left justified strings, the only supported fill character is a
 |    space, regardless of what may be specified.  It is not clear if this is
 |    ANSI standard or just the way the Microsoft function works, but we emulate
 |    the Microsoft behavior.
 |
 |  @param pcBuffer     A pointer to the output buffer.
 |  @param ulBufferLen  The output buffer length.
 |  @param pszFormat    A pointer to the null terminated ANSI format string.
 |  @param arglist      Variable argument list.
 |
 |  @return  The length output, or -1 if the buffer filled up.  If -1 is
 |           returned, the output buffer may not be null-terminated.
 */
int32_t RedVSNPrintf( char * pcBuffer,
                      uint32_t ulBufferLen,
                      const char * pszFormat,
                      va_list arglist )
{
    uint32_t ulBufIdx = 0U;
    uint32_t ulFmtIdx = 0U;
    int32_t iLen;

    while( ( pszFormat[ ulFmtIdx ] != '\0' ) && ( ulBufIdx < ulBufferLen ) )
    {
        PRINTFORMAT fmt;
        uint32_t ulSpecifierLen;
        uint32_t ulWidth;

        /*  Process the next segment of the format string, outputting
         *  any non-format specifiers, as output buffer space allows,
         *  and return information about the next format specifier.
         */
        ulWidth = ProcessFormatSegment( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, &pszFormat[ ulFmtIdx ], &fmt, &ulSpecifierLen );

        if( ulWidth )
        {
            REDASSERT( ulWidth <= ( ulBufferLen - ulBufIdx ) );

            ulBufIdx += ulWidth;
        }

        /*  If no specifier was found, or if the output buffer is
         *  full, we're done -- get out.
         */
        if( ( ulSpecifierLen == 0U ) || ( ulBufIdx == ulBufferLen ) )
        {
            break;
        }

        /*  Otherwise, the math should add up for these things...
         */
        REDASSERT( &pszFormat[ fmt.ulSpecifierIdx ] == &pszFormat[ ulWidth ] );

        /*  Point past the specifier, to the next piece of the format string.
         */
        ulFmtIdx = ulFmtIdx + fmt.ulSpecifierIdx + ulSpecifierLen;

        if( fmt.fHasVarWidth )
        {
            int iFillLen = va_arg( arglist, int );

            if( iFillLen >= 0 )
            {
                fmt.ulFillLen = ( uint32_t ) iFillLen;
            }
            else
            {
                /*  Bogus fill length.  Ignore.
                 */
                fmt.ulFillLen = 0U;
            }
        }

        switch( fmt.type )
        {
            case PRFMT_DOUBLEPERCENT:

                /*  Nothing to do.  A single percent has already been output,
                 *  and we just finished skipping past the second percent.
                 */
                break;

            /*----------------->  Small int handling  <------------------
             *
             *  Values smaller than "int" will be promoted to "int" by
             *  the compiler, so we must retrieve them using "int" when
             *  calling va_arg().  Once we've done that, we immediately
             *  put the value into the desired data type.
             *---------------------------------------------------------*/

            case PRFMT_CHAR:
                pcBuffer[ ulBufIdx ] = ( char ) va_arg( arglist, int );
                ulBufIdx++;
                break;

            case PRFMT_SIGNED8BIT:
               {
                   int8_t num = ( int8_t ) va_arg( arglist, int );

                   ulBufIdx += LtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, num, fmt.ulFillLen, fmt.cFillChar );
                   break;
               }

            case PRFMT_UNSIGNED8BIT:
               {
                   uint8_t bNum = ( uint8_t ) va_arg( arglist, unsigned );

                   ulBufIdx += ULtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, bNum, false, fmt.ulFillLen, fmt.cFillChar );
                   break;
               }

            case PRFMT_HEX8BIT:
               {
                   uint8_t bNum = ( uint8_t ) va_arg( arglist, unsigned );

                   ulBufIdx += ULtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, bNum, true, fmt.ulFillLen, fmt.cFillChar );
                   break;
               }

            case PRFMT_SIGNED16BIT:
               {
                   int16_t num = ( int16_t ) va_arg( arglist, int );

                   ulBufIdx += LtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, num, fmt.ulFillLen, fmt.cFillChar );
                   break;
               }

            case PRFMT_UNSIGNED16BIT:
               {
                   uint16_t uNum = ( uint16_t ) va_arg( arglist, unsigned );

                   ulBufIdx += ULtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, uNum, false, fmt.ulFillLen, fmt.cFillChar );
                   break;
               }

            case PRFMT_HEX16BIT:
               {
                   uint16_t uNum = ( uint16_t ) va_arg( arglist, unsigned );

                   ulBufIdx += ULtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, uNum, true, fmt.ulFillLen, fmt.cFillChar );
                   break;
               }

            case PRFMT_SIGNED32BIT:
               {
                   int32_t lNum = va_arg( arglist, int32_t );

                   ulBufIdx += LtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, lNum, fmt.ulFillLen, fmt.cFillChar );
                   break;
               }

            case PRFMT_UNSIGNED32BIT:
               {
                   uint32_t ulNum = va_arg( arglist, uint32_t );

                   ulBufIdx += ULtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, ulNum, false, fmt.ulFillLen, fmt.cFillChar );
                   break;
               }

            case PRFMT_HEX32BIT:
               {
                   uint32_t ulNum = va_arg( arglist, uint32_t );

                   ulBufIdx += ULtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, ulNum, true, fmt.ulFillLen, fmt.cFillChar );
                   break;
               }

            case PRFMT_SIGNED64BIT:
               {
                   int64_t llNum = va_arg( arglist, int64_t );

                   ulBufIdx += LLtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, llNum, fmt.ulFillLen, fmt.cFillChar );
                   break;
               }

            case PRFMT_UNSIGNED64BIT:
               {
                   uint64_t ullNum = va_arg( arglist, uint64_t );

                   ulBufIdx += ULLtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, ullNum, false, fmt.ulFillLen, fmt.cFillChar );
                   break;
               }

            case PRFMT_HEX64BIT:
               {
                   uint64_t ullNum = va_arg( arglist, uint64_t );

                   ulBufIdx += ULLtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, ullNum, true, fmt.ulFillLen, fmt.cFillChar );
                   break;
               }

            case PRFMT_POINTER:
               {
                   const void * ptr = va_arg( arglist, const void * );

                   /*  Assert our assumption.
                    */
                   REDASSERT( sizeof( void * ) <= 8U );

                   /*  Format as either a 64-bit or a 32-bit value.
                    */
                   if( sizeof( void * ) > 4U )
                   {
                       /*  Attempt to quiet warnings.
                        */
                       uintptr_t ptrval = ( uintptr_t ) ptr;
                       uint64_t ullPtrVal = ( uint64_t ) ptrval;

                       ulBufIdx += ULLtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, ullPtrVal, true, fmt.ulFillLen, fmt.cFillChar );
                   }
                   else
                   {
                       /*  Attempt to quiet warnings.
                        */
                       uintptr_t ptrval = ( uintptr_t ) ptr;
                       uint32_t ulPtrVal = ( uint32_t ) ptrval;

                       ulBufIdx += ULtoA( &pcBuffer[ ulBufIdx ], ulBufferLen - ulBufIdx, ulPtrVal, true, fmt.ulFillLen, fmt.cFillChar );
                   }

                   break;
               }

            case PRFMT_ANSISTRING:
               {
                   const char * pszArg = va_arg( arglist, const char * );
                   uint32_t ulArgIdx = 0U;

                   if( pszArg == NULL )
                   {
                       pszArg = "null";
                   }

                   if( fmt.ulFillLen > 0U )
                   {
                       if( !fmt.fLeftJustified )
                       {
                           uint32_t ulLen = RedStrLen( pszArg );

                           /*  So long as we are not left justifying, fill as many
                            *  characters as is necessary to make the string right
                            *  justified.
                            */
                           while( ( ( ulBufferLen - ulBufIdx ) > 0U ) && ( fmt.ulFillLen > ulLen ) )
                           {
                               pcBuffer[ ulBufIdx ] = fmt.cFillChar;
                               ulBufIdx++;
                               fmt.ulFillLen--;
                           }
                       }

                       /*  Move as many characters as we have space for into the
                        *  output buffer.
                        */
                       while( ( ( ulBufferLen - ulBufIdx ) > 0U ) && ( pszArg[ ulArgIdx ] != '\0' ) )
                       {
                           pcBuffer[ ulBufIdx ] = pszArg[ ulArgIdx ];
                           ulBufIdx++;
                           ulArgIdx++;

                           if( fmt.ulFillLen > 0U )
                           {
                               fmt.ulFillLen--;
                           }
                       }

                       /*  If there is any space left to fill, do it (the string
                        *  must have been left justified).
                        */
                       while( ( ( ulBufferLen - ulBufIdx ) > 0U ) && ( fmt.ulFillLen > 0U ) )
                       {
                           /*  This is NOT a typo -- when using left justified
                            *  strings, spaces are the only allowed fill character.
                            *  See the errata.
                            */
                           pcBuffer[ ulBufIdx ] = ' ';
                           ulBufIdx++;
                           fmt.ulFillLen--;
                       }
                   }
                   else
                   {
                       /*  No fill characters, just move up to as many
                        *  characters as we have space for in the output
                        *  buffer.
                        */
                       while( ( ( ulBufferLen - ulBufIdx ) > 0U ) && ( pszArg[ ulArgIdx ] != '\0' ) )
                       {
                           pcBuffer[ ulBufIdx ] = pszArg[ ulArgIdx ];
                           ulBufIdx++;
                           ulArgIdx++;
                       }
                   }

                   break;
               }

            default:
                REDERROR();
                break;
        }
    }

    /*  If there is space, tack on a null and return the output length
     *  processed, not including the null.
     */
    if( ulBufIdx < ulBufferLen )
    {
        pcBuffer[ ulBufIdx ] = '\0';
        iLen = ( int32_t ) ulBufIdx;
    }
    else
    {
        /*  Not enough space, just return -1, with no null termination
         */
        iLen = -1;
    }

    return iLen;
}


/** @brief  Process the next segment of the format string, outputting any
 *          non-format specifiers, as output buffer space allows, and return
 *          information about the next format specifier.
 *
 *  @note   If the returned value is the same as the supplied @p ulBufferLen,
 *          the output buffer will not be null-terminated.  In all other cases,
 *          the result will be null-terminated.  The returned length will never
 *          include the null in the count.
 *
 *  @param pcBuffer         The output buffer.
 *  @param ulBufferLen      The output buffer length.
 *  @param pszFormat        The format string to process.
 *  @param pFormat          The PRINTFORMAT structure to fill.
 *  @param pulSpecifierLen  Returns the length of any format specifier string,
 *                          or zero if no specifier was found.
 *
 *  @return The count of characters from pszFormatt which were processed and
 *          copied to pcBuffer.
 *      - If zero is returned and *pulSpecifierLen is non-zero, then
 *        a format specifier string was found at the start of pszFmt.
 *      - If non-zero is returned and *pulSpecifierLen is zero, then
 *        no format specifier string was found, and the entire pszFmt
 *        string was copied to pBuffer (or as much as will fit).
 */
static uint32_t ProcessFormatSegment( char * pcBuffer,
                                      uint32_t ulBufferLen,
                                      const char * pszFormat,
                                      PRINTFORMAT * pFormat,
                                      uint32_t * pulSpecifierLen )
{
    uint32_t ulWidth = 0U;

    /*  Find the next format specifier string, and information about it.
     */
    *pulSpecifierLen = ParseFormatSpecifier( pszFormat, pFormat );

    if( *pulSpecifierLen == 0U )
    {
        /*  If no specifier was found at all, then simply output the full length
         *  of the string, or as much as will fit.
         */
        ulWidth = REDMIN( ulBufferLen, RedStrLen( pszFormat ) );

        RedMemCpy( pcBuffer, pszFormat, ulWidth );
    }
    else
    {
        /*  If we encountered a double percent, skip past one of them so it is
         *  copied into the output buffer.
         */
        if( pFormat->type == PRFMT_DOUBLEPERCENT )
        {
            pFormat->ulSpecifierIdx++;

            /*  A double percent specifier always has a length of two.  Since
             *  we're processing one of those percent signs, reduce the length
             *  to one.  Assert it so.
             */
            REDASSERT( *pulSpecifierLen == 2U );

            ( *pulSpecifierLen )--;
        }

        /*  So long as the specifier is not the very first thing in the format
         *  string...
         */
        if( pFormat->ulSpecifierIdx != 0U )
        {
            /*  A specifier was found, but there is other data preceding it.
             *  Copy as much as allowed to the output buffer.
             */
            ulWidth = REDMIN( ulBufferLen, pFormat->ulSpecifierIdx );

            RedMemCpy( pcBuffer, pszFormat, ulWidth );
        }
    }

    /*  If there is room in the output buffer, null-terminate whatever is there.
     *  But note that the returned length never includes the null.
     */
    if( ulWidth < ulBufferLen )
    {
        pcBuffer[ ulWidth ] = 0U;
    }

    return ulWidth;
}


/** @brief Parse the specified format string for a valid RedVSNPrintf() format
 *         sequence, and return information about it.
 *
 *  @param pszFormat    The format string to process.
 *  @param pFormatType  The PRINTFORMAT structure to fill.  The data is only
 *                      valid if a non-zero length is returned.
 *
 *  @return The length of the full format specifier string, starting at
 *          pFormat->ulSpecifierIdx.  Returns zero if a valid specifier was
 *          not found.
 */
static uint32_t ParseFormatSpecifier( char const * pszFormat,
                                      PRINTFORMAT * pFormatType )
{
    bool fContainsIllegalSequence = false;
    uint32_t ulLen = 0U;
    uint32_t ulIdx = 0U;

    while( pszFormat[ ulIdx ] != '\0' )
    {
        uint32_t ulTypeLen;

        /*  general output
         */
        if( pszFormat[ ulIdx ] != '%' )
        {
            ulIdx++;
        }
        else
        {
            RedMemSet( pFormatType, 0U, sizeof( *pFormatType ) );

            /*  Record the location of the start of the format sequence
             */
            pFormatType->ulSpecifierIdx = ulIdx;
            ulIdx++;

            if( pszFormat[ ulIdx ] == '-' )
            {
                pFormatType->fLeftJustified = true;
                ulIdx++;
            }

            if( ( pszFormat[ ulIdx ] == '0' ) || ( pszFormat[ ulIdx ] == '_' ) )
            {
                pFormatType->cFillChar = pszFormat[ ulIdx ];
                ulIdx++;
            }
            else
            {
                pFormatType->cFillChar = ' ';
            }

            if( pszFormat[ ulIdx ] == '*' )
            {
                pFormatType->fHasVarWidth = true;
                ulIdx++;
            }
            else if( ISDIGIT( pszFormat[ ulIdx ] ) )
            {
                pFormatType->ulFillLen = ( uint32_t ) RedAtoI( &pszFormat[ ulIdx ] );

                while( ISDIGIT( pszFormat[ ulIdx ] ) )
                {
                    ulIdx++;
                }
            }
            else
            {
                /*  No fill length.
                 */
            }

            pFormatType->type = ParseFormatType( &pszFormat[ ulIdx ], &ulTypeLen );

            if( pFormatType->type != PRFMT_UNKNOWN )
            {
                /*  Even though we are returning successfully, keep track of
                 *  whether an illegal sequence was encountered and skipped.
                 */
                pFormatType->fHasIllegalType = fContainsIllegalSequence;

                ulLen = ( ulIdx - pFormatType->ulSpecifierIdx ) + ulTypeLen;
                break;
            }

            /*  In the case of an unrecognized type string, simply ignore
             *  it entirely.  Reset the pointer to the position following
             *  the percent sign, so it is not found again.
             */
            fContainsIllegalSequence = false;
            ulIdx = pFormatType->ulSpecifierIdx + 1U;
        }
    }

    return ulLen;
}


/** @brief Parse a RedPrintf() format type string to determine the proper data
 *         type.
 *
 *  @param pszFormat    The format string to process.  This must be a pointer to
 *                      the character following any width or justification
 *                      characters.
 *  @param pulTypeLen   The location in which to store the type length.  The
 *                      value will be 0 if PRFMT_UNKNOWN is returned.
 *
 *  @return Rhe PRFMT_* type value, or PRFMT_UNKNOWN if the type is not
 *          recognized.
 */
static PRINTTYPE ParseFormatType( const char * pszFormat,
                                  uint32_t * pulTypeLen )
{
    PRINTTYPE fmtType = PRFMT_UNKNOWN;
    uint32_t ulIdx = 0U;

    switch( pszFormat[ ulIdx ] )
    {
        case '%':
            fmtType = PRFMT_DOUBLEPERCENT;
            break;

        case 'c':
            fmtType = PRFMT_CHAR;
            break;

        case 's':
            fmtType = PRFMT_ANSISTRING;
            break;

        case 'p':
            fmtType = PRFMT_POINTER;
            break;

        case 'd':
            fmtType = MAPINT;
            break;

        case 'u':
            fmtType = MAPUINT;
            break;

        case 'x':
            fmtType = MAPHEXUINT;
            break;

        case 'h':
            ulIdx++;

            switch( pszFormat[ ulIdx ] )
            {
                case 'd':
                    fmtType = MAPSHORT;
                    break;

                case 'u':
                    fmtType = MAPUSHORT;
                    break;

                case 'x':
                    fmtType = MAPHEXUSHORT;
                    break;

                default:
                    break;
            }

            break;

        case 'l':
            ulIdx++;

            switch( pszFormat[ ulIdx ] )
            {
                case 'd':
                    fmtType = MAPLONG;
                    break;

                case 'u':
                    fmtType = MAPULONG;
                    break;

                case 'x':
                    fmtType = MAPHEXULONG;
                    break;

                case 'l':
                    ulIdx++;

                    switch( pszFormat[ ulIdx ] )
                    {
                        case 'd':
                            fmtType = MAPLONGLONG;
                            break;

                        case 'u':
                            fmtType = MAPULONGLONG;
                            break;

                        case 'x':
                        case 'X':
                            fmtType = MAPHEXULONGLONG;
                            break;

                        default:
                            break;
                    }

                    break;

                default:
                    break;
            }

            break;

        default:
            break;
    }

    if( fmtType != PRFMT_UNKNOWN )
    {
        *pulTypeLen = ulIdx + 1U;
    }
    else
    {
        *pulTypeLen = 0U;
    }

    return fmtType;
}


/** @brief Format a signed 32-bit integer as a base 10 ASCII string.
 *
 *  @note   If the output buffer length is exhausted, the result will *not* be
 *          null-terminated.
 *
 *  @note   If the @p ulFillLen value is greater than or equal to the buffer
 *          length, the result will not be null-terminated, even if the
 *          formatted portion of the data is shorter than the buffer length.
 *
 *  @param pcBuffer     The output buffer
 *  @param ulBufferLen  A pointer to the output buffer length
 *  @param lNum         The 32-bit signed number to convert
 *  @param ulFillLen    The fill length, if any
 *  @param cFill        The fill character to use
 *
 *  @return The length of the string.
 */
static uint32_t LtoA( char * pcBuffer,
                      uint32_t ulBufferLen,
                      int32_t lNum,
                      uint32_t ulFillLen,
                      char cFill )
{
    uint32_t ulLen;

    if( pcBuffer == NULL )
    {
        REDERROR();
        ulLen = 0U;
    }
    else
    {
        char ach[ 12U ]; /* big enough for a int32_t in base 10 */
        uint32_t ulDigits = 0U;
        uint32_t ulNum;
        bool fSign;

        if( lNum < 0 )
        {
            fSign = true;
            ulNum = ( uint32_t ) -lNum;
        }
        else
        {
            fSign = false;
            ulNum = ( uint32_t ) lNum;
        }

        do
        {
            ach[ ulDigits ] = gacDigits[ ulNum % 10U ];
            ulNum = ulNum / 10U;
            ulDigits++;
        }
        while( ulNum );

        if( fSign )
        {
            ach[ ulDigits ] = '-';
            ulDigits++;
        }

        ulLen = FinishToA( ach, ulDigits, pcBuffer, ulBufferLen, ulFillLen, cFill );
    }

    return ulLen;
}


/** @brief Format a signed 64-bit integer as a base 10 ASCII string.
 *
 *  @note   If the output buffer length is exhausted, the result will *not* be
 *          null-terminated.
 *
 *  @note   If the @p ulFillLen value is greater than or equal to the buffer
 *          length, the result will not be null-terminated, even if the
 *          formatted portion of the data is shorter than the buffer length.
 *
 *  @param pcBuffer     The output buffer
 *  @param ulBufferLen  A pointer to the output buffer length
 *  @param llNum        The 64-bit signed number to convert
 *  @param ulFillLen    The fill length, if any
 *  @param cFill        The fill character to use
 *
 *  @return The length of the string.
 */
static uint32_t LLtoA( char * pcBuffer,
                       uint32_t ulBufferLen,
                       int64_t llNum,
                       uint32_t ulFillLen,
                       char cFill )
{
    uint32_t ulLen;

    if( pcBuffer == NULL )
    {
        REDERROR();
        ulLen = 0U;
    }
    else
    {
        char ach[ 12U ]; /* big enough for a int32_t in base 10 */
        uint32_t ulDigits = 0U;
        uint64_t ullNum;
        bool fSign;

        if( llNum < 0 )
        {
            fSign = true;
            ullNum = ( uint64_t ) -llNum;
        }
        else
        {
            fSign = false;
            ullNum = ( uint64_t ) llNum;
        }

        /*  Not allowed to assume that 64-bit division is OK, so use a
         *  software division routine.
         */
        do
        {
            uint64_t ullQuotient;
            uint32_t ulRemainder;

            /*  Note: RedUint64DivMod32() is smart enough to use normal division
             *  once ullNumericVal <= UINT32_MAX.
             */
            ullQuotient = RedUint64DivMod32( ullNum, 10U, &ulRemainder );

            ach[ ulDigits ] = gacDigits[ ulRemainder ];
            ullNum = ullQuotient;
            ulDigits++;
        }
        while( ullNum > 0U );

        if( fSign )
        {
            ach[ ulDigits ] = '-';
            ulDigits++;
        }

        ulLen = FinishToA( ach, ulDigits, pcBuffer, ulBufferLen, ulFillLen, cFill );
    }

    return ulLen;
}


/** @brief Format an unsigned 32-bit integer as an ASCII string as decimal or
 *         hex.
 *
 *  @note If the output buffer length is exhausted, the result will *not* be
 *        null-terminated.
 *
 *  @param pcBuffer     The output buffer
 *  @param ulBufferLen  The output buffer length
 *  @param ulNum        The 32-bit unsigned number to convert
 *  @param fHex         If true, format as hex; if false, decimal.
 *  @param ulFillLen    The fill length, if any
 *  @param cFill        The fill character to use
 *
 *  @return The length of the string.
 */
static uint32_t ULtoA( char * pcBuffer,
                       uint32_t ulBufferLen,
                       uint32_t ulNum,
                       bool fHex,
                       uint32_t ulFillLen,
                       char cFill )
{
    uint32_t ulLen;

    if( pcBuffer == NULL )
    {
        REDERROR();
        ulLen = 0U;
    }
    else
    {
        char ach[ 11U ]; /* Big enough for a uint32_t in radix 10 */
        uint32_t ulDigits = 0U;
        uint32_t ulNumericVal = ulNum;
        uint32_t ulRadix = fHex ? 16U : 10U;

        do
        {
            ach[ ulDigits ] = gacDigits[ ulNumericVal % ulRadix ];
            ulNumericVal = ulNumericVal / ulRadix;
            ulDigits++;
        }
        while( ulNumericVal > 0U );

        ulLen = FinishToA( ach, ulDigits, pcBuffer, ulBufferLen, ulFillLen, cFill );
    }

    return ulLen;
}


/** @brief Format an unsigned 64-bit integer as an ASCII string as decimal or
 *         hex.
 *
 *  @note If the output buffer length is exhausted, the result will *not* be
 *        null-terminated.
 *
 *  @param pcBuffer     The output buffer.
 *  @param ulBufferLen  The output buffer length.
 *  @param ullNum       The unsigned 64-bit number to convert.
 *  @param fHex         If true, format as hex; if false, decimal.
 *  @param ulFillLen    The fill length, if any.
 *  @param cFill        The fill character to use.
 *
 *  @return The length of the string.
 */
static uint32_t ULLtoA( char * pcBuffer,
                        uint32_t ulBufferLen,
                        uint64_t ullNum,
                        bool fHex,
                        uint32_t ulFillLen,
                        char cFill )
{
    uint32_t ulLen;

    if( pcBuffer == NULL )
    {
        REDERROR();
        ulLen = 0U;
    }
    else
    {
        char ach[ 21U ]; /* Big enough for a uint64_t in radix 10 */
        uint32_t ulDigits = 0U;
        uint64_t ullNumericVal = ullNum;

        if( fHex )
        {
            /*  We can figure out the digits using bit operations.
             */
            do
            {
                ach[ ulDigits ] = gacDigits[ ullNumericVal & 15U ];
                ullNumericVal >>= 4U;
                ulDigits++;
            }
            while( ullNumericVal > 0U );
        }
        else
        {
            /*  Not allowed to assume that 64-bit division is OK, so use a
             *  software division routine.
             */
            do
            {
                uint64_t ullQuotient;
                uint32_t ulRemainder;

                /*  Note: RedUint64DivMod32() is smart enough to use normal division
                 *  once ullNumericVal <= UINT32_MAX.
                 */
                ullQuotient = RedUint64DivMod32( ullNumericVal, 10U, &ulRemainder );

                ach[ ulDigits ] = gacDigits[ ulRemainder ];
                ullNumericVal = ullQuotient;
                ulDigits++;
            }
            while( ullNumericVal > 0U );
        }

        ulLen = FinishToA( ach, ulDigits, pcBuffer, ulBufferLen, ulFillLen, cFill );
    }

    return ulLen;
}


/** @brief Finish converting a number into an ASCII string representing that
 *         number.
 *
 *  This helper function contains common logic that needs to run at the end of
 *  all the "toA" functions.  It adds the fill character and reverses the digits
 *  string.
 *
 *  @param pcDigits     The digits (and sign) for the ASCII string, in reverse
 *                      order as they were computed.
 *  @param ulDigits     The number of digit characters.
 *  @param pcOutBuffer  The output buffer.
 *  @param ulBufferLen  The length of the output buffer.
 *  @param ulFillLen    The fill length.  If the number string is shorter than
 *                      this, the remaining bytes are filled with @p cFill.
 *  @param cFill        The fill character.
 *
 *  @return The length of @p pcOutBuffer.
 */
static uint32_t FinishToA( const char * pcDigits,
                           uint32_t ulDigits,
                           char * pcOutBuffer,
                           uint32_t ulBufferLen,
                           uint32_t ulFillLen,
                           char cFill )
{
    uint32_t ulIdx = 0U;
    uint32_t ulDigitIdx = ulDigits;

    /*  user may have asked for a fill char
     */
    if( ulFillLen > ulDigits )
    {
        uint32_t ulFillRem = ulFillLen - ulDigits;

        while( ( ulFillRem > 0U ) && ( ulIdx < ulBufferLen ) )
        {
            pcOutBuffer[ ulIdx ] = cFill;
            ulIdx++;
            ulFillRem--;
        }
    }

    /*  reverse the string
     */
    while( ( ulDigitIdx > 0 ) && ( ulIdx < ulBufferLen ) )
    {
        ulDigitIdx--;
        pcOutBuffer[ ulIdx ] = pcDigits[ ulDigitIdx ];
        ulIdx++;
    }

    if( ulIdx < ulBufferLen )
    {
        pcOutBuffer[ ulIdx ] = '\0';
    }

    return ulIdx;
}
