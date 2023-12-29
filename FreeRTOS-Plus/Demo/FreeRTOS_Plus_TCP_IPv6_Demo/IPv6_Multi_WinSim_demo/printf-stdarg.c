/*
 *  Copyright 2001, 2002 Georges Menie (www.menie.org)
 *  stdarg version contributed by Christian Ettinger
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  Changes for the FreeRTOS ports:
 *
 *  - The dot in "%-8.8s"
 *  - The specifiers 'l' (long) and 'L' (long long)
 *  - The specifier 'u' for unsigned
 *  - Dot notation for IP addresses:
 *    sprintf("IP = %xip\n", 0xC0A80164);
 *    will produce "IP = 192.168.1.100\n"
 *    sprintf("IP = %pip\n", pxIPv6_Address);
 */

#include <stdarg.h>
#include <stdio.h>

#include <stdlib.h>
#include <string.h>


#if ( USE_FREERTOS != 0 )
    #include "FreeRTOS.h"
#else
    #include <stdint.h>
    typedef int        BaseType_t;
    typedef uint32_t   TickType_t;
    #define pdTRUE     1
    #define pdFALSE    0
    #define pdMS_TO_TICKS( x )    ( x )
#endif

#define PAD_RIGHT    1
#define PAD_ZERO     2

int sprintf( char * apBuf,
             const char * apFmt,
             ... );

/*
 * Return 1 for readable, 2 for writable, 3 for both.
 * Function must be provided by the application.
 */
extern BaseType_t xApplicationMemoryPermissions( uint32_t aAddress );
extern void vOutputChar( const char cChar,
                         const TickType_t xTicksToWait );

#ifdef __GNUC__

    __attribute__( ( weak ) ) BaseType_t xApplicationMemoryPermissions( uint32_t aAddress )
    {
        ( void ) aAddress;
        /* Return 1 for readable, 2 for writable, 3 for both. */
        return 0x03;
    }


    __attribute__( ( weak ) ) void vOutputChar( const char cChar,
                                                const TickType_t xTicksToWait )
    {
        ( void ) cChar;
        ( void ) xTicksToWait;
        /* Do nothing. */
    }

#endif /* __GNUC__ */

static const TickType_t xTicksToWait = pdMS_TO_TICKS( 20 );

int tiny_printf( const char * format,
                 ... );

/* Defined here: write a large amount as GB, MB, KB or bytes */
const char * mkSize( unsigned long long aSize,
                     char * apBuf,
                     int aLen );

typedef union
{
    uint8_t ucBytes[ 4 ];
    uint16_t ucShorts[ 2 ];
    uint32_t ulWords[ 1 ];
} _U32;

struct xPrintFlags
{
    int base;
    int width;
    int printLimit;
    unsigned
        pad : 8,
        letBase : 8,
        isSigned : 1,
        isNumber : 1,
        long32 : 1,
        long64 : 1;
};

struct SStringBuf
{
    char * str;
    const char * orgStr;
    const char * nulPos;
    int curLen;
    struct xPrintFlags flags;
};

#ifdef __GNUC__
    const static _U32 u32 =
    {
        ucBytes : { 0, 1, 2, 3 }
    };
#else
const static _U32 u32 = { 0, 1, 2, 3 };
#endif

static void strbuf_init( struct SStringBuf * apStr,
                         char * apBuf,
                         const char * apMaxStr )
{
    apStr->str = apBuf;
    apStr->orgStr = apBuf;
    apStr->nulPos = apMaxStr - 1;
    apStr->curLen = 0;

    memset( &apStr->flags, '\0', sizeof apStr->flags );
}
/*-----------------------------------------------------------*/

static BaseType_t strbuf_printchar( struct SStringBuf * apStr,
                                    int c )
{
    if( apStr->str == NULL )
    {
        vOutputChar( ( char ) c, xTicksToWait );
        apStr->curLen++;
        return pdTRUE;
    }

    if( apStr->str < apStr->nulPos )
    {
        *( apStr->str++ ) = c;
        apStr->curLen++;
        return pdTRUE;
    }

    if( apStr->str == apStr->nulPos )
    {
        *( apStr->str++ ) = '\0';
    }

    return pdFALSE;
}
/*-----------------------------------------------------------*/

static __inline BaseType_t strbuf_printchar_inline( struct SStringBuf * apStr,
                                                    int c )
{
    if( apStr->str == NULL )
    {
        vOutputChar( ( char ) c, xTicksToWait );

        if( c == 0 )
        {
            return pdFALSE;
        }

        apStr->curLen++;
        return pdTRUE;
    }

    if( apStr->str < apStr->nulPos )
    {
        *( apStr->str++ ) = c;

        if( c == 0 )
        {
            return pdFALSE;
        }

        apStr->curLen++;
        return pdTRUE;
    }

    if( apStr->str == apStr->nulPos )
    {
        *( apStr->str++ ) = '\0';
    }

    return pdFALSE;
}
/*-----------------------------------------------------------*/

static __inline int i2hex( int aCh )
{
    int iResult;

    if( aCh < 10 )
    {
        iResult = '0' + aCh;
    }
    else
    {
        iResult = 'A' + aCh - 10;
    }

    return iResult;
}
/*-----------------------------------------------------------*/

static BaseType_t prints( struct SStringBuf * apBuf,
                          const char * apString )
{
    register int padchar = ' ';
    int i, len;

    if( xApplicationMemoryPermissions( ( uint32_t ) apString ) == 0 )
    {
        /* The user has probably made a mistake with the parameter
         * for '%s', the memory is not readable. */
        apString = "INV_MEM";
    }

    if( apBuf->flags.width > 0 )
    {
        register int count = 0;
        register const char * ptr;

        for( ptr = apString; *ptr; ++ptr )
        {
            ++count;
        }

        if( count >= apBuf->flags.width )
        {
            apBuf->flags.width = 0;
        }
        else
        {
            apBuf->flags.width -= count;
        }

        if( apBuf->flags.pad & PAD_ZERO )
        {
            padchar = '0';
        }
    }

    if( ( apBuf->flags.pad & PAD_RIGHT ) == 0 )
    {
        for( ; apBuf->flags.width > 0; --apBuf->flags.width )
        {
            if( strbuf_printchar( apBuf, padchar ) == 0 )
            {
                return pdFALSE;
            }
        }
    }

    if( ( apBuf->flags.isNumber == pdTRUE ) && ( apBuf->flags.pad == pdTRUE ) )
    {
        /* The string to print represents an integer number.
         * In this case, printLimit is the min number of digits to print
         * If the length of the number to print is less than the min nb of i
         * digits to display, we add 0 before printing the number
         */
        len = strlen( apString );

        if( len < apBuf->flags.printLimit )
        {
            i = apBuf->flags.printLimit - len;

            for( ; i; i-- )
            {
                if( strbuf_printchar( apBuf, '0' ) == 0 )
                {
                    return pdFALSE;
                }
            }
        }
    }

    /* The string to print is not the result of a number conversion to ascii.
     * For a string, printLimit is the max number of characters to display
     */
    for( ; apBuf->flags.printLimit && *apString; ++apString, --apBuf->flags.printLimit )
    {
        if( !strbuf_printchar( apBuf, *apString ) )
        {
            return pdFALSE;
        }
    }

    for( ; apBuf->flags.width > 0; --apBuf->flags.width )
    {
        if( !strbuf_printchar( apBuf, padchar ) )
        {
            return pdFALSE;
        }
    }

    return pdTRUE;
}
/*-----------------------------------------------------------*/

/* the following should be enough for 32 bit int */
#define PRINT_BUF_LEN    12 /* to print 4294967296 */

#if SPRINTF_LONG_LONG
    #warning 64-bit libraries will be included as well
    static BaseType_t printll( struct SStringBuf * apBuf,
                               long long i )
    {
        char print_buf[ 2 * PRINT_BUF_LEN ];
        register char * s;
        register int t, neg = 0;
        register unsigned long long u = i;
        lldiv_t lldiv_result;

/* typedef struct
 * {
 *  long long int quot; // quotient
 *  long long int rem;  // remainder
 * } lldiv_t;
 */

        apBuf->flags.isNumber = pdTRUE; /* Parameter for prints */

        if( i == 0LL )
        {
            print_buf[ 0 ] = '0';
            print_buf[ 1 ] = '\0';
            return prints( apBuf, print_buf );
        }

        if( ( apBuf->flags.isSigned == pdTRUE ) && ( apBuf->flags.base == 10 ) && ( i < 0LL ) )
        {
            neg = 1;
            u = -i;
        }

        s = print_buf + sizeof print_buf - 1;

        *s = '\0';

        /* 18446744073709551616 */
        while( u != 0 )
        {
            lldiv_result = lldiv( u, ( unsigned long long ) apBuf->flags.base );
            t = lldiv_result.rem;

            if( t >= 10 )
            {
                t += apBuf->flags.letBase - '0' - 10;
            }

            *( --s ) = t + '0';
            u = lldiv_result.quot;
        }

        if( neg != 0 )
        {
            if( ( apBuf->flags.width != 0 ) && ( apBuf->flags.pad & PAD_ZERO ) )
            {
                if( !strbuf_printchar( apBuf, '-' ) )
                {
                    return pdFALSE;
                }

                --apBuf->flags.width;
            }
            else
            {
                *( --s ) = '-';
            }
        }

        return prints( apBuf, s );
    }
#endif /* SPRINTF_LONG_LONG */
/*-----------------------------------------------------------*/

static BaseType_t printi( struct SStringBuf * apBuf,
                          int i )
{
    char print_buf[ PRINT_BUF_LEN ];
    register char * s;
    register int t, neg = 0;
    register unsigned int u = i;
    register unsigned base = apBuf->flags.base;

    apBuf->flags.isNumber = pdTRUE; /* Parameter for prints */

    if( i == 0 )
    {
        print_buf[ 0 ] = '0';
        print_buf[ 1 ] = '\0';
        return prints( apBuf, print_buf );
    }

    if( ( apBuf->flags.isSigned == pdTRUE ) && ( base == 10 ) && ( i < 0 ) )
    {
        neg = 1;
        u = -i;
    }

    s = print_buf + sizeof print_buf - 1;

    *s = '\0';

    switch( base )
    {
        case 16:

            while( u != 0 )
            {
                t = u & 0xF;

                if( t >= 10 )
                {
                    t += apBuf->flags.letBase - '0' - 10;
                }

                *( --s ) = t + '0';
                u >>= 4;
            }

            break;

        case 8:
        case 10:

            /* GCC compiles very efficient */
            while( u )
            {
                t = u % base;
                *( --s ) = t + '0';
                u /= base;
            }

            break;

/*
 *  // The generic case, not yet in use
 *  default:
 *      while( u )
 *      {
 *          t = u % base;
 *          if( t >= 10)
 *          {
 *              t += apBuf->flags.letBase - '0' - 10;
 *          }
 *( --s ) = t + '0';
 *          u /= base;
 *      }
 *      break;
 */
    }

    if( neg != 0 )
    {
        if( apBuf->flags.width && ( apBuf->flags.pad & PAD_ZERO ) )
        {
            if( strbuf_printchar( apBuf, '-' ) == 0 )
            {
                return pdFALSE;
            }

            --apBuf->flags.width;
        }
        else
        {
            *( --s ) = '-';
        }
    }

    return prints( apBuf, s );
}
/*-----------------------------------------------------------*/

static BaseType_t printIp( struct SStringBuf * apBuf,
                           unsigned i )
{
    char print_buf[ 16 ];

    sprintf( print_buf, "%u.%u.%u.%u",
             i >> 24,
             ( i >> 16 ) & 0xff,
             ( i >> 8 ) & 0xff,
             i & 0xff );
    apBuf->flags.isNumber = pdTRUE; /* Parameter for prints */
    prints( apBuf, print_buf );

    return pdTRUE;
}
/*-----------------------------------------------------------*/

static uint16_t usNetToHost( uint16_t usValue )
{
    if( u32.ulWords[ 0 ] == 0x00010203 )
    {
        return usValue;
    }
    else
    {
        return ( usValue << 8 ) | ( usValue >> 8 );
    }
}

static BaseType_t printIPv6( struct SStringBuf * apBuf,
                             uint16_t * pusAddress )
{
    int iIndex;
    int iZeroStart = -1;
    int iZeroLength = 0;
    int iCurStart = 0;
    int iCurLength = 0;

    for( iIndex = 0; iIndex < 8; iIndex++ )
    {
        uint16_t usValue = pusAddress[ iIndex ];

        if( usValue == 0 )
        {
            if( iCurLength == 0 )
            {
                iCurStart = iIndex;
            }

            iCurLength++;
        }

        if( ( usValue != 0 ) || ( iIndex == 7 ) )
        {
            if( iZeroLength < iCurLength )
            {
                iZeroLength = iCurLength;
                iZeroStart = iCurStart;
            }

            iCurLength = 0;
        }
    }

    apBuf->flags.base = 16;
    apBuf->flags.letBase = 'a'; /* use lower-case letters 'a' to 'f' */

    for( iIndex = 0; iIndex < 8; iIndex++ )
    {
        if( iIndex == iZeroStart )
        {
            iIndex += iZeroLength - 1;
            strbuf_printchar( apBuf, ':' );

            if( iIndex == 7 )
            {
                strbuf_printchar( apBuf, ':' );
            }
        }
        else
        {
            if( iIndex > 0 )
            {
                strbuf_printchar( apBuf, ':' );
            }

            printi( apBuf, ( int ) ( ( uint32_t ) usNetToHost( pusAddress[ iIndex ] ) ) );
        }
    }

    return pdTRUE;
}
/*-----------------------------------------------------------*/

static void tiny_print( struct SStringBuf * apBuf,
                        const char * format,
                        va_list args )
{
    char scr[ 2 ];

    for( ; ; )
    {
        int ch = *( format++ );

        if( ch != '%' )
        {
            do
            {
                /* Put the most like flow in a small loop */
                if( strbuf_printchar_inline( apBuf, ch ) == 0 )
                {
                    return;
                }

                ch = *( format++ );
            } while( ch != '%' );
        }

        ch = *( format++ );
        /* Now ch has character after '%', format pointing to next */

        if( ch == '\0' )
        {
            break;
        }

        if( ch == '%' )
        {
            if( strbuf_printchar( apBuf, ch ) == 0 )
            {
                return;
            }

            continue;
        }

        memset( &apBuf->flags, '\0', sizeof apBuf->flags );

        if( ch == '-' )
        {
            ch = *( format++ );
            apBuf->flags.pad = PAD_RIGHT;
        }

        while( ch == '0' )
        {
            ch = *( format++ );
            apBuf->flags.pad |= PAD_ZERO;
        }

        if( ch == '*' )
        {
            ch = *( format++ );
            apBuf->flags.width = va_arg( args, int );
        }
        else
        {
            while( ch >= '0' && ch <= '9' )
            {
                apBuf->flags.width *= 10;
                apBuf->flags.width += ch - '0';
                ch = *( format++ );
            }
        }

        if( ch == '.' )
        {
            ch = *( format++ );

            if( ch == '*' )
            {
                apBuf->flags.printLimit = va_arg( args, int );
                ch = *( format++ );
            }
            else
            {
                while( ch >= '0' && ch <= '9' )
                {
                    apBuf->flags.printLimit *= 10;
                    apBuf->flags.printLimit += ch - '0';
                    ch = *( format++ );
                }
            }
        }

        if( apBuf->flags.printLimit == 0 )
        {
            apBuf->flags.printLimit--; /* -1: make it unlimited */
        }

        if( ch == 'p' )
        {
            if( ( format[ 0 ] == 'i' ) && ( format[ 1 ] == 'p' ) )
            {
                format += 2; /* eat the "pi" of "pip" */

                /* Print a IPv6 address */
                if( printIPv6( apBuf, va_arg( args, uint16_t * ) ) == 0 )
                {
                    break;
                }

                continue;
            }
        }

        if( ch == 's' )
        {
            register char * s = ( char * ) va_arg( args, int );

            if( prints( apBuf, s ? s : "(null)" ) == 0 )
            {
                break;
            }

            continue;
        }

        if( ch == 'c' )
        {
            /* char are converted to int then pushed on the stack */
            scr[ 0 ] = ( char ) va_arg( args, int );

            if( strbuf_printchar( apBuf, scr[ 0 ] ) == 0 )
            {
                return;
            }

            continue;
        }

        if( ch == 'l' )
        {
            ch = *( format++ );
            apBuf->flags.long32 = 1;
            /* Makes not difference as u32 == long */
        }

        if( ch == 'L' )
        {
            ch = *( format++ );
            apBuf->flags.long64 = 1;
            /* Does make a difference */
        }

        apBuf->flags.base = 10;
        apBuf->flags.letBase = 'a';

        if( ( ch == 'd' ) || ( ch == 'u' ) )
        {
            apBuf->flags.isSigned = ( ch == 'd' );
            #if SPRINTF_LONG_LONG
                if( apBuf->flags.long64 != pdFALSE )
                {
                    if( printll( apBuf, va_arg( args, long long ) ) == 0 )
                    {
                        break;
                    }
                }
                else
            #endif /* SPRINTF_LONG_LONG */

            if( printi( apBuf, va_arg( args, int ) ) == 0 )
            {
                break;
            }

            continue;
        }

        apBuf->flags.base = 16; /* From here all hexadecimal */

        if( ( ch == 'x' ) && ( format[ 0 ] == 'i' ) && ( format[ 1 ] == 'p' ) )
        {
            format += 2; /* eat the "xi" of "xip" */

            /* Will use base 10 again */
            if( printIp( apBuf, va_arg( args, int ) ) == 0 )
            {
                break;
            }

            continue;
        }

        if( ( ch == 'x' ) || ( ch == 'X' ) || ( ch == 'p' ) || ( ch == 'o' ) )
        {
            if( ch == 'X' )
            {
                apBuf->flags.letBase = 'A';
            }
            else if( ch == 'o' )
            {
                apBuf->flags.base = 8;
            }

            #if SPRINTF_LONG_LONG
                if( apBuf->flags.long64 != pdFALSE )
                {
                    if( printll( apBuf, va_arg( args, long long ) ) == 0 )
                    {
                        break;
                    }
                }
                else
            #endif /* SPRINTF_LONG_LONG */

            if( printi( apBuf, va_arg( args, int ) ) == 0 )
            {
                break;
            }

            continue;
        }
    }

    strbuf_printchar( apBuf, '\0' );
}
/*-----------------------------------------------------------*/

int tiny_printf( const char * format,
                 ... )
{
    va_list args;

    va_start( args, format );
    struct SStringBuf strBuf;
    strbuf_init( &strBuf, NULL, ( const char * ) NULL );
    tiny_print( &strBuf, format, args );
    va_end( args );

    return strBuf.curLen;
}
/*-----------------------------------------------------------*/

int vsnprintf( char * apBuf,
               size_t aMaxLen,
               const char * apFmt,
               va_list args )
{
    struct SStringBuf strBuf;

    strbuf_init( &strBuf, apBuf, ( const char * ) apBuf + aMaxLen );
    tiny_print( &strBuf, apFmt, args );

    return strBuf.curLen;
}
/*-----------------------------------------------------------*/

/*void timer_start( void ); */
/*void timer_stop( void ); */

int snprintf( char * apBuf,
              size_t aMaxLen,
              const char * apFmt,
              ... )
{
    va_list args;

/*timer_stop(); */
    va_start( args, apFmt );
    struct SStringBuf strBuf;
    strbuf_init( &strBuf, apBuf, ( const char * ) apBuf + aMaxLen );
    tiny_print( &strBuf, apFmt, args );
    va_end( args );
/*timer_start(); */

    return strBuf.curLen;
}
/*-----------------------------------------------------------*/

int sprintf( char * apBuf,
             const char * apFmt,
             ... )
{
    va_list args;

    va_start( args, apFmt );
    struct SStringBuf strBuf;
    strbuf_init( &strBuf, apBuf, ( const char * ) apBuf + 1024 );
    tiny_print( &strBuf, apFmt, args );
    va_end( args );

    return strBuf.curLen;
}
/*-----------------------------------------------------------*/

int vsprintf( char * apBuf,
              const char * apFmt,
              va_list args )
{
    struct SStringBuf strBuf;

    strbuf_init( &strBuf, apBuf, ( const char * ) apBuf + 1024 );
    tiny_print( &strBuf, apFmt, args );

    return strBuf.curLen;
}
/*-----------------------------------------------------------*/

const char * mkSize( unsigned long long aSize,
                     char * apBuf,
                     int aLen )
{
    static char retString[ 33 ];
    size_t gb, mb, kb, sb;

    if( apBuf == NULL )
    {
        apBuf = retString;
        aLen = sizeof retString;
    }

    gb = aSize / ( 1024 * 1024 * 1024 );
    aSize -= gb * ( 1024 * 1024 * 1024 );
    mb = aSize / ( 1024 * 1024 );
    aSize -= mb * ( 1024 * 1024 );
    kb = aSize / ( 1024 );
    aSize -= kb * ( 1024 );
    sb = aSize;

    if( gb )
    {
        snprintf( apBuf, aLen, "%u.%02u GB", ( unsigned ) gb, ( unsigned ) ( ( 100 * mb ) / 1024ul ) );
    }
    else if( mb )
    {
        snprintf( apBuf, aLen, "%u.%02u MB", ( unsigned ) mb, ( unsigned ) ( ( 100 * kb ) / 1024ul ) );
    }
    else if( kb != 0ul )
    {
        snprintf( apBuf, aLen, "%u.%02u KB", ( unsigned ) kb, ( unsigned ) ( ( 100 * sb ) / 1024ul ) );
    }
    else
    {
        snprintf( apBuf, aLen, "%u bytes", ( unsigned ) sb );
    }

    return apBuf;
}

#ifdef _MSC_VER

    #if defined( _NO_CRT_STDIO_INLINE )

        int printf( char const * const _Format,
                    ... )
        {
            int _Result;
            va_list _ArgList;

            __crt_va_start( _ArgList, _Format );
            _Result = _vfprintf_l( stdout, _Format, NULL, _ArgList );
            __crt_va_end( _ArgList );
            return _Result;
        }

    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */

    #if defined( _NO_CRT_STDIO_INLINE )

        int sscanf( char const * const _Buffer,
                    char const * const _Format,
                    ... )
        {
            int _Result;
            va_list _ArgList;

            __crt_va_start( _ArgList, _Format );
            _Result = _vsscanf_l( _Buffer, _Format, NULL, _ArgList );
            __crt_va_end( _ArgList );
            return _Result;
        }

    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */

    #if defined( _NO_CRT_STDIO_INLINE )

        int _vfprintf_l( FILE * const _Stream,
                         char const * const _Format,
                         _locale_t const _Locale,
                         va_list _ArgList )
        {
            return __stdio_common_vfprintf( _CRT_INTERNAL_LOCAL_PRINTF_OPTIONS, _Stream, _Format, _Locale, _ArgList );
        }

    #endif

    #if defined( _NO_CRT_STDIO_INLINE )

        int _vsscanf_l( char const * const _Buffer,
                        char const * const _Format,
                        _locale_t const _Locale,
                        va_list _ArgList )
        {
            return __stdio_common_vsscanf(
                _CRT_INTERNAL_LOCAL_SCANF_OPTIONS,
                _Buffer, ( size_t ) -1, _Format, _Locale, _ArgList );
        }

    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */

    #if defined( _NO_CRT_STDIO_INLINE )
        int scanf( char const * const _Format,
                   ... )
        {
            int _Result;
            va_list _ArgList;

            __crt_va_start( _ArgList, _Format );
            _Result = _vfscanf_l( stdin, _Format, NULL, _ArgList );
            __crt_va_end( _ArgList );
            return _Result;
        }
    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */

    #if defined( _NO_CRT_STDIO_INLINE )
        int _vfscanf_l( _Inout_ FILE * const _Stream,
                        char const * const _Format,
                        const _locale_t _Locale,
                        va_list _ArgList )
        {
            return __stdio_common_vfscanf(
                _CRT_INTERNAL_LOCAL_SCANF_OPTIONS,
                _Stream, _Format, _Locale, _ArgList );
        }

    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */


    #if defined( _NO_CRT_STDIO_INLINE )
        int vsnprintf_s( char * const _Buffer,
                         size_t const _BufferCount,
                         size_t const _MaxCount,
                         char const * const _Format,
                         va_list _ArgList )
        {
            return _vsnprintf_s_l( _Buffer, _BufferCount, _MaxCount, _Format, NULL, _ArgList );
        }
        int _vsnprintf_s( char * const _Buffer,
                          size_t const _BufferCount,
                          size_t const _MaxCount,
                          char const * const _Format,
                          va_list _ArgList )
        {
            return _vsnprintf_s_l( _Buffer, _BufferCount, _MaxCount, _Format, NULL, _ArgList );
        }

    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */

    #if defined( _NO_CRT_STDIO_INLINE )
        int _vsnprintf_s_l( char * const _Buffer,
                            size_t const _BufferCount,
                            size_t const _MaxCount,
                            char const * const _Format,
                            _locale_t const _Locale,
                            va_list _ArgList )
        {
            int const _Result = __stdio_common_vsnprintf_s(
                _CRT_INTERNAL_LOCAL_PRINTF_OPTIONS,
                _Buffer, _BufferCount, _MaxCount, _Format, _Locale, _ArgList );

            return _Result < 0 ? -1 : _Result;
        }
    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */

#endif /* __WIN32__ */
