/*
	Copyright 2001, 2002 Georges Menie (www.menie.org)
	stdarg version contributed by Christian Ettinger

	This program is free software; you can redistribute it and/or modify
	it under the terms of the GNU Lesser General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	Changes for the FreeRTOS ports:

	- The dot in "%-8.8s"
	- The specifiers 'l' (long) and 'L' (long long)
	- The specifier 'u' for unsigned
	- Dot notation for IP addresses:
	  sprintf("IP = %xip\n", 0xC0A80164);
      will produce "IP = 192.168.1.100\n"
*/

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "FreeRTOS.h"

#define PAD_RIGHT 1
#define PAD_ZERO 2

/*
 * Return 1 for readable, 2 for writeable, 3 for both.
 * Function must be provided by the application.
 */
extern BaseType_t xApplicationMemoryPermissions( uint32_t aAddress );

extern void vOutputChar( const char cChar, const TickType_t xTicksToWait  );
static const TickType_t xTicksToWait = pdMS_TO_TICKS( 20 );

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
	char *str;
	const char *orgStr;
	const char *nulPos;
	int curLen;
	struct xPrintFlags flags;
};

static void strbuf_init( struct SStringBuf *apStr, char *apBuf, const char *apMaxStr )
{
	apStr->str = apBuf;
	apStr->orgStr = apBuf;
	apStr->nulPos = apMaxStr-1;
	apStr->curLen = 0;

	memset( &apStr->flags, '\0', sizeof( apStr->flags ) );
}
/*-----------------------------------------------------------*/

static BaseType_t strbuf_printchar( struct SStringBuf *apStr, int c )
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

static portINLINE BaseType_t strbuf_printchar_inline( struct SStringBuf *apStr, int c )
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
		*(apStr->str++) = c;
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

static portINLINE int i2hex( int aCh )
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

static BaseType_t prints(struct SStringBuf *apBuf, const char *apString )
{
	register int padchar = ' ';
	int i,len;

	if( xApplicationMemoryPermissions( ( uint32_t )apString ) == 0 )
	{
		/* The user has probably made a mistake with the parameter
		for '%s', the memory is not readbale. */
		apString = "INV_MEM";
	}

	if( apBuf->flags.width > 0 )
	{
		register int len = 0;
		register const char *ptr;
		for( ptr = apString; *ptr; ++ptr )
		{
			++len;
		}

		if( len >= apBuf->flags.width )
		{
			apBuf->flags.width = 0;
		}
		else
		{
			apBuf->flags.width -= len;
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
				if( strbuf_printchar( apBuf, '0' )  == 0 )
				{
					return pdFALSE;
				}
			}
		}
	}
	/* The string to print is not the result of a number conversion to ascii.
	 * For a string, printLimit is the max number of characters to display
	 */
	for( ; apBuf->flags.printLimit && *apString ; ++apString, --apBuf->flags.printLimit )
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
#define PRINT_BUF_LEN 12	/* to print 4294967296 */

#if	SPRINTF_LONG_LONG
#warning 64-bit libraries will be included as well
static BaseType_t printll( struct SStringBuf *apBuf, long long i )
{
	char print_buf[ 2 * PRINT_BUF_LEN ];
	register char *s;
	register int t, neg = 0;
	register unsigned long long u = i;
	lldiv_t lldiv_result;

/* typedef struct
 * {
 * 	long long int quot; // quotient
 * 	long long int rem;  // remainder
 * } lldiv_t;
 */

	apBuf->flags.isNumber = pdTRUE;	/* Parameter for prints */
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

	s = print_buf + sizeof( print_buf ) - 1;

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
#endif	/* SPRINTF_LONG_LONG */
/*-----------------------------------------------------------*/

static BaseType_t printi( struct SStringBuf *apBuf, int i )
{
	char print_buf[ PRINT_BUF_LEN ];
	register char *s;
	register int t, neg = 0;
	register unsigned int u = i;
	register unsigned base = apBuf->flags.base;

	apBuf->flags.isNumber = pdTRUE;	/* Parameter for prints */

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

	s = print_buf + sizeof( print_buf ) - 1;

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
	// The generic case, not yet in use
	default:
		while( u )
		{
			t = u % base;
			if( t >= 10)
			{
				t += apBuf->flags.letBase - '0' - 10;
			}
			*( --s ) = t + '0';
			u /= base;
		}
		break;
*/
	}

	if( neg != 0 )
	{
		if( apBuf->flags.width && (apBuf->flags.pad & PAD_ZERO ) )
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

static BaseType_t printIp(struct SStringBuf *apBuf, unsigned i )
{
	char print_buf[16];

	sprintf( print_buf, "%u.%u.%u.%u",
		i >> 24,
		( i >> 16 ) & 0xff,
		( i >> 8 ) & 0xff,
		i & 0xff );
	apBuf->flags.isNumber = pdTRUE;	/* Parameter for prints */
	prints( apBuf, print_buf );

	return pdTRUE;
}
/*-----------------------------------------------------------*/

static void tiny_print( struct SStringBuf *apBuf, const char *format, va_list args )
{
	char scr[2];

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
		memset( &apBuf->flags, '\0', sizeof( apBuf->flags ) );

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
			apBuf->flags.printLimit--;  /* -1: make it unlimited */
		}
		if( ch == 's' )
		{
			register char *s = ( char * )va_arg( args, int );
			if( prints( apBuf, s ? s : "(null)" ) == 0 )
			{
				break;
			}
			continue;
		}
		if( ch == 'c' )
		{
			/* char are converted to int then pushed on the stack */
			scr[0] = ( char ) va_arg( args, int );

			if( strbuf_printchar( apBuf, scr[0] )  == 0 )
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

		if( ch == 'd' || ch == 'u' )
		{
			apBuf->flags.isSigned = ( ch == 'd' );
#if	SPRINTF_LONG_LONG
			if( apBuf->flags.long64 != pdFALSE )
			{
				if( printll( apBuf, va_arg( args, long long ) ) == 0 )
				{
					break;
				}
			} else
#endif	/* SPRINTF_LONG_LONG */
			if( printi( apBuf, va_arg( args, int ) ) == 0 )
			{
				break;
			}
			continue;
		}

		apBuf->flags.base = 16;		/* From here all hexadecimal */

		if( ch == 'x' && format[0] == 'i' && format[1] == 'p' )
		{
			format += 2;	/* eat the "xi" of "xip" */
			/* Will use base 10 again */
			if( printIp( apBuf, va_arg( args, int ) ) == 0 )
			{
				break;
			}
			continue;
		}
		if( ch == 'x' || ch == 'X' || ch == 'p' || ch == 'o' )
		{
			if( ch == 'X' )
			{
				apBuf->flags.letBase = 'A';
			}
			else if( ch == 'o' )
			{
				apBuf->flags.base = 8;
			}
#if	SPRINTF_LONG_LONG
			if( apBuf->flags.long64 != pdFALSE )
			{
				if( printll( apBuf, va_arg( args, long long ) ) == 0 )
				{
					break;
				}
			} else
#endif	/* SPRINTF_LONG_LONG */
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

int vsnprintf( char *apBuf, size_t aMaxLen, const char *apFmt, va_list args )
{
	struct SStringBuf strBuf;
	strbuf_init( &strBuf, apBuf, ( const char* )apBuf + aMaxLen );
	tiny_print( &strBuf, apFmt, args );

	return strBuf.curLen;
}
/*-----------------------------------------------------------*/

int snprintf( char *apBuf, size_t aMaxLen, const char *apFmt, ... )
{
	va_list args;

	va_start( args,  apFmt );
	struct SStringBuf strBuf;
	strbuf_init( &strBuf, apBuf, ( const char* )apBuf + aMaxLen );
	tiny_print( &strBuf, apFmt, args );
	va_end( args );

	return strBuf.curLen;
}
/*-----------------------------------------------------------*/

int sprintf( char *apBuf, const char *apFmt, ... )
{
	va_list args;

	va_start( args,  apFmt );
	struct SStringBuf strBuf;
	strbuf_init( &strBuf, apBuf, ( const char * )apBuf + 1024 );
	tiny_print( &strBuf, apFmt, args );
	va_end( args );

	return strBuf.curLen;
}
/*-----------------------------------------------------------*/

int vsprintf( char *apBuf, const char *apFmt, va_list args )
{
	struct SStringBuf strBuf;
	strbuf_init( &strBuf, apBuf, ( const char* ) apBuf + 1024 );
	tiny_print( &strBuf, apFmt, args );

	return strBuf.curLen;
}
/*-----------------------------------------------------------*/

const char *mkSize (unsigned long long aSize, char *apBuf, int aLen)
{
static char retString[33];
size_t gb, mb, kb, sb;

	if (apBuf == NULL) {
		apBuf = retString;
		aLen = sizeof( retString );
	}
	gb = aSize / (1024*1024*1024);
	aSize -= gb * (1024*1024*1024);
	mb = aSize / (1024*1024);
	aSize -= mb * (1024*1024);
	kb = aSize / (1024);
	aSize -= kb * (1024);
	sb = aSize;
	if( gb )
	{
		snprintf (apBuf, aLen, "%u.%02u GB", ( unsigned ) gb, ( unsigned ) ( ( 100 * mb ) / 1024ul ) );
	}
	else if( mb )
	{
		snprintf (apBuf, aLen, "%u.%02u MB", ( unsigned ) mb, ( unsigned ) ( ( 100 * kb) / 1024ul ) );
	}
	else if( kb != 0ul )
	{
		snprintf (apBuf, aLen, "%u.%02u KB", ( unsigned ) kb, ( unsigned ) ( ( 100 * sb) / 1024ul ) );
	}
	else
	{
		snprintf (apBuf, aLen, "%u bytes", ( unsigned ) sb);
	}
	return apBuf;
}
