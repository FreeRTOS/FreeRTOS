/*
 * FreeRTOS+FAT build 191128 - Note:  FreeRTOS+FAT is still in the lab!
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Authors include James Walmsley, Hein Tibosch and Richard Barry
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
 *
 */

/**
 *	@file		ff_string.c
 *	@ingroup	STRING
 *
 *	@defgroup	STRING	FreeRTOS+FAT String Library
 *	@brief		Portable String Library for FreeRTOS+FAT
 *
 *
 **/

#ifndef _FF_STRING_H_
#define _FF_STRING_H_

#include "FreeRTOSFATConfig.h"
#include <string.h>

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
#include <wchar.h>
typedef wchar_t			FF_T_WCHAR;		/*/< Unicode UTF-16 Character type, for FreeRTOS+FAT when UNICODE is enabled. */
#endif

#if defined( _MSC_VER ) && ( _MSC_VER <= 1600 )
	#define FF_stricmp	_stricmp
#else
	#define FF_stricmp	strcasecmp
#endif

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	void			FF_tolower		( FF_T_WCHAR *string, uint32_t strLen );
	void			FF_toupper		( FF_T_WCHAR *string, uint32_t strLen );
	BaseType_t		FF_strmatch		( const FF_T_WCHAR *str1, const FF_T_WCHAR *str2, BaseType_t len );
	FF_T_WCHAR		*FF_strtok		( const FF_T_WCHAR *string, FF_T_WCHAR *token, uint16_t *tokenNumber, BaseType_t *last, BaseType_t xLength );
	BaseType_t		FF_wildcompare	( const FF_T_WCHAR *pcWildCard, const FF_T_WCHAR *pszString );

	/* ASCII to UTF16 and UTF16 to ASCII routines. -- These are lossy routines, and are only for converting ASCII to UTF-16 */
	/* and the equivalent back to ASCII. Do not use them for international text. */
	void FF_cstrtowcs(FF_T_WCHAR *wcsDest, const char *szpSource);
	void FF_wcstocstr(char *szpDest, const FF_T_WCHAR *wcsSource);
	void FF_cstrntowcs(FF_T_WCHAR *wcsDest, const char *szpSource, uint32_t len);
	void FF_wcsntocstr(char *szpDest, const FF_T_WCHAR *wcsSource, uint32_t len);
#else
	void			FF_tolower		( char *string, uint32_t strLen );
	void			FF_toupper		( char *string, uint32_t strLen );
	BaseType_t		FF_strmatch		( const char *str1, const char *str2, BaseType_t len );
	char			*FF_strtok		( const char *string, char *token, uint16_t *tokenNumber, BaseType_t *last, BaseType_t xLength );
	BaseType_t		FF_wildcompare	( const char *pcWildCard, const char *pszString );
#endif /* ffconfigUNICODE_UTF16_SUPPORT */

/* UTF8 / UTF16 Transformation Functions. */

#if ( ( ffconfigUNICODE_UTF16_SUPPORT != 0 ) && ( WCHAR_MAX > 0xFFFF ) ) || ( ffconfigUNICODE_UTF8_SUPPORT != 0 )
	UBaseType_t FF_GetUtf16SequenceLen	(uint16_t usLeadChar);
#endif

#if( ffconfigUNICODE_UTF8_SUPPORT != 0 )
	int32_t FF_Utf8ctoUtf16c		(uint16_t *utf16Dest, const uint8_t *utf8Source, uint32_t ulSize);
	int32_t FF_Utf16ctoUtf8c		(uint8_t *utf8Dest, const uint16_t *utf16Source, uint32_t ulSize);
#endif	/* ffconfigUNICODE_UTF8_SUPPORT */

/* UTF16 / UTF32 Transformation Functions. */

#if( ffconfigNOT_USED_FOR_NOW != 0 )
	int32_t FF_Utf16ctoUtf32c(uint32_t *utf32Dest, const uint16_t *utf16Source);
#endif

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 ) && ( WCHAR_MAX > 0xFFFF )
	int32_t FF_Utf32ctoUtf16c(uint16_t *utf16Dest, uint32_t utf32char, uint32_t ulSize);
#endif

/* String transformations. */
int32_t FF_Utf32stoUtf8s(uint8_t *Utf8String, uint32_t *Utf32String);

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	#define STRNCPY( target, src, maxlen )	wcsncpy( ( target ), ( src ), ( maxlen ) )
	#define STRLEN( string )				wcslen( ( string ) )
#else
	#define STRNCPY( target, src, maxlen )	strncpy( ( target ), ( src ), ( maxlen ) );
	#define STRLEN( string )				strlen( ( string ) )
#endif

#endif

