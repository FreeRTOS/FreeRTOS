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

#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "ff_headers.h"

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	#include <wchar.h>
	#include <wctype.h>
#endif

/*
 *	These will eventually be moved into a platform independent string
 *	library. Which will be optional. (To allow the use of system specific versions).
 */

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	void FF_cstrntowcs( FF_T_WCHAR *wcsDest, const int8_t *szpSource, uint32_t ulLength )
	{
		while( ( *szpSource != '\0' )  && ( ulLength-- != 0 ) )
		{
			*( wcsDest++ ) = *( szpSource++ );
		}
		*wcsDest = '\0';
	}
#endif /* ffconfigUNICODE_UTF16_SUPPORT */
/*-----------------------------------------------------------*/

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	void FF_cstrtowcs( FF_T_WCHAR *wcsDest, const int8_t *szpSource )
	{
		while( *szpSource != '\0' )
		{
			*wcsDest++ = ( FF_T_WCHAR ) *( szpSource++ );
		}
		*wcsDest = '\0';
	}
#endif /* ffconfigUNICODE_UTF16_SUPPORT */
/*-----------------------------------------------------------*/

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	void FF_wcstocstr( int8_t *szpDest, const FF_T_WCHAR *wcsSource )
	{
		while( *wcsSource != '\0' )
		{
			*szpDest++ = ( int8_t )*( wcsSource++ );
		}
		*szpDest = '\0';
	}
#endif /* ffconfigUNICODE_UTF16_SUPPORT */
/*-----------------------------------------------------------*/

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	void FF_wcsntocstr( int8_t *szpDest, const FF_T_WCHAR *wcsSource, uint32_t ulLength )
	{
		while( ( *wcsSource != '\0' ) && ( ulLength-- != 0 ) )
		{
			*( szpDest++ ) = ( int8_t ) *( wcsSource++ );
		}
		*szpDest = '\0';
	}
#endif /* ffconfigUNICODE_UTF16_SUPPORT */
/*-----------------------------------------------------------*/

/*-----------------------------------------------------------*/

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	void FF_toupper( FF_T_WCHAR *string, uint32_t ulLength )
	{
	uint32_t i;

		for( i = 0; i < ulLength; i++ )
		{
			string[ i ] = towupper( string[ i ] );
		}
	}
	/*-----------------------------------------------------------*/

	void FF_tolower( FF_T_WCHAR *string, uint32_t ulLength )
	{
	uint32_t i;
		for( i = 0; i < ulLength; i++ )
		{
			string[ i ] = towlower( string[ i ] );
		}
	}
	/*-----------------------------------------------------------*/

#else	/* ffconfigUNICODE_UTF16_SUPPORT */
	void FF_toupper( char *string, uint32_t ulLength )
	{
	uint32_t i;

		for( i = 0; i < ulLength; i++ )
		{
			if( ( string[ i ] >= 'a' ) && ( string[ i ] <= 'z' ) )
			{
				string[ i ] -= 32;
			}
			if( string[ i ] == '\0' )
			{
				break;
			}
		}
	}
	/*-----------------------------------------------------------*/

	void FF_tolower( char *string, uint32_t ulLength )
	{
	uint32_t i;

		for( i = 0; i < ulLength; i++ )
		{
			if( ( string[ i ] >= 'A' ) && ( string[ i ] <= 'Z' ) )
			{
				string[ i ] += 32;
			}
			if( string[ i ] == '\0' )
			{
				break;
			}
		}
	}
	/*-----------------------------------------------------------*/

#endif	/* ffconfigUNICODE_UTF16_SUPPORT */


/**
 *	@private
 *	@brief	Compares 2 strings for the specified length, and returns pdTRUE is they are identical
 *			otherwise pdFALSE is returned.
 *
 **/

#if( ffconfigUNICODE_UTF16_SUPPORT == 0 )
	BaseType_t FF_strmatch( const char *str1, const char *str2, BaseType_t xLength )
	{
		register BaseType_t i;
		register char	char1, char2;

		if( xLength == 0 )
		{
			xLength = strlen( str1 );
			if( xLength != ( BaseType_t )strlen( str2 ) )
			{
				return pdFALSE;
			}
		}

		for( i = 0; i < xLength; i++ )
		{
			char1 = str1[ i ];
			char2 = str2[ i ];
			if( ( char1 >= 'A' ) && ( char1 <= 'Z' ) )
			{
				char1 += 32;
			}
			if( ( char2 >= 'A' ) && ( char2 <= 'Z' ) )
			{
				char2 += 32;
			}

			if( char1 != char2 )
			{
				return pdFALSE;
			}
		}

		return pdTRUE;
	}
#else	/* ffconfigUNICODE_UTF16_SUPPORT */
	BaseType_t FF_strmatch( const FF_T_WCHAR *str1, const FF_T_WCHAR *str2, BaseType_t xLength )
	{
	register BaseType_t i;
	register FF_T_WCHAR	char1, char2;

		if( xLength == 0 )
		{
			xLength = wcslen( str1 );
			if( xLength != wcslen( str2 ) )
			{
				return pdFALSE;
			}
		}

		for( i = 0; i < xLength; i++ )
		{
			char1 = towlower( str1[ i ] );
			char2 = towlower( str2[ i ] );
			if( char1 != char2 )
			{
				return pdFALSE;
			}
		}

		return pdTRUE;
	}
#endif	/* ffconfigUNICODE_UTF16_SUPPORT */

/**
 *	@private
 *	@brief	A re-entrant Strtok function. No documentation is provided :P
 *			Use at your own risk. (This is for FreeRTOS+FAT's use only).
 **/

#if( ffconfigUNICODE_UTF16_SUPPORT == 0 )
	char *FF_strtok( const char *string, char *token, uint16_t *tokenNumber, BaseType_t *last, BaseType_t xLength )
	{
		uint16_t i,y, tokenStart, tokenEnd = 0;

		i = 0;
		y = 0;

		if( ( string[ i ] == '\\' ) || ( string[ i ] == '/' ) )
		{
			i++;
		}

		tokenStart = i;

		while( i < xLength )
		{
			if( ( string[ i ] == '\\' ) || ( string[ i ] == '/' ) )
			{
				y++;
				if( y == *tokenNumber )
				{
					tokenStart = ( uint16_t )( i + 1 );
				}
				if( y == ( *tokenNumber + 1 ) )
				{
					tokenEnd = i;
					break;
				}
			}
			i++;
		}

		if( tokenEnd == 0 )
		{
			if( *last == pdTRUE )
			{
				return NULL;
			}
			else
			{
				*last = pdTRUE;
			}
			tokenEnd = i;
		}
		if( ( tokenEnd - tokenStart ) < ffconfigMAX_FILENAME )
		{
			memcpy( token, ( string + tokenStart ), ( uint32_t )( tokenEnd - tokenStart ) );
			token[ tokenEnd - tokenStart ] = '\0';
		}
		else
		{
			memcpy( token, ( string + tokenStart ), ( uint32_t )( ffconfigMAX_FILENAME ) );
			token[ ffconfigMAX_FILENAME - 1 ] = '\0';
		}
		/*token[tokenEnd - tokenStart] = '\0'; */
		*tokenNumber += 1;

		return token;
	}
#else	/* ffconfigUNICODE_UTF16_SUPPORT */
	FF_T_WCHAR *FF_strtok( const FF_T_WCHAR *string, FF_T_WCHAR *token, uint16_t *tokenNumber, BaseType_t *last, BaseType_t xLength )
	{
		uint16_t i,y, tokenStart, tokenEnd = 0;

		i = 0;
		y = 0;

		if( ( string[ i ] == '\\' ) || ( string[ i ] == '/' ) )
		{
			i++;
		}

		tokenStart = i;

		while( i < xLength )
		{
			if( ( string[ i ] == '\\' ) || ( string[ i ] == '/' ) )
			{
				y++;
				if( y == *tokenNumber )
				{
					tokenStart = ( uint16_t ) ( i + 1 );
				}
				if( y == ( *tokenNumber + 1 ) )
				{
					tokenEnd = i;
					break;
				}
			}
			i++;
		}

		if( tokenEnd == 0 )
		{
			if( *last == pdTRUE )
			{
				return NULL;
			}
			else
			{
				*last = pdTRUE;
			}
			tokenEnd = i;
		}
		if( ( tokenEnd - tokenStart ) < ffconfigMAX_FILENAME )
		{
			memcpy( token, ( string + tokenStart ), ( uint32_t )( tokenEnd - tokenStart ) * sizeof( FF_T_WCHAR ) );
			token[ tokenEnd - tokenStart ] = '\0';
		}
		else
		{
			memcpy( token, ( string + tokenStart ), ( uint32_t )( ffconfigMAX_FILENAME ) * sizeof( FF_T_WCHAR ) );
			token[ ffconfigMAX_FILENAME - 1 ] = '\0';
		}
		/*token[tokenEnd - tokenStart] = '\0'; */
		*tokenNumber += 1;

		return token;
	}
#endif	/* ffconfigUNICODE_UTF16_SUPPORT */

/* UTF-8 Routines */

/*
   UCS-4 range (hex.)           UTF-8 octet sequence (binary)
   0000 0000-0000 007F   0xxxxxxx
   0000 0080-0000 07FF   110xxxxx 10xxxxxx
   0000 0800-0000 FFFF   1110xxxx 10xxxxxx 10xxxxxx

   0001 0000-001F FFFF   11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
   0020 0000-03FF FFFF   111110xx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx	-- We don't encode these because we won't receive them. (Invalid UNICODE).
   0400 0000-7FFF FFFF   1111110x 10xxxxxx ... 10xxxxxx					-- We don't encode these because we won't receive them. (Invalid UNICODE).
*/

#if ( ( ffconfigUNICODE_UTF16_SUPPORT != 0 ) && ( WCHAR_MAX > 0xFFFF ) ) || ( ffconfigUNICODE_UTF8_SUPPORT != 0 )
	UBaseType_t FF_GetUtf16SequenceLen( uint16_t usLeadChar )
	{
	UBaseType_t uxReturn;
		if( ( usLeadChar & 0xFC00 ) == 0xD800 )
		{
			uxReturn = 2;
		}
		else
		{
			uxReturn = 1;
		}

		return uxReturn;
	}	/* FF_GetUtf16SequenceLen() */
#endif
/*-----------------------------------------------------------*/

/*
	Returns the number of UTF-8 units read.
	Will not exceed ulSize UTF-16 units. (ulSize * 2 bytes).
*/
/*
   UCS-4 range (hex.)           UTF-8 octet sequence (binary)
   0000 0000-0000 007F   0xxxxxxx
   0000 0080-0000 07FF   110xxxxx 10xxxxxx
   0000 0800-0000 FFFF   1110xxxx 10xxxxxx 10xxxxxx

   0001 0000-001F FFFF   11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
   0020 0000-03FF FFFF   111110xx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx	-- We don't encode these because we won't receive them. (Invalid UNICODE).
   0400 0000-7FFF FFFF   1111110x 10xxxxxx ... 10xxxxxx					-- We don't encode these because we won't receive them. (Invalid UNICODE).
*/
#if ( ffconfigUNICODE_UTF8_SUPPORT != 0 )
	int32_t FF_Utf8ctoUtf16c( uint16_t *utf16Dest, const uint8_t *utf8Source, uint32_t ulSize )
	{
	uint32_t ulUtf32char;
	uint16_t utf16Source = 0;
	register int32_t lSequenceNumber = 0;

		/* Count number of set bits before a zero. */
		while( ( ( *utf8Source != '\0' ) & ( 0x80 >> ( lSequenceNumber ) ) ) )
		{
			lSequenceNumber++;
		}

		if( lSequenceNumber == 0UL )
		{
			lSequenceNumber++;
		}

		if( ulSize == 0UL )
		{
			/* Returned value becomes an error, with the highest bit set. */
			lSequenceNumber = FF_ERR_UNICODE_DEST_TOO_SMALL | FF_UTF8CTOUTF16C;
		}
		else
		{
			switch( lSequenceNumber )
			{
			case 1:
				utf16Source = (uint16_t) *utf8Source;
				memcpy(utf16Dest,&utf16Source,sizeof(uint16_t));
				break;

			case 2:
				utf16Source =(uint16_t) ((*utf8Source & 0x1F) << 6) | ((*(utf8Source + 1) & 0x3F));
				memcpy(utf16Dest,&utf16Source,sizeof(uint16_t));
				break;

			case 3:
				utf16Source =(uint16_t) ((*utf8Source & 0x0F) << 12) | ((*(utf8Source + 1) & 0x3F) << 6) | ((*(utf8Source + 2) & 0x3F));
				memcpy(utf16Dest,&utf16Source,sizeof(uint16_t));
				break;

			case 4:
				if( ulSize < 2 )
				{
					/* Returned value becomes an error. */
					lSequenceNumber = FF_ERR_UNICODE_DEST_TOO_SMALL | FF_UTF8CTOUTF16C;
				}
				else
				{
					/* Convert to UTF-32 and then into UTF-16 */
					ulUtf32char = ( uint16_t )
						( ( *utf8Source & 0x0F ) << 18 ) |
						( ( *( utf8Source + 1 ) & 0x3F ) << 12 ) |
						( ( *( utf8Source + 2 ) & 0x3F ) << 6 ) |
						( ( *( utf8Source + 3 ) & 0x3F ) );

					utf16Source = ( uint16_t ) ( ( ( ulUtf32char - 0x10000 ) & 0xFFC00 ) >> 10 ) | 0xD800;
					memcpy( utf16Dest, &utf16Source, sizeof( uint16_t ) );
					utf16Source = ( uint16_t ) ( ( ( ulUtf32char - 0x10000 ) & 0x003FF ) >> 00 ) | 0xDC00;
					memcpy( utf16Dest + 1, &utf16Source, sizeof( uint16_t ) );
				}
				break;

			default:
				break;
			}
		}

		return lSequenceNumber;
	}	/* FF_Utf8ctoUtf16c() */
#endif	/* ffconfigUNICODE_UTF8_SUPPORT */

/*-----------------------------------------------------------*/

/*
	Returns the number of UTF-8 units required to encode the UTF-16 sequence.
	Will not exceed ulSize UTF-8 units. (ulSize  * 1 bytes).
*/
#if ( ffconfigUNICODE_UTF8_SUPPORT != 0 )
	int32_t FF_Utf16ctoUtf8c( uint8_t *utf8Dest, const uint16_t *utf16Source, uint32_t ulSize )
	{
	uint32_t ulUtf32char;
	uint16_t ulUtf16char;
	int32_t lReturn = 0L;

		do
		{
			if( ulSize == 0UL )
			{
				lReturn = FF_ERR_UNICODE_DEST_TOO_SMALL | FF_UTF16CTOUTF8C;
				break;
			}
			memcpy( &ulUtf16char, utf16Source, sizeof( uint16_t ) );

			/* A surrogate sequence was encountered. Must transform to UTF32 first. */
			if( ( ulUtf16char & 0xF800) == 0xD800 )
			{
				ulUtf32char = ( ( uint32_t ) ( ulUtf16char & 0x003FF ) << 10 ) + 0x10000;

				memcpy( &ulUtf16char, utf16Source + 1, sizeof( uint16_t ) );
				if( ( ulUtf16char & 0xFC00 ) != 0xDC00 )
				{
					/* Invalid UTF-16 sequence. */
					lReturn = FF_ERR_UNICODE_INVALID_SEQUENCE | FF_UTF16CTOUTF8C;
					break;
				}
				ulUtf32char |= ( ( uint32_t ) ( ulUtf16char & 0x003FF ) );
			}
			else
			{
				ulUtf32char = ( uint32_t ) ulUtf16char;
			}

			/* Now convert to the UTF-8 sequence. */
			/* Single byte UTF-8 sequence. */
			if( ulUtf32char < 0x00000080 )
			{
				*( utf8Dest + 0 ) = ( uint8_t )ulUtf32char;
				lReturn = 1;
				break;
			}

			/* Double byte UTF-8 sequence. */
			if( ulUtf32char < 0x00000800 )
			{
				if( ulSize < 2 )
				{
					lReturn = FF_ERR_UNICODE_DEST_TOO_SMALL | FF_UTF16CTOUTF8C;
				}
				else
				{
					*( utf8Dest + 0 ) = ( uint8_t ) ( 0xC0 | ( ( ulUtf32char >> 6 ) & 0x1F ) );
					*( utf8Dest + 1 ) = ( uint8_t ) ( 0x80 | ( ( ulUtf32char >> 0 ) & 0x3F ) );
					lReturn = 2;
				}
				break;
			}

			/* Triple byte UTF-8 sequence. */
			if( ulUtf32char < 0x00010000 )
			{
				if( ulSize < 3 )
				{
					lReturn = FF_ERR_UNICODE_DEST_TOO_SMALL | FF_UTF16CTOUTF8C;
				}
				else
				{
					*( utf8Dest + 0 ) = ( uint8_t ) ( 0xE0 | ( ( ulUtf32char >> 12 ) & 0x0F ) );
					*( utf8Dest + 1 ) = ( uint8_t ) ( 0x80 | ( ( ulUtf32char >> 6 ) & 0x3F ) );
					*( utf8Dest + 2 ) = ( uint8_t ) ( 0x80 | ( ( ulUtf32char >> 0 ) & 0x3F ) );
					lReturn = 3;
				}
				break;
			}

			/* Quadruple byte UTF-8 sequence. */
			if( ulUtf32char < 0x00200000 )
			{
				if( ulSize < 4 )
				{
					lReturn = FF_ERR_UNICODE_DEST_TOO_SMALL | FF_UTF16CTOUTF8C;
				}
				else
				{
					*( utf8Dest + 0 ) = ( uint8_t ) (0xF0 | ( ( ulUtf32char >> 18 ) & 0x07 ) );
					*( utf8Dest + 1 ) = ( uint8_t ) (0x80 | ( ( ulUtf32char >> 12 ) & 0x3F ) );
					*( utf8Dest + 2 ) = ( uint8_t ) (0x80 | ( ( ulUtf32char >> 6 ) & 0x3F ) );
					*( utf8Dest + 3 ) = ( uint8_t ) (0x80 | ( ( ulUtf32char >> 0 ) & 0x3F ) );
					lReturn = 4;
				}
				break;
			}
			lReturn = FF_ERR_UNICODE_INVALID_CODE | FF_UTF16CTOUTF8C;	/* Invalid Character */
		}
		while( pdFALSE );

		return lReturn;
	}	/* FF_Utf16ctoUtf8c() */
#endif	/* ffconfigUNICODE_UTF8_SUPPORT */
/*-----------------------------------------------------------*/

/* UTF-16 Support Functions */

/* Converts a UTF-32 Character into its equivalent UTF-16 sequence. */
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 ) && ( WCHAR_MAX > 0xFFFF )
	int32_t FF_Utf32ctoUtf16c( uint16_t *utf16Dest, uint32_t utf32char, uint32_t ulSize )
	{
	int32_t lReturn;
		/* Check that its a valid UTF-32 wide-char!	*/

		/* This range is not a valid Unicode code point. */
		if( ( utf32char >= 0xD800 ) && ( utf32char <= 0xDFFF ) )
		{
			lReturn = FF_ERR_UNICODE_INVALID_CODE | FF_UTF32CTOUTF16C; /* Invalid character. */
		}
		else if( utf32char < 0x10000 )
		{
			*utf16Dest = (uint16_t) utf32char; /* Simple conversion! Char comes within UTF-16 space (without surrogates). */
			lReturn = 1;
		}
		else if( ulSize < 2 )
		{
			lReturn FF_ERR_UNICODE_DEST_TOO_SMALL | FF_UTF32CTOUTF16C;	/* Not enough UTF-16 units to record this character. */
		}
		else if( utf32char < 0x00200000 )
		{
			/* Conversion to a UTF-16 Surrogate pair! */
			/*valueImage = utf32char - 0x10000; */
			*( utf16Dest + 0 ) = ( uint16_t ) ( ( ( utf32char - 0x10000 ) & 0xFFC00 ) >> 10 ) | 0xD800;
			*( utf16Dest + 1 ) = ( uint16_t ) ( ( ( utf32char - 0x10000 ) & 0x003FF ) >> 00 ) | 0xDC00;

			lReturn = 2;	/* Surrogate pair encoded value. */
		}
		else
		{
			/* Invalid Character */
			lReturn = FF_ERR_UNICODE_INVALID_CODE | FF_UTF32CTOUTF16C;
		}

		return lReturn;
	}	/* FF_Utf32ctoUtf16c() */
#endif /* #if( ffconfigUNICODE_UTF16_SUPPORT != 0 ) && ( WCHAR_MAX > 0xFFFF ) */
/*-----------------------------------------------------------*/

/* Converts a UTF-16 sequence into its equivalent UTF-32 code point. */
#if( ffconfigNOT_USED_FOR_NOW != 0 )
	int32_t FF_Utf16ctoUtf32c( uint32_t *utf32Dest, const uint16_t *utf16Source )
	{
	int32_t lReturn;

		/*Not a surrogate sequence. */
		if( ( *utf16Source & 0xFC00 ) != 0xD800 )
		{
			*utf32Dest = ( uint32_t )*utf16Source;
			lReturn = 1;	/* A single UTF-16 item was used to represent the character. */
		}
		else
		{
			*utf32Dest = ( ( uint32_t) ( * ( utf16Source + 0 ) & 0x003FF ) << 10 ) + 0x10000;
			if( ( *(utf16Source + 1) & 0xFC00 ) != 0xDC00 )
			{
				lReturn = FF_ERR_UNICODE_INVALID_SEQUENCE | FF_UTF16CTOUTF32C;	/* Invalid UTF-16 sequence. */
			}
			else
			{
				*utf32Dest |= ( ( uint32_t ) ( *( utf16Source + 1 ) & 0x003FF ) );
				lReturn = 2;	/* 2 utf-16 units make up the Unicode code-point. */
			}
		}

		return lReturn;
	}	/* FF_Utf16ctoUtf32c() */
#endif /* ffconfigNOT_USED_FOR_NOW */
/*-----------------------------------------------------------*/

/*
	Returns the total number of UTF-16 items required to represent
	the provided UTF-32 string in UTF-16 form.
*/
/*
UBaseType_t FF_Utf32GetUtf16Len( const uint32_t *utf32String )
{
	UBaseType_t utf16len = 0;

	while( *utf32String )
	{
		if( *utf32String++ <= 0xFFFF )
		{
			utf16len++;
		}
		else
		{
			utf16len += 2;
		}
	}

	return utf16len;
}
*/
/*-----------------------------------------------------------*/


/* String conversions */

#if( ffconfigNOT_USED_FOR_NOW != 0 )
	int32_t FF_Utf32stoUtf8s( uint8_t *Utf8String, uint32_t *Utf32String )
	{
		int i = 0,y = 0;

		uint16_t utf16buffer[ 2 ];

		while( Utf32String[ i ] != '\0' )
		{
			/* Convert to a UTF16 char. */
			FF_Utf32ctoUtf16c( utf16buffer, Utf32String[ i ], 2 );
			/* Now convert the UTF16 to UTF8 sequence. */
			y += FF_Utf16ctoUtf8c( &Utf8String[ y ], utf16buffer, 4 );
			i++;
		}

		Utf8String[ y ] = '\0';

		return 0;
	}	/* FF_Utf32stoUtf8s() */
#endif /* ffconfigNOT_USED_FOR_NOW */
/*-----------------------------------------------------------*/
