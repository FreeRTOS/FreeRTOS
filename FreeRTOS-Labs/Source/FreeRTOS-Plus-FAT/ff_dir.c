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
 *	@file		ff_dir.c
 *	@ingroup	DIR
 *
 *	@defgroup	DIR Handles Directory Traversal
 *	@brief		Handles DIR access and traversal.
 *
 *	Provides FindFirst() and FindNext() Interfaces
 **/

#include "ff_headers.h"

#include <stdio.h>

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
#include <wchar.h>
#endif

#if defined( WIN32 )
	#define wcsicmp _wcsicmp
#else
	#define wcsicmp wcscasecmp
	#include <ctype.h>
#endif

/* Calculate a simple LFN checmsum. */
static uint8_t FF_CreateChkSum( const uint8_t *pa_pShortName );

static BaseType_t FF_ShortNameExists( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster, char *pcShortName, FF_Error_t *pxError );

#if( ffconfigSHORTNAME_CASE != 0 )
	/* For short-name entries, NT/XP etc store case information in byte 0x0c
	 * Use this to show proper case of "README.txt" or "source.H".
	 */
	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
		static void FF_CaseShortName( FF_T_WCHAR *pcName, uint8_t attrib );
	#else
		static void FF_CaseShortName( char *pcName, uint8_t attrib );
	#endif
#endif /* ffconfigSHORTNAME_CASE */

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )

	/* For unicode, the short name can be expanded to wchar
	 * by inserting zero's.
	 */
	static void FF_ShortNameExpand( FF_T_WCHAR * );

#endif

/*
 * Transform a name as stored on disk "README__TXT"
 * to a nul-terminated string: "README.TXT", "FILE001".
 * A dot is only added if an extension is present.
 */
static void FF_ProcessShortName( char *pcName );

#if( ffconfigTIME_SUPPORT != 0 )
	static void FF_PlaceTime( uint8_t *pucEntryBuffer, uint32_t Offset, FF_SystemTime_t *pxTime );
	static void FF_PlaceDate( uint8_t *pucEntryBuffer, uint32_t Offset, FF_SystemTime_t *pxTime );
	static void FF_GetTime( FF_SystemTime_t *pxTime, const uint8_t *pucEntryBuffer, uint32_t ulOffset );
	static void FF_GetDate( FF_SystemTime_t *pxTime, const uint8_t *pucEntryBuffer, uint32_t ulOffset );
#endif /* ffconfigTIME_SUPPORT */
static FF_Error_t FF_Traverse( FF_IOManager_t *pxIOManager, uint32_t ulEntry, FF_FetchContext_t *pxContext );
static int32_t FF_FindFreeDirent( FF_IOManager_t *pxIOManager, FF_FindParams_t *pxFindParams, uint16_t usSequential );

#if( ffconfigLFN_SUPPORT != 0 )
	static int8_t FF_CreateLFNEntry( uint8_t *pucEntryBuffer, uint8_t *pcName, UBaseType_t uxNameLength, UBaseType_t uxLFN, uint8_t ucCheckSum );
#endif /* ffconfigLFN_SUPPORT */

static BaseType_t FF_ValidShortChar( char cChar );

#if( ffconfigLFN_SUPPORT != 0 )
	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
		static FF_Error_t FF_CreateLFNs( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster, FF_T_WCHAR *pcName, uint8_t ucCheckSum, uint16_t usEntry );
	#else
		static FF_Error_t FF_CreateLFNs( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster, char *pcName, uint8_t ucCheckSum, uint16_t usEntry );
	#endif
#endif

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	static void FF_MakeNameCompliant( FF_T_WCHAR *pcName );
#else
	static void FF_MakeNameCompliant( char *pcName );
#endif

#if ( FF_NOSTRCASECMP == 0 )
	static portINLINE unsigned char prvToLower( unsigned char c )
	{
	unsigned char cReturnChar;
		if( c >= 'A' && c <= 'Z' )
		{
			cReturnChar = c + 0x20;
		}
		else
		{
			cReturnChar = c;
		}

		return cReturnChar;
	}

	int strcasecmp( const char *pcString1, const char *pcString2 )
	{
		unsigned char c1,c2;
		do
		{
			c1 = *pcString1++;
			c2 = *pcString2++;
			c1 = ( unsigned char ) prvToLower( ( unsigned char ) c1 );
			c2 = ( unsigned char ) prvToLower( ( unsigned char ) c2 );
		}
		while( ( c1 == c2 ) && ( c1 != '\0' ) );

		return ( int ) c1 - c2;
	}	/* strcasecmp() */
#endif
/*-----------------------------------------------------------*/

static uint8_t FF_CreateChkSum( const uint8_t *pa_pShortName )
{
uint8_t	cNameLen;
uint8_t	ChkSum = 0;

	for( cNameLen = 11; cNameLen != 0; cNameLen-- )
	{
		ChkSum = ( uint8_t )
			( ( ( ChkSum & 1 ) ? 0x80 : 0 ) + ( ChkSum >> 1 ) + *( pa_pShortName++ ) );
	}

	return ChkSum;
}	/* FF_CreateChkSum() */
/*-----------------------------------------------------------*/

/* _HT_ Does not need a wchar version because a short name is treated  a normal string of bytes */
static BaseType_t FF_ShortNameExists( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster, char *pcShortName, FF_Error_t *pxError )
{
BaseType_t xIndex;
const uint8_t *pucEntryBuffer = NULL; /* initialisation not necessary, just for the compiler */
uint8_t ucAttrib;
FF_FetchContext_t xFetchContext;
char pcMyShortName[ FF_SIZEOF_DIRECTORY_ENTRY ];
BaseType_t xResult = -1;

#if( ffconfigHASH_CACHE != 0 )
	uint32_t ulHash;
#endif

	*pxError = FF_ERR_NONE;

	#if( ffconfigHASH_CACHE != 0 )
	{
		if( !FF_DirHashed( pxIOManager, ulDirCluster ) )
		{
			/* Hash the directory. */
			FF_HashDir( pxIOManager, ulDirCluster );
		}

		#if ffconfigHASH_FUNCTION == CRC16
		{
			ulHash = ( uint32_t ) FF_GetCRC16( ( uint8_t * ) pcShortName, strlen( pcShortName ) );
		}
		#else /* ffconfigHASH_FUNCTION == CRC8 */
		{
			ulHash = ( uint32_t ) FF_GetCRC8( ( uint8_t * ) pcShortName, strlen( pcShortName ) );
		}
		#endif
		{
			/* FF_CheckDirentHash result: 0 not found, 1 found, -1 directory not hashed */
			xResult = FF_CheckDirentHash( pxIOManager, ulDirCluster, ulHash );
		}
	}
	#endif

	if( xResult < 0 )
	{
		xResult = pdFALSE;
		*pxError = FF_InitEntryFetch( pxIOManager, ulDirCluster, &xFetchContext );

		if( FF_isERR( *pxError ) == pdFALSE )
		{
			for( xIndex = 0; xIndex < FF_MAX_ENTRIES_PER_DIRECTORY; xIndex++ )
			{
				/* Call FF_FetchEntryWithContext only once for every 512-byte block */
				if( ( xIndex == 0 ) ||
					( pucEntryBuffer >= xFetchContext.pxBuffer->pucBuffer + ( FF_SIZEOF_SECTOR - FF_SIZEOF_DIRECTORY_ENTRY ) ) )
				{
					*pxError = FF_FetchEntryWithContext( pxIOManager, ( uint32_t ) xIndex, &xFetchContext, NULL );
					if( FF_isERR( *pxError ) )
					{
						break;
					}
					pucEntryBuffer = xFetchContext.pxBuffer->pucBuffer;
				}
				else
				{
					/* Advance 32 bytes to get the next directory entry. */
					pucEntryBuffer += FF_SIZEOF_DIRECTORY_ENTRY;
				}

				if( FF_isEndOfDir( pucEntryBuffer ) )
				{
					break;
				}
				if( FF_isDeleted( pucEntryBuffer ) == pdFALSE )
				{
					ucAttrib = FF_getChar( pucEntryBuffer, FF_FAT_DIRENT_ATTRIB );
					if( ( ucAttrib & FF_FAT_ATTR_LFN ) != FF_FAT_ATTR_LFN )
					{
						memcpy( pcMyShortName, pucEntryBuffer, sizeof( pcMyShortName ) );
						FF_ProcessShortName( pcMyShortName );
						if( strcmp( ( const char * )pcShortName, ( const char * )pcMyShortName ) == 0 )
						{
							xResult = pdTRUE;
							break;
						}
					}
				}
			} /* for ( xIndex = 0; xIndex < FF_MAX_ENTRIES_PER_DIRECTORY; xIndex++ ) */
		}
		*pxError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
	}

    return xResult;
}	/* FF_ShortNameExists() */
/*-----------------------------------------------------------*/

/* _HT_ When adding many files to a single directory, FF_FindEntryInDir was sometimes */
/* _HT_ called 3 times before inserting a single file. With these changes it is called one time only */
/* _HT_ pxFindParams caches some information: */
/* _HT_ 1: the first free entry 2: whether the short-name version already exists */
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
uint32_t FF_FindEntryInDir( FF_IOManager_t *pxIOManager, FF_FindParams_t *pxFindParams, const FF_T_WCHAR *pcName, uint8_t pa_Attrib, FF_DirEnt_t *pxDirEntry, FF_Error_t *pxError )
#else
uint32_t FF_FindEntryInDir( FF_IOManager_t *pxIOManager, FF_FindParams_t *pxFindParams, const char *pcName, uint8_t pa_Attrib, FF_DirEnt_t *pxDirEntry, FF_Error_t *pxError )
#endif
{
FF_FetchContext_t xFetchContext;
/* const pointer to read from pBuffer */
const uint8_t *src = NULL;
/* As we're walking through a directory, we might as well
find the first free entry to help FF_FindFreeDirent( )
The result will be stored in 'pxFindParams->lFreeEntry' */
BaseType_t	entriesNeeded;
BaseType_t	freeCount = 0;
FF_Error_t xError;
/* If the file name fits into a short file name
then the existence of that short file name will be checked as well. */
BaseType_t	testShortname;
uint32_t xResult = 0ul;
#if( ffconfigUNICODE_UTF8_SUPPORT == 1 )
	int32_t	utf8Error;
#endif

#if( ffconfigLFN_SUPPORT != 0 )
	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
		FF_T_WCHAR	*pcCurPtr;		/* Pointer to store a LFN. */
		FF_T_WCHAR	*pcLastPtr = pxDirEntry->pcFileName + sizeof( pxDirEntry->pcFileName );
	#else
		char	*pcCurPtr;		/* Pointer to store a LFN. */
		char	*pcLastPtr = pxDirEntry->pcFileName + sizeof( pxDirEntry->pcFileName );
	#endif /* ffconfigUNICODE_UTF16_SUPPORT */

	uint16_t lfnItem = 0;
	uint8_t ucCheckSum = 0;
	BaseType_t xLFNCount = 0;
	BaseType_t xLFNTotal = 0;
	uint8_t lastAttrib;

	BaseType_t xIndex;
#endif /* ffconfigLFN_SUPPORT */

	#if( ffconfigLFN_SUPPORT != 0 )
	{
		#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
			BaseType_t	NameLen = ( BaseType_t ) wcslen( ( const char * )pcName );
		#else
			BaseType_t	NameLen = ( BaseType_t ) strlen( ( const char * )pcName );
		#endif
		/* Find enough places for the LFNs and the ShortName. */
		entriesNeeded = ( uint8_t )( ( NameLen + 12 ) / 13 ) + 1;
	}
	#else
	{
		entriesNeeded = 1;
	}
	#endif /* ffconfigLFN_SUPPORT */

	if( ( pxFindParams->ulFlags & FIND_FLAG_FITS_SHORT_OK ) == FIND_FLAG_FITS_SHORT_OK )
	{
		testShortname = pdTRUE;
	}
	else
	{
		testShortname = pdFALSE;
	}

	pxDirEntry->ucAttrib = 0;

	if( ( pxFindParams->ulFlags & FIND_FLAG_CREATE_FLAG ) != 0 )
	{
		/* A file is to be created: keep track of the first free entry big enough
		to hold this file name. */
		pxFindParams->lFreeEntry = -1;
	}
	else
	{
		pxFindParams->lFreeEntry = 0;
	}

	xError = FF_InitEntryFetch( pxIOManager, pxFindParams->ulDirCluster, &xFetchContext );

	if( FF_isERR( xError ) == pdFALSE )
	{
		for( pxDirEntry->usCurrentItem = 0; pxDirEntry->usCurrentItem < FF_MAX_ENTRIES_PER_DIRECTORY; pxDirEntry->usCurrentItem++ )
		{
			if( ( src == NULL ) ||
				( src >= xFetchContext.pxBuffer->pucBuffer + ( FF_SIZEOF_SECTOR - FF_SIZEOF_DIRECTORY_ENTRY ) ) )
			{
				xError = FF_FetchEntryWithContext( pxIOManager, pxDirEntry->usCurrentItem, &xFetchContext, NULL );

				if( FF_isERR( xError ) != pdFALSE )
				{
					break;
				}
				src = xFetchContext.pxBuffer->pucBuffer;
			}
			else
			{
				/* Advance 32 bytes. */
				src += FF_SIZEOF_DIRECTORY_ENTRY;
			}

			if( FF_isEndOfDir( src ) )
			{
				/* 0x00 end-of-dir. */
				break;
			}

			if( FF_isDeleted( src ) )
			{
				/* Entry not used or deleted. */
				pxDirEntry->ucAttrib = 0;
				if( ( pxFindParams->lFreeEntry < 0 ) && ( ++freeCount == entriesNeeded ) )
				{
					/* Remember the beginning entry in the sequential sequence. */
					pxFindParams->lFreeEntry = ( pxDirEntry->usCurrentItem - ( entriesNeeded - 1 ) );
				}
				continue;
			}

			/* The current entry is in use, so reset the free-entry-counter */
			freeCount = 0;
			#if( ffconfigLFN_SUPPORT != 0 )
			{
				lastAttrib = pxDirEntry->ucAttrib;
			}
			#endif

			pxDirEntry->ucAttrib = FF_getChar( src, FF_FAT_DIRENT_ATTRIB );

			if( ( pxDirEntry->ucAttrib & FF_FAT_ATTR_LFN ) == FF_FAT_ATTR_LFN )
			{
				/* LFN Processing. */
				#if( ffconfigLFN_SUPPORT != 0 )
				{
					if( ( xLFNCount == 0 ) || ( lastAttrib & FF_FAT_ATTR_LFN ) != FF_FAT_ATTR_LFN )
					{
						xLFNTotal = xLFNCount = ( BaseType_t )( src[ 0 ] & ~0x40 );
						lfnItem = pxDirEntry->usCurrentItem;
						ucCheckSum = FF_getChar( src, FF_FAT_LFN_CHECKSUM );
						pcLastPtr[ -1 ] = '\0';
					}

					if( xLFNCount != 0 )
					{
						xLFNCount--;
						pcCurPtr = pxDirEntry->pcFileName + ( xLFNCount * 13 );

						/*
							This section needs to extract the name and do the comparison
							dependent on UNICODE settings in the FreeRTOSFATConfig.h file.
						*/
						#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
						{
							/* Add UTF-16 Routine here. */
							/* Copy first 5 UTF-16 chars ( 10 bytes ). */
							memcpy( pcCurPtr, &src[ FF_FAT_LFN_NAME_1 ], 10 );
							/* Increment Filename pointer 5 utf16 chars. */
							pcCurPtr += 5;

							/* Copy next 6 chars ( 12 bytes ). */
							memcpy( pcCurPtr, &src[ FF_FAT_LFN_NAME_2 ], 12 );
							pcCurPtr += 6;

							/* You're getting the idea by now! */
							memcpy( pcCurPtr, &src[ FF_FAT_LFN_NAME_3 ], 4 );
							pcCurPtr += 2;
						}	/* ffconfigUNICODE_UTF16_SUPPORT */
						#elif( ffconfigUNICODE_UTF8_SUPPORT != 0 )
						{
							/* UTF-8 Routine here. */
							for( xIndex = 0; ( xIndex < 5 ) && ( pcCurPtr < pcLastPtr ); xIndex++ )
							{
								/* Was there a surrogate sequence? -- Add handling here. */
								utf8Error = FF_Utf16ctoUtf8c( ( uint8_t * ) pcCurPtr, ( uint16_t * ) &src[ FF_FAT_LFN_NAME_1 + ( 2 * xIndex ) ], pcLastPtr - pcCurPtr );
								if( utf8Error > 0 )
								{
									pcCurPtr += utf8Error;
								}
								else
								{
									if( FF_GETERROR( utf8Error ) == FF_ERR_UNICODE_INVALID_SEQUENCE )
									{
										/* Handle potential surrogate sequence across entries. */
									}
								}
							}

							for( xIndex = 0; xIndex < 6 && pcCurPtr < pcLastPtr; xIndex++ )
							{
								/* Was there a surrogate sequence? -- To add handling here. */
								utf8Error = FF_Utf16ctoUtf8c( ( uint8_t * ) pcCurPtr, ( uint16_t * ) &src[ FF_FAT_LFN_NAME_2 + ( 2 * xIndex ) ], pcLastPtr - pcCurPtr );
								if( utf8Error > 0 )
								{
									pcCurPtr += utf8Error;
								}
								else
								{
									if( FF_GETERROR( utf8Error ) == FF_ERR_UNICODE_INVALID_SEQUENCE )
									{
										/* Handle potential surrogate sequence across entries. */
									}
								}
							}

							for( xIndex = 0; xIndex < 2 && pcCurPtr < pcLastPtr; xIndex++ )
							{
								/* Was there a surrogate sequence? -- To add handling here. */
								utf8Error = FF_Utf16ctoUtf8c( ( uint8_t * ) pcCurPtr, ( uint16_t * ) &src[ FF_FAT_LFN_NAME_3 + ( 2 * xIndex ) ], pcLastPtr - pcCurPtr );
								if( utf8Error > 0 )
								{
									pcCurPtr += utf8Error;
								}
								else
								{
									if( FF_GETERROR( utf8Error ) == FF_ERR_UNICODE_INVALID_SEQUENCE )
									{
										/* Handle potential surrogate sequence across entries. */
									}
								}
							}
						}	/* ffconfigUNICODE_UTF8_SUPPORT */
						#else
						{	/* use ASCII notation. */
							for( xIndex = 0; ( xIndex < 10 ) && ( pcCurPtr < pcLastPtr ); xIndex += 2 )
							{
								*( pcCurPtr++ ) = src[ FF_FAT_LFN_NAME_1 + xIndex ];
							}
							for( xIndex = 0; ( xIndex < 12 )  && ( pcCurPtr < pcLastPtr ); xIndex += 2 )
							{
								*( pcCurPtr++ ) = src[ FF_FAT_LFN_NAME_2 + xIndex ];
							}

							for( xIndex = 0; ( xIndex < 4 ) && ( pcCurPtr < pcLastPtr ); xIndex += 2 )
							{
								*( pcCurPtr++ ) = src[ FF_FAT_LFN_NAME_3 + xIndex ];
							}
						}
						#endif /* ( ffconfigUNICODE_UTF16_SUPPORT == 0 ) && !( ffconfigUNICODE_UTF8_SUPPORT == 0 ) */
						if( ( xLFNCount == xLFNTotal - 1 ) && ( pcCurPtr < pcLastPtr ) )
						{
							*pcCurPtr = '\0';	/* Important when name len is multiple of 13. */
						}
					} /* if( xLFNCount ) */
				}
				#endif /* ffconfigLFN_SUPPORT */
				continue;
			}

			if( ( pxDirEntry->ucAttrib & FF_FAT_ATTR_VOLID ) == FF_FAT_ATTR_VOLID )
			{
				#if( ffconfigLFN_SUPPORT != 0 )
				{
					xLFNTotal = 0;
				}
				#endif /* ffconfigLFN_SUPPORT */
				continue;
			}

		#if( ffconfigLFN_SUPPORT != 0 )
			if( ( xLFNTotal == 0 ) || ( ucCheckSum != FF_CreateChkSum( src ) ) )
		#endif /* ffconfigLFN_SUPPORT */
			{
				/* This entry has only a short name, or the checksum isn't correct
				 * Use the short name for comparison */
				memcpy( pxDirEntry->pcFileName, src, 11 );
				FF_ProcessShortName( ( char * ) pxDirEntry->pcFileName );
				#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
				{
					/* FileName now contains a 8-bit short name
					Expand it to a FF_T_WCHAR string. */
					FF_ShortNameExpand( pxDirEntry->pcFileName );
				}
				#endif /* ffconfigUNICODE_UTF16_SUPPORT */
				#if( ffconfigLFN_SUPPORT != 0)
				{
					xLFNTotal = 0;
				}
				#endif /* ffconfigLFN_SUPPORT */
			}

			/* This function FF_FindEntryInDir( ) is either called with
			 * pa_Attrib==0 or with pa_Attrib==FF_FAT_ATTR_DIR
			 * In the last case the caller is looking for a directory */
			if( ( pxDirEntry->ucAttrib & pa_Attrib ) == pa_Attrib )
			{
				if( testShortname )
				{
					/* Both strings are stored in the directory format
					 * e.g. "README  TXT", without a dot */
					if( memcmp( src, pxFindParams->pcEntryBuffer, 11 ) == 0 )
					{
						pxFindParams->ulFlags |= FIND_FLAG_SHORTNAME_CHECKED | FIND_FLAG_SHORTNAME_FOUND;
					}
				}

			#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
				if( wcsicmp( ( const char * )pcName, ( const char * )pxDirEntry->pcFileName ) == 0 )
			#else
				if( FF_stricmp( ( const char * )pcName, ( const char * )pxDirEntry->pcFileName ) == 0 )
			#endif /* ffconfigUNICODE_UTF16_SUPPORT */
				{
					/* Finally get the complete information. */
				#if( ffconfigLFN_SUPPORT != 0 )
					if( xLFNTotal )
					{
						xError = FF_PopulateLongDirent( pxIOManager, pxDirEntry, ( uint16_t ) lfnItem, &xFetchContext );
						if( FF_isERR( xError ) )
						{
							break;
						}
					}
					else
				#endif /* ffconfigLFN_SUPPORT */
					{
						FF_PopulateShortDirent( pxIOManager, pxDirEntry, src );
						/* HT: usCurrentItem wasn't increased here. */
						pxDirEntry->usCurrentItem++;
					}
					/* Object found, the cluster number will be returned. */
					xResult = pxDirEntry->ulObjectCluster;
					break;
				}
			}
			#if( ffconfigLFN_SUPPORT != 0 )
			{
				xLFNTotal = 0;
			}
			#endif
		}	/* for( ; pxDirEntry->usCurrentItem < FF_MAX_ENTRIES_PER_DIRECTORY; pxDirEntry->usCurrentItem++ ) */

		{
		FF_Error_t xTempError;
			xTempError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = xTempError;
			}
		}
	} /* if( FF_isERR( xError ) == pdFALSE ) */

	if( FF_isERR( xError ) == pdFALSE )
	{
		/* If a free entry wasn't found yet, put it to the current (last) item */
		if( pxFindParams->lFreeEntry < 0 )
		{
			pxFindParams->lFreeEntry = pxDirEntry->usCurrentItem;
		}

		/* If we were checking the existence of the short-name
		set the Checked flag now */
		if( testShortname )
		{
			pxFindParams->ulFlags |= FIND_FLAG_SHORTNAME_CHECKED;
		}
	}

	if( pxError != NULL )
	{
		*pxError = xError;
	}

	return xResult;
}	/* FF_FindEntryInDir() */
/*-----------------------------------------------------------*/


/**
 *	@private
 **/
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
uint32_t FF_FindDir( FF_IOManager_t *pxIOManager, const FF_T_WCHAR *pcPath, uint16_t pathLen, FF_Error_t *pxError )
#else
uint32_t FF_FindDir( FF_IOManager_t *pxIOManager, const char *pcPath, uint16_t pathLen, FF_Error_t *pxError )
#endif
{
uint16_t it = 0;         /* Re-entrancy Variables for FF_strtok( ). */
BaseType_t last = pdFALSE;
FF_DirEnt_t xMyDirectory;
FF_FindParams_t  xFindParams;
FF_Error_t xError;
BaseType_t xFound;

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	FF_T_WCHAR mytoken[ ffconfigMAX_FILENAME ];
	FF_T_WCHAR *token;
#else
	char mytoken[ ffconfigMAX_FILENAME ];
	char *pcToken;
#endif

#if( ffconfigPATH_CACHE != 0 )
	BaseType_t xIndex;
#endif

	memset( &xFindParams, '\0', sizeof( xFindParams ) );
	xFindParams.ulDirCluster = pxIOManager->xPartition.ulRootDirCluster;

	xError = FF_ERR_NONE;

    if( pathLen <= 1 )
	{
		/* Must be the root directory.
		'xFindParams.ulDirCluster' will be returned containing 'pxIOManager->xPartition.ulRootDirCluster'. */
		xFound = pdTRUE;
    }
	else
	{
		/* Only the root directory '/' shall have a trailing slash in its name. */
		if( ( pcPath[ pathLen - 1 ] == '\\' ) || ( pcPath[ pathLen - 1 ] == '/' ) )
		{
			pathLen--;
		}
		xFound = pdFALSE;

		#if( ffconfigPATH_CACHE != 0 )	/* Is the requested pcPath in the PATH CACHE? */
		{
			FF_PendSemaphore( pxIOManager->pvSemaphore );	/* Thread safety on shared object! */
			{
				for( xIndex = 0; xIndex < ffconfigPATH_CACHE_DEPTH; xIndex++ )
				{
				#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
					if( wcslen( pxIOManager->xPartition.pxPathCache[ xIndex ].pcPath ) == ( size_t )pathLen )
				#else
					if( strlen( pxIOManager->xPartition.pxPathCache[ xIndex ].pcPath ) == ( size_t )pathLen )
				#endif
					{
						if( FF_strmatch( pxIOManager->xPartition.pxPathCache[ xIndex ].pcPath, pcPath, pathLen ) )
						{
							xFindParams.ulDirCluster = pxIOManager->xPartition.pxPathCache[ xIndex ].ulDirCluster;
							xFound = pdTRUE;
							break;
						}
					}
				}
			}
			FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
		}
		#endif /* ffconfigPATH_CACHE */
	}
	if( xFound == pdFALSE )
	{
		pcToken = FF_strtok( pcPath, mytoken, &it, &last, pathLen );

		do
		{
			xMyDirectory.usCurrentItem = 0;
			xFindParams.ulDirCluster = FF_FindEntryInDir( pxIOManager, &xFindParams, pcToken, ( uint8_t ) FF_FAT_ATTR_DIR, &xMyDirectory, &xError );

			if( xFindParams.ulDirCluster == 0ul )
			{
				break;
			}

			pcToken = FF_strtok( pcPath, mytoken, &it, &last, pathLen );

		} while( pcToken != NULL );
		if( ( pcToken != NULL ) &&
			( ( FF_isERR( xError ) == pdFALSE ) || ( FF_GETERROR( xError ) == FF_ERR_DIR_END_OF_DIR ) ) )
		{
			xError = ( FF_Error_t ) ( FF_FINDDIR | FF_ERR_FILE_INVALID_PATH );
		}
		#if( ffconfigPATH_CACHE != 0 )	/* Update the PATH CACHE with a new PATH. */
		{
			/* Only cache if the dir was actually found! */
			if( ( FF_isERR( xError ) == pdFALSE ) && ( xFindParams.ulDirCluster != 0ul ) )
			{
				FF_PendSemaphore( pxIOManager->pvSemaphore );
				{
					if( pathLen < ffconfigMAX_FILENAME )	/* Ensure the PATH won't cause a buffer overrun. */
					{
						#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
						{
							memcpy( pxIOManager->xPartition.pxPathCache[ pxIOManager->xPartition.ulPCIndex ].pcPath, pcPath, pathLen * sizeof( FF_T_WCHAR ) );
						}
						#else
						{
							memcpy( pxIOManager->xPartition.pxPathCache[ pxIOManager->xPartition.ulPCIndex ].pcPath, pcPath, pathLen );
						}
						#endif

						pxIOManager->xPartition.pxPathCache[ pxIOManager->xPartition.ulPCIndex ].pcPath[ pathLen ] = '\0';
						pxIOManager->xPartition.pxPathCache[ pxIOManager->xPartition.ulPCIndex ].ulDirCluster = xFindParams.ulDirCluster;

						pxIOManager->xPartition.ulPCIndex += 1;
						if( pxIOManager->xPartition.ulPCIndex >= ffconfigPATH_CACHE_DEPTH )
						{
							pxIOManager->xPartition.ulPCIndex = 0;
						}
					}
				}
				FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
			}
		}
		#endif /* ffconfigPATH_CACHE */
	} /* if( pathLen > 1 ) */

	if( pxError != NULL )
	{
		*pxError = xError;
	}

    return xFindParams.ulDirCluster;
}	/* FF_FindDir() */
/*-----------------------------------------------------------*/


#if( ffconfigSHORTNAME_CASE != 0 )
	/**
	 *	@private
	 *  For short-name entries, NT/XP etc store case information in byte 0x0c
	 *  Use this to show proper case of "README.txt" or "source.H"
	 **/
	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	static void FF_CaseShortName( FF_T_WCHAR *pcName, uint8_t attrib )
	#else
	static void FF_CaseShortName( char *pcName, uint8_t attrib )
	#endif
	{
	uint8_t testAttrib = FF_FAT_CASE_ATTR_BASE;

		for ( ; *pcName != '\0'; pcName++ )
		{
			if( *pcName == '.' )
			{
				testAttrib = FF_FAT_CASE_ATTR_EXT;
			}
			else if ( ( attrib & testAttrib ) != 0 )
			{
				if( ( *pcName >= 'A' ) && ( *pcName <= 'Z' ) )
				{
					*pcName += 0x20;
				}
			}
			else if( ( *pcName >= 'a' ) && ( *pcName <= 'z' ) )
			{
				*pcName -= 0x20;
			}
		}
	}
#endif /* ffconfigSHORTNAME_CASE */
/*-----------------------------------------------------------*/

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	/**
	 *	@private
	 *	Expand a short-name, adding a zero after each character
	 **/

	static void FF_ShortNameExpand( FF_T_WCHAR *pFileName )
	{
		int8_t *pSource = ( ( int8_t * ) pFileName ) + 13;
		int8_t *pTarget = ( ( int8_t * ) pFileName ) + 26;
		/* "aaaaaaaa.eee": 12 characters plus a zero makes 13
		 * Copy from the right to the left */
		while( pTarget > ( int8_t * ) pFileName )
		{
			pTarget[ -1 ] = 0;
			pTarget[ -2 ] = *( --pSource );
			pTarget -= 2;
		}
	}
#endif /* ffconfigUNICODE_UTF16_SUPPORT */
/*-----------------------------------------------------------*/

/**
 *	@private
 **/

static void FF_ProcessShortName( char *pcName )
{
	char	pcShortName[ 13 ];
	char	*pcTarget = pcName;
	int		iSource;
	memcpy( pcShortName, pcName, 11 );

	for( iSource = 0; iSource < 11; iSource++ )
	{
		if( pcShortName[ iSource ] == 0x20 )
		{
			if( iSource >= 8 )
			{
				break;
			}
			iSource = 7;
		}
		else
		{
			if( iSource == 8 )
			{
				*( pcTarget++ ) = '.';
			}
			*( pcTarget++ ) = pcShortName[ iSource ];
		}
	}
	*pcTarget = '\0';
}
/*-----------------------------------------------------------*/


#if( ffconfigTIME_SUPPORT != 0 )
	static void FF_PlaceTime( uint8_t *pucEntryBuffer, uint32_t Offset, FF_SystemTime_t *pxTime )
	{
		uint16_t myShort;

		/* HT time changes:
		E.g. Unzip needs to use original time rather than
		the result of FF_GetSystemTime */

		myShort = 0;
		myShort |= ( ( pxTime->Hour    << 11 ) & 0xF800 );
		myShort |= ( ( pxTime->Minute  <<  5 ) & 0x07E0 );
		myShort |= ( ( pxTime->Second   /  2 ) & 0x001F );
		FF_putShort( pucEntryBuffer, ( uint16_t ) Offset, myShort );
	}
#endif /* ffconfigTIME_SUPPORT */
/*-----------------------------------------------------------*/


#if( ffconfigTIME_SUPPORT != 0 )
	static void FF_PlaceDate( uint8_t *pucEntryBuffer, uint32_t Offset, FF_SystemTime_t *pxTime )
	{
		uint16_t myShort;

		/* HT time changes:
		Unzip needs to use original date rather than
		the current date, so make it a parameter. */
		myShort = 0;
		myShort |= ( ( ( pxTime->Year- 1980 )  <<  9 ) & 0xFE00 ) ;
		myShort |= ( ( pxTime->Month <<  5 ) & 0x01E0 );
		myShort |= ( pxTime->Day & 0x001F );
		FF_putShort( pucEntryBuffer, ( uint16_t ) Offset, myShort );
	}
#endif /*  ffconfigTIME_SUPPORT */
/*-----------------------------------------------------------*/


#if( ffconfigTIME_SUPPORT != 0 )
	static void FF_GetTime( FF_SystemTime_t *pxTime, const uint8_t *pucEntryBuffer, uint32_t Offset )
	{
		uint16_t myShort;
		myShort = FF_getShort( pucEntryBuffer, ( uint16_t ) Offset );
		pxTime->Hour		= ( ( ( myShort & 0xF800 ) >> 11 ) & 0x001F );
		pxTime->Minute	= ( ( ( myShort & 0x07E0 ) >>  5 ) & 0x003F );
		pxTime->Second	= 2 * ( myShort & 0x01F );
	}
#endif /*  ffconfigTIME_SUPPORT */
/*-----------------------------------------------------------*/


#if( ffconfigTIME_SUPPORT != 0 )
	static void FF_GetDate( FF_SystemTime_t *pxTime, const uint8_t *pucEntryBuffer, uint32_t Offset )
	{
		uint16_t myShort;
		myShort = FF_getShort( pucEntryBuffer, ( uint16_t ) Offset );
		pxTime->Year		= 1980 + ( ( ( myShort & 0xFE00 ) >> 9 ) & 0x07F );
		pxTime->Month	= ( ( ( myShort & 0x01E0 ) >> 5 ) & 0x000F );
		pxTime->Day		= myShort & 0x01F;
	}
#endif /*  ffconfigTIME_SUPPORT */
/*-----------------------------------------------------------*/

void FF_PopulateShortDirent( FF_IOManager_t *pxIOManager, FF_DirEnt_t *pxDirEntry, const uint8_t *pucEntryBuffer )
{
	memcpy( pxDirEntry->pcFileName, pucEntryBuffer, 11 );	/* Copy the filename into the Dirent object. */
#if( ffconfigLFN_SUPPORT != 0 ) && ( ffconfigINCLUDE_SHORT_NAME != 0 )
	memcpy( pxDirEntry->pcShortName, pucEntryBuffer, 11 );
	pxDirEntry->pcShortName[ 11 ] = '\0';
	FF_ProcessShortName( pxDirEntry->pcShortName );	/* For debuggers only. */
#endif
	FF_ProcessShortName( ( char * ) pxDirEntry->pcFileName );		/* Format the shortname, for pleasant viewing. */

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	/* FileName contains a 8-bit short name
	 * Expand it to a FF_T_WCHAR string */
	FF_ShortNameExpand( pxDirEntry->pcFileName );
#endif

	( void )pxIOManager;	/* Silence a compiler warning, about not referencing pxIOManager. */

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	FF_tolower( pxDirEntry->pcFileName, ( uint32_t )wcslen( pxDirEntry->pcFileName ) );
#else
	FF_tolower( pxDirEntry->pcFileName, ( uint32_t )strlen( pxDirEntry->pcFileName ) );
#endif

	/* Get the item's Cluster address. */
	pxDirEntry->ulObjectCluster =
		( ( uint32_t )FF_getShort( pucEntryBuffer, FF_FAT_DIRENT_CLUS_HIGH ) << 16 ) |
		  ( uint32_t )FF_getShort( pucEntryBuffer, FF_FAT_DIRENT_CLUS_LOW );
#if( ffconfigTIME_SUPPORT != 0 )
	/* Get the creation Time & Date. */
	FF_GetTime( &pxDirEntry->xCreateTime, pucEntryBuffer, FF_FAT_DIRENT_CREATE_TIME );
	FF_GetDate( &pxDirEntry->xCreateTime, pucEntryBuffer, FF_FAT_DIRENT_CREATE_DATE );
	/* Get the modified Time & Date
	HT Here xCreateTime became xModifiedTime: */
	FF_GetTime( &pxDirEntry->xModifiedTime, pucEntryBuffer, FF_FAT_DIRENT_LASTMOD_TIME );
	FF_GetDate( &pxDirEntry->xModifiedTime, pucEntryBuffer, FF_FAT_DIRENT_LASTMOD_DATE );
	/* Get the last accessed Date. */
	FF_GetDate( &pxDirEntry->xAccessedTime, pucEntryBuffer, FF_FAT_DIRENT_LASTACC_DATE );
	pxDirEntry->xAccessedTime.Hour		= 0;
	pxDirEntry->xAccessedTime.Minute	= 0;
	pxDirEntry->xAccessedTime.Second	= 0;
#endif
	/* Get the filesize. */
	pxDirEntry->ulFileSize = FF_getLong( pucEntryBuffer, ( uint16_t )( FF_FAT_DIRENT_FILESIZE ) );
	/* Get the attribute. */
	pxDirEntry->ucAttrib = FF_getChar( pucEntryBuffer, ( uint16_t )( FF_FAT_DIRENT_ATTRIB ) );
}
/*-----------------------------------------------------------*/


/* Initialises a context object for FF_FetchEntryWithContext(  */
FF_Error_t FF_InitEntryFetch( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster, FF_FetchContext_t *pxContext )
{
	FF_Error_t xError;

	memset( pxContext, 0, sizeof( FF_FetchContext_t ) );

	/* Get the total length of the chain. */
	pxContext->ulChainLength = FF_GetChainLength( pxIOManager, ulDirCluster, NULL, &xError );

	if( FF_isERR( xError ) == pdFALSE )
	{
		pxContext->ulDirCluster = ulDirCluster;
		pxContext->ulCurrentClusterLCN = ulDirCluster;

		if( pxIOManager->xPartition.ucType != FF_T_FAT32 )
		{
			/* Handle Root Dirs that don't have cluster chains! */
			if( pxContext->ulDirCluster == pxIOManager->xPartition.ulRootDirCluster )
			{
				/* This is a RootDIR, special consideration needs to be made, because it doesn't have a Cluster chain! */
				pxContext->ulChainLength = pxIOManager->xPartition.ulRootDirSectors / pxIOManager->xPartition.ulSectorsPerCluster;
				if( pxContext->ulChainLength == 0 )		/* Some media has ulRootDirSectors < ulSectorsPerCluster. This is wrong, as it should be atleast 1 cluster! */
				{
					pxContext->ulChainLength = 1;
				}
			}
		}
	}

	return xError;
}	/* FF_InitEntryFetch() */
/*-----------------------------------------------------------*/

FF_Error_t FF_CleanupEntryFetch( FF_IOManager_t *pxIOManager, FF_FetchContext_t *pxContext )
{
	FF_Error_t xError = FF_ERR_NONE;
	if( pxContext->pxBuffer )
	{
		xError = FF_ReleaseBuffer( pxIOManager, pxContext->pxBuffer );
		pxContext->pxBuffer = NULL;
	}

	return xError;
}	/* FF_CleanupEntryFetch() */
/*-----------------------------------------------------------*/

/**
 *	@private
 *	@brief	Find the cluster for a given Entry within a directory
 *  @brief	Make an exception for the root directory ( non FAT32 only ):
 *  @brief	Just calculate the cluster ( don't consult the actual FAT )
 *
 *	@param	pxIOManager FF_IOManager_t object that was created by FF_CreateIOManger( ).
 *	@param	ulEntry     The sequence number of the entry of interest
 *  @param	pxContext   Context of current search
 *
 *	@Return	FF_ERR_NONE on success
 *	@Return	Possible error returned by FF_TraverseFAT( ) or END_OF_DIR
 *
 *  Side effects:
 *    - pxContext->ulCurrentClusterNum : relative cluster number ( 0 <= Num < ulChainLength )
 *    - pxContext->ulCurrentClusterLCN : fysical cluster on the partition
 **/

static FF_Error_t FF_Traverse( FF_IOManager_t *pxIOManager, uint32_t ulEntry, FF_FetchContext_t *pxContext )
{
uint32_t ulClusterNum = FF_getClusterChainNumber( pxIOManager, ulEntry, ( uint16_t ) FF_SIZEOF_DIRECTORY_ENTRY );
FF_Error_t xError = FF_ERR_NONE;

	/* Check if we're past the last cluster ( ulChainLength is also valid for root sectors ). */
	if( ( ulClusterNum + 1 ) > pxContext->ulChainLength )
	{
		xError = FF_ERR_DIR_END_OF_DIR | FF_TRAVERSE;	/* End of Dir was reached! */
	}
	else if( ( pxIOManager->xPartition.ucType != FF_T_FAT32 ) &&
		( pxContext->ulDirCluster == pxIOManager->xPartition.ulRootDirCluster ) )
	{
		/* Double-check if the entry number isn't too high. */
		if( ulEntry > ( ( pxIOManager->xPartition.ulRootDirSectors * pxIOManager->xPartition.usBlkSize ) / FF_SIZEOF_DIRECTORY_ENTRY ) )
		{
			xError = ( FF_Error_t ) ( FF_ERR_DIR_END_OF_DIR | FF_FETCHENTRYWITHCONTEXT );
		}
		else
		{
			pxContext->ulCurrentClusterLCN = pxContext->ulDirCluster;
		}
	}
	else if( ulClusterNum != pxContext->ulCurrentClusterNum )
	{
		/* Traverse the fat gently! */
		if( ulClusterNum > pxContext->ulCurrentClusterNum )
		{
			/* Start traverse from the current entry. */
			pxContext->ulCurrentClusterLCN = FF_TraverseFAT( pxIOManager, pxContext->ulCurrentClusterLCN, ( ulClusterNum - pxContext->ulCurrentClusterNum ), &xError );
		}
		else
		{
			/* Start traverse from the beginning. */
			pxContext->ulCurrentClusterLCN = FF_TraverseFAT( pxIOManager, pxContext->ulDirCluster, ulClusterNum, &xError );
		}
	}
	if( FF_isERR( xError ) == pdFALSE )
	{
		pxContext->ulCurrentClusterNum = ulClusterNum;
	}

	return xError;
}	/* FF_Traverse() */
/*-----------------------------------------------------------*/

FF_Error_t FF_FetchEntryWithContext( FF_IOManager_t *pxIOManager, uint32_t ulEntry, FF_FetchContext_t *pxContext, uint8_t *pEntryBuffer )
{
	uint32_t ulItemLBA;
	uint32_t ulRelItem;
	FF_Error_t xError;

	xError = FF_Traverse( pxIOManager, ulEntry, pxContext );

	if( FF_isERR( xError ) == pdFALSE )
	{
		ulRelItem     = FF_getMinorBlockEntry ( pxIOManager, ulEntry, ( uint32_t )FF_SIZEOF_DIRECTORY_ENTRY );

		ulItemLBA = FF_Cluster2LBA ( pxIOManager, pxContext->ulCurrentClusterLCN ) +
			FF_getMajorBlockNumber( pxIOManager, ulEntry, ( uint32_t ) FF_SIZEOF_DIRECTORY_ENTRY );
		if( ( pxIOManager->xPartition.ucType != FF_T_FAT32 ) &&
			( pxContext->ulDirCluster == pxIOManager->xPartition.ulRootDirCluster ) )
		{
			ulItemLBA += ( ulEntry / ( ( pxIOManager->xPartition.usBlkSize * pxIOManager->xPartition.ulSectorsPerCluster ) /
				FF_SIZEOF_DIRECTORY_ENTRY ) * pxIOManager->xPartition.ulSectorsPerCluster );
		}

		ulItemLBA = FF_getRealLBA ( pxIOManager, ulItemLBA ) + FF_getMinorBlockNumber( pxIOManager, ulRelItem, ( uint32_t )FF_SIZEOF_DIRECTORY_ENTRY );

		if( ( pxContext->pxBuffer == NULL ) ||
			( pxContext->pxBuffer->ulSector != ulItemLBA ) ||
			( ( pxContext->pxBuffer->ucMode & FF_MODE_WRITE ) != 0 ) )
		{
			if( pxContext->pxBuffer != NULL )
			{
				xError = FF_ReleaseBuffer( pxIOManager, pxContext->pxBuffer );
				pxContext->pxBuffer = NULL;
			}

			if( FF_isERR( xError ) == pdFALSE )
			{
				pxContext->pxBuffer = FF_GetBuffer( pxIOManager, ulItemLBA, FF_MODE_READ );
				if( pxContext->pxBuffer == NULL )
				{
					xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_FETCHENTRYWITHCONTEXT );
				}
			}
		}

		if ( ( pEntryBuffer != NULL ) && ( pxContext->pxBuffer != NULL ) )
		{
			memcpy( pEntryBuffer, pxContext->pxBuffer->pucBuffer + ( ulRelItem * FF_SIZEOF_DIRECTORY_ENTRY ), FF_SIZEOF_DIRECTORY_ENTRY );
		}
	}

    return xError;
}	/* FF_FetchEntryWithContext() */
/*-----------------------------------------------------------*/


FF_Error_t FF_PushEntryWithContext( FF_IOManager_t *pxIOManager, uint32_t ulEntry, FF_FetchContext_t *pxContext, uint8_t *pEntryBuffer )
{
	uint32_t	ulItemLBA;
	uint32_t	ulRelItem;
	FF_Error_t	xError;

	xError = FF_Traverse( pxIOManager, ulEntry, pxContext );
	if( FF_isERR( xError ) == pdFALSE )
	{
		ulRelItem     = FF_getMinorBlockEntry ( pxIOManager, ulEntry, ( uint32_t ) FF_SIZEOF_DIRECTORY_ENTRY );

		ulItemLBA = FF_Cluster2LBA ( pxIOManager, pxContext->ulCurrentClusterLCN ) + FF_getMajorBlockNumber( pxIOManager, ulEntry, ( uint32_t ) FF_SIZEOF_DIRECTORY_ENTRY );
		if( ( pxIOManager->xPartition.ucType != FF_T_FAT32 ) &&
			( pxContext->ulDirCluster == pxIOManager->xPartition.ulRootDirCluster ) )
		{
			ulItemLBA += ( ulEntry /
				( ( pxIOManager->xPartition.usBlkSize * pxIOManager->xPartition.ulSectorsPerCluster ) / FF_SIZEOF_DIRECTORY_ENTRY ) * pxIOManager->xPartition.ulSectorsPerCluster );
		}

		ulItemLBA = FF_getRealLBA ( pxIOManager, ulItemLBA ) + FF_getMinorBlockNumber( pxIOManager, ulRelItem, ( uint32_t )FF_SIZEOF_DIRECTORY_ENTRY );

		if( ( pxContext->pxBuffer == NULL ) ||
			( pxContext->pxBuffer->ulSector != ulItemLBA ) ||
			( ( pxContext->pxBuffer->ucMode & FF_MODE_WRITE ) == 0 ) )
		{
			if( pxContext->pxBuffer != NULL )
			{
				xError = FF_ReleaseBuffer( pxIOManager, pxContext->pxBuffer );
				pxContext->pxBuffer = NULL;
			}
			if( FF_isERR( xError ) == pdFALSE )
			{
				pxContext->pxBuffer = FF_GetBuffer( pxIOManager, ulItemLBA, FF_MODE_WRITE );
				if( pxContext->pxBuffer == NULL )
				{
					xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_FETCHENTRYWITHCONTEXT );
				}
			}
		}

		/* Now change the entry: */
		if( pxContext->pxBuffer != NULL )
		{
			memcpy( pxContext->pxBuffer->pucBuffer + ( ulRelItem * FF_SIZEOF_DIRECTORY_ENTRY ), pEntryBuffer, FF_SIZEOF_DIRECTORY_ENTRY );
		}
	}

    return xError;
}	/* FF_PushEntryWithContext() */
/*-----------------------------------------------------------*/


/**
 *	@private
 **/
FF_Error_t FF_GetEntry( FF_IOManager_t *pxIOManager, uint16_t usEntry, uint32_t ulDirCluster, FF_DirEnt_t *pxDirEntry )
{
/* A 32 byte directory entry. */
uint8_t ucEntryBuffer[ FF_SIZEOF_DIRECTORY_ENTRY ];
FF_FetchContext_t	xFetchContext;
FF_Error_t				xError;

#if( ffconfigLFN_SUPPORT == 0 )
	BaseType_t xLFNCount;
#endif
	xError = FF_InitEntryFetch( pxIOManager, ulDirCluster, &xFetchContext );

	if( FF_isERR( xError ) == pdFALSE )
	{
		xError = FF_FetchEntryWithContext( pxIOManager, usEntry, &xFetchContext, ucEntryBuffer );

		if( ( FF_isERR( xError ) == pdFALSE ) &&
			( FF_isDeleted( ucEntryBuffer ) == pdFALSE ) )
		{
			if( FF_isEndOfDir( ucEntryBuffer ) != pdFALSE )
			{
				xError = ( FF_Error_t ) ( FF_ERR_DIR_END_OF_DIR | FF_GETENTRY );
			}
			else
			{
				pxDirEntry->ucAttrib = FF_getChar( ucEntryBuffer, ( uint16_t )( FF_FAT_DIRENT_ATTRIB ) );

				if( ( pxDirEntry->ucAttrib & FF_FAT_ATTR_LFN ) == FF_FAT_ATTR_LFN )
				{
			#if( ffconfigLFN_SUPPORT != 0 )
					xError = FF_PopulateLongDirent( pxIOManager, pxDirEntry, usEntry, &xFetchContext );
			#else
					/* LFN Processing. */
					xLFNCount = ( BaseType_t )( ucEntryBuffer[0] & ~0x40 );
					pxDirEntry->usCurrentItem += ( xLFNCount - 1 );
			#endif
				}
				else if( ( pxDirEntry->ucAttrib & FF_FAT_ATTR_VOLID ) != FF_FAT_ATTR_VOLID )
				{
					FF_PopulateShortDirent( pxIOManager, pxDirEntry, ucEntryBuffer );
					pxDirEntry->usCurrentItem += 1;
				}
			}
		}
		{
		FF_Error_t xTempError;
			xTempError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = xTempError;
			}
		}
	}

	return xError;
}	/* FF_GetEntry() */
/*-----------------------------------------------------------*/


FF_Error_t FF_PopulateLongDirent( FF_IOManager_t *pxIOManager, FF_DirEnt_t *pxDirEntry, uint16_t usEntry, FF_FetchContext_t *pxFetchContext )
{
/* First get the entire name as UTF-16 from the LFN's.
Then transform into the API's native string format. */

FF_Error_t xError;
BaseType_t xNumLFNs;
uint8_t	ucCheckSum;
/* A 32 byte directory entry. */
uint8_t	pucEntryBuffer[ FF_SIZEOF_DIRECTORY_ENTRY ];
char pcShortName[ 13 ];

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	UBaseType_t	uiLfnLength = 0;
#endif

#if( ffconfigUNICODE_UTF16_SUPPORT == 0 )
	BaseType_t	xIndex, y;
#endif

#if( ffconfigUNICODE_UTF16_SUPPORT == 0 ) && ( ffconfigUNICODE_UTF8_SUPPORT == 0 )
	char	*pcLastPtr = pxDirEntry->pcFileName + sizeof( pxDirEntry->pcFileName );
	char	*pcCurPtr;
#endif

#if( ffconfigUNICODE_UTF8_SUPPORT != 0 )
	uint16_t nLfnBegin;
	uint16_t	usUtf8Len = 0;
#endif /* ffconfigUNICODE_UTF8_SUPPORT */

	do
	{
		xError = FF_FetchEntryWithContext( pxIOManager, usEntry++, pxFetchContext, pucEntryBuffer );
		if( FF_isERR( xError ) )
		{
			/* After breaking from this do {} while ( pdFALSE ) loop, xResult will be returned. */
			break;
		}

		xNumLFNs = ( BaseType_t )( pucEntryBuffer[0] & ~0x40 );
		ucCheckSum = FF_getChar( pucEntryBuffer, FF_FAT_LFN_CHECKSUM );

		#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
		{
			/* UTF-16 Can simply get segments of the UTF-16 sequence
			going forward in the directory entries ( but reversed order ). */
			while( xNumLFNs > 0 )
			{
				/* Avoid stack intensive use of a UTF-16 buffer. Stream direct to FileName dirent field in correct format. */
				/* memcpy direct! -UTF-16 support. */
				memcpy( pxDirEntry->pcFileName + ( ( xNumLFNs - 1 ) * 13 ) + 0,  &( pucEntryBuffer[ FF_FAT_LFN_NAME_1] ), 10 );
				memcpy( pxDirEntry->pcFileName + ( ( xNumLFNs - 1 ) * 13 ) + 5,  &( pucEntryBuffer[ FF_FAT_LFN_NAME_2] ), 12 );
				memcpy( pxDirEntry->pcFileName + ( ( xNumLFNs - 1 ) * 13 ) + 11, &( pucEntryBuffer[ FF_FAT_LFN_NAME_3] ), 4 );
				uiLfnLength += 13;

				xError = FF_FetchEntryWithContext( pxIOManager, usEntry++, pxFetchContext, pucEntryBuffer );
				if( FF_isERR( xError ) )
				{
					break;
				}
				xNumLFNs--;
			}
			if( FF_isERR( xError ) )
			{
				break;
			}
			pxDirEntry->pcFileName[ uiLfnLength ] = '\0';
		}
		#endif /* ffconfigUNICODE_UTF16_SUPPORT */

		#if ( ffconfigUNICODE_UTF8_SUPPORT != 0 )
		{
			/* UTF-8 Sequence, we can only convert this from the beginning, must receive entries in reverse. */
			nLfnBegin = usEntry - 1;

			for( xIndex = 0; xIndex < xNumLFNs; xIndex++ )
			{
				xError = FF_FetchEntryWithContext( pxIOManager, ( nLfnBegin + ( xNumLFNs - 1 ) - xIndex ), pxFetchContext, pucEntryBuffer );
				if( FF_isERR( xError ) )
				{
					break;
				}

				/* Now have the first part of the UTF-16 sequence. Stream into a UTF-8 sequence. */
				for( y = 0; y < 5; y++ )
				{
					xError = FF_Utf16ctoUtf8c( ( uint8_t * )&pxDirEntry->pcFileName[ usUtf8Len ],
						( uint16_t * )&pucEntryBuffer[ FF_FAT_LFN_NAME_1 + ( y * 2 ) ], sizeof( pxDirEntry->pcFileName ) - usUtf8Len );
					if( xError > 0 )
					{
						usUtf8Len += ( uint16_t )xError;
					}
				}

				for( y = 0; y < 6; y++ )
				{
					xError = FF_Utf16ctoUtf8c( ( uint8_t * )&pxDirEntry->pcFileName[ usUtf8Len ],
						( uint16_t * )&pucEntryBuffer[ FF_FAT_LFN_NAME_2 + ( y * 2 ) ], sizeof( pxDirEntry->pcFileName ) - usUtf8Len );
					if( xError > 0 )
					{
						usUtf8Len += ( uint16_t )xError;
					}
				}

				for( y = 0; y < 2; y++ )
				{
					xError = FF_Utf16ctoUtf8c( ( uint8_t * )&pxDirEntry->pcFileName[ usUtf8Len ],
						( uint16_t * )&pucEntryBuffer[ FF_FAT_LFN_NAME_3 +  ( y * 2 ) ], sizeof( pxDirEntry->pcFileName ) - usUtf8Len );
					if( xError > 0 )
					{
						usUtf8Len += ( uint16_t ) xError;
					}
				}
				usEntry++;
			}
			if( FF_isERR( xError ) )
			{
				break;
			}

			pxDirEntry->pcFileName[ usUtf8Len ] = '\0';

			/* Put Entry context to correct position. */
			xError = FF_FetchEntryWithContext( pxIOManager, usEntry-1, pxFetchContext, pucEntryBuffer );
			if( FF_isERR( xError ) )
			{
				break;
			}
		}
		#endif /* ( ffconfigUNICODE_UTF8_SUPPORT != 0 ) */

		#if( ffconfigUNICODE_UTF16_SUPPORT == 0 ) && ( ffconfigUNICODE_UTF8_SUPPORT == 0 )	/* No Unicode, simple ASCII. */
		{
			pcLastPtr[ -1 ] = '\0';
			y = xNumLFNs;
			while( xNumLFNs-- )
			{
				pcCurPtr = pxDirEntry->pcFileName + ( xNumLFNs * 13 );
				for( xIndex = 0; ( xIndex < 10 ) && ( pcCurPtr < pcLastPtr ); xIndex += 2 )
				{
					*( pcCurPtr++ ) = pucEntryBuffer[ FF_FAT_LFN_NAME_1 + xIndex ];
				}

				for( xIndex = 0; ( xIndex < 12 ) && ( pcCurPtr < pcLastPtr ); xIndex += 2 )
				{
					*( pcCurPtr++ ) = pucEntryBuffer[ FF_FAT_LFN_NAME_2 + xIndex ];
				}

				for( xIndex = 0; ( xIndex < 4 ) && ( pcCurPtr < pcLastPtr ); xIndex += 2 )
				{
					*( pcCurPtr++ ) = pucEntryBuffer[ FF_FAT_LFN_NAME_3 + xIndex ];
				}
				if( ( xNumLFNs == ( y - 1 ) ) && ( pcCurPtr < pcLastPtr ) )
				{
					*pcCurPtr = '\0';
				}
				xError = FF_FetchEntryWithContext( pxIOManager, usEntry++, pxFetchContext, pucEntryBuffer );
				if( FF_isERR( xError ) )
				{
					break;
				}
			}
			if( FF_isERR( xError ) )
			{
				break;
			}
		}
		#endif /* ( ffconfigUNICODE_UTF16_SUPPORT == 0 ) && ( ffconfigUNICODE_UTF8_SUPPORT == 0 ) */

		/* Process the Shortname. -- LFN Transformation is now complete.
		Process the ShortName Entry. */

		/* if SHORTNAMES must be included, simple byte copy into shortname buffer. */
		#if( ffconfigLFN_SUPPORT != 0 ) && ( ffconfigINCLUDE_SHORT_NAME != 0 )
		{
			memcpy( pxDirEntry->pcShortName, pucEntryBuffer, 11 );
			pxDirEntry->pcShortName[ 11 ] = '\0';
			FF_ProcessShortName( pxDirEntry->pcShortName );
		}
		#endif /* ( != 0 ffconfigLFN_SUPPORT ) && ( ffconfigINCLUDE_SHORT_NAME != 0 ) */

		memcpy( pcShortName, pucEntryBuffer, 11 );
		FF_ProcessShortName( pcShortName );
		if( ucCheckSum != FF_CreateChkSum( pucEntryBuffer ) )
		{
			strcpy( pxDirEntry->pcFileName, pcShortName );
			#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
			{
				FF_ShortNameExpand( pxDirEntry->pcFileName );
			}
			#endif /* ffconfigUNICODE_UTF16_SUPPORT */
		}

		/* Finally fill in the other details. */
		pxDirEntry->ulObjectCluster =
			( ( uint32_t )FF_getShort( pucEntryBuffer, FF_FAT_DIRENT_CLUS_HIGH ) << 16 ) |
			  ( uint32_t )FF_getShort( pucEntryBuffer, FF_FAT_DIRENT_CLUS_LOW );

		#if( ffconfigTIME_SUPPORT != 0 )
		{
			/* Get the creation Time & Date. */
			FF_GetTime( &pxDirEntry->xCreateTime, pucEntryBuffer, FF_FAT_DIRENT_CREATE_TIME );
			FF_GetDate( &pxDirEntry->xCreateTime, pucEntryBuffer, FF_FAT_DIRENT_CREATE_DATE );
			/* Get the modified Time & Date. */
			/* HT Here xCreateTime has become xModifiedTime, as it should: */
			FF_GetTime( &pxDirEntry->xModifiedTime, pucEntryBuffer, FF_FAT_DIRENT_LASTMOD_TIME );
			FF_GetDate( &pxDirEntry->xModifiedTime, pucEntryBuffer, FF_FAT_DIRENT_LASTMOD_DATE );
			/* Get the last accessed Date. */
			FF_GetDate( &pxDirEntry->xAccessedTime, pucEntryBuffer, FF_FAT_DIRENT_LASTACC_DATE );
			/* HT Why should these times be zero'd ? */
			pxDirEntry->xAccessedTime.Hour		= 0;
			pxDirEntry->xAccessedTime.Minute	= 0;
			pxDirEntry->xAccessedTime.Second	= 0;
		}
		#endif /* ffconfigTIME_SUPPORT */

		/* Get the filesize. */
		pxDirEntry->ulFileSize = FF_getLong( pucEntryBuffer, ( uint16_t ) ( FF_FAT_DIRENT_FILESIZE ) );
		/* Get the attribute. */
		pxDirEntry->ucAttrib = FF_getChar( pucEntryBuffer, ( uint16_t ) ( FF_FAT_DIRENT_ATTRIB ) );

		pxDirEntry->usCurrentItem = usEntry;
	}
	while ( pdFALSE );

	return xError;
}	/* FF_PopulateLongDirent() */
/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Find's the first directory entry for the provided path.
 *
 *	All values recorded in pxDirEntry must be preserved to and between calls to
 *	FF_FindNext( ).
 *
 *	If ffconfigFINDAPI_ALLOW_WILDCARDS is defined, then path will have the following behaviour:
 *
 *	path = "\" 					- Open the root dir, and iterate through all items.
 *	path = "\*.c"				- Open the root dir, showing only files matching *.c wildcard.
 *	path = "\sub1\newdir"		- Get the DIRENT for the newdir directory in /sub1/ if one exists.
 *	path = "\sub1\newdir\"		- Open the directory /sub1/newdir/ and iterate through all items.
 *	path = "\sub1\newdir\*.c"	- Open the directory /sub1/newdir/ and iterate through all items matching the *.c wildcard.
 *
 *	It is important to distinguish the differences in behaviour between opening a Find operation
 *	on a path like /sub1 and /sub1/. ( /sub1 gets the sub1 dirent from the / dir, whereas /sub/ opens the sub1 dir ).
 *
 *	Note, as compatible with other similar APIs, FreeRTOS+FAT also accepts \sub1\* for the same behaviour as
 *	/sub1/.
 *
 *	@param	pxIOManager FF_IOManager_t object that was created by FF_CreateIOManger( ).
 *	@param	pxDirEntry	FF_DirEnt_t object to store the entry information.
 *	@param	path		String to of the path to the Dir being listed.
 *
 *	@Return	0 on success
 *	@Return	FF_ERR_DEVICE_DRIVER_FAILED if device access failed.
 *	@Return -2 if Dir was not found.
 *
 **/
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
FF_Error_t FF_FindFirst( FF_IOManager_t *pxIOManager, FF_DirEnt_t *pxDirEntry, const FF_T_WCHAR *pcPath )
#else
FF_Error_t FF_FindFirst( FF_IOManager_t *pxIOManager, FF_DirEnt_t *pxDirEntry, const char *pcPath )
#endif
{
FF_Error_t xError;
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	uint16_t	PathLen = ( uint16_t ) wcslen( pcPath );
#else
	uint16_t	PathLen = ( uint16_t ) strlen( pcPath );
#endif

#if( ffconfigFINDAPI_ALLOW_WILDCARDS != 0 )
	BaseType_t xIndex = 0;
	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
		const FF_T_WCHAR *pcWildCard;	/* Check for a Wild-card. */
	#else
		const char *pcWildCard;	/* Check for a Wild-card. */
	#endif
#endif

	memset( pxDirEntry, 0, sizeof( FF_DirEnt_t ) );

	if( pxIOManager == NULL )
	{
		xError = ( FF_Error_t ) ( FF_ERR_NULL_POINTER | FF_FINDFIRST );
	}
#if( ffconfigREMOVABLE_MEDIA != 0 )
	else if( ( pxIOManager->ucFlags & FF_IOMAN_DEVICE_IS_EXTRACTED ) != 0 )
	{
		xError = ( FF_Error_t ) ( FF_ERR_IOMAN_DRIVER_NOMEDIUM | FF_FINDFIRST );
	}
#endif /* ffconfigREMOVABLE_MEDIA */
	else
	{
		#if( ffconfigFINDAPI_ALLOW_WILDCARDS != 0 )
		{
			pxDirEntry->pcWildCard[0] = '\0';	/* WildCard blank if its not a wildCard. */

			pcWildCard = &pcPath[ PathLen - 1 ];

			if( PathLen != 0 )
			{
				/* Open the dir of the last token. */
				while( ( *pcWildCard != '\\' ) && ( *pcWildCard != '/' ) )
				{
					xIndex++;
					pcWildCard--;
					if( PathLen == xIndex )
					{
						break;
					}
				}
			}

			pxDirEntry->ulDirCluster = FF_FindDir( pxIOManager, pcPath, PathLen - xIndex, &xError );
			if( FF_isERR( xError ) == pdFALSE )
			{
				if( pxDirEntry->ulDirCluster != 0 )
				{
					/* Valid Dir found, copy the wildCard to filename! */
			#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
					wcsncpy( pxDirEntry->pcWildCard, ++pcWildCard, ffconfigMAX_FILENAME );
			#else
					strncpy( pxDirEntry->pcWildCard, ++pcWildCard, ffconfigMAX_FILENAME );
			#endif
					if( pxDirEntry->pcWildCard[ xIndex - 1 ] == ':' )
					{
						pxDirEntry->xInvertWildCard = pdTRUE;
						pxDirEntry->pcWildCard[ xIndex - 1 ] = '\0';
					}
				}
			}
		}
		#else /* ffconfigFINDAPI_ALLOW_WILDCARDS */
		{
			/* Get the directory cluster, if it exists. */
			pxDirEntry->ulDirCluster = FF_FindDir( pxIOManager, pcPath, PathLen, &xError );
		}
		#endif /* ffconfigFINDAPI_ALLOW_WILDCARDS */

		if( FF_isERR( xError ) == pdFALSE )
		{
			if( pxDirEntry->ulDirCluster == 0 )
			{
				xError = ( FF_Error_t ) ( FF_ERR_DIR_INVALID_PATH | FF_FINDFIRST );
			}
			else
			{
				/* Initialise the Fetch Context. */
				xError = FF_InitEntryFetch( pxIOManager, pxDirEntry->ulDirCluster, &( pxDirEntry->xFetchContext ) );
				if( FF_isERR( xError ) == pdFALSE )
				{
					pxDirEntry->usCurrentItem = 0;
					xError = FF_FindNext( pxIOManager, pxDirEntry );
				}
			}
		}
	}

	return xError;
}	/* FF_FindFirst() */
/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Get's the next Entry based on the data recorded in the FF_DirEnt_t object.
 *
 *	All values recorded in pxDirEntry must be preserved to and between calls to
 *	FF_FindNext( ). Please see @see FF_FindFirst( ) for find initialisation.
 *
 *	@param	pxIOManager		FF_IOManager_t object that was created by FF_CreateIOManger( ).
 *	@param	pxDirEntry		FF_DirEnt_t object to store the entry information. ( As initialised by FF_FindFirst( )).
 *
 *	@Return FF_ERR_DEVICE_DRIVER_FAILED is device access failed.
 *
 **/
FF_Error_t FF_FindNext( FF_IOManager_t *pxIOManager, FF_DirEnt_t *pxDirEntry )
{
FF_Error_t xError;
BaseType_t xLFNCount;
const uint8_t *pucEntryBuffer = NULL;
#if( ffconfigFINDAPI_ALLOW_WILDCARDS != 0 )
	BaseType_t	b;
#endif

	if( pxIOManager == NULL )
	{
		xError = ( FF_Error_t ) ( FF_ERR_NULL_POINTER | FF_FINDNEXT );
	}
#if( ffconfigREMOVABLE_MEDIA != 0 )
	else if( ( pxIOManager->ucFlags & FF_IOMAN_DEVICE_IS_EXTRACTED ) != 0 )
	{
		xError = ( FF_Error_t ) ( FF_ERR_IOMAN_DRIVER_NOMEDIUM | FF_FINDNEXT );
	}
#endif /* ffconfigREMOVABLE_MEDIA */
	else
	{
		xError = FF_ERR_NONE;
		for( ; pxDirEntry->usCurrentItem < FF_MAX_ENTRIES_PER_DIRECTORY; pxDirEntry->usCurrentItem++ )
		{
			if( ( pucEntryBuffer == NULL ) ||
				( pucEntryBuffer >= ( pxDirEntry->xFetchContext.pxBuffer->pucBuffer + ( FF_SIZEOF_SECTOR - FF_SIZEOF_DIRECTORY_ENTRY ) ) ) )
			{
				xError = FF_FetchEntryWithContext( pxIOManager, pxDirEntry->usCurrentItem, &( pxDirEntry->xFetchContext ), NULL );

				if( FF_isERR( xError ) )
				{
					break;
				}

				if( pucEntryBuffer == NULL )
				{
					pucEntryBuffer = pxDirEntry->xFetchContext.pxBuffer->pucBuffer +
						( FF_SIZEOF_DIRECTORY_ENTRY * ( pxDirEntry->usCurrentItem % ( FF_SIZEOF_SECTOR/FF_SIZEOF_DIRECTORY_ENTRY ) ) );
				}
				else
				{
					pucEntryBuffer = pxDirEntry->xFetchContext.pxBuffer->pucBuffer;
				}
			}
			else
			{
				pucEntryBuffer += FF_SIZEOF_DIRECTORY_ENTRY;
			}

			if( FF_isDeleted( pucEntryBuffer ) != pdFALSE )
			{
				/* The entry is not in use or deleted. */
				continue;
			}

			if( FF_isEndOfDir( pucEntryBuffer ) )
			{
				/* End of directory, generate a pseudo error 'DIR_END_OF_DIR'. */
				xError = ( FF_Error_t ) ( FF_ERR_DIR_END_OF_DIR | FF_FINDNEXT );
				break;
			}

			pxDirEntry->ucAttrib = FF_getChar( pucEntryBuffer, ( uint16_t ) ( FF_FAT_DIRENT_ATTRIB ) );

			if( ( pxDirEntry->ucAttrib & FF_FAT_ATTR_LFN ) == FF_FAT_ATTR_LFN )
			{
				/* LFN Processing. */
				xLFNCount = ( BaseType_t )( pucEntryBuffer[0] & ~0x40 );
				/* Get the shortname and check if it is marked deleted. */
				#if( ffconfigLFN_SUPPORT != 0 )
				{
				/* Reserve 32 bytes to hold one directory entry. */
				uint8_t	Buffer[ FF_SIZEOF_DIRECTORY_ENTRY ];

					/* Fetch the shortname, and get it's checksum, or for a deleted item with
					orphaned LFN entries. */
					xError = FF_FetchEntryWithContext( pxIOManager, ( uint32_t ) ( pxDirEntry->usCurrentItem + xLFNCount ), &pxDirEntry->xFetchContext, Buffer );
					if( FF_isERR( xError ) )
					{
						break;
					}

					if( FF_isDeleted( Buffer ) == pdFALSE )
					{
						xError = FF_PopulateLongDirent( pxIOManager, pxDirEntry, pxDirEntry->usCurrentItem, &pxDirEntry->xFetchContext );
						if( FF_isERR( xError ) )
						{
							break;
						}
						#if( ffconfigINCLUDE_SHORT_NAME != 0 )
						{
							pxDirEntry->ucAttrib |= FF_FAT_ATTR_IS_LFN;
						}
						#endif

						#if( ffconfigFINDAPI_ALLOW_WILDCARDS != 0 )
						{
						#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
							if( wcscmp( pxDirEntry->pcWildCard, L"" ) )
						#else
							if( pxDirEntry->pcWildCard[0] )
						#endif
							{
								b = FF_wildcompare( pxDirEntry->pcWildCard, pxDirEntry->pcFileName );
								if( pxDirEntry->xInvertWildCard != pdFALSE )
								{
									b = !b;
								}
								if( b != 0 )
								{
									break;
								}

								/* 'usCurrentItem' has already incremented by FF_PopulateLongDirent(),
								this loop will incremente it again. */
								pxDirEntry->usCurrentItem -= 1;

								/* xFetchContext/usCurrentItem have changed.  Update
								'pucEntryBuffer' to point to the current buffer position. */
								pucEntryBuffer = pxDirEntry->xFetchContext.pxBuffer->pucBuffer +
									( FF_SIZEOF_DIRECTORY_ENTRY * ( pxDirEntry->usCurrentItem % ( FF_SIZEOF_SECTOR/FF_SIZEOF_DIRECTORY_ENTRY ) ) );
							}
							else
							{
								break;
							}
						}
						#else	/* ffconfigFINDAPI_ALLOW_WILDCARDS == 0 */
						{
							/* usCurrentItem has been incremented by FF_PopulateLongDirent().
							Entry will be returned. */
							break;
						}
						#endif
					}
				}
				#else /* ffconfigLFN_SUPPORT */
				{
					/* Increment 'usCurrentItem' with (xLFNCount-1),
					the loop will do an extra increment. */
					pxDirEntry->usCurrentItem += ( xLFNCount - 1 );
				}
				#endif /* ffconfigLFN_SUPPORT */
			} /* ( ( pxDirEntry->ucAttrib & FF_FAT_ATTR_LFN ) == FF_FAT_ATTR_LFN ) */
			else if( ( pxDirEntry->ucAttrib & FF_FAT_ATTR_VOLID ) != FF_FAT_ATTR_VOLID )
			{
				/* If it's not a LFN entry, neither a Volume ID, it is a normal short name entry. */
				FF_PopulateShortDirent( pxIOManager, pxDirEntry, pucEntryBuffer );
				#if( ffconfigSHORTNAME_CASE != 0 )
				{
					/* Apply NT/XP+ bits to get correct case. */
					FF_CaseShortName( pxDirEntry->pcFileName, FF_getChar( pucEntryBuffer, FF_FAT_CASE_OFFS ) );
				}
				#endif

				#if( ffconfigFINDAPI_ALLOW_WILDCARDS != 0 )
				{
					if( pxDirEntry->pcWildCard[ 0 ] )
					{
						b = FF_wildcompare( pxDirEntry->pcWildCard, pxDirEntry->pcFileName );
						if( pxDirEntry->xInvertWildCard != pdFALSE )
						{
							b = !b;
						}
						if( b != 0 )
						{
							pxDirEntry->usCurrentItem += 1;
							break;
						}
					}
					else
					{
						pxDirEntry->usCurrentItem += 1;
						break;
					}
				}
				#else /* ffconfigFINDAPI_ALLOW_WILDCARDS */
				{
					pxDirEntry->usCurrentItem += 1;
					break;
				}
				#endif
			}
		} /* for ( ; pxDirEntry->usCurrentItem < FF_MAX_ENTRIES_PER_DIRECTORY; pxDirEntry->usCurrentItem++ ) */

		if( pxDirEntry->usCurrentItem == FF_MAX_ENTRIES_PER_DIRECTORY )
		{
			xError = ( FF_Error_t ) ( FF_ERR_DIR_END_OF_DIR | FF_FINDNEXT );
		}

		{
		FF_Error_t xTempError;
			xTempError = FF_CleanupEntryFetch( pxIOManager, &pxDirEntry->xFetchContext );

			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = xTempError;
			}
		}
	}

	return xError;
}	/* FF_FindNext() */
/*-----------------------------------------------------------*/


/*
	Returns >= 0 for a free dirent entry.
	Returns <  0 with and xError code if anything goes wrong.
*/
static int32_t FF_FindFreeDirent( FF_IOManager_t *pxIOManager, FF_FindParams_t *pxFindParams, uint16_t usSequential )
{
const uint8_t *pucEntryBuffer = NULL;
uint16_t freeCount = 0;
UBaseType_t uxEntry = 0;
BaseType_t xEntryFound = pdFALSE;
FF_Error_t xError;
uint32_t DirLength;
FF_FetchContext_t xFetchContext;
uint32_t ulDirCluster = pxFindParams->ulDirCluster;

	xError = FF_InitEntryFetch( pxIOManager, ulDirCluster, &xFetchContext );

	if( FF_isERR( xError ) == pdFALSE )
	{
		uxEntry = pxFindParams->lFreeEntry >= 0 ? pxFindParams->lFreeEntry : 0;
		for ( ; uxEntry < FF_MAX_ENTRIES_PER_DIRECTORY; uxEntry++ )
		{
			if( ( pucEntryBuffer == NULL ) ||
				( pucEntryBuffer >= xFetchContext.pxBuffer->pucBuffer + ( FF_SIZEOF_SECTOR - FF_SIZEOF_DIRECTORY_ENTRY ) ) )
			{
				xError = FF_FetchEntryWithContext( pxIOManager, uxEntry, &xFetchContext, NULL );
				if( FF_GETERROR( xError ) == FF_ERR_DIR_END_OF_DIR )
				{

					xError = FF_ExtendDirectory( pxIOManager, ulDirCluster );
					/* The value of xEntryFound will be ignored in case there was an error. */
					xEntryFound = pdTRUE;
					break;
				}
				else if( FF_isERR( xError ) )
				{
					break;
				}
				if( pucEntryBuffer == NULL )
				{
					pucEntryBuffer = xFetchContext.pxBuffer->pucBuffer +
						( FF_SIZEOF_DIRECTORY_ENTRY * ( uxEntry % ( FF_SIZEOF_SECTOR / FF_SIZEOF_DIRECTORY_ENTRY ) ) );
				}
				else
				{
					pucEntryBuffer = xFetchContext.pxBuffer->pucBuffer;
				}
			}
			else
			{
				/* Advance 32 bytes to point to the next directory entry. */
				pucEntryBuffer += FF_SIZEOF_DIRECTORY_ENTRY;
			}
			if( FF_isEndOfDir( pucEntryBuffer ) )	/* If its the end of the Dir, then FreeDirents from here. */
			{
				/* Check if the directory has enough space */
				DirLength = xFetchContext.ulChainLength;
				if( ( uxEntry + usSequential ) >
					( ( DirLength * ( ( UBaseType_t )pxIOManager->xPartition.ulSectorsPerCluster * pxIOManager->xPartition.usBlkSize ) ) / FF_SIZEOF_DIRECTORY_ENTRY ) )
				{
					xError = FF_ExtendDirectory( pxIOManager, ulDirCluster );
				}
				xEntryFound = pdTRUE;
				break;
			}
			if( FF_isDeleted( pucEntryBuffer ) )
			{
				if( ++freeCount == usSequential )
				{
					xError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
					xEntryFound = pdTRUE;
					uxEntry = ( uxEntry - ( usSequential - 1 ) );/* Return the beginning entry in the sequential sequence. */
					break;
				}
			}
			else
			{
				freeCount = 0;
			}
		}	/* for ( uxEntry = 0; uxEntry < FF_MAX_ENTRIES_PER_DIRECTORY; uxEntry++ ) */

		{
		FF_Error_t xTempError;

			xTempError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = xTempError;
			}
		}

	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		if( xEntryFound != pdFALSE )
		{
			/* No error has occurred and a free directory entry has been found. */
			xError = uxEntry;
		}
		else
		{
			xError = ( FF_Error_t ) ( FF_ERR_DIR_DIRECTORY_FULL | FF_FINDFREEDIRENT );
		}
	}

	return xError;
}	/* FF_FindFreeDirent() */
/*-----------------------------------------------------------*/

/* _HT_ Now FF_PutEntry has a new optional parameter *pucContents */
/* _HT_ so it can be used FF_MkDir( ) to save some code when adding . and .. entries  */
FF_Error_t FF_PutEntry( FF_IOManager_t *pxIOManager, uint16_t usEntry, uint32_t ulDirCluster, FF_DirEnt_t *pxDirEntry, uint8_t *pucContents )
{
FF_Error_t xError;
/* Reserve 32 bytes to hold one directory entry. */
uint8_t	pucEntryBuffer[ FF_SIZEOF_DIRECTORY_ENTRY ];
FF_FetchContext_t xFetchContext;

	/* HT: use the standard access routine to get the same logic for root dirs. */
	xError = FF_InitEntryFetch( pxIOManager, ulDirCluster, &xFetchContext );
	if( FF_isERR( xError ) == pdFALSE )
	{
		xError = FF_FetchEntryWithContext( pxIOManager, usEntry, &xFetchContext, pucEntryBuffer );
		if( FF_isERR( xError ) == pdFALSE )
		{
			/* Cleanup probably not necessary here?
			FF_PushEntryWithContext checks for R/W flag. */
			xError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
			if( FF_isERR( xError ) == pdFALSE )
			{
				if ( pucContents != NULL )
				{
					memcpy ( pucEntryBuffer, pucContents, sizeof( pucEntryBuffer ) );
				}
				FF_putChar( pucEntryBuffer,  FF_FAT_DIRENT_ATTRIB,    ( uint32_t ) pxDirEntry->ucAttrib );
				FF_putShort( pucEntryBuffer, FF_FAT_DIRENT_CLUS_HIGH, ( uint32_t ) ( pxDirEntry->ulObjectCluster >> 16 ) );
				FF_putShort( pucEntryBuffer, FF_FAT_DIRENT_CLUS_LOW,  ( uint32_t ) ( pxDirEntry->ulObjectCluster ) );
				FF_putLong( pucEntryBuffer,  FF_FAT_DIRENT_FILESIZE,  pxDirEntry->ulFileSize );
				#if( ffconfigTIME_SUPPORT != 0 )
				{
					FF_GetSystemTime( &pxDirEntry->xAccessedTime );	/*/< Date of Last Access. */
					FF_PlaceTime( pucEntryBuffer, FF_FAT_DIRENT_LASTACC_DATE, &pxDirEntry->xAccessedTime );
					FF_PlaceDate( pucEntryBuffer, FF_FAT_DIRENT_LASTACC_DATE, &pxDirEntry->xAccessedTime );	/* Last accessed date. */
					FF_PlaceTime( pucEntryBuffer, FF_FAT_DIRENT_CREATE_TIME,  &pxDirEntry->xCreateTime );
					FF_PlaceDate( pucEntryBuffer, FF_FAT_DIRENT_CREATE_DATE,  &pxDirEntry->xCreateTime );
					FF_PlaceTime( pucEntryBuffer, FF_FAT_DIRENT_LASTMOD_TIME, &pxDirEntry->xModifiedTime );
					FF_PlaceDate( pucEntryBuffer, FF_FAT_DIRENT_LASTMOD_DATE, &pxDirEntry->xModifiedTime );
				}
				#endif	/* ffconfigTIME_SUPPORT */
				xError = FF_PushEntryWithContext( pxIOManager, usEntry, &xFetchContext, pucEntryBuffer );
			}
		}
	}

	FF_CleanupEntryFetch( pxIOManager, &xFetchContext );

	return xError;
}	/* FF_PutEntry() */
/*-----------------------------------------------------------*/

static BaseType_t FF_ValidShortChar( char cChar )
{
	return ( cChar >= 'A' && cChar <= 'Z' ) ||
		( cChar >= 'a' && cChar <= 'z' ) ||	/* lower-case can be stored using NT/XP attribute. */
		( cChar >= '0' && cChar <= '9' ) ||
		strchr ( "$%-_@~`!(){}^#&", cChar ) != NULL;
}	/* FF_ValidShortChar() */
/*-----------------------------------------------------------*/

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
void FF_CreateShortName( FF_FindParams_t *pxFindParams, const FF_T_WCHAR *pcLongName )
#else
void FF_CreateShortName( FF_FindParams_t *pxFindParams, const char *pcLongName )
#endif
{
BaseType_t xIndex, xPosition, xLastDot;
uint16_t NameLen;

#if( ffconfigSHORTNAME_CASE != 0 )
	uint8_t testAttrib = FF_FAT_CASE_ATTR_BASE;
#endif

	/* Examples:
	 * "readme.TXT" will get the attribute FF_FAT_CASE_ATTR_BASE
	 * "README.txt" will get the attribute FF_FAT_CASE_ATTR_EXT
	 * "Readme.txt" can not be store as a short name */

	pxFindParams->ucCaseAttrib = 0;		/* May get the value FF_FAT_CASE_ATTR_BASE or FF_FAT_CASE_ATTR_EXT */
	pxFindParams->ucFirstTilde = 6;		/* The numerical position of the ~ */
	pxFindParams->ulFlags |= FIND_FLAG_SHORTNAME_SET | FIND_FLAG_FITS_SHORT | FIND_FLAG_SIZE_OK;

	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	{
		NameLen = ( uint16_t ) wcslen( pcLongName );
	}
	#else
	{
		NameLen = ( uint16_t ) strlen( pcLongName );
	}
	#endif

	/* Does pcLongName fit a shortname? */

	for( xIndex = 0, xPosition = 0, xLastDot = NameLen; xIndex < NameLen; xIndex++ )
	{
		if( pcLongName[ xIndex ] != '.' )
		{
			xPosition++;
		}
		else
		{
			xLastDot = xIndex;
		}
	}
	/* For example:
	"FILENAME.EXT": NameLen = 12, xLastDot = 8, xPosition = 11
	".cproject"   : NameLen =  9, xLastDot = 0, xPosition =  8
	*/

	if( ( NameLen > 12 ) ||				/* If name is longer than 12 characters (8.3). */
		( NameLen - xPosition > 1 ) ||	/* If it contains more than 1 dot. */
		( NameLen - xLastDot > 4 ) ||	/* If the file name extension is longer than 3 characters. */
		( xLastDot > 8 ) )				/* If the file name base is too long. */
	{
		pxFindParams->ulFlags &= ~FIND_FLAG_SIZE_OK;
	}

	for( xIndex = 0, xPosition = 0; xIndex < 11; xPosition++ )
	{
		char ch = pcLongName[ xPosition ];
		if( !ch )
			break;
		if( ( xIndex == 0 ) && ( ch == '.' ) )
		{
			pxFindParams->ulFlags &= ~FIND_FLAG_FITS_SHORT;
			continue;
		}
		if( xPosition == xLastDot )
		{
			/* Remember where we put the first space. */
			if ( pxFindParams->ucFirstTilde > xIndex )
			{
				pxFindParams->ucFirstTilde = xIndex;
			}
			while ( xIndex < 8 )
			{
				pxFindParams->pcEntryBuffer[ xIndex++ ] = 0x20;
			}
			#if( ffconfigSHORTNAME_CASE != 0 )
			{
				testAttrib = FF_FAT_CASE_ATTR_EXT;
			}
			#endif
		}
		else
		{
			if( xIndex == 8 )
			{
				if( xPosition <= xLastDot )
				{
					xPosition = xLastDot;
					ch = ( int8_t ) pcLongName[ xPosition ];
					if( ch == '\0' )
					{
						break;
					}
					ch = ( int8_t ) pcLongName[ ++xPosition ];
					#if( ffconfigSHORTNAME_CASE != 0 )
					{
						testAttrib = FF_FAT_CASE_ATTR_EXT;
					}
					#endif
				}
			}
			if( !FF_ValidShortChar ( ch ) )
			{
				pxFindParams->ulFlags &= ~FIND_FLAG_FITS_SHORT;
				continue;
			}
			#if( ffconfigSHORTNAME_CASE != 0 )
			{
				if( ( ch >= 'a' ) && ( ch <= 'z' ) )
				{
					ch -= 0x20;
					if ( testAttrib )
					{
						pxFindParams->ucCaseAttrib |= testAttrib;
					}
					else
					{
						pxFindParams->ulFlags &= ~FIND_FLAG_FITS_SHORT;	/* We had capital: does not fit. */
					}
				}
				else if( ( ch >= 'A' ) && ( ch <= 'Z' ) )
				{
					if( ( pxFindParams->ucCaseAttrib & testAttrib ) != 0 )
					{
						pxFindParams->ulFlags &= ~FIND_FLAG_FITS_SHORT;	/* We had lower-case: does not fit. */
					}
					testAttrib = 0;
				}
			}
			#else
			{
				if( ( ch >= 'a' ) && ( ch <= 'z' ) )
				{
					ch -= 0x20;
				}
			}
			#endif /* ffconfigSHORTNAME_CASE */
			pxFindParams->pcEntryBuffer[ xIndex++ ] = ch;
		}
	}

	if( ( xLastDot == 0 ) && ( xIndex < 6 ) )
	{
		/* This is a file name like ".info" or ".root" */
		pxFindParams->ucFirstTilde = xIndex;
	}

	while ( xIndex < 11 )
	{
		pxFindParams->pcEntryBuffer[ xIndex++ ] = 0x20;
	}

	if( ( xLastDot < pxFindParams->ucFirstTilde ) && ( xLastDot > 0 ) )
	{
		pxFindParams->ucFirstTilde = xLastDot;
	}

	if( NameLen < pxFindParams->ucFirstTilde )	/* Names like "Abc" will become "~Abc". */
	{
		pxFindParams->ucFirstTilde = ( uint8_t ) NameLen;
	}
}	/* FF_CreateShortName() */
/*-----------------------------------------------------------*/

int32_t FF_FindShortName( FF_IOManager_t *pxIOManager, FF_FindParams_t *pxFindParams )
{
char pcMyShortName[ 13 ];
FF_DirEnt_t xMyDirectory;
FF_Error_t xResult = 0;
BaseType_t xIndex, x, y;
uint16_t NameLen;
char pcNumberBuf[ 12 ];
uint32_t ulCluster;

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	FF_T_WCHAR	pcFileName[ 13 ];
#else
	char	*pcFileName = pcMyShortName;
#endif	/* ffconfigUNICODE_UTF16_SUPPORT */

#if( ipconfigQUICK_SHORT_FILENAME_CREATION != 0 )
	uint16_t usShortHash;
	uint32_t ulRand = 0ul;
#endif

	memcpy( pcMyShortName, pxFindParams->pcEntryBuffer, 11 );
	FF_ProcessShortName( pcMyShortName );
	if( ( pxFindParams->ulFlags & FIND_FLAG_FITS_SHORT_OK ) == FIND_FLAG_FITS_SHORT_OK )
	{
		/* This entry will not get a LFN entry because it fits
		 * perfectly into a host name */
		if( ( pxFindParams->ulFlags & FIND_FLAG_SHORTNAME_CHECKED ) != 0 )
		{
			if( ( pxFindParams->ulFlags & FIND_FLAG_SHORTNAME_FOUND ) != 0 )
			{
				xResult = ( FF_Error_t ) ( FF_ERR_DIR_OBJECT_EXISTS | FF_CREATESHORTNAME );
			}
			else
			{
				xResult = pxFindParams->ucCaseAttrib | 0x01;
			}
		}
		else
		{
			#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
			{
				memcpy( pcFileName, pcMyShortName, sizeof( pcMyShortName ) );
				FF_ShortNameExpand( pcFileName );
			}
			#endif
			ulCluster = FF_FindEntryInDir( pxIOManager, pxFindParams, pcFileName, 0x00, &xMyDirectory, &xResult );

			/* END_OF_DIR is not a fatal error, it only means that the entry was not found. */
			if( ( FF_isERR( xResult ) == pdFALSE ) || ( FF_GETERROR( xResult ) == FF_ERR_DIR_END_OF_DIR ) )
			{
				if( ulCluster == 0UL )
				{
					xResult = pxFindParams->ucCaseAttrib | 0x01;
				}
				else
				{
					xResult = ( FF_Error_t ) ( FF_ERR_DIR_OBJECT_EXISTS | FF_CREATESHORTNAME );
				}
			}
			else
			{
				/* There was an error, which will be returned. */
			}
		}
	}
	else
	{
		for( xIndex = ( ( pxFindParams->ulFlags & FIND_FLAG_SIZE_OK ) ? 0 : 1 ); ; xIndex++ )
		{
			if( xIndex != 0 )
			{
				#if( ipconfigQUICK_SHORT_FILENAME_CREATION != 0 )
				{
					/* In the first round, check if the original name can be used
					Makefile will be stored as "makefile" and not as "makefi~1". */

					/* This method saves a lot of time when creating directories with
					many similar file names: when the short name version of a LFN already
					exists, try at most 3 entries with a tilde:
						README~1.TXT
						README~2.TXT
						README~3.TXT
					After that create entries with pseudo-random 4-digit hex digits:
						REA~E7BB.TXT
						REA~BA32.TXT
						REA~D394.TXT
					*/
					if( xIndex <= 4 )
					{
						snprintf( pcNumberBuf, sizeof( pcNumberBuf ), "%d", ( int ) xIndex );
					}
					else
					{
						if( ulRand == 0ul )
						{
							ulRand = pxIOManager->xPartition.ulLastFreeCluster;
							usShortHash = FF_GetCRC16( ( uint8_t *)&ulRand, sizeof( ulRand ) );
						}
						else
						{
							usShortHash = FF_GetCRC16( ( uint8_t *)&usShortHash, sizeof( usShortHash ) );
						}
						snprintf( pcNumberBuf, sizeof( pcNumberBuf ), "%04X", ( int ) usShortHash );
					}
				}
				#else
				{
					snprintf( pcNumberBuf, sizeof( pcNumberBuf ), "%d", ( int ) xIndex );
				}
				#endif

				NameLen = ( uint16_t ) strlen( pcNumberBuf );
				x = 7 - NameLen;
				if ( x > pxFindParams->ucFirstTilde )
				{
					x = pxFindParams->ucFirstTilde;
				}
				pxFindParams->pcEntryBuffer[ x++ ] = '~';
				for( y = 0; y < NameLen; y++ )
				{
					pxFindParams->pcEntryBuffer[ x + y ] = pcNumberBuf[ y ];
				}
			}
			memcpy( pcMyShortName, pxFindParams->pcEntryBuffer, 11 );
			FF_ProcessShortName( pcMyShortName );
			if( FF_ShortNameExists( pxIOManager, pxFindParams->ulDirCluster, pcMyShortName, &xResult ) == pdFALSE )
			{
				break;
			}
			if( xIndex >= FF_MAX_ENTRIES_PER_DIRECTORY )
			{
				xResult = ( FF_Error_t ) ( FF_ERR_DIR_DIRECTORY_FULL | FF_CREATESHORTNAME );
				break;
			}
		}
		/* Add a tail and special number until we're happy :D. */
	}

	return xResult;
}	/* FF_FindShortName () */
/*-----------------------------------------------------------*/


#if( ffconfigLFN_SUPPORT != 0 )
	static int8_t FF_CreateLFNEntry( uint8_t *pucEntryBuffer, uint8_t *pcName, UBaseType_t uxNameLength, UBaseType_t uxLFN, uint8_t ucCheckSum )
	{
		/*
		 *	HT for JW:
		 *	Changed *pcName from 16- to of 8-bits
		 *	The caller of this function doesn't need an expensive
		 *	uint16_t usUtf16Name[ffconfigMAX_FILENAME + 1];
		 *  in case UNICODE isn't used
		 *  Also did quite a bit of optimisation here
		 *  and tested well
		 */
		UBaseType_t uxIndex, x;

		memset( pucEntryBuffer, 0, FF_SIZEOF_DIRECTORY_ENTRY );

		FF_putChar( pucEntryBuffer, FF_FAT_LFN_ORD, ( uint8_t )( ( uxLFN & ~0x40 ) ) );
		FF_putChar( pucEntryBuffer, FF_FAT_DIRENT_ATTRIB, ( uint8_t ) FF_FAT_ATTR_LFN );
		FF_putChar( pucEntryBuffer, FF_FAT_LFN_CHECKSUM, ( uint8_t ) ucCheckSum );

		/* Name_1. */
		uxIndex = 0;
		for( x = FF_FAT_LFN_NAME_1; uxIndex < 5u; uxIndex++, x += 2 )
		{
			if( uxIndex < uxNameLength )
			{
				pucEntryBuffer[ x ] = *( pcName++ );
				#if( ffconfigUNICODE_UTF16_SUPPORT != 0 ) || ( ffconfigUNICODE_UTF8_SUPPORT != 0 )
				{
					pucEntryBuffer[ x + 1 ] = *( pcName++ );
				}
				#endif
			}
			else if ( uxIndex > uxNameLength )
			{
				pucEntryBuffer[ x] = 0xFF;
				pucEntryBuffer[ x + 1 ] = 0xFF;
			}
		}

		/* Name_2. */
		for( x = FF_FAT_LFN_NAME_2; uxIndex < 11u; uxIndex++, x += 2 )
		{
			if( uxIndex < uxNameLength )
			{
				pucEntryBuffer[ x ] = *( pcName++ );
				#if( ffconfigUNICODE_UTF16_SUPPORT != 0 ) || ( ffconfigUNICODE_UTF8_SUPPORT != 0 )
				{
					pucEntryBuffer[ x + 1 ] = *( pcName++ );
				}
				#endif
			}
			else if( uxIndex > uxNameLength )
			{
				pucEntryBuffer[ x ] = 0xFF;
				pucEntryBuffer[ x + 1 ] = 0xFF;
			}
		}

		/* Name_3. */
		for( x = FF_FAT_LFN_NAME_3; uxIndex < 13u; uxIndex++, x += 2 )
		{
			if( uxIndex < uxNameLength )
			{
				pucEntryBuffer[ x ] = *( pcName++ );
				#if( ffconfigUNICODE_UTF16_SUPPORT != 0 ) || ( ffconfigUNICODE_UTF8_SUPPORT != 0 )
				{
					pucEntryBuffer[ x + 1 ] = *( pcName++ );
				}
				#endif
			}
			else if( uxIndex > uxNameLength )
			{
				pucEntryBuffer[ x ] = 0xFF;
				pucEntryBuffer[ x + 1 ] = 0xFF;
			}
		}

		return FF_ERR_NONE;
	}	/* FF_CreateLFNEntry() */
#endif /* ffconfigLFN_SUPPORT */
/*-----------------------------------------------------------*/

#if( ffconfigLFN_SUPPORT != 0 )
	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	static FF_Error_t FF_CreateLFNs( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster, FF_T_WCHAR *pcName, uint8_t ucCheckSum, uint16_t usEntry )
	#else
	static FF_Error_t FF_CreateLFNs( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster, char *pcName, uint8_t ucCheckSum, uint16_t usEntry )
	#endif
	{
	FF_Error_t xError = FF_ERR_NONE;
	BaseType_t xNumLFNs;
	BaseType_t xEndPos;
	BaseType_t xIndex, y;
	FF_FetchContext_t xFetchContext;
	uint8_t pucEntryBuffer[ FF_SIZEOF_DIRECTORY_ENTRY ];

	#if ( ffconfigUNICODE_UTF8_SUPPORT != 0 )
		int32_t slRetVal;
	#endif

	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 ) || ( ffconfigUNICODE_UTF8_SUPPORT != 0 )
		uint16_t usUtf16Name[ ffconfigMAX_FILENAME + 1 ];
	#endif

	#if( ffconfigUNICODE_UTF16_SUPPORT == 0 )
		char *NamePtr;
	#else
		int16_t *NamePtr;
	#endif


		#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
		{
			#if WCHAR_MAX <= 0xFFFF
			{
				y = wcslen( pcName );
				if( y > ffconfigMAX_FILENAME )
				{
					xError = ( FF_Error_t ) ( FF_ERR_DIR_NAME_TOO_LONG | FF_CREATELFNS );
				}
				else
				{
					wcsncpy( usUtf16Name, pcName, ffconfigMAX_FILENAME );
				}
			}
			#else
			{
				xIndex = 0;
				y = 0;
				while( pcName[ xIndex ] )
				{
					FF_Utf32ctoUtf16c( &usUtf16Name[ y ], ( uint32_t ) pcName[xIndex], ffconfigMAX_FILENAME - xIndex );
					y += FF_GetUtf16SequenceLen( usUtf16Name[ y ] );
					xIndex++;
					if( y > ffconfigMAX_FILENAME )
					{
						xError = ( FF_Error_t ) ( FF_ERR_DIR_NAME_TOO_LONG | FF_CREATELFNS );
						break;
					}
				}
			}
			#endif
		}
		#endif /* ffconfigUNICODE_UTF16_SUPPORT */

		/* Convert the name into UTF-16 format. */
		#if ( ffconfigUNICODE_UTF8_SUPPORT != 0 )
		{
			/* Simply convert the UTF8 to UTF16 and be done with it. */
			xIndex = 0;
			y = 0;
			while( pcName[ xIndex ] != 0 )
			{
				slRetVal = FF_Utf8ctoUtf16c( &( usUtf16Name[ y ] ), ( uint8_t * )&( pcName[ xIndex ] ), ffconfigMAX_FILENAME - xIndex );
				if( slRetVal > 0 )
				{
					xIndex += slRetVal;
				}
				else
				{
					break;	/* No more space in the UTF-16 buffer, simply truncate for safety. */
				}
				y += FF_GetUtf16SequenceLen( usUtf16Name[ y ] );
				if( y > ffconfigMAX_FILENAME )
				{
					xError = ( FF_Error_t ) ( FF_ERR_DIR_NAME_TOO_LONG | FF_CREATELFNS );
					break;
				}
			}
		}
		#elif ( ffconfigUNICODE_UTF16_SUPPORT == 0 )
		{
			/* Just check the length. */
			y = strlen( pcName );
			if( y > ffconfigMAX_FILENAME )
			{
				xError = ( FF_Error_t ) ( FF_ERR_DIR_NAME_TOO_LONG | FF_CREATELFNS );
			}
		}
		#endif

		/* Whole name is now in a valid UTF-16 format. Lets go make thos LFN's.
		At this point, it should a be the length of the name. */
		if( FF_isERR( xError ) == pdFALSE )
		{
			xNumLFNs	= y / 13;	/* Number of LFNs is the total number of UTF-16 units, divided by 13 ( 13 units per LFN ). */
			xEndPos	= y % 13;	/* The ending position in an LFN, of the last LFN UTF-16 character. */

			if( xEndPos )
			{
				xNumLFNs++;
			}
			else
			{
				xEndPos = 13;
			}

			xError = FF_InitEntryFetch( pxIOManager, ulDirCluster, &xFetchContext );
			if( FF_isERR( xError ) == pdFALSE )
			{
				#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
				{
					NamePtr = ( int16_t * ) ( usUtf16Name + 13 * ( xNumLFNs - 1 ) );
				}
				#elif ( ffconfigUNICODE_UTF8_SUPPORT != 0 )
				{
					NamePtr = ( int8_t * ) ( usUtf16Name + 13 * ( xNumLFNs - 1 ) );
				}
				#else
				{
					NamePtr = pcName + 13 * ( xNumLFNs - 1 );
				}
				#endif
				/* After this point, xIndex is no longer the length of the Filename in UTF-16 units. */
				for( xIndex = xNumLFNs; xIndex > 0; xIndex-- )
				{
					if( xIndex == xNumLFNs )
					{
						FF_CreateLFNEntry( pucEntryBuffer, ( uint8_t * ) NamePtr, ( UBaseType_t ) xEndPos, ( UBaseType_t ) xIndex, ucCheckSum );
						pucEntryBuffer[0] |= 0x40;
					}
					else
					{
						FF_CreateLFNEntry( pucEntryBuffer, ( uint8_t * ) NamePtr, ( UBaseType_t ) 13u, ( UBaseType_t ) xIndex, ucCheckSum );
					}
					NamePtr -= 13;

					xError = FF_PushEntryWithContext( pxIOManager, ( uint32_t ) ( usEntry + ( xNumLFNs - xIndex ) ), &xFetchContext, pucEntryBuffer );
					if( FF_isERR( xError ) )
					{
						break;
					}
				}

				{
				FF_Error_t xTempError;

					/* Release any buffers that were used. */
					xTempError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
					if( FF_isERR( xTempError ) == pdFALSE )
					{
						xError = xTempError;
					}
				}
			}
		}

		return xError;
	}	/* FF_CreateLFNs() */
#endif /* ffconfigLFN_SUPPORT */
/*-----------------------------------------------------------*/

FF_Error_t FF_ExtendDirectory( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster )
{
uint32_t xCurrentCluster;
uint32_t xNextCluster = 0UL;
FF_Error_t xError = FF_ERR_NONE;
FF_FATBuffers_t xFATBuffers;

	if( ( ulDirCluster == pxIOManager->xPartition.ulRootDirCluster ) &&
		( pxIOManager->xPartition.ucType != FF_T_FAT32 ) )
	{
		/* root directories on FAT12 and FAT16 can not be extended. */
		xError = ( FF_Error_t ) ( FF_ERR_DIR_CANT_EXTEND_ROOT_DIR | FF_EXTENDDIRECTORY );
	}
	else if( pxIOManager->xPartition.ulFreeClusterCount == 0UL )
	{
		/* The number of free clusters was not yet calculated or equal to zero. */
		pxIOManager->xPartition.ulFreeClusterCount = FF_CountFreeClusters( pxIOManager, &xError );
	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		if( pxIOManager->xPartition.ulFreeClusterCount == 0UL )
		{
			xError = ( FF_Error_t ) ( FF_ERR_FAT_NO_FREE_CLUSTERS | FF_EXTENDDIRECTORY );
		}
		else
		{
			FF_LockFAT( pxIOManager );
			{
				xCurrentCluster = FF_FindEndOfChain( pxIOManager, ulDirCluster, &xError );
				if( FF_isERR( xError ) == pdFALSE )
				{
					xNextCluster = FF_FindFreeCluster( pxIOManager, &xError, pdTRUE );
					if( FF_isERR( xError ) == pdFALSE )
					{
						FF_InitFATBuffers ( &xFATBuffers, FF_MODE_WRITE );
						/* xNextCluster already has been set to 0xFFFFFFFF,
						now let xCurrentCluster point to xNextCluster. */

						xError = FF_putFATEntry( pxIOManager, xCurrentCluster, xNextCluster, &xFATBuffers );
						{
						FF_Error_t xTempError;

							xTempError = FF_ReleaseFATBuffers( pxIOManager, &xFATBuffers );
							if( FF_isERR( xError ) == pdFALSE )
							{
								xError = xTempError;
							}

							xTempError = FF_DecreaseFreeClusters( pxIOManager, 1 );
							if( FF_isERR( xError ) == pdFALSE )
							{
								xError = xTempError;
							}
						}
					}
				}
			}
			FF_UnlockFAT( pxIOManager );

			if( FF_isERR( xError ) == pdFALSE )
			{
				/* The entire cluster will be filled with zero's,
				because it will contain directory data. */
				xError = FF_ClearCluster( pxIOManager, xNextCluster );
			}
		}
	}

	return xError;
}	/* FF_ExtendDirectory() */
/*-----------------------------------------------------------*/

static const uint8_t forbiddenChrs[] =
{
/* Windows says: don't use these characters: '\/:*?"<>|'
    "     *     /	    :     <     >     ?    '\'    ?     | */
	0x22, 0x2A, 0x2F, 0x3A, 0x3C, 0x3E, 0x3F, 0x5C, 0x7F, 0x7C
};

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
static void FF_MakeNameCompliant( FF_T_WCHAR *pcName )
#else
static void FF_MakeNameCompliant( char *pcName )
#endif
{
	BaseType_t index;
	if( ( uint8_t ) pcName[ 0 ] == FF_FAT_DELETED )	/* Support Japanese KANJI symbol0xE5. */
	{
		pcName[ 0 ] = 0x05;
	}
	for( ; *pcName; pcName++ )
	{
		for( index = 0; index < ( BaseType_t ) sizeof( forbiddenChrs ); index++ )
		{
			if( *pcName == forbiddenChrs[index] )
			{
				*pcName = '_';
				break;
			}
		}
	}
}	/* FF_MakeNameCompliant() */
/*-----------------------------------------------------------*/

FF_Error_t FF_CreateDirent( FF_IOManager_t *pxIOManager, FF_FindParams_t *pxFindParams, FF_DirEnt_t *pxDirEntry )
{
uint8_t	pucEntryBuffer[ FF_SIZEOF_DIRECTORY_ENTRY ];

BaseType_t xLFNCount;
int32_t	lFreeEntry = 0L;
FF_Error_t xReturn = FF_ERR_NONE;
BaseType_t xEntryCount;
FF_FetchContext_t xFetchContext;
uint32_t	ulDirCluster = pxFindParams->ulDirCluster;
int32_t lFitShort;

#if( ffconfigHASH_CACHE != 0 )
	char pcShortName[ 13 ];
#endif
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	uint16_t NameLen = ( uint16_t ) wcslen( pxDirEntry->pcFileName );
#else
	uint16_t NameLen = ( uint16_t ) strlen( pxDirEntry->pcFileName );
#endif

#if( ffconfigLFN_SUPPORT != 0 )
	uint8_t	ucCheckSum;
#endif

	/* Round-up the number of LFN's needed: */
	xLFNCount = ( BaseType_t ) ( ( NameLen + 12 ) / 13 );

	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	{
		FF_MakeNameCompliant( pxDirEntry->pcFileName );	/* Ensure we don't break the Dir tables. */
	}
	#else
	{
		FF_MakeNameCompliant( pxDirEntry->pcFileName );	/* Ensure we don't break the Dir tables. */
	}
	#endif
	memset( pucEntryBuffer, 0, sizeof( pucEntryBuffer ) );

	#if( ffconfigLFN_SUPPORT != 0 )
	{
		/* Create and push the LFN's. */
		/* Find enough places for the LFNs and the ShortName. */
		xEntryCount = xLFNCount + 1;
	}
	#else
	{
		xEntryCount = 1;
	}
	#endif

	/* Create the ShortName. */
	FF_LockDirectory( pxIOManager );
	do
	{
		/* Open a do {} while( pdFALSE ) loop to allow the use of break statements. */
		/* As FF_FindShortName( ) can fail, it should be called before finding a free directory entry. */
		if( ( pxFindParams->ulFlags & FIND_FLAG_SHORTNAME_SET ) == 0 )
		{
			FF_CreateShortName( pxFindParams, pxDirEntry->pcFileName );
		}
		lFitShort = FF_FindShortName ( pxIOManager, pxFindParams );

		memcpy( pucEntryBuffer, pxFindParams->pcEntryBuffer, sizeof( pucEntryBuffer ) );

		if( FF_isERR( lFitShort ) )
		{
			xReturn = lFitShort;
			break;
		}
		if( lFitShort != 0 )
		{
			/* There is no need to create a LFN entry because the file name
			fits into a normal 32-byte entry.. */
			xLFNCount = 0;
			xEntryCount = 1;
		}
		lFreeEntry = FF_FindFreeDirent( pxIOManager, pxFindParams, ( uint16_t ) xEntryCount );

		if( FF_isERR( lFreeEntry ) )
		{
			xReturn = lFreeEntry;
			break;
		}
		#if( ffconfigLFN_SUPPORT != 0 )
		{
			if( xLFNCount > 0 )
			{
				ucCheckSum = FF_CreateChkSum( pucEntryBuffer );
				xReturn = FF_CreateLFNs( pxIOManager, ulDirCluster, pxDirEntry->pcFileName, ucCheckSum, ( uint16_t ) lFreeEntry );
			}
		}
		#else
		{
			xLFNCount = 0;
		}
		#endif /* ffconfigLFN_SUPPORT */
		if( FF_isERR( xReturn ) == pdFALSE )
		{
			#if( ffconfigTIME_SUPPORT != 0 )
			{
				FF_GetSystemTime( &pxDirEntry->xCreateTime );		/* Date and Time Created. */
				pxDirEntry->xModifiedTime = pxDirEntry->xCreateTime;	/* Date and Time Modified. */
				pxDirEntry->xAccessedTime = pxDirEntry->xCreateTime;	/* Date of Last Access. */
				FF_PlaceTime( pucEntryBuffer, FF_FAT_DIRENT_CREATE_TIME, &pxDirEntry->xCreateTime );
				FF_PlaceDate( pucEntryBuffer, FF_FAT_DIRENT_CREATE_DATE, &pxDirEntry->xCreateTime );
				FF_PlaceTime( pucEntryBuffer, FF_FAT_DIRENT_LASTMOD_TIME, &pxDirEntry->xModifiedTime );
				FF_PlaceDate( pucEntryBuffer, FF_FAT_DIRENT_LASTMOD_DATE, &pxDirEntry->xModifiedTime );
			}
			#endif /*  ffconfigTIME_SUPPORT */

			FF_putChar( pucEntryBuffer,  FF_FAT_DIRENT_ATTRIB, pxDirEntry->ucAttrib );
		#if( ffconfigSHORTNAME_CASE != 0 )
			FF_putChar( pucEntryBuffer,  FF_FAT_CASE_OFFS, ( uint32_t ) lFitShort & ( FF_FAT_CASE_ATTR_BASE | FF_FAT_CASE_ATTR_EXT ) );
		#endif
			FF_putShort( pucEntryBuffer, FF_FAT_DIRENT_CLUS_HIGH, ( uint16_t )( pxDirEntry->ulObjectCluster >> 16 ) );
			FF_putShort( pucEntryBuffer, FF_FAT_DIRENT_CLUS_LOW, ( uint16_t )( pxDirEntry->ulObjectCluster ) );
			FF_putLong( pucEntryBuffer,  FF_FAT_DIRENT_FILESIZE, pxDirEntry->ulFileSize );

			xReturn = FF_InitEntryFetch( pxIOManager, ulDirCluster, &xFetchContext );
			if( FF_isERR( xReturn ) )
			{
				break;
			}
			xReturn = FF_PushEntryWithContext( pxIOManager, ( uint16_t ) ( lFreeEntry + xLFNCount ), &xFetchContext, pucEntryBuffer );

			{
			FF_Error_t xTempError;

				xTempError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
				if( FF_isERR( xReturn ) == pdFALSE )
				{
					xReturn = xTempError;
				}
			}
			if( FF_isERR( xReturn ) )
			{
				break;
			}

			#if( ffconfigHASH_CACHE != 0 )
			{
				if( FF_DirHashed( pxIOManager, ulDirCluster ) == pdFALSE )
				{
					/* Hash the directory. */
					FF_HashDir( pxIOManager, ulDirCluster );
				}
				memcpy( pcShortName, pucEntryBuffer, 11 );
				FF_ProcessShortName( pcShortName );		/* Format the shortname to 8.3. */
				#if( ffconfigHASH_FUNCTION == CRC16 )
				{
					FF_AddDirentHash( pxIOManager, ulDirCluster, ( uint32_t )FF_GetCRC16( ( uint8_t * ) pcShortName, strlen( pcShortName ) ) );
				}
				#elif( ffconfigHASH_FUNCTION == CRC8 )
				{
					FF_AddDirentHash( pxIOManager, ulDirCluster, ( uint32_t )FF_GetCRC8( ( uint8_t * ) pcShortName, strlen( pcShortName ) ) );
				}
				#endif /* ffconfigHASH_FUNCTION */
			}
			#endif /* ffconfigHASH_CACHE*/
		}
	}
	while( pdFALSE );

	FF_UnlockDirectory( pxIOManager );

	if( FF_isERR( xReturn ) == pdFALSE )
	{
		if( pxDirEntry != NULL )
		{
			pxDirEntry->usCurrentItem = ( uint16_t )( lFreeEntry + xLFNCount );
		}
	}

	return xReturn;
}	/* FF_CreateDirent() */
/*-----------------------------------------------------------*/


#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
uint32_t FF_CreateFile( FF_IOManager_t *pxIOManager, FF_FindParams_t *pxFindParams, FF_T_WCHAR *pcFileName, FF_DirEnt_t *pxDirEntry, FF_Error_t *pxError )
#else
uint32_t FF_CreateFile( FF_IOManager_t *pxIOManager, FF_FindParams_t *pxFindParams, char *pcFileName, FF_DirEnt_t *pxDirEntry, FF_Error_t *pxError )
#endif
{
FF_DirEnt_t xMyFile;
FF_Error_t xTempError, xError = FF_ERR_NONE;
uint32_t ulResult;

	memset ( &xMyFile, '\0', sizeof( xMyFile ) );

	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	{
		wcsncpy( xMyFile.pcFileName, pcFileName, ffconfigMAX_FILENAME );
	}
	#else
	{
		strncpy( xMyFile.pcFileName, pcFileName, ffconfigMAX_FILENAME );
	}
	#endif

	xMyFile.ulObjectCluster = FF_CreateClusterChain( pxIOManager, &xError );

	if( FF_isERR( xError ) == pdFALSE )
	{
		xError = FF_CreateDirent( pxIOManager, pxFindParams, &xMyFile );
		if( FF_isERR( xError ) == pdFALSE )
		{
			/* The new file now has a cluster chain and it has an entry
			in its directory.  Copy data to a pointer provided by caller: */
			if( pxDirEntry != NULL )
			{
				memcpy( pxDirEntry, &xMyFile, sizeof( FF_DirEnt_t ) );
			}
		}
		else
		{
			/* An error occurred in FF_CreateDirent().
			Unlink the file's cluster chain: */
			FF_LockFAT( pxIOManager );
			{
				FF_UnlinkClusterChain( pxIOManager, xMyFile.ulObjectCluster, 0 );
				xMyFile.ulObjectCluster = 0ul;
			}
			FF_UnlockFAT( pxIOManager );
		}
		/* Now flush all buffers to disk. */
		xTempError = FF_FlushCache( pxIOManager );
		if( FF_isERR( xError ) == pdFALSE )
		{
			xError = xTempError;
		}
	}

	*pxError = xError;

	if( FF_isERR( xError ) == pdFALSE )
	{
		ulResult = xMyFile.ulObjectCluster;
	}
	else
	{
		ulResult = 0;
	}

	return ulResult;
}	/* FF_CreateFile() */
/*-----------------------------------------------------------*/


/**
 *	@brief Creates a Directory of the specified path.
 *
 *	@param	pxIOManager	Pointer to the FF_IOManager_t object.
 *	@param	pcPath	Path of the directory to create.
 *
 *	@Return	FF_ERR_NULL_POINTER if pxIOManager was NULL.
 *	@Return FF_ERR_DIR_OBJECT_EXISTS if the object specified by path already exists.
 *	@Return	FF_ERR_DIR_INVALID_PATH
 *	@Return FF_ERR_NONE on success.
 **/
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
FF_Error_t FF_MkDir( FF_IOManager_t *pxIOManager, const FF_T_WCHAR *pcPath )
#else
FF_Error_t FF_MkDir( FF_IOManager_t *pxIOManager, const char *pcPath )
#endif
{
FF_DirEnt_t	xMyDirectory;

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	const FF_T_WCHAR *pcDirName;
#else
	const char	*pcDirName;
#endif
uint8_t	pucEntryBuffer[ FF_SIZEOF_DIRECTORY_ENTRY ];
uint32_t ulObjectCluster;
BaseType_t xIndex;
FF_Error_t xError = FF_ERR_NONE;

FF_FindParams_t xFindParams;

	memset ( &xFindParams, '\0', sizeof( xFindParams ) );
	/* Inform the functions that the entry will be created if not found */
	xFindParams.ulFlags |= FIND_FLAG_CREATE_FLAG;

	/* Open a do {} while ( pdFALSE ) loop */
	do
	{
		if( pxIOManager == NULL )
		{
			xError = ( FF_Error_t ) ( FF_ERR_NULL_POINTER | FF_MKDIR );
			break;
		}
#if( ffconfigREMOVABLE_MEDIA != 0 )
		if( ( pxIOManager->ucFlags & FF_IOMAN_DEVICE_IS_EXTRACTED ) != 0 )
		{
			xError = ( FF_Error_t ) ( FF_ERR_IOMAN_DRIVER_NOMEDIUM | FF_MKDIR );
			break;
		}
#endif /* ffconfigREMOVABLE_MEDIA */

		#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
		{
			xIndex = ( BaseType_t ) wcslen( pcPath );
		}
		#else
		{
			xIndex = ( BaseType_t ) strlen( pcPath );
		}
		#endif

		/* Find the last slash in the path. */
		while( xIndex != 0 )
		{
			if( ( pcPath[ xIndex ] == '\\' ) || ( pcPath[ xIndex ] == '/' ) )
			{
				break;
			}
			xIndex--;
		}

		pcDirName = pcPath + xIndex + 1;

		if( xIndex == 0 )
		{
			xIndex = 1;
		}

		if( pcDirName[ 0 ] == '\0' )
		{
			xError = ( FF_ERR_DIR_OBJECT_EXISTS | FF_MKDIR );
			break;
		}

		xFindParams.ulDirCluster = FF_FindDir( pxIOManager, pcPath, ( uint16_t ) xIndex, &xError );

		if( FF_isERR( xError ) )
		{
			break;
		}

		if( xFindParams.ulDirCluster == 0UL )
		{
			xError = ( FF_Error_t ) ( FF_ERR_DIR_INVALID_PATH | FF_MKDIR );
			break;
		}
		memset( &xMyDirectory, '\0', sizeof( xMyDirectory ) );

		/* Will set flags FIND_FLAG_FITS_SHORT and FIND_FLAG_SIZE_OK */
		FF_CreateShortName( &xFindParams, pcDirName );

		if( FF_FindEntryInDir( pxIOManager, &xFindParams, pcDirName, 0x00, &xMyDirectory, &xError ) )
		{
			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = ( FF_Error_t ) ( FF_ERR_DIR_OBJECT_EXISTS | FF_MKDIR );
			}
			break;
		}

		if( ( FF_isERR( xError ) ) && ( FF_GETERROR( xError ) != FF_ERR_DIR_END_OF_DIR ) )
		{
			break;
		}

		#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
		{
			wcsncpy( xMyDirectory.pcFileName, pcDirName, ffconfigMAX_FILENAME );
		}
		#else
		{
			strncpy( xMyDirectory.pcFileName, pcDirName, ffconfigMAX_FILENAME );
		}
		#endif

		xMyDirectory.ulFileSize = 0;
		xMyDirectory.ucAttrib = FF_FAT_ATTR_DIR;
		xMyDirectory.ulObjectCluster = FF_CreateClusterChain( pxIOManager, &xError );

		/* Give all entries a proper time stamp, looks nicer than 1 Jan 1970 */
		#if( ffconfigTIME_SUPPORT != 0 )
		{
			FF_GetSystemTime( &xMyDirectory.xCreateTime );
			FF_GetSystemTime( &xMyDirectory.xModifiedTime );
		}
		#endif

		if( FF_isERR( xError ) )
		{
			break;
		}
		if( xMyDirectory.ulObjectCluster == 0UL )
		{
			/* Couldn't allocate any space for the dir! */
			xError = ( FF_Error_t ) ( FF_ERR_DIR_EXTEND_FAILED | FF_MKDIR );
			break;
		}

		xError = FF_ClearCluster( pxIOManager, xMyDirectory.ulObjectCluster );
		if( FF_isERR( xError ) == pdFALSE )
		{
			xError = FF_CreateDirent( pxIOManager, &xFindParams, &xMyDirectory );
		}

		if( FF_isERR( xError ) )
		{
			FF_LockFAT( pxIOManager );
			{
				FF_UnlinkClusterChain( pxIOManager, xMyDirectory.ulObjectCluster, 0 );
			}
			FF_UnlockFAT( pxIOManager );
			FF_FlushCache( pxIOManager );	/* Don't override error. */
			break;
		}

		/* Write 8.3 entry "." */
		pucEntryBuffer[ 0 ] = '.';
		/* folowed by 10 spaces: */
		memset( pucEntryBuffer + 1, ' ', 10 );
		/* Clear the rest of the structure. */
		memset( pucEntryBuffer + 11, 0, FF_SIZEOF_DIRECTORY_ENTRY - 11 );

		ulObjectCluster = xMyDirectory.ulObjectCluster;
		xError = FF_PutEntry( pxIOManager, ( uint16_t ) 0u, ulObjectCluster, &xMyDirectory, pucEntryBuffer );

		if( FF_isERR( xError ) == pdFALSE )
		{
			pucEntryBuffer[ 1 ] = '.';

			if( xFindParams.ulDirCluster == pxIOManager->xPartition.ulRootDirCluster )
			{
				xMyDirectory.ulObjectCluster = 0;
			}
			else
			{
				xMyDirectory.ulObjectCluster = xFindParams.ulDirCluster;
			}
			xError = FF_PutEntry( pxIOManager, 1u, ulObjectCluster, &xMyDirectory, pucEntryBuffer );

			xMyDirectory.ulObjectCluster = ulObjectCluster;
		}

		if( FF_isERR( xError ) )
		{
			FF_LockFAT( pxIOManager );
			{
				FF_UnlinkClusterChain( pxIOManager, xMyDirectory.ulObjectCluster, 0 );
			}
			FF_UnlockFAT( pxIOManager );
		}
		FF_FlushCache( pxIOManager );
	}
	while( pdFALSE );

	return xError;
}	/* FF_MkDir() */
/*-----------------------------------------------------------*/


FF_Error_t FF_RmLFNs( FF_IOManager_t *pxIOManager, uint16_t usDirEntry, FF_FetchContext_t *pxContext )
{
FF_Error_t xError = FF_ERR_NONE;
uint8_t	pucEntryBuffer[ FF_SIZEOF_DIRECTORY_ENTRY ];

	if( usDirEntry != 0 )
	{
		usDirEntry--;

		do
		{
			xError = FF_FetchEntryWithContext( pxIOManager, usDirEntry, pxContext, pucEntryBuffer );
			if( FF_isERR( xError ) )
			{
				break;
			}

			if( FF_getChar( pucEntryBuffer, ( uint16_t )( FF_FAT_DIRENT_ATTRIB ) ) == FF_FAT_ATTR_LFN )
			{
				FF_putChar( pucEntryBuffer, ( uint16_t ) 0, ( uint8_t ) FF_FAT_DELETED );
				xError = FF_PushEntryWithContext( pxIOManager, usDirEntry, pxContext, pucEntryBuffer );
				if( FF_isERR( xError ) )
				{
					break;
				}
			}

			if( usDirEntry == 0 )
			{
				break;
			}
			usDirEntry--;
		} while( FF_getChar( pucEntryBuffer, ( uint16_t )( FF_FAT_DIRENT_ATTRIB ) ) == FF_FAT_ATTR_LFN );
	}

	return xError;
}	/* FF_RmLFNs() */
/*-----------------------------------------------------------*/

#if( ffconfigHASH_CACHE != 0 )
	FF_Error_t FF_HashDir( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster )
	{
		/* Find most suitable Hash Table to replace! */
	BaseType_t xIndex;
	FF_HashTable_t *pxHashCache = NULL;
	FF_FetchContext_t xFetchContext;
	const uint8_t *pucEntryBuffer = NULL;
	uint8_t ucAttrib;
	uint32_t ulHash;
	FF_Error_t xError;

		for( xIndex = 0; xIndex < ffconfigHASH_CACHE_DEPTH; xIndex++ )
		{
			if( pxIOManager->xHashCache[ xIndex ].ulNumHandles == 0 )
			{
				if( pxHashCache == NULL )
				{
					pxHashCache = &pxIOManager->xHashCache[ xIndex ];
				}
				else
				{
					if( ( pxIOManager->xHashCache[ xIndex ].ulMisses > pxHashCache->ulMisses ) )
					{
						pxHashCache = &pxIOManager->xHashCache[ xIndex ];
					}
				}
			}
		}

		if( pxHashCache != NULL )
		{
		#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
			FF_T_WCHAR	pcMyShortName[ 13 ];
		#else
			char pcMyShortName[ 13 ];
		#endif
			/* Clear the hash table! */
			memset( pxHashCache, '\0', sizeof( *pxHashCache ) );
			pxHashCache->ulDirCluster = ulDirCluster;
			pxHashCache->ulMisses = 0;

			/* Hash the directory! */

			xError = FF_InitEntryFetch( pxIOManager, ulDirCluster, &xFetchContext );

			if( FF_isERR( xError ) == pdFALSE )
			{
				for( xIndex = 0; xIndex < FF_MAX_ENTRIES_PER_DIRECTORY; xIndex++ )
				{
					if( ( pucEntryBuffer == NULL ) ||
						( pucEntryBuffer >= xFetchContext.pxBuffer->pucBuffer + ( FF_SIZEOF_SECTOR - FF_SIZEOF_DIRECTORY_ENTRY ) ) )
					{
						xError = FF_FetchEntryWithContext( pxIOManager, ( uint32_t ) xIndex, &xFetchContext, NULL );
						if( FF_isERR( xError ) )
						{
							break;
						}
						pucEntryBuffer = xFetchContext.pxBuffer->pucBuffer;
					}
					else
					{
						/* Advance the pointer 32 bytes to the next directory entry. */
						pucEntryBuffer += FF_SIZEOF_DIRECTORY_ENTRY;
					}
					if( FF_isDeleted( pucEntryBuffer ) == pdFALSE )
					{
						ucAttrib = FF_getChar( pucEntryBuffer, FF_FAT_DIRENT_ATTRIB );
						if( ( ( ucAttrib & FF_FAT_ATTR_LFN ) != FF_FAT_ATTR_LFN ) &&
							( ( ucAttrib & FF_FAT_ATTR_VOLID ) != FF_FAT_ATTR_VOLID ) )
						{
							memcpy ( pcMyShortName, pucEntryBuffer, 11 );
							FF_ProcessShortName( pcMyShortName );
							if( FF_isEndOfDir( pucEntryBuffer ) )
							{
								break;
							}

							/* Generate the Hash. */
							#if( ffconfigHASH_FUNCTION == CRC16 )
							{
								ulHash = FF_GetCRC16( ( uint8_t * ) pcMyShortName, strlen( pcMyShortName ) );
							}
							#else /* ffconfigHASH_FUNCTION == CRC8 */
							{
								ulHash = FF_GetCRC8( pcMyShortName, strlen( pcMyShortName ) );
							}
							#endif
							FF_SetHash( pxHashCache, ulHash );
						}
					}
				} /* for( xIndex = 0; xIndex < FF_MAX_ENTRIES_PER_DIRECTORY; xIndex++ ) */
				{
				FF_Error_t xTempError;
					xTempError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
					if( FF_isERR( xError ) == pdFALSE )
					{
						xError = xTempError;
					}
				}
			}
		} /* if( pxHashCache != NULL ) */
		else
		{
			xError = -1;
		}

		return xError;
	}	/* FF_HashDir() */
#endif /* ffconfigHASH_CACHE != 0 */
/*-----------------------------------------------------------*/

#if( ffconfigHASH_CACHE != 0 )
	/* FF_UnHashDir() : invalidate the hash tables of a given directory.
	It is called when a file or sub-directory is removed or when the
	directory itself is removed. */
	void FF_UnHashDir( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster )
	{
	FF_HashTable_t *pxHash = pxIOManager->xHashCache;
	FF_HashTable_t *pxLast = pxIOManager->xHashCache + ffconfigHASH_CACHE_DEPTH;

		for( ; pxHash < pxLast; pxHash++ )
		{
			if( pxHash->ulDirCluster == ulDirCluster )
			{
				pxHash->ulDirCluster = 0;
				break;
			}
		}
	}	/* FF_UnHashDir() */
#endif /* ffconfigHASH_CACHE */
/*-----------------------------------------------------------*/

#if( ffconfigHASH_CACHE != 0 )
	/**
	 *
	 *
	 **/
	void FF_SetHash( FF_HashTable_t *pxHash, uint32_t ulHash )
	{
	uint32_t tblIndex = ( ulHash / 32 ) % FF_HASH_TABLE_ENTRY_COUNT;
	uint32_t tblBit = ulHash % 32;

		pxHash->ulBitTable[ tblIndex ] |= ( 0x80000000ul >> tblBit );
	}	/* FF_SetHash() */
#endif /* ffconfigHASH_CACHE */
/*-----------------------------------------------------------*/

#if( ffconfigHASH_CACHE != 0 )
	void FF_ClearHash( FF_HashTable_t *pxHash, uint32_t ulHash )
	{
		if( pxHash != NULL )
		{
		uint32_t tblIndex = ( ulHash / 32 ) % FF_HASH_TABLE_ENTRY_COUNT;
		uint32_t tblBit = ulHash % 32;

			pxHash->ulBitTable[ tblIndex ] &= ~( 0x80000000ul >> tblBit );
		}
	}	/* FF_ClearHash() */
#endif /* ffconfigHASH_CACHE */
/*-----------------------------------------------------------*/

#if( ffconfigHASH_CACHE != 0 )
	BaseType_t FF_isHashSet( FF_HashTable_t *pxHash, uint32_t ulHash )
	{
	FF_Error_t xResult;

		xResult = pdFALSE;

		if( pxHash != NULL )
		{
		uint32_t tblIndex = ( ulHash / 32 ) % FF_HASH_TABLE_ENTRY_COUNT;
		uint32_t tblBit = ulHash % 32;

			if( pxHash->ulBitTable[ tblIndex ] & ( 0x80000000ul >> tblBit ) )
			{
				xResult = pdTRUE;
			}
		}

		return xResult;
	}	/* FF_isHashSet() */
#endif /* ffconfigHASH_CACHE */
/*-----------------------------------------------------------*/

#if( ffconfigHASH_CACHE != 0 )
	void FF_AddDirentHash( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster, uint32_t ulHash )
	{
	FF_HashTable_t *pxHash = pxIOManager->xHashCache;
	FF_HashTable_t *pxLast = pxIOManager->xHashCache + ffconfigHASH_CACHE_DEPTH;

		for( ; pxHash < pxLast; pxHash++ )
		{
			if( pxHash->ulDirCluster == ulDirCluster )
			{
				FF_SetHash( pxHash, ulHash );
				break;
			}
		}
	}	/* FF_AddDirentHash() */
#endif /* ffconfigHASH_CACHE*/
/*-----------------------------------------------------------*/

#if( ffconfigHASH_CACHE != 0 )
	BaseType_t FF_CheckDirentHash( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster, uint32_t ulHash )
	{
	FF_HashTable_t *pxHash = pxIOManager->xHashCache;
	FF_HashTable_t *pxLast = pxIOManager->xHashCache + ffconfigHASH_CACHE_DEPTH;
	BaseType_t xResult;

		for( ; ; )
		{
			if( pxHash->ulDirCluster == ulDirCluster )
			{
				xResult = FF_isHashSet( pxHash, ulHash );
				break;
			}
			pxHash++;
			if( pxHash >= pxLast )
			{
				xResult = -1;
				break;
			}
		}

		return xResult;
	}	/* FF_CheckDirentHash() */
#endif /* ffconfigHASH_CACHE */
/*-----------------------------------------------------------*/

#if( ffconfigHASH_CACHE != 0 )
	BaseType_t FF_DirHashed( FF_IOManager_t *pxIOManager, uint32_t ulDirCluster )
	{
	FF_HashTable_t *pxHash = pxIOManager->xHashCache;
	FF_HashTable_t *pxLast = pxIOManager->xHashCache + ffconfigHASH_CACHE_DEPTH;
	BaseType_t xResult;

		for( ; ; )
		{
			if( pxHash->ulDirCluster == ulDirCluster )
			{
				xResult = pdTRUE;
				break;
			}
			pxHash++;
			if( pxHash >= pxLast )
			{
				xResult = pdFALSE;
				break;
			}
		}

		return xResult;
	}	/* FF_DirHashed() */
#endif /* ffconfigHASH_CACHE */
/*-----------------------------------------------------------*/

