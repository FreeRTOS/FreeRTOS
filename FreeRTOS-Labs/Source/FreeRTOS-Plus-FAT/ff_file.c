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
 *	@file		ff_file.c
 *	@ingroup	FILEIO
 *
 *	@defgroup	FILEIO FILE I/O Access
 *	@brief		Provides an interface to allow File I/O on a mounted IOMAN.
 *
 *	Provides file-system interfaces for the FAT file-system.
 **/

#include "ff_headers.h"

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
#include <wchar.h>
#endif

static FF_Error_t FF_Truncate( FF_FILE *pxFile, BaseType_t bClosing );

static int32_t FF_ReadPartial( FF_FILE *pxFile, uint32_t ulItemLBA, uint32_t ulRelBlockPos, uint32_t ulCount,
	uint8_t *pucBuffer, FF_Error_t *pxError );

static int32_t FF_WritePartial( FF_FILE *pxFile, uint32_t ulItemLBA, uint32_t ulRelBlockPos, uint32_t ulCount,
	const uint8_t *pucBuffer, FF_Error_t *pxError );

static uint32_t FF_SetCluster( FF_FILE *pxFile, FF_Error_t *pxError );
static uint32_t FF_FileLBA( FF_FILE *pxFile );

/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Converts STDIO mode strings into the equivalent FreeRTOS+FAT mode.
 *
 *	@param	Mode	The mode string e.g. "rb" "rb+" "w" "a" "r" "w+" "a+" etc
 *
 *	@return	Returns the mode bits that should be passed to the FF_Open function.
 **/
uint8_t FF_GetModeBits( const char *pcMode )
{
uint8_t ucModeBits = 0x00;

	while( *pcMode != '\0' )
	{
		switch( *pcMode )
		{
			case 'r':						/* Allow Read. */
			case 'R':
				ucModeBits |= FF_MODE_READ;
				break;

			case 'w':						/* Allow Write. */
			case 'W':
				ucModeBits |= FF_MODE_WRITE;
				ucModeBits |= FF_MODE_CREATE; /* Create if not exist. */
				ucModeBits |= FF_MODE_TRUNCATE;
				break;

			case 'a':						/* Append new writes to the end of the file. */
			case 'A':
				ucModeBits |= FF_MODE_WRITE;
				ucModeBits |= FF_MODE_APPEND;
				ucModeBits |= FF_MODE_CREATE; /* Create if not exist. */
				break;

			case '+':						/* Update the file, don't Append! */
				ucModeBits |= FF_MODE_READ;
				ucModeBits |= FF_MODE_WRITE;	/* RW Mode. */
				break;

			case 'D':
				/* Internal use only! */
				ucModeBits |= FF_MODE_DIR;
				break;

			case 'b':
			case 'B':
				/* b|B flags not supported (Binary mode is native anyway). */
				break;

			default:
				break;
		}

		pcMode++;
	}

	return ucModeBits;
}	/* FF_GetModeBits() */
/*-----------------------------------------------------------*/

static FF_FILE *prvAllocFileHandle( FF_IOManager_t *pxIOManager, FF_Error_t *pxError )
{
FF_FILE *pxFile;

	pxFile = ffconfigMALLOC( sizeof( FF_FILE ) );
	if( pxFile == NULL )
	{
		*pxError = ( FF_Error_t ) ( FF_ERR_NOT_ENOUGH_MEMORY | FF_OPEN );
	}
	else
	{
		memset( pxFile, 0, sizeof( *pxFile ) );

		#if( ffconfigOPTIMISE_UNALIGNED_ACCESS != 0 )
		{
			pxFile->pucBuffer = ( uint8_t * ) ffconfigMALLOC( pxIOManager->usSectorSize );
			if( pxFile->pucBuffer != NULL )
			{
				memset( pxFile->pucBuffer, 0, pxIOManager->usSectorSize );
			}
			else
			{
				*pxError = ( FF_Error_t ) ( FF_ERR_NOT_ENOUGH_MEMORY | FF_OPEN );
				ffconfigFREE( pxFile );
				/* Make sure that NULL will be returned. */
				pxFile = NULL;
			}
		}
		#else
		{
			/* Remove compiler warnings. */
			( void ) pxIOManager;
		}
		#endif
	}

	return pxFile;
}	/* prvAllocFileHandle() */
/*-----------------------------------------------------------*/

/**
 * FF_Open() Mode Information
 * - FF_MODE_WRITE
 *   - Allows WRITE access to the file.
 *   .
 * - FF_MODE_READ
 *   - Allows READ access to the file.
 *   .
 * - FF_MODE_CREATE
 *   - Create file if it doesn't exist.
 *   .
 * - FF_MODE_TRUNCATE
 *   - Erase the file if it already exists and overwrite.
 *   *
 * - FF_MODE_APPEND
 *   - Causes all writes to occur at the end of the file. (Its impossible to overwrite other data in a file with this flag set).
 *   .
 * .
 *
 * Some sample modes:
 * - (FF_MODE_WRITE | FF_MODE_CREATE | FF_MODE_TRUNCATE)
 *   - Write access to the file. (Equivalent to "w").
 *   .
 * - (FF_MODE_WRITE | FF_MODE_READ)
 *   - Read and Write access to the file. (Equivalent to "rb+").
 *   .
 * - (FF_MODE_WRITE | FF_MODE_READ | FF_MODE_APPEND | FF_MODE_CREATE)
 *   - Read and Write append mode access to the file. (Equivalent to "a+").
 *   .
 * .
 * Be careful when choosing modes. For those using FF_Open() at the application layer
 * its best to use the provided FF_GetModeBits() function, as this complies to the same
 * behaviour as the stdio.h fopen() function.
 *
 **/

/**
 *	@public
 *	@brief	Opens a File for Access
 *
 *	@param	pxIOManager	FF_IOManager_t object that was created by FF_CreateIOManger().
 *	@param	pcPath		Path to the File or object.
 *	@param	ucMode		Access Mode required. Modes are a little complicated, the function FF_GetModeBits()
 *	@param	ucMode		will convert a stdio Mode string into the equivalent Mode bits for this parameter.
 *	@param	pxError		Pointer to a signed byte for error checking. Can be NULL if not required.
 *	@param	pxError		To be checked when a NULL pointer is returned.
 *
 *	@return	NULL pointer on error, in which case pxError should be checked for more information.
 *	@return	pxError can be:
 **/
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
FF_FILE *FF_Open( FF_IOManager_t *pxIOManager, const FF_T_WCHAR *pcPath, uint8_t ucMode, FF_Error_t *pxError )
#else
FF_FILE *FF_Open( FF_IOManager_t *pxIOManager, const char *pcPath, uint8_t ucMode, FF_Error_t *pxError )
#endif
{
FF_FILE *pxFile = NULL;
FF_FILE *pxFileChain;
FF_DirEnt_t xDirEntry;
uint32_t ulFileCluster;
FF_Error_t xError;
BaseType_t xIndex;
FF_FindParams_t xFindParams;
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	FF_T_WCHAR pcFileName[ ffconfigMAX_FILENAME ];
#else
	char pcFileName[ ffconfigMAX_FILENAME ];
#endif

	memset( &xFindParams, '\0', sizeof( xFindParams ) );

	/* Inform the functions that the entry will be created if not found. */
	if( ( ucMode & FF_MODE_CREATE ) != 0 )
	{
		xFindParams.ulFlags |= FIND_FLAG_CREATE_FLAG;
	}

	if( pxIOManager == NULL )
	{
		/* Use the error function code 'FF_OPEN' as this static
		function is only called from that function. */
		xError = ( FF_Error_t ) ( FF_ERR_NULL_POINTER | FF_OPEN );
	}
#if( ffconfigREMOVABLE_MEDIA != 0 )
	else if( ( pxIOManager->ucFlags & FF_IOMAN_DEVICE_IS_EXTRACTED ) != 0 )
	{
		xError = ( FF_Error_t ) ( FF_ERR_IOMAN_DRIVER_NOMEDIUM | FF_OPEN );
	}
#endif /* ffconfigREMOVABLE_MEDIA */
	else
	{
		xError = FF_ERR_NONE;

		/* Let xIndex point to the last occurrence of '/' or '\',
		to separate the path from the file name. */
		xIndex = ( BaseType_t ) STRLEN( pcPath );
		while( xIndex != 0 )
		{
			if( ( pcPath[ xIndex ] == '\\' ) || ( pcPath[ xIndex ] == '/' ) )
			{
				break;
			}
			xIndex--;
		}

		/* Copy the file name, i.e. the string that comes after the last separator. */
		STRNCPY( pcFileName, pcPath + xIndex + 1, ffconfigMAX_FILENAME );

		if( xIndex == 0 )
		{
			/* Only for the root, the slash is part of the directory name.
			'xIndex' now equals to the length of the path name. */
			xIndex = 1;
		}

		/* FF_CreateShortName() might set flags FIND_FLAG_FITS_SHORT and FIND_FLAG_SIZE_OK. */
		FF_CreateShortName( &xFindParams, pcFileName );

		/* Lookup the path and find the cluster pointing to the directory: */
		xFindParams.ulDirCluster = FF_FindDir( pxIOManager, pcPath, xIndex, &xError );
		if( xFindParams.ulDirCluster == 0ul )
		{
			if( ( ucMode & FF_MODE_WRITE ) != 0 )
			{
				FF_PRINTF( "FF_Open[%s]: Path not found\n", pcPath );
			}
			/* The user tries to open a file but the path leading to the file does not exist. */
		}
		else if( FF_isERR( xError ) == pdFALSE )
		{
			/* Allocate an empty file handle and buffer space for 'unaligned access'. */
			pxFile = prvAllocFileHandle( pxIOManager, &xError );
		}
	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		/* Copy the Mode Bits. */
		pxFile->ucMode = ucMode;

		/* See if the file does exist within the given directory. */
		ulFileCluster = FF_FindEntryInDir( pxIOManager, &xFindParams, pcFileName, 0x00, &xDirEntry, &xError );

		if( ulFileCluster == 0ul )
		{
			/* If cluster 0 was returned, it might be because the file has no allocated cluster,
			i.e. only a directory entry and no stored data. */
			if( STRLEN( pcFileName ) == STRLEN( xDirEntry.pcFileName ) )
			{
				if( ( xDirEntry.ulFileSize == 0 ) && ( FF_strmatch( pcFileName, xDirEntry.pcFileName, ( BaseType_t ) STRLEN( pcFileName ) ) == pdTRUE ) )
				{
					/* It is the file, give it a pseudo cluster number '1'. */
					ulFileCluster = 1;
					/* And reset any error. */
					xError = FF_ERR_NONE;
				}
			}
		}

		/* Test 'ulFileCluster' again, it might have been changed. */
		if( ulFileCluster == 0ul )
		{
			/* The path is found, but it does not contain the file name yet.
			Maybe the user wants to create it? */
			if( ( ucMode & FF_MODE_CREATE ) == 0 )
			{
				xError = ( FF_Error_t ) ( FF_ERR_FILE_NOT_FOUND | FF_OPEN );
			}
			else
			{
				ulFileCluster = FF_CreateFile( pxIOManager, &xFindParams, pcFileName, &xDirEntry, &xError );
				if( FF_isERR( xError ) == pdFALSE )
				{
					xDirEntry.usCurrentItem += 1;
				}
			}
		}
	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		/* Now the file exists, or it has been created.
		Check if the Mode flags are allowed: */
		if( ( xDirEntry.ucAttrib == FF_FAT_ATTR_DIR ) && ( ( ucMode & FF_MODE_DIR ) == 0 ) )
		{
			/* Not the object, File Not Found! */
			xError = ( FF_Error_t ) ( FF_ERR_FILE_OBJECT_IS_A_DIR | FF_OPEN );
		}
		/*---------- Ensure Read-Only files don't get opened for Writing. */
		else if( ( ( ucMode & ( FF_MODE_WRITE | FF_MODE_APPEND ) ) != 0 ) && ( ( xDirEntry.ucAttrib & FF_FAT_ATTR_READONLY ) != 0 ) )
		{
			xError = ( FF_Error_t ) ( FF_ERR_FILE_IS_READ_ONLY | FF_OPEN );
		}
	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		pxFile->pxIOManager = pxIOManager;
		pxFile->ulFilePointer = 0;
		/* Despite the warning output by MSVC - it is not possible to get here
		if xDirEntry has not been initialised. */
		pxFile->ulObjectCluster = xDirEntry.ulObjectCluster;
		pxFile->ulFileSize = xDirEntry.ulFileSize;
		pxFile->ulCurrentCluster = 0;
		pxFile->ulAddrCurrentCluster = pxFile->ulObjectCluster;

		pxFile->pxNext = NULL;
		pxFile->ulDirCluster = xFindParams.ulDirCluster;
		pxFile->usDirEntry = xDirEntry.usCurrentItem - 1;
		pxFile->ulChainLength = 0;
		pxFile->ulEndOfChain = 0;
		pxFile->ulValidFlags &= ~( FF_VALID_FLAG_DELETED );

		/* Add pxFile onto the end of our linked list of FF_FILE objects.
		But first make sure that there are not 2 handles with write access
		to the same object. */
		FF_PendSemaphore( pxIOManager->pvSemaphore );
		{
			pxFileChain = ( FF_FILE * ) pxIOManager->FirstFile;
			if( pxFileChain == NULL )
			{
				pxIOManager->FirstFile = pxFile;
			}
			else
			{
				for( ; ; )
				{
					/* See if two file handles point to the same object. */
					if( ( pxFileChain->ulObjectCluster == pxFile->ulObjectCluster ) &&
						( pxFileChain->ulDirCluster == pxFile->ulDirCluster ) &&
						( pxFileChain->usDirEntry == pxFile->usDirEntry ) )
					{
						/* Fail if any of the two has write access to the object. */
						if( ( ( pxFileChain->ucMode | pxFile->ucMode ) & ( FF_MODE_WRITE | FF_MODE_APPEND ) ) != 0 )
						{
							/* File is already open! DON'T ALLOW IT! */
							xError = ( FF_Error_t ) ( FF_ERR_FILE_ALREADY_OPEN | FF_OPEN );
							break;
						}
					}

					if( pxFileChain->pxNext == NULL )
					{
						pxFileChain->pxNext = pxFile;
						break;
					}

					pxFileChain = ( FF_FILE * ) pxFileChain->pxNext;
				}
			}
		}

		FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		/* If the file is opened with the truncate flag, truncate its contents. */
		if( ( ucMode & FF_MODE_TRUNCATE ) != 0 )
		{
			/* Set the current size and position to zero. */
			pxFile->ulFileSize = 0;
			pxFile->ulFilePointer = 0;
		}
	}

	if( FF_isERR( xError ) != pdFALSE )
	{
		if( pxFile != NULL )
		{
			#if( ffconfigOPTIMISE_UNALIGNED_ACCESS != 0 )
			{
				ffconfigFREE( pxFile->pucBuffer );
			}
			#endif
			ffconfigFREE( pxFile );
		}
		pxFile = NULL;
	}

	if( pxError != NULL )
	{
		*pxError = xError;
	}

	return pxFile;
}  /* FF_Open() */
/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Tests if a Directory contains any other files or folders.
 *
 *	@param	pxIOManager	FF_IOManager_t object returned from the FF_CreateIOManger() function.
 *
 **/
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
BaseType_t FF_isDirEmpty ( FF_IOManager_t * pxIOManager, const FF_T_WCHAR *pcPath )
#else
BaseType_t FF_isDirEmpty ( FF_IOManager_t * pxIOManager, const char *pcPath )
#endif
{
FF_DirEnt_t	xDirEntry;
FF_Error_t	xError = FF_ERR_NONE;
BaseType_t xReturn;

	if( pxIOManager == NULL )
	{
		xReturn = pdFALSE;
	}
	else
	{
		xError = FF_FindFirst( pxIOManager, &xDirEntry, pcPath );

		/* Assume the directory is empty until a file is
		encountered with a name other than ".." or "." */
		xReturn = pdTRUE;

		while( xError == 0 )
		{
			/* As we can't be sure the first 2 entries contain
			 * "." and "..", check it, not just count them
			 */
		#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
			if( ( wcscmp( xDirEntry.pcFileName, L".." ) != 0 ) && ( wcscmp( xDirEntry.pcFileName, L"." ) != 0 ) )
		#else
			if( ( strcmp( xDirEntry.pcFileName, ".." ) != 0 ) && ( strcmp( xDirEntry.pcFileName, "." ) != 0 ) )
		#endif
			{
				xReturn = pdFALSE;
				break;
			}
			xError = FF_FindNext( pxIOManager, &xDirEntry );
		}
	}

	return xReturn;
}	/* FF_isDirEmpty() */
/*-----------------------------------------------------------*/

#if( ffconfigPATH_CACHE != 0 )
	/* _HT_ After a directory has been renamed, the path cache becomes out-of-date */
	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	static void FF_RmPathCache ( FF_IOManager_t * pxIOManager, const FF_T_WCHAR * pcPath )
	#else
	static void FF_RmPathCache ( FF_IOManager_t * pxIOManager, const char *pcPath )
	#endif
	{
		/*
	* The directory 'path' will be removed or renamed
	* now clear all entries starting with 'path' in the path cache
	*/
		BaseType_t	xIndex;
		BaseType_t	pathLen = STRLEN( pcPath );

		FF_PendSemaphore( pxIOManager->pvSemaphore );
		{
			for( xIndex = 0; xIndex < ffconfigPATH_CACHE_DEPTH; xIndex++ )
			{
				BaseType_t	len2 = STRLEN( pxIOManager->xPartition.pxPathCache[ xIndex ].pcPath );

				if( len2 >= pathLen && FF_strmatch( pxIOManager->xPartition.pxPathCache[ xIndex ].pcPath, pcPath, pathLen ) )
				{
					pxIOManager->xPartition.pxPathCache[ xIndex ].pcPath[ 0 ] = '\0';
					pxIOManager->xPartition.pxPathCache[ xIndex ].ulDirCluster = 0;
				}
			}
		}

		FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
	}
#endif /* ffconfigPATH_CACHE */
/*-----------------------------------------------------------*/


#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
FF_Error_t FF_RmDir( FF_IOManager_t *pxIOManager, const FF_T_WCHAR *pcPath )
#else
FF_Error_t FF_RmDir( FF_IOManager_t *pxIOManager, const char *pcPath )
#endif
{
FF_FILE				*pxFile;
uint8_t				ucEntryBuffer[32];
FF_FetchContext_t	xFetchContext;
FF_Error_t			xError = FF_ERR_NONE;

	if( pxIOManager == NULL )
	{
		xError = ( FF_Error_t ) ( FF_ERR_NULL_POINTER | FF_RMDIR );
	}
#if( ffconfigREMOVABLE_MEDIA != 0 )
	else if( ( pxIOManager->ucFlags & FF_IOMAN_DEVICE_IS_EXTRACTED ) != 0 )
	{
		xError = ( FF_Error_t ) ( FF_ERR_IOMAN_DRIVER_NOMEDIUM | FF_RMDIR );
	}
#endif /* ffconfigREMOVABLE_MEDIA */
	else
	{
		pxFile = FF_Open( pxIOManager, pcPath, FF_MODE_DIR, &xError );

		if( pxFile != NULL )
		{
			pxFile->ulValidFlags |= FF_VALID_FLAG_DELETED;

			/* Clear the struct to allow a call to FF_CleanupEntryFetch() in any
			state. */
			memset( &xFetchContext, '\0', sizeof( xFetchContext ) );

			/* This task will get the unique right to change directories. */
			FF_LockDirectory( pxIOManager );
			do /* while( pdFALSE ) */
			{
				/* This while loop is only introduced to be able to use break
				statements. */
				if( FF_isDirEmpty( pxIOManager, pcPath ) == pdFALSE )
				{
					xError = ( FF_ERR_DIR_NOT_EMPTY | FF_RMDIR );
					break;
				}
				FF_LockFAT( pxIOManager );
				#if( ffconfigHASH_CACHE != 0 )
				{
					/* A directory is removed so invalidate any hash table
					referring to this directory. */
					FF_UnHashDir( pxIOManager, pxFile->ulObjectCluster );
				}
				#endif	/* ffconfigHASH_CACHE */
				{
					/* Add parameter 0 to delete the entire chain!
					The actual directory entries on disk will be freed. */
					xError = FF_UnlinkClusterChain( pxIOManager, pxFile->ulObjectCluster, 0 );
				}
				FF_UnlockFAT( pxIOManager );
				if( FF_isERR( xError ) )
				{
					break;
				}

				/* Now remove this directory from its parent directory.
				Initialise the dirent Fetch Context object for faster removal of
				dirents. */
				xError = FF_InitEntryFetch( pxIOManager, pxFile->ulDirCluster, &xFetchContext );
				if( FF_isERR( xError ) )
				{
					break;
				}

				#if( ffconfigHASH_CACHE != 0 )
				{
					/* Invalidate any hash table of the parent directory
					as well. */
					FF_UnHashDir( pxIOManager, pxFile->ulDirCluster );
				}
				#endif	/* ffconfigHASH_CACHE */

				/* Edit the Directory Entry, so it will show as deleted.
				First remove the LFN entries: */
				xError = FF_RmLFNs( pxIOManager, pxFile->usDirEntry, &xFetchContext );
				if( FF_isERR( xError ) )
				{
					break;
				}

				/* And remove the Short file name entry: */
				xError = FF_FetchEntryWithContext( pxIOManager, pxFile->usDirEntry, &xFetchContext, ucEntryBuffer );
				if( FF_isERR( xError ) == pdFALSE )
				{
					ucEntryBuffer[0] = FF_FAT_DELETED;
					FF_putShort( ucEntryBuffer, FF_FAT_DIRENT_CLUS_HIGH, ( uint32_t ) 0ul );
					FF_putShort( ucEntryBuffer, FF_FAT_DIRENT_CLUS_LOW,  ( uint32_t ) 0ul );

					xError = FF_PushEntryWithContext( pxIOManager, pxFile->usDirEntry, &xFetchContext, ucEntryBuffer );
				}
				if( FF_isERR( xError ) )
				{
					break;
				}

				#if( ffconfigPATH_CACHE != 0 )
				{
					/* We're removing a directory which might contain
					subdirectories.  Instead of iterating through all
					subdirectories, just clear the path cache. */
					FF_RmPathCache( pxIOManager, pcPath );
				}
				#endif
			} while( pdFALSE );
			{
			FF_Error_t xTempError;
				xTempError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
				if( FF_isERR( xError ) == pdFALSE )
				{
					xError = xTempError;
				}
				FF_UnlockDirectory( pxIOManager );

				/* Free the file pointer resources. */
				xTempError = FF_Close( pxFile );
				if( FF_isERR( xError ) == pdFALSE )
				{
					xError = xTempError;
				}

				xTempError = FF_FlushCache( pxIOManager );
				if( FF_isERR( xError ) == pdFALSE )
				{
					xError = xTempError;
				}
			}
		}	/* if( pxFile != NULL ) */
	}	/* else if( pxIOManager != NULL ) */

	return xError;
}	/* FF_RmDir() */
/*-----------------------------------------------------------*/

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
FF_Error_t FF_RmFile( FF_IOManager_t *pxIOManager, const FF_T_WCHAR *pcPath )
#else
FF_Error_t FF_RmFile( FF_IOManager_t *pxIOManager, const char *pcPath )
#endif
{
FF_FILE *pxFile;
FF_Error_t xError = FF_ERR_NONE;
uint8_t ucEntryBuffer[32];
FF_FetchContext_t xFetchContext;

	/* Opening the file-to-be-deleted in WR mode has two advantages:
	1. The file handle gives all necessary information to delete it such
	   as the data clusters and directory entries.
	2. The file is now locked, it can not be opened by another task. */
	pxFile = FF_Open( pxIOManager, pcPath, FF_MODE_WRITE, &xError );

	if( pxFile != NULL )
	{
		/* FF_Close() will see this flag and won't do any disc access. */
		pxFile->ulValidFlags |= FF_VALID_FLAG_DELETED;

		/* Ensure there is actually a cluster chain to delete! */
		if( pxFile->ulObjectCluster != 0 )
		{
			/* Lock the FAT so its thread-safe. */
			FF_LockFAT( pxIOManager );
			{
				/* 0 to delete the entire chain! */
				xError = FF_UnlinkClusterChain( pxIOManager, pxFile->ulObjectCluster, 0 );
			}
			FF_UnlockFAT( pxIOManager );
		}

		if( FF_isERR( xError ) == pdFALSE )
		{
			/* Clear the struct to allow a call to FF_CleanupEntryFetch() in any
			state. */
			memset( &xFetchContext, '\0', sizeof( xFetchContext ) );

			/* Get sole access to "directory changes" */
			FF_LockDirectory( pxIOManager );

			/* Edit the Directory Entry! (So it appears as deleted); */
			do {
				xError = FF_InitEntryFetch( pxIOManager, pxFile->ulDirCluster, &xFetchContext );
				if( FF_isERR( xError ) )
				{
					break;
				}

				#if( ffconfigHASH_CACHE != 0 )
				{
					FF_UnHashDir( pxIOManager, pxFile->ulDirCluster );
				}
				#endif	/* ffconfigHASH_CACHE */
				/* Remove LFN entries, if any. */
				xError = FF_RmLFNs( pxIOManager, ( uint16_t ) pxFile->usDirEntry, &xFetchContext );
				if( FF_isERR( xError ) )
				{
					break;
				}

				/* Remove the Short file name entry. */
				xError = FF_FetchEntryWithContext( pxIOManager, pxFile->usDirEntry, &xFetchContext, ucEntryBuffer );
				if( FF_isERR( xError ) == pdFALSE )
				{
					ucEntryBuffer[0] = FF_FAT_DELETED;
					FF_putShort( ucEntryBuffer, FF_FAT_DIRENT_CLUS_HIGH, ( uint32_t ) 0ul );
					FF_putShort( ucEntryBuffer, FF_FAT_DIRENT_CLUS_LOW,  ( uint32_t ) 0ul );

					xError = FF_PushEntryWithContext( pxIOManager, pxFile->usDirEntry, &xFetchContext, ucEntryBuffer );
				}
			} while( pdFALSE );
			{
			FF_Error_t xTempError;
				xTempError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
				if( FF_isERR( xError ) == pdFALSE )
				{
					xError = xTempError;
				}
				FF_UnlockDirectory( pxIOManager );

				/* Free the file pointer resources. */
				xTempError = FF_Close( pxFile );
				if( FF_isERR( xError ) == pdFALSE )
				{
					xError = xTempError;
				}

				xTempError = FF_FlushCache( pxIOManager );
				if( FF_isERR( xError ) == pdFALSE )
				{
					xError = xTempError;
				}
			}
		}
	}	/* if( pxFile != NULL ) */

	return xError;
}	/* FF_RmFile() */
/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Moves a file or directory from source to destination.
 *
 *	@param	pxIOManager				The FF_IOManager_t object pointer.
 *	@param	szSourceFile		String of the source file to be moved or renamed.
 *	@param	szDestinationFile	String of the destination file to where the source should be moved or renamed.
 *
 *	@return	FF_ERR_NONE on success.
 *	@return FF_ERR_FILE_DESTINATION_EXISTS if the destination file exists.
 *	@return FF_ERR_FILE_COULD_NOT_CREATE_DIRENT if dirent creation failed (fatal error!).
 *	@return FF_ERR_FILE_DIR_NOT_FOUND if destination directory was not found.
 *	@return FF_ERR_FILE_SOURCE_NOT_FOUND if the source file was not found.
 *
 **/

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
FF_Error_t FF_Move( FF_IOManager_t *pxIOManager, const FF_T_WCHAR*szSourceFile,
	const FF_T_WCHAR *szDestinationFile, BaseType_t xDeleteIfExists )
#else
FF_Error_t FF_Move( FF_IOManager_t *pxIOManager, const char	*szSourceFile,
	const char	*szDestinationFile, BaseType_t	xDeleteIfExists )
#endif
{
FF_Error_t xError;
FF_FILE *pSrcFile, *pxDestFile;
FF_DirEnt_t xMyFile;
uint8_t ucEntryBuffer[32];
BaseType_t xIndex;
uint32_t ulDirCluster = 0ul;
FF_FetchContext_t xFetchContext;
#if( ffconfigPATH_CACHE != 0 )
	BaseType_t xIsDirectory = pdFALSE;
#endif

	memset( &xFetchContext, '\0', sizeof( xFetchContext ) );

	if( pxIOManager == NULL )
	{
		xError = ( FF_Error_t ) ( FF_ERR_NULL_POINTER | FF_MOVE );
	}
#if( ffconfigREMOVABLE_MEDIA != 0 )
	else if( ( pxIOManager->ucFlags & FF_IOMAN_DEVICE_IS_EXTRACTED ) != 0 )
	{
		xError = ( FF_Error_t ) ( FF_ERR_IOMAN_DRIVER_NOMEDIUM | FF_MOVE );
	}
#endif /* ffconfigREMOVABLE_MEDIA */
	else
	{
		/* Check destination file doesn't exist! */
		pxDestFile = FF_Open( pxIOManager, szDestinationFile, FF_MODE_READ, &xError );

		if( ( pxDestFile != NULL) || ( FF_GETERROR( xError ) == FF_ERR_FILE_OBJECT_IS_A_DIR ) )
		{
			xError = ( FF_Error_t ) ( FF_ERR_FILE_DESTINATION_EXISTS | FF_MOVE );
			if( pxDestFile != NULL )
			{
				FF_Close( pxDestFile );
				if( xDeleteIfExists != pdFALSE )
				{
					xError = FF_RmFile( pxIOManager, szDestinationFile );
				}
			}
		}
		else
		{
			/* Discard the error set by FF_Open().
			The target file (or directory) is not found: continue renaming. */
			xError = FF_ERR_NONE;
		}
	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		/* About to move/rename 'szSourceFile'.  When opening it with 'FF_MODE_WRITE'
		only succeeds if it has no other open handle to it. */
		pSrcFile = FF_Open( pxIOManager, szSourceFile, FF_MODE_WRITE, &xError );

		if( FF_GETERROR( xError ) == FF_ERR_FILE_OBJECT_IS_A_DIR )
		{
			/* Open a directory for moving! */
			pSrcFile = FF_Open( pxIOManager, szSourceFile, FF_MODE_DIR, &xError );
	#if( ffconfigPATH_CACHE != 0 )
			xIsDirectory = pdTRUE;
	#endif
		}

		if( pSrcFile != NULL )
		{
			/* Collect information about the current directory entry. */
			xError = FF_InitEntryFetch( pxIOManager, pSrcFile->ulDirCluster, &xFetchContext );
			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = FF_FetchEntryWithContext( pxIOManager, pSrcFile->usDirEntry, &xFetchContext, ucEntryBuffer );
				if( FF_isERR( xError ) == pdFALSE )
				{
					xMyFile.ucAttrib = FF_getChar( ucEntryBuffer, ( uint16_t ) ( FF_FAT_DIRENT_ATTRIB ) );
					xMyFile.ulFileSize = pSrcFile->ulFileSize;
					xMyFile.ulObjectCluster = pSrcFile->ulObjectCluster;
					xMyFile.usCurrentItem = 0;

					xIndex = ( BaseType_t ) STRLEN( szDestinationFile );

					while( xIndex != 0 )
					{
						if( ( szDestinationFile[ xIndex ] == '\\' ) || ( szDestinationFile[ xIndex ] == '/' ) )
						{
							break;
						}

						xIndex--;
					}

					/* Copy the base name of the destination file. */
					STRNCPY( xMyFile.pcFileName, ( szDestinationFile + xIndex + 1 ), ffconfigMAX_FILENAME );

					if( xIndex == 0 )
					{
						xIndex = 1;
					}

					/* Find the (cluster of the) directory in which the target file will be located.
					It must exist before calling FF_Move(). */
					ulDirCluster = FF_FindDir( pxIOManager, szDestinationFile, xIndex, &xError );
				}
			}
		}

		if( FF_isERR( xError ) == pdFALSE )
		{
			if( ulDirCluster != 0ul )
			{
				FF_FindParams_t	xFindParams;
				memset( &xFindParams, '\0', sizeof( xFindParams ) );

				/* Clean up because FF_CreateDirent might want to write to the same sector. */
				xError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );

				if( FF_isERR( xError ) == pdFALSE )
				{
					/* Destination directory was found, we can now create the new entry. */
					xFindParams.ulDirCluster = ulDirCluster;
					xError = FF_CreateDirent( pxIOManager, &xFindParams, &xMyFile );
				}

				if( FF_isERR( xError ) == pdFALSE )
				{
					/* Edit the Directory Entry! (So it appears as deleted); */
					FF_LockDirectory( pxIOManager );
					{
						xError = FF_RmLFNs( pxIOManager, pSrcFile->usDirEntry, &xFetchContext );

						if( FF_isERR( xError ) == pdFALSE )
						{
							xError = FF_FetchEntryWithContext( pxIOManager, pSrcFile->usDirEntry, &xFetchContext, ucEntryBuffer );

							if( FF_isERR( xError ) == pdFALSE )
							{
							FF_Error_t xTempError;
								ucEntryBuffer[0] = FF_FAT_DELETED;
								FF_putShort( ucEntryBuffer, FF_FAT_DIRENT_CLUS_HIGH, ( uint32_t ) 0ul );
								FF_putShort( ucEntryBuffer, FF_FAT_DIRENT_CLUS_LOW,  ( uint32_t ) 0ul );

								xError = FF_PushEntryWithContext( pxIOManager, pSrcFile->usDirEntry, &xFetchContext, ucEntryBuffer );
								/* The contents of 'xFetchContext' has changed, flush it to disk now. */
								xTempError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
								if( FF_isERR( xError ) == pdFALSE )
								{
									xError = xTempError;
								}
							}
						}
					}
					FF_UnlockDirectory( pxIOManager );
				}

				#if( ffconfigPATH_CACHE != 0 )
				{
					if( xIsDirectory != 0 )
					{
						/* We've renamed a directory which might contain
						subdirectories.  To avoid having false entries, clear
						the path cache. */
						FF_RmPathCache( pxIOManager, szSourceFile );
					}
				}
				#endif
			}
			else	/* ulDirCluster == 0ul */
			{
				xError = ( FF_Error_t ) ( FF_ERR_FILE_DIR_NOT_FOUND | FF_MOVE );
			}
		}

		if( pSrcFile != NULL )
		{
			/* The source file was opened in WRITE mode just to lock it.
			Now clear the write flags to avoid writing back any changes. */
			pSrcFile->ucMode &= ~( FF_MODE_WRITE | FF_MODE_APPEND | FF_MODE_CREATE );
			FF_Close( pSrcFile );
		}
	}

	{
	FF_Error_t xTempError;

		xTempError = FF_FlushCache( pxIOManager );
		if( FF_isERR( xError ) == pdFALSE )
		{
			xError = xTempError;
		}
		xTempError = FF_CleanupEntryFetch( pxIOManager, &xFetchContext );
		if( FF_isERR( xError ) == pdFALSE )
		{
			xError = xTempError;
		}
	}

	return xError;
}	/* FF_Move() */
/*-----------------------------------------------------------*/

					/**
 *	@public
 *	@brief	Get's the next Entry based on the data recorded in the FF_DirEnt_t object.
 *
 *	@param	pxFile	FF_FILE object that was created by FF_Open().
 *
 *	@return pdTRUE if End of File was reached. pdFALSE if not.
 *	@return pdFALSE if a null pointer was provided.
 *
 **/
BaseType_t FF_isEOF( FF_FILE *pxFile )
{
BaseType_t xReturn;

	if( ( pxFile != NULL ) && ( pxFile->ulFilePointer >= pxFile->ulFileSize ) )
	{
		xReturn = pdTRUE;
	}
	else
	{
		xReturn = pdFALSE;
	}

	return xReturn;
}	/* FF_isEOF() */
/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Checks the number of bytes left on a read handle
 *
 *	@param	pxFile		An open file handle
 *
 *	@return	Less than zero: an error code
 *	@return	Number of bytes left to read from handle
 **/
int32_t FF_BytesLeft( FF_FILE *pxFile )
{
BaseType_t xReturn;

	if( pxFile == NULL )
	{
		xReturn = FF_ERR_NULL_POINTER | FF_BYTESLEFT;
	}
	else if( ( pxFile->ucMode & FF_MODE_READ ) == 0 )
	{
		xReturn = FF_ERR_FILE_NOT_OPENED_IN_READ_MODE | FF_BYTESLEFT;
	}
	else if( pxFile->ulFilePointer >= pxFile->ulFileSize )
	{
		xReturn = 0;
	}
	else
	{
		xReturn = pxFile->ulFileSize - pxFile->ulFilePointer;
	}

	return xReturn;
}	/* FF_BytesLeft() */
/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Returns the file size of a read handle
 *
 *	@param	pxFile		An open file handle
 *
 *	@return	Less than zero: an error code
 *	@return	Number of bytes left to read from handle
 **/
FF_Error_t FF_GetFileSize( FF_FILE *pxFile, uint32_t *pulSize ) /* Writes # of bytes in a file to the parameter. */
{
BaseType_t xReturn;

	if( pxFile == NULL )
	{
		xReturn = ( FF_Error_t ) ( FF_ERR_NULL_POINTER | FF_BYTESLEFT );
		*( pulSize ) = ( uint32_t ) 0u;
	}
	else if( FF_isERR( FF_CheckValid( pxFile ) ) )
	{
		xReturn = ( FF_Error_t ) ( FF_ERR_FILE_BAD_HANDLE | FF_BYTESLEFT );
		*( pulSize ) = ( uint32_t ) 0u;
	}
	else
	{
		xReturn = 0;
		*( pulSize ) = pxFile->ulFileSize;
	}

	return xReturn;
}	/* FF_GetFileSize */

int32_t FF_FileSize( FF_FILE *pxFile )
{
uint32_t ulLength;
FF_Error_t xResult;

	/* Function is deprecated. Please use FF_GetFileSize(). */
	xResult = FF_GetFileSize( pxFile, &( ulLength ) );

	if( FF_isERR( xResult ) == 0 )
	{
		xResult = ( int32_t ) ulLength;
	}

	return ( int32_t ) xResult;
}	/* FF_FileSize() */
/*-----------------------------------------------------------*/

static uint32_t FF_GetSequentialClusters( FF_IOManager_t *pxIOManager, uint32_t ulStartCluster, uint32_t ulLimit, FF_Error_t *pxError )
{
uint32_t ulCurrentCluster;
uint32_t ulNextCluster = ulStartCluster;
uint32_t ulIndex = 0;

	FF_FATBuffers_t xFATBuffers;
	FF_InitFATBuffers( &xFATBuffers, FF_MODE_READ );

	*pxError = FF_ERR_NONE;

	FF_LockFAT( pxIOManager );
	do
	{
		ulCurrentCluster = ulNextCluster;
		ulNextCluster = FF_getFATEntry( pxIOManager, ulCurrentCluster, pxError, &xFATBuffers );
		if( FF_isERR( *pxError ) )
		{
			ulIndex = 0;
			break;
		}

		if( ulNextCluster == ( ulCurrentCluster + 1 ) )
		{
			ulIndex++;
		}
		else
		{
			break;
		}

		if( ( ulLimit != 0 ) && ( ulIndex == ulLimit ) )
		{
			break;
		}
	}
	while( ulNextCluster == ( ulCurrentCluster + 1 ) );

	FF_UnlockFAT( pxIOManager );

	*pxError = FF_ReleaseFATBuffers( pxIOManager, &xFATBuffers );

	return ulIndex;
}	/* FF_GetSequentialClusters() */
/*-----------------------------------------------------------*/

static FF_Error_t FF_ReadClusters( FF_FILE *pxFile, uint32_t ulCount, uint8_t *buffer )
{
uint32_t ulSectors;
uint32_t ulSequentialClusters = 0;
uint32_t ulItemLBA;
FF_Error_t xError = FF_ERR_NONE;

	while( ulCount != 0 )
	{
		if( ( ulCount - 1 ) > 0 )
		{
			ulSequentialClusters =
				FF_GetSequentialClusters( pxFile->pxIOManager, pxFile->ulAddrCurrentCluster, ulCount - 1, &xError );
			if( FF_isERR( xError ) )
			{
				break;
			}
		}

		ulSectors = ( ulSequentialClusters + 1 ) * pxFile->pxIOManager->xPartition.ulSectorsPerCluster;
		ulItemLBA = FF_Cluster2LBA( pxFile->pxIOManager, pxFile->ulAddrCurrentCluster );
		ulItemLBA = FF_getRealLBA( pxFile->pxIOManager, ulItemLBA );

		xError = FF_BlockRead( pxFile->pxIOManager, ulItemLBA, ulSectors, buffer, pdFALSE );
		if( FF_isERR( xError ) )
		{
			break;
		}

		ulCount -= ( ulSequentialClusters + 1 );

		FF_LockFAT( pxFile->pxIOManager );
		{
			pxFile->ulAddrCurrentCluster =
				FF_TraverseFAT( pxFile->pxIOManager, pxFile->ulAddrCurrentCluster, ulSequentialClusters + 1, &xError );
		}
		FF_UnlockFAT( pxFile->pxIOManager );
		if( FF_isERR( xError ) )
		{
			break;
		}

		pxFile->ulCurrentCluster += ( ulSequentialClusters + 1 );
		buffer += ulSectors * pxFile->pxIOManager->usSectorSize;
		ulSequentialClusters = 0;
	}

	return xError;
}	/* FF_ReadClusters ()*/
/*-----------------------------------------------------------*/

static FF_Error_t FF_ExtendFile( FF_FILE *pxFile, uint32_t ulSize )
{
FF_IOManager_t *pxIOManager = pxFile->pxIOManager;
uint32_t ulBytesPerCluster = pxIOManager->xPartition.usBlkSize * pxIOManager->xPartition.ulSectorsPerCluster;
uint32_t ulTotalClustersNeeded = ( ulSize + ulBytesPerCluster - 1 ) / ulBytesPerCluster;
uint32_t ulClusterToExtend;
/* Initialise xIndex just for the compiler. */
BaseType_t xIndex = 0;
FF_DirEnt_t xOriginalEntry;
FF_Error_t xError = FF_ERR_NONE;
FF_FATBuffers_t xFATBuffers;

	if( ( pxFile->ucMode & FF_MODE_WRITE ) != FF_MODE_WRITE )
	{
		xError = ( FF_Error_t ) ( FF_ERR_FILE_NOT_OPENED_IN_WRITE_MODE | FF_EXTENDFILE );
	}
	else
	{
		if( ( pxFile->ulFileSize == 0 ) && ( pxFile->ulObjectCluster == 0 ) )
		{
			/* If there is no object cluster yet, create it.*/
			pxFile->ulAddrCurrentCluster = FF_CreateClusterChain( pxFile->pxIOManager, &xError );

			if( FF_isERR( xError ) == pdFALSE )
			{
				/* The directory denotes the address of the first data cluster of every file.
				Now change it to 'ulAddrCurrentCluster': */
				xError = FF_GetEntry( pxIOManager, pxFile->usDirEntry, pxFile->ulDirCluster, &xOriginalEntry );

				if( FF_isERR( xError ) == pdFALSE )
				{
					xOriginalEntry.ulObjectCluster = pxFile->ulAddrCurrentCluster;
					xError = FF_PutEntry( pxIOManager, pxFile->usDirEntry, pxFile->ulDirCluster, &xOriginalEntry, NULL );

					if( FF_isERR( xError ) == pdFALSE )
					{
						pxFile->ulObjectCluster = pxFile->ulAddrCurrentCluster;
						pxFile->ulChainLength = 1;
						pxFile->ulCurrentCluster = 0;
						pxFile->ulEndOfChain = pxFile->ulAddrCurrentCluster;
					}
				}
			}
		}
		else
		{
			/* This file already has at least one cluster. */
		}
	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		if( pxFile->ulChainLength == 0 )
		{
			/* This is the first extension requiring the chain length.
			Calculate it now: */
			pxFile->ulChainLength = FF_GetChainLength( pxIOManager, pxFile->ulObjectCluster, &pxFile->ulEndOfChain, &xError );
		}
	}

	if( ( FF_isERR( xError ) == pdFALSE ) && ( ulTotalClustersNeeded > pxFile->ulChainLength ) )
	{
	uint32_t ulCurrentCluster, ulNextCluster;

		ulClusterToExtend = ( ulTotalClustersNeeded - pxFile->ulChainLength );
		/* Now the file has at least 1 cluster, but it needs more clusters. */
		ulNextCluster = pxFile->ulAddrCurrentCluster;
		FF_LockFAT( pxIOManager );

		ulCurrentCluster = FF_FindEndOfChain( pxIOManager, ulNextCluster, &xError );

		if( FF_isERR( xError ) == pdFALSE )
		{
			for( xIndex = 0; xIndex < ( BaseType_t ) ulClusterToExtend; xIndex++ )
			{
				/* In FF_ExtendFile() */
				ulNextCluster = FF_FindFreeCluster( pxIOManager, &xError, pdTRUE );
				if( ( FF_isERR( xError ) == pdFALSE ) && ( ulNextCluster == 0UL ) )
				{
					xError = ( FF_Error_t ) ( FF_ERR_FAT_NO_FREE_CLUSTERS | FF_EXTENDFILE );
				}

				if( FF_isERR( xError ) )
				{
					break;
				}

				/* Can not use this buffer earlier because of FF_FindEndOfChain/FF_FindFreeCluster */
				FF_InitFATBuffers( &xFATBuffers, FF_MODE_WRITE );
				xError = FF_putFATEntry( pxIOManager, ulCurrentCluster, ulNextCluster, &xFATBuffers );
				if( FF_isERR( xError ) )
				{
					break;
				}
				xError = FF_ReleaseFATBuffers( pxIOManager, &xFATBuffers );
				if( FF_isERR( xError ) )
				{
					break;
				}
				ulCurrentCluster = ulNextCluster;
			}

			if( FF_isERR( xError ) == pdFALSE )
			{
				pxFile->ulEndOfChain = ulCurrentCluster;
			}
			pxFile->ulChainLength += xIndex;
		}
		FF_UnlockFAT( pxIOManager );

		{
		FF_Error_t xTempError;
			xTempError = FF_DecreaseFreeClusters( pxIOManager, ( uint32_t ) xIndex );	/* Keep Tab of Numbers for fast FreeSize() */
			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = xTempError;
			}
		}

		/* We must ensure that the ulAddrCurrentCluster is not out-of-sync with the CurrentCluster number.
		This could have occurred in append mode, where the file was opened with a filesize % clustersize == 0
		because of a seek, where the ulAddrCurrentCluster was not updated after extending. This caused the data to
		be written to the previous cluster(s). */
		if( ( pxFile->ulCurrentCluster == pxFile->ulChainLength - 1 ) &&
			( pxFile->ulAddrCurrentCluster != pxFile->ulEndOfChain ) )
		{
			pxFile->ulAddrCurrentCluster = pxFile->ulEndOfChain;
		}

		/* By default, 'ffconfigFILE_EXTEND_FLUSHES_BUFFERS' is
		defined as 1.
		Users may set it to zero in order to increase the
		speed of writing to disk. */

		#if( ffconfigFILE_EXTEND_FLUSHES_BUFFERS != 0 )
		{
		FF_Error_t xTempError;

			xTempError = FF_FlushCache( pxIOManager );
			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = xTempError;
			}
		}
		#endif	/* ffconfigFILE_EXTEND_FLUSHES_BUFFERS */
	} /* if( ulTotalClustersNeeded > pxFile->ulChainLength ) */

	return xError;
}	/* FF_ExtendFile() */
/*-----------------------------------------------------------*/

static FF_Error_t FF_WriteClusters( FF_FILE *pxFile, uint32_t ulCount, uint8_t *buffer )
{
uint32_t ulSectors;
uint32_t ulSequentialClusters = 0;
uint32_t ulItemLBA;
FF_Error_t xError = FF_ERR_NONE;

	while( ulCount != 0 )
	{
		if( ( ulCount - 1 ) > 0 )
		{
			ulSequentialClusters =
				FF_GetSequentialClusters( pxFile->pxIOManager, pxFile->ulAddrCurrentCluster, ulCount - 1, &xError );
			if( FF_isERR( xError ) )
			{
				break;
			}
		}

		ulSectors = ( ulSequentialClusters + 1 ) * pxFile->pxIOManager->xPartition.ulSectorsPerCluster;
		ulItemLBA = FF_Cluster2LBA( pxFile->pxIOManager, pxFile->ulAddrCurrentCluster );
		ulItemLBA = FF_getRealLBA( pxFile->pxIOManager, ulItemLBA );

		xError = FF_BlockWrite( pxFile->pxIOManager, ulItemLBA, ulSectors, buffer, pdFALSE );

		if( FF_isERR( xError ) )
		{
			break;
		}

		ulCount -= ulSequentialClusters + 1;

		FF_LockFAT( pxFile->pxIOManager );
		{
			pxFile->ulAddrCurrentCluster =
				FF_TraverseFAT( pxFile->pxIOManager, pxFile->ulAddrCurrentCluster, ulSequentialClusters + 1, &xError );
		}
		FF_UnlockFAT( pxFile->pxIOManager );
		if( FF_isERR( xError ) )
		{
			break;
		}

		pxFile->ulCurrentCluster += ( ulSequentialClusters + 1 );
		buffer += ulSectors * pxFile->pxIOManager->usSectorSize;
		ulSequentialClusters = 0;
	}

	return xError;
}	/* FF_WriteClusters */
/*-----------------------------------------------------------*/

/**
 *	@private
 *	@brief	Calculate the Logical Block Address (LBA)
 *
 *	@param	pxFile       The file handle
 *
 *	@return	LBA
 *
 *  Must be set:
 *    - pxFile->ulFilePointer        : byte offset in file
 *    - pxFile->ulAddrCurrentCluster : physical cluster on the partition
 **/
static uint32_t FF_FileLBA( FF_FILE *pxFile )
{
	uint32_t	ulItemLBA;
	ulItemLBA = FF_Cluster2LBA( pxFile->pxIOManager, pxFile->ulAddrCurrentCluster );
	ulItemLBA += FF_getMajorBlockNumber( pxFile->pxIOManager, pxFile->ulFilePointer, 1 );
	ulItemLBA = FF_getRealLBA( pxFile->pxIOManager, ulItemLBA );
	ulItemLBA += FF_getMinorBlockNumber( pxFile->pxIOManager, pxFile->ulFilePointer, 1 );

	return ulItemLBA;
}	/* FF_FileLBA() */
/*-----------------------------------------------------------*/

/**
 *	@private
 *	@brief	Depending on FilePointer, calculate CurrentCluster
 *  @brief	and traverse the FAT to find the right ulAddrCurrentCluster
 *
 *	@param	pxFile       The file handle
 *
 *	@return	FF_ERR_NONE on success
 *	@return	Possible error returned by FF_TraverseFAT() or END_OF_DIR
 *
 *  Side effects:
 *    - pxFile->ulCurrentCluster     : relative cluster number (0 <= Num < ulChainLength)
 *    - pxFile->ulAddrCurrentCluster : fysical cluster on the partition
 **/
static uint32_t FF_SetCluster( FF_FILE *pxFile, FF_Error_t *pxError )
{
FF_IOManager_t *pxIOManager = pxFile->pxIOManager;
uint32_t ulNewCluster = FF_getClusterChainNumber( pxIOManager, pxFile->ulFilePointer, 1 );
FF_Error_t xResult = FF_ERR_NONE;
uint32_t ulReturn;

	if( ulNewCluster > pxFile->ulCurrentCluster )
	{
		FF_LockFAT( pxIOManager );
		{
			pxFile->ulAddrCurrentCluster = FF_TraverseFAT( pxIOManager, pxFile->ulAddrCurrentCluster,
				ulNewCluster - pxFile->ulCurrentCluster, &xResult );
		}
		FF_UnlockFAT( pxIOManager );
	}
	else if( ulNewCluster < pxFile->ulCurrentCluster )
	{
		FF_LockFAT( pxIOManager );
		{
			pxFile->ulAddrCurrentCluster = FF_TraverseFAT( pxIOManager, pxFile->ulObjectCluster, ulNewCluster, &xResult );
		}
		FF_UnlockFAT( pxIOManager );
	}
	else
	{
		/* Well positioned. */
	}

	if( FF_isERR( xResult ) == pdFALSE )
	{
		pxFile->ulCurrentCluster = ulNewCluster;
		ulReturn = FF_FileLBA( pxFile );
	}
	else
	{
		ulReturn = 0;
	}
	*pxError = xResult;

	return ulReturn;
}	/* FF_SetCluster() */
/*-----------------------------------------------------------*/

static int32_t FF_ReadPartial( FF_FILE *pxFile, uint32_t ulItemLBA, uint32_t ulRelBlockPos, uint32_t ulCount,
	uint8_t *pucBuffer, FF_Error_t *pxError )
{
FF_Error_t xError = FF_ERR_NONE;
uint32_t ulBytesRead;

	/* Bytes to read are within a block and less than a block size. */
	#if( ffconfigOPTIMISE_UNALIGNED_ACCESS != 0 )
	{
	BaseType_t xLastRead;

		/* Optimised method: each file handle holds one data block
		in cache: 'pxFile->pucBuffer'. */
		/* See if the current block will be accessed after this read: */
		if( ( ulRelBlockPos + ulCount ) >= ( uint32_t ) pxFile->pxIOManager->usSectorSize )
		{
			/* After this read, ulFilePointer will point to the next block/sector. */
			xLastRead = pdTRUE;
		}
		else
		{
			/* It is not the last read within this block/sector. */
			xLastRead = pdFALSE;
		}

		if( ( pxFile->ucState & FF_BUFSTATE_VALID ) == 0 )
		{
			xError = FF_BlockRead( pxFile->pxIOManager, ulItemLBA, 1, pxFile->pucBuffer, pdFALSE );
			if( FF_isERR( xError ) == pdFALSE )
			{
				pxFile->ucState = FF_BUFSTATE_VALID;
			}
		}

		if( ( pxFile->ucState & FF_BUFSTATE_VALID ) != 0 )
		{
			memcpy( pucBuffer, pxFile->pucBuffer + ulRelBlockPos, ulCount );
			pxFile->ulFilePointer += ulCount;
			ulBytesRead = ulCount;
			if( ( xLastRead == pdTRUE ) && ( ( pxFile->ucState & FF_BUFSTATE_WRITTEN ) != 0 ) )
			{
				/* If the data was changed (file in 'update' mode), store the changes: */
				xError = FF_BlockWrite( pxFile->pxIOManager, ulItemLBA, 1, pxFile->pucBuffer, pdFALSE );
			}
		}
		else
		{
			ulBytesRead = 0ul;
		}
		if( xLastRead == pdTRUE )
		{
			/* As the next FF_Read() will go passed the current block, invalidate the buffer now. */
			pxFile->ucState = FF_BUFSTATE_INVALID;
		}
	}
	#else
	{
	FF_Buffer_t *pxBuffer;
		/* Reading in the standard way, using FF_Buffer_t. */
		pxBuffer = FF_GetBuffer( pxFile->pxIOManager, ulItemLBA, FF_MODE_READ );
		if( pxBuffer == NULL )
		{
			xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_READ );
			ulBytesRead = 0ul;
		}
		else
		{
			memcpy( pucBuffer, pxBuffer->pucBuffer + ulRelBlockPos, ulCount );
			/* Releasing a buffer in FF_MODE_READ mode will not lead to an error,
			because no disk access is needed. */
			xError = FF_ReleaseBuffer( pxFile->pxIOManager, pxBuffer );
			pxFile->ulFilePointer += ulCount;
			ulBytesRead = ulCount;
		}
	}
	#endif

	*pxError = xError;

	return ulBytesRead;
}	/* FF_ReadPartial() */
/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Equivalent to fread()
 *
 *	@param	pxFile			FF_FILE object that was created by FF_Open().
 *	@param	ulElementSize	The size of an element to read.
 *	@param	ulCount			The number of elements to read.
 *	@param	buffer			A pointer to a buffer of adequate size to be filled with the requested data.
 *
 *	@return Number of bytes read.
 *
 * FF_Read() and FF_Write() work very similar. They both complete their task in 5 steps:
 *	1. Read bytes up to a sector border:  FF_ReadPartial()
 *	2. Read sectors up to cluster border: FF_BlockRead()
 *	3. Read complete clusters:            FF_ReadClusters()
 *	4. Read remaining sectors:            FF_BlockRead()
 *	5. Read remaining bytes:              FF_ReadPartial()
 **/
int32_t FF_Read( FF_FILE *pxFile, uint32_t ulElementSize, uint32_t ulCount, uint8_t *pucBuffer )
{
uint32_t ulBytesLeft = ulElementSize * ulCount;
uint32_t ulBytesRead = 0;
uint32_t ulBytesToRead;
FF_IOManager_t *pxIOManager;
uint32_t ulRelBlockPos;
uint32_t ulItemLBA;
int32_t lResult;
uint32_t ulSectors;
uint32_t ulRelClusterPos;
uint32_t ulBytesPerCluster;
FF_Error_t xError;

	if( pxFile == NULL )
	{
		xError = ( FF_Error_t ) ( FF_ERR_NULL_POINTER | FF_READ );
	}
	else
	{
		/* Check validity of the handle and the current position within the file. */
		xError = FF_CheckValid( pxFile );
		if( FF_isERR( xError ) == pdFALSE )
		{
			if( ( pxFile->ucMode & FF_MODE_READ ) == 0 )
			{
				/* File was not opened with READ mode access. */
				xError = ( FF_Error_t ) ( FF_ERR_FILE_NOT_OPENED_IN_READ_MODE | FF_READ );
			}
			else if( pxFile->ulFilePointer >= pxFile->ulFileSize )
			{
				/* The end-of-file is reached.  The error READ_ZERO will not be
				returned, it is just used to avoid further processing. */
				xError = ( FF_Error_t ) ( FF_ERR_FILE_READ_ZERO | FF_READ );
			}
			else if( ( pxFile->ulFilePointer + ulBytesLeft ) > pxFile->ulFileSize )
			{
				/* Note that many bytes can be read. */
				ulBytesLeft = pxFile->ulFileSize - pxFile->ulFilePointer;
			}
		}
		else
		{
			/* The file handle is not valid. */
		}
	}	/* else pxFile != NULL */

	if( FF_isERR( xError ) == pdFALSE )
	{
		pxIOManager = pxFile->pxIOManager;

		/* And calculate the Logical Block Address. */
		ulItemLBA = FF_SetCluster( pxFile, &xError );

		/* Get the position within a block. */
		ulRelBlockPos = FF_getMinorBlockEntry( pxIOManager, pxFile->ulFilePointer, 1 );
		/* Open a do {} while( 0 ) loop to allow easy breaks: */
		do
		{
			if( ( ulRelBlockPos + ulBytesLeft ) <= ( uint32_t ) pxIOManager->usSectorSize )
			{
				/*---------- A small read within the current block only. */
				ulBytesRead = FF_ReadPartial( pxFile, ulItemLBA, ulRelBlockPos, ulBytesLeft, pucBuffer, &xError );
				break;
			}
			/*---------- Read (memcpy) to a Sector Boundary. */
			if( ulRelBlockPos != 0 )
			{
				/* Not on a sector boundary, at this point the LBA is known. */
				ulBytesToRead = pxIOManager->usSectorSize - ulRelBlockPos;
				ulBytesRead = FF_ReadPartial( pxFile, ulItemLBA, ulRelBlockPos, ulBytesToRead, pucBuffer, &xError );
				if( FF_isERR( xError ) )
				{
					break;
				}
				ulBytesLeft -= ulBytesRead;
				pucBuffer += ulBytesRead;
			}

			/*---------- Read sectors, up to a Cluster Boundary. */
			ulBytesPerCluster = ( pxIOManager->xPartition.ulSectorsPerCluster * pxIOManager->usSectorSize );
			ulRelClusterPos = pxFile->ulFilePointer % ( ulBytesPerCluster * pxIOManager->xPartition.ucBlkFactor );

			if( ( ulRelClusterPos != 0 ) && ( ( ulRelClusterPos + ulBytesLeft ) >= ulBytesPerCluster ) )
			{
				/* Need to get to cluster boundary. */
				ulItemLBA = FF_SetCluster( pxFile, &xError );
				if( FF_isERR( xError ) )
				{
					break;
				}
				ulSectors = pxIOManager->xPartition.ulSectorsPerCluster - ( ulRelClusterPos / pxIOManager->usSectorSize );
				xError = FF_BlockRead( pxIOManager, ulItemLBA, ulSectors, pucBuffer, pdFALSE );
				if( FF_isERR( xError ) )
				{
					break;
				}
				ulBytesToRead = ulSectors * pxIOManager->usSectorSize;
				ulBytesLeft -= ulBytesToRead;
				pucBuffer += ulBytesToRead;
				ulBytesRead += ulBytesToRead;
				pxFile->ulFilePointer += ulBytesToRead;
			}

			/*---------- Read entire clusters. */
			if( ulBytesLeft >= ulBytesPerCluster )
			{
			uint32_t ulClusters;

			FF_SetCluster( pxFile, &xError );
				if( FF_isERR( xError ) )
				{
					break;
				}

				ulClusters = ulBytesLeft / ulBytesPerCluster;

				xError = FF_ReadClusters( pxFile, ulClusters, pucBuffer );
				if( FF_isERR( xError ) )
				{
					break;
				}
				ulBytesToRead = ulBytesPerCluster * ulClusters;
				pxFile->ulFilePointer += ulBytesToRead;
				ulBytesLeft -= ulBytesToRead;
				pucBuffer += ulBytesToRead;
				ulBytesRead += ulBytesToRead;
			}

			/*---------- Read Remaining Blocks. */
			while( ulBytesLeft >= ( uint32_t ) pxIOManager->usSectorSize )
			{
				ulSectors = ulBytesLeft / pxIOManager->usSectorSize;
				{
					/* HT: I'd leave these pPart/ulOffset for readability */
					/* and shorter code lines */
					FF_Partition_t *pPart = &( pxIOManager->xPartition );
					uint32_t ulOffset = ( pxFile->ulFilePointer / pxIOManager->usSectorSize ) % pPart->ulSectorsPerCluster;
					uint32_t ulRemain = pPart->ulSectorsPerCluster - ulOffset;
					if( ulSectors > ulRemain )
					{
						ulSectors = ulRemain;
					}
				}

				ulItemLBA = FF_SetCluster( pxFile, &xError );
				if( FF_isERR( xError ) )
				{
					break;
				}
				xError = FF_BlockRead( pxIOManager, ulItemLBA, ulSectors, pucBuffer, pdFALSE );

				if( FF_isERR( xError ) )
				{
					break;
				}
				ulBytesToRead = ulSectors * pxIOManager->usSectorSize;
				pxFile->ulFilePointer += ulBytesToRead;
				ulBytesLeft -= ulBytesToRead;
				pucBuffer += ulBytesToRead;
				ulBytesRead += ulBytesToRead;
			}

			/*---------- Read (memcpy) Remaining Bytes */
			if( ulBytesLeft == 0 )
			{
				break;
			}
			ulItemLBA = FF_SetCluster( pxFile, &xError );
			if( FF_isERR( xError ) )
			{
				break;
			}
			/* Bytes to read are within a block and less than a block size. */
			FF_ReadPartial( pxFile, ulItemLBA, 0, ulBytesLeft, pucBuffer, &xError );
			if( FF_isERR( xError ) == pdFALSE )
			{
				ulBytesRead += ulBytesLeft;
			}
		}
		while( pdFALSE );
	} /* if( FF_isERR( xError ) == pdFALSE ) */

	if( FF_GETERROR( xError ) == FF_ERR_FILE_READ_ZERO )
	{
		lResult = 0;
	}
	else if( FF_isERR( xError ) )
	{
		lResult = xError;
	}
	else
	{
		lResult = ( int32_t )( ulBytesRead / ulElementSize );
	}

	return lResult;
}	/* FF_Read() */
/*-----------------------------------------------------------*/

/**
*	@public
*	@brief	Equivalent to fgetc()
*
*	@param	pxFile		FF_FILE object that was created by FF_Open().
*
*	@return The character that was read (cast as a 32-bit interger). -1 on EOF.
*	@return FF_Error_t code. (Check with if(FF_isERR(xRetVal)) {}).
*	@return -1 EOF (end of file).
*
**/
int32_t FF_GetC( FF_FILE *pxFile )
{
uint32_t ulItemLBA;
uint8_t ucReturnedChar;
uint32_t ulRelBlockPos;
FF_Error_t xResult;

	if( pxFile == NULL )
	{
		xResult = FF_ERR_NULL_POINTER | FF_GETC;	/* Ensure this is a signed error. */
	}
	else if( ( pxFile->ucMode & FF_MODE_READ ) == 0 )
	{
		xResult = FF_ERR_FILE_NOT_OPENED_IN_READ_MODE | FF_GETC;
	}
	else if( pxFile->ulFilePointer >= pxFile->ulFileSize )
	{
		/* The end-of-file is reached.  The error READ_ZERO will not be
		returned, it is just used to avoid further processing. */
		xResult = FF_ERR_FILE_READ_ZERO | FF_READ;
	}
	else
	{
		ulRelBlockPos = FF_getMinorBlockEntry( pxFile->pxIOManager, pxFile->ulFilePointer, 1 );

		ulItemLBA = FF_SetCluster( pxFile, &xResult );
		if( FF_isERR( xResult ) == pdFALSE )
		{
			FF_ReadPartial( pxFile, ulItemLBA, ulRelBlockPos, 1, &ucReturnedChar, &xResult );
			if( FF_isERR( xResult ) == pdFALSE )
			{
				xResult = ( int32_t ) ( ( uint32_t ) ucReturnedChar );
			}
		}
	}

	return ( int32_t ) xResult;
}	/* FF_GetC() */
/*-----------------------------------------------------------*/

/**
* @public
* @brief	Gets a Line from a Text File, but no more than ulLimit characters. The line will be NULL terminated.
*
*			The behaviour of this function is undefined when called on a binary file.
*			It should just read in ulLimit bytes of binary, and ZERO terminate the line.
*
*			This function works for both UNIX line feeds, and Windows CRLF type files.
*
* @param	pxFile	The FF_FILE object pointer.
* @param	szLine	The character buffer where the line should be stored.
* @param	ulLimit	This should be the max number of characters that szLine can hold.
*
* @return	The number of characters read from the line, on success.
* @return	0 when no more lines are available, or when ulLimit is 0.
* @return	FF_ERR_NULL_POINTER if pxFile or szLine are NULL;
*
**/
int32_t FF_GetLine( FF_FILE *pxFile, char *pcLine, uint32_t ulLimit )
{
int32_t iChar = 0;
BaseType_t xIndex;
FF_Error_t xResult = FF_ERR_NONE;

	if( ( pxFile == NULL ) || ( pcLine == NULL ) )
	{
		xResult = FF_ERR_NULL_POINTER | FF_GETLINE;
	}
	else
	{
		for( xIndex = 0; xIndex < ( BaseType_t ) ( ulLimit - 1 ); ++xIndex )
		{
			iChar = FF_GetC( pxFile );

			if( FF_isERR( iChar ) == pdFALSE )
			{
				pcLine[ xIndex ] = ( char ) iChar;

				if( iChar == '\n' )
				{
					/* Read until the first linefeed.  Move xIndex forward so the
					null terminator does not overwrite the \n.  xIndex must be less
					thank ( ulLimit - 1 ), so incrementing it here cannot make it
					greater than ulLimit - 1, so the NULL can be inserted without
					overflowing the buffer. */
					xIndex++;
					break;
				}
			}
			else
			{
				if( ( FF_GETERROR( iChar ) == FF_ERR_FILE_READ_ZERO ) && ( xIndex > 0 ) )
				{
					/* Although FF_GetC() returns an End Of File,
					the last few characters will be returned first. */
					iChar = xIndex;
				}
				break;
			}
		}

		/* Make sure that the resulting string always ends with a zero: */
		pcLine[ xIndex ] = '\0';

		/*_RB_ In some paths this will be the second time FF_isERR() is called
		on the same value. */
		if( FF_isERR( iChar ) == pdFALSE )
		{
			/* Return the number of bytes read. */
			xResult = xIndex;
		}
		else
		{
			/* Return iChar as an error code (see FF_GetC()). */
			xResult = iChar;
		}
	}

	return xResult;
}	/* FF_GetLine() */
/*-----------------------------------------------------------*/

static int32_t FF_WritePartial( FF_FILE *pxFile, uint32_t ulItemLBA, uint32_t ulRelBlockPos, uint32_t ulCount,
	const uint8_t *pucBuffer, FF_Error_t *pxError )
{
FF_Error_t xError;
uint32_t ulBytesWritten;

	#if( ffconfigOPTIMISE_UNALIGNED_ACCESS != 0 )
	{
		BaseType_t xLastRead;
		if( ( ulRelBlockPos + ulCount ) >= ( uint32_t ) pxFile->pxIOManager->usSectorSize )
		{
			/* After this read, ulFilePointer will point to the next block/sector. */
			xLastRead = pdTRUE;
		}
		else
		{
			/* It is not the last read within this block/sector. */
			xLastRead = pdFALSE;
		}

		if( ( ( pxFile->ucState & FF_BUFSTATE_VALID ) == 0 ) &&
			( ( ulRelBlockPos != 0 ) || ( pxFile->ulFilePointer < pxFile->ulFileSize ) ) )
		{
			xError = FF_BlockRead( pxFile->pxIOManager, ulItemLBA, 1, pxFile->pucBuffer, pdFALSE );
			/* pxFile->ucState will be set later on. */
		}
		else
		{
			xError = FF_ERR_NONE;
			/* the buffer is valid or a whole block/sector will be written, so it is
			not necessary to read the contents first. */
		}
		if( FF_isERR( xError ) == pdFALSE )
		{
			memcpy( pxFile->pucBuffer + ulRelBlockPos, pucBuffer, ulCount );
			if( xLastRead == pdTRUE )
			{
				xError = FF_BlockWrite( pxFile->pxIOManager, ulItemLBA, 1, pxFile->pucBuffer, pdFALSE );
				pxFile->ucState = FF_BUFSTATE_INVALID;
			}
			else
			{
				pxFile->ucState |= FF_BUFSTATE_WRITTEN | FF_BUFSTATE_VALID;
			}
		}
		else
		{
			pxFile->ucState = FF_BUFSTATE_INVALID;
		}
	}
	#else
	{
	FF_Buffer_t *pxBuffer;
		if( ( ulRelBlockPos == 0 ) && ( pxFile->ulFilePointer >= pxFile->ulFileSize ) )
		{
			/* An entire sector will be written. */
			pxBuffer = FF_GetBuffer( pxFile->pxIOManager, ulItemLBA, FF_MODE_WR_ONLY );
		}
		else
		{
			/* A partial write will be done, make sure to read the contents before
			changing anything. */
			pxBuffer = FF_GetBuffer( pxFile->pxIOManager, ulItemLBA, FF_MODE_WRITE );
		}

		if( pxBuffer == NULL )
		{
			xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_WRITE );
		}
		else
		{
			/* Here we copy to the sector boundary. */
			memcpy( ( pxBuffer->pucBuffer + ulRelBlockPos ), pucBuffer, ulCount );

			xError = FF_ReleaseBuffer( pxFile->pxIOManager, pxBuffer );
		}
	}
	#endif
	if( FF_isERR( xError ) == pdFALSE )
	{
		pxFile->ulFilePointer += ulCount;
		ulBytesWritten = ulCount;

		if( pxFile->ulFilePointer > pxFile->ulFileSize )
		{
			pxFile->ulFileSize = pxFile->ulFilePointer;
		}
	}
	else
	{
		ulBytesWritten = 0ul;
	}
	*pxError = xError;

	return ulBytesWritten;
}	/* FF_WritePartial() */
/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Writes data to a File.
 *
 *	@param	pxFile			FILE Pointer.
 *	@param	ulElementSize		Size of an Element of Data to be copied. (in bytes).
 *	@param	ulCount			Number of Elements of Data to be copied. (ulElementSize * ulCount must not exceed ((2^31)-1) bytes. (2GB). For best performance, multiples of 512 bytes or Cluster sizes are best.
 *	@param	pucBuffer			Byte-wise pucBuffer containing the data to be written.
 *
 * FF_Read() and FF_Write() work very similar. They both complete their task in 5 steps:
 *	1. Write bytes up to a sector border:  FF_WritePartial()
 *	2. Write sectors up to cluster border: FF_BlockWrite()
 *	3. Write complete clusters:            FF_WriteClusters()
 *	4. Write remaining sectors:            FF_BlockWrite()
 *	5. Write remaining bytes:              FF_WritePartial()
 *	@return
**/
int32_t FF_Write( FF_FILE *pxFile, uint32_t ulElementSize, uint32_t ulCount, uint8_t *pucBuffer )
{
uint32_t ulBytesLeft = ulElementSize * ulCount;
uint32_t nBytesWritten = 0;
uint32_t nBytesToWrite;
FF_IOManager_t *pxIOManager;
uint32_t ulRelBlockPos;
uint32_t ulItemLBA;
int32_t lResult;
uint32_t ulSectors;
uint32_t ulRelClusterPos;
uint32_t ulBytesPerCluster;
FF_Error_t xError;

	if( pxFile == NULL )
	{
		xError = ( FF_Error_t ) ( FF_ERR_NULL_POINTER | FF_READ );
	}
	else
	{
		/* Check validity of the handle and the current position within the file. */
		xError = FF_CheckValid( pxFile );
		if( FF_isERR( xError ) == pdFALSE )
		{
			if( ( pxFile->ucMode & FF_MODE_WRITE ) == 0 )
			{
				xError = ( FF_Error_t ) ( FF_ERR_FILE_NOT_OPENED_IN_WRITE_MODE | FF_WRITE );
			}
			/* Make sure a write is after the append point. */
			else if( ( pxFile->ucMode & FF_MODE_APPEND ) != 0 )
			{
				if( pxFile->ulFilePointer < pxFile->ulFileSize )
				{
					xError = FF_Seek( pxFile, 0, FF_SEEK_END );
				}
			}
		}
	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		pxIOManager = pxFile->pxIOManager;

		/* Open a do{} while( 0 ) loop to allow the use of breaks */
		do
		{
			/* Extend File for at least ulBytesLeft!
			Handle file-space allocation
			+ 1 byte because the code assumes there is always a next cluster */
			xError = FF_ExtendFile( pxFile, pxFile->ulFilePointer + ulBytesLeft + 1 );
			if( FF_isERR( xError ) )
			{
				/* On every error, break from the while( 0 ) loop. */
				break;
			}

			ulRelBlockPos = FF_getMinorBlockEntry( pxIOManager, pxFile->ulFilePointer, 1 );	/* Get the position within a block. */
			ulItemLBA = FF_SetCluster( pxFile, &xError );
			if( FF_isERR( xError ) )
			{
				break;
			}

			if( ( ulRelBlockPos + ulBytesLeft ) <= ( uint32_t ) pxIOManager->usSectorSize )
			{
				/* Bytes to write are within a block and and do not go passed the current block. */
				nBytesWritten = FF_WritePartial( pxFile, ulItemLBA, ulRelBlockPos, ulBytesLeft, pucBuffer, &xError );
				break;
			}

			/*---------- Write (memcpy) to a Sector Boundary. */
			if( ulRelBlockPos != 0 )
			{
				/* Not writing on a sector boundary, at this point the LBA is known. */
				nBytesToWrite = pxIOManager->usSectorSize - ulRelBlockPos;
				nBytesWritten = FF_WritePartial( pxFile, ulItemLBA, ulRelBlockPos, nBytesToWrite, pucBuffer, &xError );
				if( FF_isERR( xError ) )
				{
					break;
				}

				ulBytesLeft -= nBytesWritten;
				pucBuffer += nBytesWritten;
			}

			/*---------- Write sectors, up to a Cluster Boundary. */
			ulBytesPerCluster = ( pxIOManager->xPartition.ulSectorsPerCluster * pxIOManager->usSectorSize );
			ulRelClusterPos = FF_getClusterPosition( pxIOManager, pxFile->ulFilePointer, 1 );

			if( ( ulRelClusterPos != 0 ) && ( ( ulRelClusterPos + ulBytesLeft ) >= ulBytesPerCluster ) )
			{
				/* Need to get to cluster boundary */
				ulItemLBA = FF_SetCluster( pxFile, &xError );
				if( FF_isERR( xError ) )
				{
					break;
				}

				ulSectors = pxIOManager->xPartition.ulSectorsPerCluster - ( ulRelClusterPos / pxIOManager->usSectorSize );
				xError = FF_BlockWrite( pxIOManager, ulItemLBA, ulSectors, pucBuffer, pdFALSE );
				if( FF_isERR( xError ) )
				{
					break;
				}

				nBytesToWrite = ulSectors * pxIOManager->usSectorSize;
				ulBytesLeft -= nBytesToWrite;
				pucBuffer += nBytesToWrite;
				nBytesWritten += nBytesToWrite;
				pxFile->ulFilePointer += nBytesToWrite;
				if( pxFile->ulFilePointer > pxFile->ulFileSize )
				{
					pxFile->ulFileSize = pxFile->ulFilePointer;
				}
			}

			/*---------- Write entire Clusters. */
			if( ulBytesLeft >= ulBytesPerCluster )
			{
			uint32_t ulClusters;

				FF_SetCluster( pxFile, &xError );
				if( FF_isERR( xError ) )
				{
					break;
				}

				ulClusters = ( ulBytesLeft / ulBytesPerCluster );

				xError = FF_WriteClusters( pxFile, ulClusters, pucBuffer );
				if( FF_isERR( xError ) )
				{
					break;
				}

				nBytesToWrite = ulBytesPerCluster * ulClusters;
				ulBytesLeft -= nBytesToWrite;
				pucBuffer += nBytesToWrite;
				nBytesWritten += nBytesToWrite;
				pxFile->ulFilePointer += nBytesToWrite;
				if( pxFile->ulFilePointer > pxFile->ulFileSize )
				{
					pxFile->ulFileSize = pxFile->ulFilePointer;
				}
			}

			/*---------- Write Remaining Blocks */
			while( ulBytesLeft >= ( uint32_t ) pxIOManager->usSectorSize )
			{
				ulSectors = ulBytesLeft / pxIOManager->usSectorSize;
				{
					/* HT: I'd leave these pPart/ulOffset for readability... */
					FF_Partition_t	*pPart = &( pxIOManager->xPartition );
					uint32_t ulOffset = ( pxFile->ulFilePointer / pxIOManager->usSectorSize ) % pPart->ulSectorsPerCluster;
					uint32_t ulRemain = pPart->ulSectorsPerCluster - ulOffset;
					if( ulSectors > ulRemain )
					{
						ulSectors = ulRemain;
					}
				}

				ulItemLBA = FF_SetCluster( pxFile, &xError );
				if( FF_isERR( xError ) )
				{
					break;
				}

				xError = FF_BlockWrite( pxIOManager, ulItemLBA, ulSectors, pucBuffer, pdFALSE );
				if( FF_isERR( xError ) )
				{
					break;
				}

				nBytesToWrite = ulSectors * pxIOManager->usSectorSize;
				ulBytesLeft -= nBytesToWrite;
				pucBuffer += nBytesToWrite;
				nBytesWritten += nBytesToWrite;
				pxFile->ulFilePointer += nBytesToWrite;
				if( pxFile->ulFilePointer > pxFile->ulFileSize )
				{
					pxFile->ulFileSize = pxFile->ulFilePointer;
				}
			}

			/*---------- Write (memcpy) Remaining Bytes */
			if( ulBytesLeft == 0 )
			{
				break;
			}

			ulItemLBA = FF_SetCluster( pxFile, &xError );
			if( FF_isERR( xError ) )
			{
				break;
			}
			FF_WritePartial( pxFile, ulItemLBA, 0, ulBytesLeft, pucBuffer, &xError );
			nBytesWritten += ulBytesLeft;
		}
		while( pdFALSE );
	}

	if( FF_isERR( xError ) )
	{
		lResult = xError;
	}
	else
	{
		lResult = ( int32_t )( nBytesWritten / ulElementSize );
	}

	return lResult;
}	/* FF_Write() */
/*-----------------------------------------------------------*/

/**
*	@public
*	@brief	Writes a char to a FILE.
*
*	@param	pxFile		FILE Pointer.
*	@param	ucValue	Char to be placed in the file.
*
*	@return	Returns the value written to the file, or a value less than 0.
*
**/
int32_t FF_PutC( FF_FILE *pxFile, uint8_t ucValue )
{
uint32_t ulItemLBA;
uint32_t ulRelBlockPos;
FF_Error_t xResult;

	if( pxFile == NULL )
	{	/* Ensure we don't have a Null file pointer on a Public interface. */
		xResult = FF_ERR_NULL_POINTER | FF_PUTC;
	}
	else if( ( pxFile->ucMode & FF_MODE_WRITE ) == 0 )
	{
		xResult = FF_ERR_FILE_NOT_OPENED_IN_WRITE_MODE | FF_PUTC;
	}
	else
	{
		xResult = FF_ERR_NONE;
		do
		{
			/* Make sure a write is after the append point. */
			if( ( pxFile->ucMode & FF_MODE_APPEND ) != 0 )
			{
				if( pxFile->ulFilePointer < pxFile->ulFileSize )
				{
					xResult = FF_Seek( pxFile, 0, FF_SEEK_END );
					if( FF_isERR( xResult ) )
					{
						break;
					}
				}
			}

			ulRelBlockPos = FF_getMinorBlockEntry( pxFile->pxIOManager, pxFile->ulFilePointer, 1 );

			/* Handle File Space Allocation. */
			/* We'll write 1 byte and always have a next cluster reserved. */
			xResult = FF_ExtendFile( pxFile, pxFile->ulFilePointer + 2 );
			if( FF_isERR( xResult ) )
			{
				break;
			}

			ulItemLBA = FF_SetCluster( pxFile, &xResult );
			if( FF_isERR( xResult ) )
			{
				break;
			}
			FF_WritePartial( pxFile, ulItemLBA, ulRelBlockPos, 1, &ucValue, &xResult );

			if( FF_isERR( xResult ) == pdFALSE )
			{
				xResult = ( FF_Error_t ) ucValue;
			}

		} while( pdFALSE );
	}

	return xResult;
}	/* FF_PutC() */
/*-----------------------------------------------------------*/

/**
*	@public
*	@brief	Equivalent to fseek()
*
*	@param	pxFile		FF_FILE object that was created by FF_Open().
*	@param	ulOffset	An integer (+/-) to seek to, from the specified origin.
*	@param	xOrigin		Where to seek from. (FF_SEEK_SET seek from start, FF_SEEK_CUR seek from current position, or FF_SEEK_END seek from end of file).
*
*	@return 0 on Sucess,
*	@return -2 if offset results in an invalid position in the file.
*	@return FF_ERR_NULL_POINTER if a FF_FILE pointer was not received.
*	@return -3 if an invalid origin was provided.
*
**/
FF_Error_t FF_Seek( FF_FILE *pxFile, int32_t lOffset, BaseType_t xOrigin )
{
FF_Error_t xError;
uint32_t ulPosition = 0ul;

	xError = FF_CheckValid( pxFile );

	if( FF_isERR( xError ) == pdFALSE )
	{
		xError = FF_FlushCache( pxFile->pxIOManager );

		#if( ffconfigOPTIMISE_UNALIGNED_ACCESS != 0 )
		{
			if( FF_isERR( xError ) == pdFALSE )
			{
				/* Here we must ensure that if the user tries to seek, and we had data in the file's
				write buffer that this is written to disk. */
				if( ( pxFile->ucState & FF_BUFSTATE_WRITTEN ) != 0 )
				{
					xError = FF_BlockWrite( pxFile->pxIOManager, FF_FileLBA( pxFile ), 1, pxFile->pucBuffer, pdFALSE );
				}
				pxFile->ucState = FF_BUFSTATE_INVALID;
			}
		}
		#endif	/* ffconfigOPTIMISE_UNALIGNED_ACCESS */

		if( FF_isERR( xError ) == pdFALSE )
		{
			if( xOrigin == FF_SEEK_SET )
			{
				ulPosition = ( uint32_t )lOffset;
			}
			else if( xOrigin == FF_SEEK_CUR )
			{
				if( lOffset >= ( int32_t ) 0 )
				{
					ulPosition = pxFile->ulFilePointer + ( ( uint32_t ) lOffset );
				}
				else
				{
					ulPosition = pxFile->ulFilePointer - ( ( uint32_t ) ( -lOffset ) );
				}
			}
			else if( xOrigin == FF_SEEK_END )
			{
				/* 'FF_SEEK_END' only allows zero or negative values. */
				if( lOffset <= ( int32_t ) 0 )
				{
					ulPosition = pxFile->ulFileSize - ( ( uint32_t ) ( -lOffset ) );
				}
			}
			else
			{
				xError = ( FF_Error_t ) ( FF_SEEK | FF_ERR_FILE_SEEK_INVALID_ORIGIN );
				/* To supress a compiler warning. */
				ulPosition = ( uint32_t ) 0u;
			}

			if( FF_isERR( xError ) == pdFALSE )
			{
				if( ulPosition <= ( uint32_t ) pxFile->ulFileSize )
				{
					if( ulPosition != ( uint32_t ) pxFile->ulFilePointer )
					{
						pxFile->ulFilePointer = ulPosition;
						FF_SetCluster( pxFile, &xError );
					}
				}
				else
				{
					xError = ( FF_Error_t ) ( FF_SEEK | FF_ERR_FILE_SEEK_INVALID_POSITION );
				}
			}
		}
	}

	return xError;
}	/* FF_Seek() */
/*-----------------------------------------------------------*/

#if( ffconfigREMOVABLE_MEDIA != 0 )
	/**
	*	@public
	*	@brief	Invalidate all file handles belonging to pxIOManager
	*
	*	@param	pIoMan		FF_IOManager_t object that was created by FF_CreateIOManger().
	*
	*	@return 0 if no handles were open
	*	@return >0 the amount of handles that were invalidated
	*	@return <0 probably an invalid FF_IOManager_t pointer
	*
	**/
	int32_t FF_Invalidate( FF_IOManager_t *pxIOManager )
	{
	int32_t xResult;
	FF_FILE *pxFileChain;

		if( pxIOManager == NULL )
		{
			xResult = FF_ERR_NULL_POINTER | FF_INVALIDATE;
		}
		else
		{
			xResult = 0;
			FF_PendSemaphore( pxIOManager->pvSemaphore );
			{
				pxIOManager->ucFlags |= FF_IOMAN_DEVICE_IS_EXTRACTED;
				/* Semaphore is required, or linked list might change */
				pxFileChain = ( FF_FILE * ) pxIOManager->FirstFile;
				if( pxFileChain != NULL )
				{
					/* Count elements in FirstFile */
					do
					{
						pxFileChain->ulValidFlags |= FF_VALID_FLAG_INVALID;
						xResult++;
						pxFileChain = pxFileChain->pxNext;
					}
					while( pxFileChain != NULL );
				}
			}

			FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
		}

		return xResult;
	}	/* FF_Invalidate() */
#endif /* ffconfigREMOVABLE_MEDIA */
/*-----------------------------------------------------------*/

/**
*	@public
*	@brief	Check validity of file handle
*
*	@param	pxFile		FF_FILE object that was created by FF_Open().
*
*	@return 0 on sucess.
*	@return FF_ERR_NULL_POINTER       if a null pointer was provided.
*	@return FF_ERR_FILE_BAD_HANDLE    if handle is not recognized
*	@return FF_ERR_FILE_MEDIA_REMOVED please call FF_Close
*
**/
FF_Error_t FF_CheckValid( FF_FILE *pxFile )
{
	FF_FILE		*pxFileChain;
	FF_Error_t	xError;

	if( ( pxFile == NULL ) || ( pxFile->pxIOManager == NULL ) )
	{
		xError = ( FF_Error_t ) ( FF_ERR_NULL_POINTER | FF_CHECKVALID );
	}
	else
	{
		FF_PendSemaphore( pxFile->pxIOManager->pvSemaphore );
		{
			pxFileChain = ( FF_FILE * ) pxFile->pxIOManager->FirstFile;
			xError = ( FF_Error_t ) ( FF_ERR_FILE_BAD_HANDLE | FF_CHECKVALID );
			while( pxFileChain != NULL )
			{
				if( pxFileChain == pxFile )
				{
				#if( ffconfigREMOVABLE_MEDIA != 0 )
					if( ( pxFileChain->ulValidFlags & FF_VALID_FLAG_INVALID ) != 0 )
					{
						/* The medium has been removed while this file handle was open. */
						xError = ( FF_Error_t ) ( FF_ERR_FILE_MEDIA_REMOVED | FF_CHECKVALID );
					}
					else
				#endif
					{
						/* Found the handle, so it is a valid / existing handle. */
						xError = FF_ERR_NONE;
					}

					break;
				}

				pxFileChain = pxFileChain->pxNext;
			}
		}
		FF_ReleaseSemaphore( pxFile->pxIOManager->pvSemaphore );
	}

	return xError;
}	/* FF_CheckValid() */
/*-----------------------------------------------------------*/

#if( ffconfigTIME_SUPPORT != 0 )
	/**
	*	@public
	*	@brief	Set the time-stamp(s) of a file entry
	*
	*	@param	pxFile		FF_FILE object that was created by FF_Open().
	*	@param	pxTime      FF_SystemTime_t the time stamp
	*	@param	uxWhat       UBaseType_t a combination of enum ETimeMask
	*
	*	@return 0 or FF_Error_t
	*
	**/
	FF_Error_t FF_SetFileTime( FF_FILE *pxFile, FF_SystemTime_t *pxTime, UBaseType_t uxWhat )
	{
	FF_DirEnt_t	xOriginalEntry;
	FF_Error_t	xError;

		xError = FF_CheckValid( pxFile );
		if( FF_isERR( xError ) == pdFALSE )
		{
			if( pxFile->ulValidFlags & FF_VALID_FLAG_DELETED )
			{	/*if (pxFile->FileDeleted) */
				xError = ( FF_Error_t ) ( FF_ERR_FILE_NOT_FOUND | FF_SETFILETIME );
			}
			else if( ( pxFile->ucMode & ( FF_MODE_WRITE | FF_MODE_APPEND ) ) == 0 )
			{
				xError = ( FF_Error_t ) ( FF_ERR_FILE_NOT_OPENED_IN_WRITE_MODE | FF_SETFILETIME );
			}
			else
			{
				/* Update the Dirent! */
				xError = FF_GetEntry( pxFile->pxIOManager, pxFile->usDirEntry, pxFile->ulDirCluster, &xOriginalEntry );
				if( FF_isERR( xError ) == pdFALSE )
				{
					if( uxWhat & ETimeCreate )
					{
						xOriginalEntry.xCreateTime = *pxTime;		/*/< Date and Time Created. */
					}

					if( uxWhat & ETimeMod )
					{
						xOriginalEntry.xModifiedTime = *pxTime;	/*/< Date and Time Modified. */
					}

					if( uxWhat & ETimeAccess )
					{
						xOriginalEntry.xAccessedTime = *pxTime;	/*/< Date of Last Access. */
					}

					xError = FF_PutEntry( pxFile->pxIOManager, pxFile->usDirEntry, pxFile->ulDirCluster, &xOriginalEntry, NULL );
				}

				if( FF_isERR( xError ) == pdFALSE )
				{
					xError = FF_FlushCache( pxFile->pxIOManager );		/* Ensure all modfied blocks are flushed to disk! */
				}
			}
		}

		return xError;
	}	/* FF_SetFileTime() */
#endif /* ffconfigTIME_SUPPORT */
/*-----------------------------------------------------------*/

#if( ffconfigTIME_SUPPORT != 0 )
	/**
	*	@public
	*	@brief	Set the time-stamp(s) of a file entry (by name)
	*
	*	@param	pxIOManager		FF_IOManager_t device handle
	*	@param	pcPath		int8_t/FF_T_WCHAR name of the file
	*	@param	pxTime       FF_SystemTime_t the time stamp
	*	@param	uxWhat       UBaseType_t a combination of enum ETimeMask
	*
	*	@return 0 or FF_Error_t
	*
	**/
	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	FF_Error_t FF_SetTime ( FF_IOManager_t * pxIOManager, const FF_T_WCHAR * pcPath, FF_SystemTime_t *pxTime, UBaseType_t uxWhat )
	#else
	FF_Error_t FF_SetTime ( FF_IOManager_t * pxIOManager, const char *pcPath, FF_SystemTime_t *pxTime, UBaseType_t uxWhat )
	#endif	/* ffconfigUNICODE_UTF16_SUPPORT */
	{
	FF_DirEnt_t xOriginalEntry;
	FF_Error_t xError;
	uint32_t ulFileCluster;
	BaseType_t xIndex;
	FF_FindParams_t xFindParams;
	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
		FF_T_WCHAR pcFileName[ffconfigMAX_FILENAME];
	#else
		char pcFileName[ffconfigMAX_FILENAME];
	#endif	/* ffconfigUNICODE_UTF16_SUPPORT */

		xIndex = ( BaseType_t ) STRLEN( pcPath );

		memset( &xFindParams, '\0', sizeof( xFindParams ) );

		while( xIndex != 0 )
		{
			if( pcPath[ xIndex ] == '\\' || pcPath[ xIndex ] == '/' )
			{
				break;
			}

			xIndex--;
		}

		STRNCPY( pcFileName, ( pcPath + xIndex + 1 ), ffconfigMAX_FILENAME );

		if( xIndex == 0 )
		{
			xIndex = 1;
		}

		xFindParams.ulDirCluster = FF_FindDir( pxIOManager, pcPath, ( uint16_t ) xIndex, &xError );
		if( FF_isERR( xError ) == pdFALSE )
		{
			if( xFindParams.ulDirCluster == 0 )
			{
				xError = ( FF_Error_t ) ( FF_ERR_FILE_NOT_FOUND | FF_SETTIME );
			}
			else
			{
				ulFileCluster = FF_FindEntryInDir( pxIOManager, &xFindParams, pcFileName, 0, &xOriginalEntry, &xError );
				if( ( FF_isERR( xError ) == pdFALSE ) || ( FF_GETERROR( xError ) == FF_ERR_DIR_END_OF_DIR ) )
				{
					if( ulFileCluster == 0ul )
					{
						/*FF_PRINTF ("FF_SetTime: Can not find '%s'\n", pcFileName); */
						xError = ( FF_Error_t ) ( FF_ERR_FILE_NOT_FOUND | FF_SETTIME );
					}
				}
			}
		}

		if( FF_isERR( xError ) == pdFALSE )
		{
			/* Update the Dirent! */
			if( uxWhat & ETimeCreate )
			{
				xOriginalEntry.xCreateTime = *pxTime;			/*/< Date and Time Created. */
			}

			if( uxWhat & ETimeMod )
			{
				xOriginalEntry.xModifiedTime = *pxTime;		/*/< Date and Time Modified. */
			}

			if( uxWhat & ETimeAccess )
			{
				xOriginalEntry.xAccessedTime = *pxTime;		/*/< Date of Last Access. */
			}

			xError = FF_PutEntry( pxIOManager, xOriginalEntry.usCurrentItem - 1, xFindParams.ulDirCluster, &xOriginalEntry, NULL );

			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = FF_FlushCache( pxIOManager );			/* Ensure all modified blocks are flushed to disk! */
			}
		}

		return xError;
	}	/* FF_SetTime() */
#endif /* ffconfigTIME_SUPPORT */
/*-----------------------------------------------------------*/

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
FF_Error_t FF_SetPerm( FF_IOManager_t * pxIOManager, const FF_T_WCHAR * pcPath, UBaseType_t aPerm )
#else
FF_Error_t FF_SetPerm( FF_IOManager_t * pxIOManager, const char *pcPath, UBaseType_t aPerm )
#endif
{
FF_DirEnt_t xOriginalEntry;
FF_Error_t xError;
uint32_t ulFileCluster;
BaseType_t xIndex;
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	FF_T_WCHAR pcFileName[ffconfigMAX_FILENAME];
#else
	char pcFileName[ffconfigMAX_FILENAME];
#endif
FF_FindParams_t xFindParams;

	xIndex = ( BaseType_t ) STRLEN( pcPath );

	memset( &xFindParams, '\0', sizeof( xFindParams ) );

	while( xIndex != 0 )
	{
		if( pcPath[ xIndex ] == '\\' || pcPath[ xIndex ] == '/' )
		{
			break;
		}

		xIndex--;
	}

	STRNCPY( pcFileName, ( pcPath + xIndex + 1 ), ffconfigMAX_FILENAME );

	if( xIndex == 0 )
	{
		xIndex = 1;
	}

	/* Open a do {} while( pdFALSE ) loop to allow the use of break statements. */
	do
	{
		xFindParams.ulDirCluster = FF_FindDir( pxIOManager, pcPath, ( uint16_t ) xIndex, &xError );
		if( xError )
		{
			break;
		}

		if( !xFindParams.ulDirCluster )
		{
			xError = ( FF_Error_t ) ( FF_ERR_FILE_NOT_FOUND | FF_SETTIME );
			break;
		}

		ulFileCluster = FF_FindEntryInDir( pxIOManager, &xFindParams, pcFileName, 0, &xOriginalEntry, &xError );
		if( FF_isERR( xError ) )
		{
			break;
		}

		if( ulFileCluster == 0ul )
		{
			/*FF_PRINTF ("FF_SetTime: Can not find '%s'\n", pcFileName); */
			xError = ( FF_Error_t ) ( FF_ERR_FILE_NOT_FOUND | FF_SETTIME );
			break;
		}

		/*	#define FF_FAT_ATTR_READONLY		0x01 */
		/*	#define FF_FAT_ATTR_HIDDEN			0x02 */
		/*	#define FF_FAT_ATTR_SYSTEM			0x04 */
		/*	#define FF_FAT_ATTR_VOLID			0x08 */
		/*	#define FF_FAT_ATTR_DIR				0x10 */
		/*	#define FF_FAT_ATTR_ARCHIVE			0x20 */
		/*	#define FF_FAT_ATTR_LFN				0x0F */
	#define FF_FAT_ATTR_USER	( ( uint8_t ) FF_FAT_ATTR_READONLY | FF_FAT_ATTR_HIDDEN | FF_FAT_ATTR_SYSTEM | FF_FAT_ATTR_ARCHIVE )
		/* Update the Dirent! */
		xOriginalEntry.ucAttrib &= ~FF_FAT_ATTR_USER;
		xOriginalEntry.ucAttrib |= ( aPerm & FF_FAT_ATTR_USER );
		xError = FF_PutEntry( pxIOManager, xOriginalEntry.usCurrentItem - 1, xFindParams.ulDirCluster, &xOriginalEntry, NULL );

		if( FF_isERR( xError ) == pdFALSE )
		{
			xError = FF_FlushCache( pxIOManager );			/* Ensure all modfied blocks are flushed to disk! */
		}
	}
	while( pdFALSE );

	return xError;
}	/* FF_SetPerm() */
/*-----------------------------------------------------------*/

/**
*	@public
*	@brief	Equivalent to fclose()
*
*	@param	pxFile		FF_FILE object that was created by FF_Open().
*
*	@return 0 on sucess.
*	@return -1 if a null pointer was provided.
*
**/
FF_Error_t FF_Close( FF_FILE *pxFile )
{
FF_FILE *pxFileChain;
FF_DirEnt_t xOriginalEntry;
FF_Error_t xError;

	/* Opening a do {} while( 0 )  loop to allow the use of the break statement. */
	do
	{
		if( pxFile == NULL )
		{
			xError = ( FF_Error_t ) ( FF_ERR_NULL_POINTER | FF_CLOSE );
			break;
		}

		/* It is important to check that user doesn't supply invalid
		handle or a handle invalid because of "media removed" */
		xError = FF_CheckValid( pxFile );

		#if( ffconfigREMOVABLE_MEDIA != 0 )
		{
			if( FF_GETERROR( xError ) == FF_ERR_FILE_MEDIA_REMOVED )
			{
				FF_PendSemaphore( pxFile->pxIOManager->pvSemaphore );
				{
					pxFileChain = ( FF_FILE * ) pxFile->pxIOManager->FirstFile;
					if( pxFileChain == pxFile )
					{
						pxFile->pxIOManager->FirstFile = pxFile->pxNext;
					}
					else
					{
						while( pxFileChain )
						{
							if( pxFileChain->pxNext == pxFile )
							{
								pxFileChain->pxNext = pxFile->pxNext;
								break;
							}

							pxFileChain = pxFileChain->pxNext;	/* Forgot this one */
						}
					}
				}					/* Semaphore released, linked list was shortened! */

				FF_ReleaseSemaphore( pxFile->pxIOManager->pvSemaphore );
				#if( ffconfigOPTIMISE_UNALIGNED_ACCESS != 0 )
				{
					ffconfigFREE( pxFile->pucBuffer );
				}
				#endif	/* ffconfigOPTIMISE_UNALIGNED_ACCESS */
				ffconfigFREE( pxFile );	/* So at least we have freed the pointer. */
				xError = FF_ERR_NONE;
				break;
			}
		}
		#endif	/* ffconfigREMOVABLE_MEDIA */

		if( FF_isERR( xError ) )
		{
			/* FF_ERR_FILE_BAD_HANDLE or FF_ERR_NULL_POINTER */
			break;
		}

		/* So here we have a normal valid file handle. */

		/* Sometimes FreeRTOS+FAT will leave a trailing cluster on the end of a cluster chain.
		To ensure we're compliant we shall now check for this condition and truncate it. */
		if( ( ( pxFile->ulValidFlags & FF_VALID_FLAG_DELETED ) == 0 ) &&
			( ( pxFile->ucMode & ( FF_MODE_WRITE | FF_MODE_APPEND | FF_MODE_CREATE ) ) != 0 ) )
		{
		uint32_t ulClusterSize;

			/* File is not deleted and it was opened for writing or updating */
			ulClusterSize = pxFile->pxIOManager->xPartition.usBlkSize * pxFile->pxIOManager->xPartition.ulSectorsPerCluster;

			if( ( ( pxFile->ulFileSize % ulClusterSize ) == 0 ) && ( pxFile->ulObjectCluster != 0ul ) )
			{
				/* The file's length is a multiple of cluster size.  This means
				that an extra cluster has been reserved, which wasn't necessary. */
				xError = FF_Truncate( pxFile, pdTRUE );
			}

			/* Get the directory entry and update it to show the new file size */
			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = FF_GetEntry( pxFile->pxIOManager, pxFile->usDirEntry, pxFile->ulDirCluster, &xOriginalEntry );

				/* Now update the directory entry */
				if( ( FF_isERR( xError ) == pdFALSE ) &&
					( ( pxFile->ulFileSize != xOriginalEntry.ulFileSize ) || ( pxFile->ulFileSize == 0UL ) ) )
				{
					if( pxFile->ulFileSize == 0UL )
					{
						xOriginalEntry.ulObjectCluster = 0;
					}

					xOriginalEntry.ulFileSize = pxFile->ulFileSize;
					xError = FF_PutEntry( pxFile->pxIOManager, pxFile->usDirEntry, pxFile->ulDirCluster, &xOriginalEntry, NULL );
				}
			}
		}

		/* Handle Linked list! */
		FF_PendSemaphore( pxFile->pxIOManager->pvSemaphore );
		{	/* Semaphore is required, or linked list could become corrupted. */
			pxFileChain = ( FF_FILE * ) pxFile->pxIOManager->FirstFile;
			if( pxFileChain == pxFile )
			{
				pxFile->pxIOManager->FirstFile = pxFile->pxNext;
			}
			else
			{
				while( pxFileChain )
				{
					if( pxFileChain->pxNext == pxFile )
					{
						/* Found it, remove it from the list. */
						pxFileChain->pxNext = pxFile->pxNext;
						break;
					}
					pxFileChain = pxFileChain->pxNext;
				}
			}
		}	/* Semaphore released, linked list was shortened! */
		FF_ReleaseSemaphore( pxFile->pxIOManager->pvSemaphore );

		#if( ffconfigOPTIMISE_UNALIGNED_ACCESS != 0 )
		{
			if( pxFile->pucBuffer != NULL )
			{
				/* Ensure any unaligned points are pushed to the disk! */
				if( pxFile->ucState & FF_BUFSTATE_WRITTEN )
				{
				FF_Error_t xTempError;

					xTempError = FF_BlockWrite( pxFile->pxIOManager, FF_FileLBA( pxFile ), 1, pxFile->pucBuffer, pdFALSE );
					if( FF_isERR( xError ) == pdFALSE )
					{
						xError = xTempError;
					}
				}

				ffconfigFREE( pxFile->pucBuffer );
			}
		}
		#endif
		if( FF_isERR( xError ) == pdFALSE )
		{
			xError = FF_FlushCache( pxFile->pxIOManager ); /* Ensure all modified blocks are flushed to disk! */
		}
		ffconfigFREE( pxFile );
	}
	while( pdFALSE );

	return xError;
}	/* FF_Close() */
/*-----------------------------------------------------------*/

/**
*	@public
*	@brief	Make Filesize equal to the FilePointer and truncates the file to this position
*
*	@param	pxFile		FF_FILE object that was created by FF_Open().
*
*	@return 0 on sucess.
*	@return negative if some error occurred
*
**/
FF_Error_t FF_SetEof( FF_FILE *pxFile )
{
	FF_Error_t xError;

	/* Check if the file was not deleted and if it was opened with write permissions: */
	if( ( ( pxFile->ulValidFlags & FF_VALID_FLAG_DELETED ) == 0 ) &&
		( ( pxFile->ucMode & ( FF_MODE_WRITE | FF_MODE_APPEND | FF_MODE_CREATE ) ) != 0 ) )
	{
		pxFile->ulFileSize = pxFile->ulFilePointer;
		if( pxFile->ulObjectCluster != 0ul )
		{
			xError = FF_Truncate( pxFile, pdFALSE );
		}
		else
		{
			xError = FF_ERR_NONE;
		}
	}
	else
	{
		xError = ( FF_Error_t ) ( FF_ERR_FILE_NOT_OPENED_IN_WRITE_MODE | FF_SETEOF );
	}

	return xError;
}	/* FF_SetEof() */
/*-----------------------------------------------------------*/

/**
*	@public
*	@brief	Truncate a file to 'pxFile->ulFileSize'
*
*	@param	pxFile		FF_FILE object that was created by FF_Open().
*
*	@return 0 on sucess.
*	@return negative if some error occurred
*
**/
static FF_Error_t FF_Truncate( FF_FILE *pxFile, BaseType_t bClosing )
{
FF_Error_t xError;
FF_IOManager_t *pxIOManager = pxFile->pxIOManager;

uint32_t ulClusterSize;
uint32_t ulClusterCount;
uint32_t ulClustersNeeded;

	/* The number of bytes contained in a cluster. */
	ulClusterSize = pxIOManager->xPartition.usBlkSize * pxIOManager->xPartition.ulSectorsPerCluster;

	/* See how many clusters have been allocated. */
	ulClusterCount = FF_GetChainLength( pxIOManager, pxFile->ulObjectCluster, NULL, &xError );

	/* Calculate the actual number of clusters needed, rounding up */
	ulClustersNeeded = ( pxFile->ulFileSize + ulClusterSize - 1 ) / ulClusterSize;
	if( bClosing != pdFALSE )
	{
		/* The handle will be closed after truncating.  This function is called
		because Filesize is an exact multiple of ulClusterSize. */
		ulClustersNeeded = pxFile->ulFileSize / ulClusterSize;
	}
	else
	{
		/* This function is called to make the file size equal to the current
		position within the file. Always keep an extra cluster to write to. */
		ulClustersNeeded = ( pxFile->ulFileSize + ulClusterSize ) / ulClusterSize;
	}

	/* First change the FAT chain. */
	if( ( FF_isERR( xError ) == pdFALSE ) && ( ulClusterCount > ulClustersNeeded ) )
	{
		if( ulClustersNeeded == 0ul )
		{
			FF_LockFAT( pxIOManager );
			{
				/* In FF_Truncate() */
				xError = FF_UnlinkClusterChain( pxIOManager, pxFile->ulObjectCluster, 0 );
			}
			FF_UnlockFAT( pxIOManager );

			if( FF_isERR( xError ) == pdFALSE )
			{
			FF_DirEnt_t xOriginalEntry;

				/* The directory denotes the address of the first data cluster of every file.
				Now change it to 'ulAddrCurrentCluster': */
				xError = FF_GetEntry( pxIOManager, pxFile->usDirEntry, pxFile->ulDirCluster, &xOriginalEntry );

				if( FF_isERR( xError ) == pdFALSE )
				{
					xOriginalEntry.ulObjectCluster = 0ul;
					xError = FF_PutEntry( pxIOManager, pxFile->usDirEntry, pxFile->ulDirCluster, &xOriginalEntry, NULL );

					if( FF_isERR( xError ) == pdFALSE )
					{
						pxFile->ulObjectCluster = 0ul;
						pxFile->ulChainLength = 0ul;
						pxFile->ulCurrentCluster = 0ul;
						pxFile->ulEndOfChain = 0ul;
					}
				}
			}
		}
		else
		{
			FF_LockFAT( pxIOManager );
			{
				uint32_t ulTruncateCluster = FF_TraverseFAT( pxIOManager, pxFile->ulObjectCluster, ulClustersNeeded - 1, &xError );

				if( FF_isERR( xError ) == pdFALSE )
				{
					xError = FF_UnlinkClusterChain( pxIOManager, ulTruncateCluster, 1 );
				}
			}
			FF_UnlockFAT( pxIOManager );
		}
	}

	return xError;
}	/* FF_Truncate() */
/*-----------------------------------------------------------*/
