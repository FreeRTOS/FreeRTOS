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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "portable.h"

/* FreeRTOS+FAT includes. */
#include "ff_headers.h"
#include "ff_stdio.h"

#if( ffconfigTIME_SUPPORT != 0 )
	#include <time.h>
#endif


#ifndef SIZE_MAX
	#define SIZE_MAX ( ( size_t ) -1 )
#endif

/* The number of bytes to write at a time when extending the length of a file
in a call to ff_truncate(). */
#define stdioTRUNCATE_WRITE_LENGTH	512

/* Bits set to indicate whether ".." should be included as well as ".". */
#define stdioDIR_ENTRY_DOT_1		( 1U & 0x03U )
#define stdioDIR_ENTRY_DOT_2		( 2U & 0x03U )

/* The directory entries '.' and '..' will show a file size of 1 KB. */
#define stdioDOT_ENTRY_FILE_SIZE			1024

/*-----------------------------------------------------------*/

#if( ffconfigHAS_CWD == 1 )

	/* FreeRTOS+FAT requires two thread local storage pointers.  One for errno
	and one for the CWD structure. */
	#if( configNUM_THREAD_LOCAL_STORAGE_POINTERS < 2 )
		#error FreeRTOS+FAT requires two thread local storage pointers so configNUM_THREAD_LOCAL_STORAGE_POINTERS must be at least 2 in FreeRTOSConfig.h
	#endif

	/* Each task has its own Current Working Directory (CWD).  The CWD is used
	to extend relative paths to absolute paths. */
	typedef struct WORKING_DIR
	{
		char pcCWD[ ffconfigMAX_FILENAME ];		/* The current working directory. */
		char pcFileName[ ffconfigMAX_FILENAME ];	/* The created absolute path. */
	} WorkingDirectory_t;

	/*
	 * Add the CWD to the beginning of a relative path, and copy the resultant
	 * absolute path into a thread local non const buffer.
	 */
	/*static*/ const char *prvABSPath( const char *pcPath );

	/*
	 * Lookup the CWD of the current task.
	 */
	static WorkingDirectory_t *pxFindCWD( void );

	/*
	 * Convert a string which may contain a relative path into a string that
	 * will only contain an absolute path.
	 */
	static const char *prvProcessRelativePaths( const char *pcPath );

#else /* ffconfigHAS_CWD */

	/* FreeRTOS+FAT requires one thread local storage pointers for errno. */
	#if( configNUM_THREAD_LOCAL_STORAGE_POINTERS < 2 )
		#error FreeRTOS+FAT requires one thread local storage pointers so configNUM_THREAD_LOCAL_STORAGE_POINTERS must be at least 1 in FreeRTOSConfig.h
	#endif

	/* Only absolute paths are supported so define away the prvABSPath()
	function. */
	/*static*/ const char *prvABSPath( const char *pcPath )
	{
		return pcPath;
	}

#endif /* ffconfigHAS_CWD */


#if( ffconfigUSE_DELTREE != 0 )
	/*
	 * Remove all files and directories starting from a certain path.
	 * This function uses recursion - which breaches the coding standard.  USE
	 * WITH CARE.
	 */
	static int ff_deltree_recurse( char *pcPath );
#endif

/*
 * Translate a +FAT error to a value compatible with errno.h
 * If the value represents an error, it is negative
 * The return value of this function will always be positive
 */
int prvFFErrorToErrno( FF_Error_t xError );

/*
 * Generate a time stamp for the file.
 */
#if( ffconfigTIME_SUPPORT == 1 )
	static uint32_t prvFileTime( FF_SystemTime_t *pxTime );
#endif

/*-----------------------------------------------------------*/

FF_FILE *ff_fopen( const char *pcFile, const char *pcMode )
{
FF_FILE *pxStream = NULL;
FF_DirHandler_t xHandler;
FF_Error_t xError;
uint8_t ucMode;

	/* Insert the current working directory in front of relative paths. */
	pcFile = prvABSPath( pcFile );

	/* Look-up the I/O manager for the file system. */
	if( FF_FS_Find( pcFile, &xHandler ) == pdFALSE )
	{
		stdioSET_ERRNO( pdFREERTOS_ERRNO_ENXIO );	/* No such device or address. */
	}
	else
	{
		/* Now 'xHandler.pcPath' contains an absolute path within the file system.
		Translate a type string "r|w|a[+]" to +FAT's mode bits. */
		ucMode = FF_GetModeBits( pcMode );

		pxStream = FF_Open( xHandler.pxManager, xHandler.pcPath, ucMode, &xError );
		stdioSET_ERRNO( prvFFErrorToErrno( xError ) );

		#if( ffconfigUSE_NOTIFY != 0 )
		{
			if( ( pxStream != NULL ) && ( ( ucMode & ( FF_MODE_WRITE | FF_MODE_APPEND ) ) != 0 ) )
			{
				/*_RB_ Function	name needs updating. */
				callFileEvents( pcFile, eFileCreate );
			}
		}
		#endif	/* ffconfigUSE_NOTIFY */

		#if( ffconfigDEV_SUPPORT != 0 )
		{
			if( pxStream != NULL )
			{
				FF_Device_Open( pcFile, pxStream );
			}
		}
		#endif	/* ffconfigDEV_SUPPORT */
	}

	return pxStream;
}
/*-----------------------------------------------------------*/

int ff_fclose( FF_FILE *pxStream )
{
FF_Error_t xError;
int iReturn, ff_errno;

	#if( ffconfigDEV_SUPPORT != 0 )
	{
		/* Currently device support is in an experimental state.  It will allow
		to create virtual files. The I/O data to those files will be redirected
		to their connected "drivers". */
		if( pxStream != NULL )
		{
			FF_Device_Close( pxStream );
		}
	}
	#endif

	xError = FF_Close( pxStream );
	ff_errno = prvFFErrorToErrno( xError );

	if( ff_errno == 0 )
	{
		iReturn = 0;
	}
	else
	{
		/* Return -1 for error as per normal fclose() semantics. */
		iReturn = -1;
	}

	/* Store the errno to thread local storage. */
	stdioSET_ERRNO( ff_errno );

	return iReturn;
}
/*-----------------------------------------------------------*/

int ff_fseek( FF_FILE *pxStream, long lOffset, int iWhence )
{
FF_Error_t xError;
int iReturn, ff_errno;

#if( ffconfigDEV_SUPPORT != 0 )
	if( pxStream->pxDevNode != NULL )
	{
		xError = FF_Device_Seek( pxStream, lOffset, iWhence );
	}
	else
#endif
	{
		xError = FF_Seek( pxStream, lOffset, iWhence );
	}

	ff_errno = prvFFErrorToErrno( xError );

	if( ff_errno == 0 )
	{
		iReturn = 0;
	}
	else
	{
		if( xError == FF_ERR_FILE_SEEK_INVALID_POSITION )
		{
			/* Illegal position, outside the file's space */
			ff_errno = pdFREERTOS_ERRNO_ESPIPE;
		}
		else if( xError == FF_ERR_FILE_SEEK_INVALID_ORIGIN )
		{
			/* Illegal parameter value for iWhence: SET,CUR,END. */
			ff_errno = pdFREERTOS_ERRNO_EINVAL;
		}

		/* Return -1 for error as per normal fseek() semantics. */
		iReturn = -1;
	}

	/* Store the errno to thread local storage. */
	stdioSET_ERRNO( ff_errno );

	return iReturn;
}
/*-----------------------------------------------------------*/

void ff_rewind( FF_FILE *pxStream )
{
	ff_fseek( pxStream, 0, FF_SEEK_SET );

	/* Rewind is supposed to reset errno unconditionally.  Store the errno to
	thread local storage. */
	stdioSET_ERRNO( 0 );
}
/*-----------------------------------------------------------*/

long ff_ftell( FF_FILE *pxStream )
{
long lResult;

	if( pxStream == NULL )
	{
		/* Store the errno to thread local storage. */
		stdioSET_ERRNO( pdFREERTOS_ERRNO_EBADF );

		/* Return -1 for error as per normal ftell() semantics. */
		lResult = -1;
	}
	else
	{
		lResult = ( long ) pxStream->ulFilePointer;
	}

	return lResult;
}
/*-----------------------------------------------------------*/

int ff_feof( FF_FILE *pxStream )
{
int iResult;
FF_Error_t xError;

	xError = FF_CheckValid( pxStream );
	if( FF_isERR( xError ) == pdFALSE )
	{
		/* Store the errno to thread local storage. */
		stdioSET_ERRNO( 0 );
		if( pxStream->ulFilePointer >= pxStream->ulFileSize )
		{
			iResult = pdTRUE;
		}
		else
		{
			iResult = pdFALSE;
		}
	}
	else
	{
		/* Store the errno to thread local storage. */
		stdioSET_ERRNO( prvFFErrorToErrno( xError ) );

		/* The file was invalid so a non-zero value cannot be returned. */
		iResult = pdFALSE;
	}

	return iResult;
}
/*-----------------------------------------------------------*/

size_t ff_fread( void *pvBuffer, size_t xSize, size_t xItems, FF_FILE * pxStream )
{
int32_t iReturned;
size_t xReturn;
int ff_errno;

#if( ffconfigDEV_SUPPORT != 0 )
	if( pxStream->pxDevNode != NULL )
	{
		iReturned = FF_Device_Read( pvBuffer, xSize, xItems, pxStream );
	}
	else
#endif
	{
		iReturned = FF_Read( pxStream, xSize, xItems, (uint8_t *)pvBuffer );
	}

	ff_errno = prvFFErrorToErrno( iReturned );

	if( ff_errno == pdFREERTOS_ERRNO_NONE )
	{
		/* As per the standard fread() semantics, the return value is the number
		of complete items read, which will only equal the number of bytes
		transferred when the item size is 1. */
		xReturn = ( size_t ) iReturned;
	}
	else
	{
		xReturn = 0;
	}

	/* Store the errno to thread local storage. */
	stdioSET_ERRNO( ff_errno );

	return xReturn;
}
/*-----------------------------------------------------------*/

size_t ff_fwrite( const void *pvBuffer, size_t xSize, size_t xItems, FF_FILE * pxStream )
{
int32_t iReturned;
size_t xReturn;
int ff_errno;

#if( ffconfigDEV_SUPPORT != 0 )
	if( pxStream->pxDevNode != NULL )
	{
		iReturned = FF_Device_Write( pvBuffer, xSize, xItems, pxStream );
	}
	else
#endif
	{
		iReturned = FF_Write( pxStream, xSize, xItems, (uint8_t *)pvBuffer );
	}

	ff_errno = prvFFErrorToErrno( iReturned );

	if( ff_errno == pdFREERTOS_ERRNO_NONE )
	{
		/* As per the standard fwrite() semantics, the return value is the
		number of complete items read, which will only equal the number of bytes
		transferred when the item size is 1. */
		xReturn = ( size_t ) iReturned;
	}
	else
	{
		xReturn = 0;
	}

	/* Store the errno to thread local storage. */
	stdioSET_ERRNO( ff_errno );

	return xReturn;
}
/*-----------------------------------------------------------*/

int ff_fgetc( FF_FILE * pxStream )
{
int32_t iResult;
int ff_errno;

	iResult = FF_GetC( pxStream );
	ff_errno = prvFFErrorToErrno( iResult );

	if( ff_errno != 0 )
	{
		iResult = FF_EOF;
	}

	/* Store the errno to thread local storage. */
	stdioSET_ERRNO( ff_errno );

	return iResult;
}
/*-----------------------------------------------------------*/

int ff_fputc( int iChar, FF_FILE *pxStream )
{
int iResult, ff_errno;

	iResult = FF_PutC( pxStream, ( uint8_t ) iChar );
	ff_errno = prvFFErrorToErrno( iResult );

	if( ff_errno != 0 )
	{
		iResult = FF_EOF;
	}

	/* Store the errno to thread local storage. */
	stdioSET_ERRNO( ff_errno );

	return iResult;
}
/*-----------------------------------------------------------*/

#if( ffconfigFPRINTF_SUPPORT == 1 )

	int ff_fprintf( FF_FILE * pxStream, const char *pcFormat, ... )
	{
	int iCount;
	size_t xResult;
	char *pcBuffer;
	va_list xArgs;

		pcBuffer = ( char * ) ffconfigMALLOC( ffconfigFPRINTF_BUFFER_LENGTH );
		if( pcBuffer == NULL )
		{
			/* Store the errno to thread local storage. */
			stdioSET_ERRNO( pdFREERTOS_ERRNO_ENOMEM );
			iCount = -1;
		}
		else
		{
			va_start( xArgs, pcFormat );
			iCount = vsnprintf( pcBuffer, ffconfigFPRINTF_BUFFER_LENGTH, pcFormat, xArgs );
			va_end( xArgs );

			/* ff_fwrite() will set ff_errno. */
			if( iCount > 0 )
			{
				xResult = ff_fwrite( pcBuffer, ( size_t ) 1, ( size_t ) iCount, pxStream );
				if( xResult < ( size_t ) iCount )
				{
					iCount = -1;
				}
			}

			ffconfigFREE( pcBuffer );
		}

		return iCount;
	}

#endif
/*-----------------------------------------------------------*/

/*_RB_ to comply with the norm, the second parameter should be an int, but size_t
is more appropriate. */
char *ff_fgets( char *pcBuffer, size_t xCount, FF_FILE *pxStream )
{
int32_t xResult;
int ff_errno;

	xResult = FF_GetLine( pxStream, ( char * ) pcBuffer, xCount );

	/* This call seems to result in errno being incorrectly set to
	FF_ERR_IOMAN_NO_MOUNTABLE_PARTITION when an EOF is encountered. */
	ff_errno = prvFFErrorToErrno( xResult );

	if( ff_errno != 0 )
	{
		pcBuffer = NULL;
	}

	/* Store the errno to thread local storage. */
	stdioSET_ERRNO( ff_errno );

	return pcBuffer;
}
/*-----------------------------------------------------------*/

int ff_seteof( FF_FILE *pxStream )
{
FF_Error_t iResult;
int iReturn, ff_errno;

	iResult = FF_SetEof( pxStream );

	ff_errno = prvFFErrorToErrno( iResult );

	if( ff_errno == 0 )
	{
		iReturn = 0;
	}
	else
	{
		iReturn = FF_EOF;
	}

	/* Store the errno to thread local storage. */
	stdioSET_ERRNO( ff_errno );

	return iReturn;
}
/*-----------------------------------------------------------*/

/*_RB_ The norm would be to return an int, but in either case it is not clear
what state the file is left in (open/closed). */
FF_FILE *ff_truncate( const char * pcFileName, long lTruncateSize )
{
FF_Error_t xResult = 0;
FF_FILE *pxStream;
size_t xReturned;
uint32_t ulLength, ulBytesLeftToAdd, ulBytesToWrite;
char *pcBufferToWrite;

	pxStream = ff_fopen( pcFileName, "a+");

	if( pxStream != NULL )
	{
		ulLength = pxStream->ulFileSize;
	}
	else
	{
		ulLength = 0;
	}

	if( pxStream == NULL )
	{
		/* Store the errno to thread local storage. */
		stdioSET_ERRNO( prvFFErrorToErrno( xResult ) );
	}
	else if( ulLength > ( uint32_t ) lTruncateSize )
	{
		/* Seek the desired position */
		xResult = FF_Seek( pxStream, lTruncateSize, FF_SEEK_SET );

		/* Make the current position equal to its length */
		if( FF_isERR( xResult ) == pdFALSE )
		{
			xResult = FF_SetEof( pxStream );
		}

		if( FF_isERR( xResult ) != pdFALSE )
		{
			ff_fclose( pxStream );
			pxStream = NULL;
		}

		/* Store the errno to thread local storage. */
		stdioSET_ERRNO( prvFFErrorToErrno( xResult ) );
	}
	else if( ulLength == ( uint32_t ) lTruncateSize )
	{
		/* Nothing to do, the file has the desired size
		and the open handle will be returned. */
	}
	else
	{
		/* lTruncateSize > ulLength.  The user wants to open this file with a
		larger size than it currently has.  Fill it with zeros. */
		pcBufferToWrite = ( char * ) ffconfigMALLOC( stdioTRUNCATE_WRITE_LENGTH );

		if( pcBufferToWrite == NULL )
		{
			ff_fclose( pxStream );
			pxStream = NULL;

			/* Store the errno to thread local storage. */
			stdioSET_ERRNO( pdFREERTOS_ERRNO_ENOMEM );
		}
		else
		{
			/* File has to grow */
			ulBytesLeftToAdd = ( ( uint32_t ) lTruncateSize ) - ulLength;

			/* Zeros must be written. */
			memset( pcBufferToWrite, '\0', stdioTRUNCATE_WRITE_LENGTH );

			while( ulBytesLeftToAdd > 0UL )
			{
				if( ( pxStream->ulFileSize % stdioTRUNCATE_WRITE_LENGTH ) != 0 )
				{
					/* Although +FAT's FF_Write() can handle any size at any
					offset, the driver puts data more efficiently if blocks are
					written at block boundaries. */
					ulBytesToWrite = stdioTRUNCATE_WRITE_LENGTH - ( pxStream->ulFileSize % stdioTRUNCATE_WRITE_LENGTH );

					if( ulBytesToWrite > ulBytesLeftToAdd )
					{
						ulBytesToWrite = ulBytesLeftToAdd;
					}
				}
				else
				{
					ulBytesToWrite = ulBytesLeftToAdd;

					if( ulBytesToWrite > stdioTRUNCATE_WRITE_LENGTH )
					{
						ulBytesToWrite = stdioTRUNCATE_WRITE_LENGTH;
					}
				}

				xReturned = ff_fwrite( pcBufferToWrite, sizeof( char ), ulBytesToWrite, pxStream );

				if( xReturned != ( size_t ) ulBytesToWrite )
				{
					/* Write error.  Close the stream and set the proper .
					errno. */
					ff_fclose( pxStream );
					pxStream = NULL;

					/* Not setting ff_errno because it has been set by other
					functions from this ff_stdio. */

					break;
				}

				ulBytesLeftToAdd -= ulBytesToWrite;
			}

			ffconfigFREE( pcBufferToWrite );
		}
	}

	return pxStream;
}
/*-----------------------------------------------------------*/

#if( ffconfigMKDIR_RECURSIVE == 0 )

	/* The normal mkdir() : if assumes that the directories leading to the last
	element of pcDirectory already exists.  For instance: mkdir( "/a/b/c" ) will
	succeed if the path "/a/b" already exists. */
	int ff_mkdir( const char *pcDirectory )
	{
	int iResult, ff_errno;
	FF_DirHandler_t xHandler;

		/* In case a CWD is used, get the absolute path. */
		pcDirectory = prvABSPath( pcDirectory );

		/* Find the i/o manager for this path */
		if( FF_FS_Find( pcDirectory, &xHandler ) == pdFALSE )
		{
			/* No such device or address. */
			stdioSET_ERRNO( pdFREERTOS_ERRNO_ENXIO );
			/* Return -1 for error as per normal mkdir() semantics. */
			iResult = -1;
		}
		else
		{
			/* A simple non-recursive make of a directory. */
			iResult = FF_MkDir( xHandler.pxManager, xHandler.pcPath );

			if( FF_GETERROR( iResult ) == FF_ERR_DIR_OBJECT_EXISTS )
			{
				/* No error if the target directory already exists. */
				iResult = FF_ERR_NONE;
			}
			ff_errno = prvFFErrorToErrno( iResult );

			/* Store the errno to thread local storage. */
			stdioSET_ERRNO( ff_errno  );

			if( ff_errno == pdFREERTOS_ERRNO_NONE )
			{
				iResult = 0;
			}
			else
			{
				/* Return -1 for error as per normal mkdir() semantics. */
				iResult = -1;
			}
		}

		return iResult;
	}
#else	/* ffconfigMKDIR_RECURSIVE */

	#warning This path is not yet included in the regression tests.

	/* The 'recursive mkdir() : if the parameter 'xRecursive' is non-zero,
	the function will try to create the complete path. */
	int ff_mkdir( const char *pcDirectory, int xRecursive )
	{
	int32_t lResult;
	FF_DirHandler_t xHandler;

		/* In case a CWD is used, get the absolute path. */
		pcDirectory = prvABSPath( pcDirectory );

		/* Find the i/o manager for this path */
		if( FF_FS_Find( pcDirectory, &xHandler ) == pdFALSE )
		{
			/* No such device or address.  Store the errno to thread local
			storage. */
			stdioSET_ERRNO( pdFREERTOS_ERRNO_ENXIO );
			/* Return -1 for error as per normal mkdir() semantics. */
			lResult = -1;
		}
		else
		{
			if( xRecursive == pdFALSE )
			{
				/* A simple non-recursive make of a directory. */
				lResult = FF_MkDir( xHandler.pxManager, xHandler.pcPath );

				if( FF_GETERROR( lResult ) == FF_ERR_DIR_OBJECT_EXISTS )
				{
					/* No error if the target directory already exists. */
					lResult = 0;
				}
			}
			else
			{
				/* The recursive option is used. */
				char pcTempPath[ffconfigMAX_FILENAME];
				FF_Error_t errCode;
				int iLength = snprintf( pcTempPath, sizeof( pcTempPath ), "%s", xHandler.pcPath );
				char *pcPtr = pcTempPath + 1, *pcPrev;
				const char *pcLast = pcTempPath + iLength;

				lResult = FF_ERR_NONE;

				for( ; ; )
				{
					for ( pcPrev = pcPtr; pcPtr < pcLast; pcPtr++ )
					{
						if( *pcPtr == '/' )
						{
							*pcPtr = '\0';
							break;
						}
					}

					if( pcPrev == pcPtr )
					{
						break;
					}

					errCode = FF_MkDir( xHandler.pxManager, pcTempPath );

					if( FF_isERR( errCode ) && FF_GETERROR( errCode ) != FF_ERR_DIR_OBJECT_EXISTS )
					{
						lResult = errCode;
						break;
					}

					if( pcPtr >= ( pcLast - 1 ) )
					{
						break;
					}

					*( pcPtr++ ) = '/';
				}
			}

			/* Store the errno to thread local storage. */
			stdioSET_ERRNO( prvFFErrorToErrno( lResult ) );
		}

		return lResult;
	}
#endif /* ffconfigMKDIR_RECURSIVE */
/*-----------------------------------------------------------*/

int ff_rmdir( const char *pcDirectory )
{
int32_t lResult;
int iReturn, ff_errno;
FF_DirHandler_t xHandler;

	/* In case a CWD is used, get the absolute path */
	pcDirectory = prvABSPath( pcDirectory );

	/* Find the i/o manager which can handle this path. */
	if( FF_FS_Find( pcDirectory, &xHandler ) == pdFALSE )
	{
		ff_errno = pdFREERTOS_ERRNO_ENXIO;	/* No such device or address */

		/* Return -1 for error as per normal rmdir() semantics. */
		iReturn = -1;
	}
	else
	{
		lResult = FF_RmDir( xHandler.pxManager, xHandler.pcPath );
		ff_errno = prvFFErrorToErrno( lResult );

		if( ff_errno == 0 )
		{
			iReturn = 0;
		}
		else
		{
			/* Return -1 for error as per normal rmdir() semantics. */
			iReturn = -1;
		}
	}

	/* Store the errno to thread local storage. */
	stdioSET_ERRNO( ff_errno );

	return iReturn;
}
/*-----------------------------------------------------------*/

int ff_remove( const char *pcPath )
{
FF_DirHandler_t xHandler;
FF_Error_t xError;
int iReturn, ff_errno;

	/* In case a CWD is used, get the absolute path */
	pcPath = prvABSPath( pcPath );

	/* Find the i/o manager which can handle this path. */
	if( FF_FS_Find( pcPath, &xHandler ) == pdFALSE )
	{
		/* No such device or address */
		ff_errno = pdFREERTOS_ERRNO_ENXIO;

		/* Return -1 for error as per normal remove() semantics. */
		iReturn = -1;
	}
	else
	{
		xError = FF_RmFile( xHandler.pxManager, xHandler.pcPath );
		ff_errno = prvFFErrorToErrno( xError );

		#if ffconfigUSE_NOTIFY
		{
			if( FF_isERR( xError ) == pdFALSE )
			{
				callFileEvents( pcPath, eFileRemove );
			}
		}
		#endif

		if( ff_errno == 0 )
		{
			iReturn = 0;
		}
		else
		{
			/* Return -1 for error as per normal remove() semantics. */
			iReturn = -1;
		}
	}

	/* Store the errno to thread local storage. */
	stdioSET_ERRNO( ff_errno );
	return iReturn;
}
/*-----------------------------------------------------------*/
/*_RB_ Last parameter not documented. */
int ff_rename( const char *pcOldName, const char *pcNewName, int bDeleteIfExists )
{
FF_DirHandler_t xHandlers[ 2 ];
FF_Error_t xError = FF_ERR_NONE;
int ff_errno = 0, iReturn;
#if( ffconfigHAS_CWD != 0 )
	char *pcOldCopy;
	size_t xSize;
#endif

	/* In case a CWD is used, get the absolute path */
	pcOldName = prvABSPath( pcOldName );

	/* Find the i/o manager which can handle this path */
	if( FF_FS_Find( pcOldName, &xHandlers[ 0 ] ) == pdFALSE )
	{
		xError = ( int32_t ) ( FF_ERR_NULL_POINTER | FF_MOVE );
		ff_errno = pdFREERTOS_ERRNO_ENXIO;	/* No such device or address */
	}
	else
	{
		#if( ffconfigHAS_CWD != 0 )
		{
			xSize = strlen( xHandlers[0].pcPath ) + 1;
			pcOldCopy = ( char *)ffconfigMALLOC( xSize );

			if( pcOldCopy == NULL )
			{
				/* Could not allocate space to store a file name. */
				ff_errno = pdFREERTOS_ERRNO_ENOMEM;
				xError = ( int32_t ) ( FF_ERR_NOT_ENOUGH_MEMORY | FF_MOVE );
			}
			else
			{
				/* The function prvABSPath() returns a pointer to the task
				storage space. Rename needs to call it twice and therefore the
				path must be stored before it gets overwritten. */
				memcpy( pcOldCopy, xHandlers[0].pcPath, xSize );
				xHandlers[0].pcPath = pcOldCopy;
			}
		}
		#endif /* ffconfigHAS_CWD != 0 */

#if( ffconfigHAS_CWD != 0 )
		if( pcOldCopy != NULL )
#endif /* ffconfigHAS_CWD != 0 */
		{
			pcNewName = prvABSPath( pcNewName );

			/* Find the i/o manager which can handle this path */
			if( FF_FS_Find( pcNewName, &( xHandlers[ 1 ] ) ) == pdFALSE )
			{
				xError = ( int32_t ) ( FF_ERR_NULL_POINTER | FF_MOVE );
				ff_errno = pdFREERTOS_ERRNO_ENXIO;	/* No such device or address */
			}
			else if( xHandlers[ 0 ].pxManager != xHandlers[ 1 ].pxManager )
			{
				xError = ( int32_t ) ( FF_ERR_NULL_POINTER | FF_MOVE );
				/* Cross-device link, which can not be done. */
				ff_errno = pdFREERTOS_ERRNO_EXDEV;
			}
			else
			{
				xError = FF_Move( xHandlers[ 0 ].pxManager, xHandlers[ 0 ].pcPath, xHandlers[ 1 ].pcPath, bDeleteIfExists );

				ff_errno = prvFFErrorToErrno( xError );

				#if ffconfigUSE_NOTIFY
				{
					if( FF_isERR( xError ) == pdFALSE )
					{
						callFileEvents( pcNewName, eFileChange );
					}
				}
				#endif
			}

			#if( ffconfigHAS_CWD != 0 )
			{
				ffconfigFREE( pcOldCopy );
			}
			#endif
		}
	}

	/* Store the errno to thread local storage. */
	stdioSET_ERRNO( ff_errno );

	if( ff_errno == 0 )
	{
		iReturn = 0;
	}
	else
	{
		/* Return -1 for error as per normal rmdir() semantics. */
		iReturn = -1;
	}

	return iReturn;
}
/*-----------------------------------------------------------*/

int ff_stat( const char *pcName, FF_Stat_t *pxStatBuffer )
{
FF_DirEnt_t xDirEntry;
uint32_t ulFileCluster;
FF_Error_t xError;
int iResult;
FF_DirHandler_t xHandler;
BaseType_t xIndex;
FF_FindParams_t xFindParams;
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	const FF_T_WCHAR *pcFileName = NULL;
#else
	/* Initialised to prevent MSVC incorrectly claiming the variable is used
	without being initialised. */
	const char *pcFileName = NULL;
#endif

	memset( &xFindParams, '\0', sizeof( xFindParams ) );

	/* Insert the current working directory in front of relative paths. */
	pcName = prvABSPath( pcName );

	/* Look-up the I/O manager for the file system. */
	if( FF_FS_Find( pcName, &xHandler ) == pdFALSE )
	{
		/* No such device or address. */
		xError = ( FF_Error_t ) ( pdFREERTOS_ERRNO_ENXIO | FF_STAT_FUNC );
	}
	else
	{
		xError = FF_ERR_NONE;
		pcName = xHandler.pcPath;

		/* Let xIndex point to the last occurrence of '/' or '\', to separate
		the path from the file name. */
		xIndex = ( BaseType_t ) STRLEN( pcName );
		while( xIndex != 0 )
		{
			if( ( pcName[ xIndex ] == '\\' ) || ( pcName[ xIndex ] == '/' ) )
			{
				break;
			}

			xIndex--;
		}

		/* Copy the file name, i.e. the string that comes after the last
		separator. */
		pcFileName = pcName + xIndex + 1;

		if( xIndex == 0 )
		{
			/* Only for the root, the slash is part of the directory name.
			'xIndex' now equals to the length of the path name. */
			xIndex = 1;
		}

		/* FF_CreateShortName() might set flags FIND_FLAG_FITS_SHORT and
		FIND_FLAG_SIZE_OK. */
		FF_CreateShortName( &xFindParams, pcFileName );

		/* Lookup the path and find the cluster pointing to the directory: */
		xFindParams.ulDirCluster = FF_FindDir( xHandler.pxManager, pcName, xIndex, &xError );
	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		/* See if the file does exist within the given directory. */
		ulFileCluster = FF_FindEntryInDir( xHandler.pxManager, &xFindParams, pcFileName, 0x00, &xDirEntry, &xError );

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
			xError = FF_ERR_FILE_NOT_FOUND | FF_STAT_FUNC;
		}
	}

	if( ( pxStatBuffer != NULL ) && ( FF_isERR( xError ) == pdFALSE ) )
	{
		if( ( xDirEntry.ucAttrib & FF_FAT_ATTR_DIR ) != 0 )
		{
			pxStatBuffer->st_mode = ( unsigned short ) FF_IFDIR;
		}
		else
		{
			pxStatBuffer->st_mode = ( unsigned short ) FF_IFREG;
		}

		#if( ffconfigDEV_SUPPORT != 0 )
		{
		BaseType_t bIsDeviceDir = xCheckDevicePath( pcFileName );

			if( bIsDeviceDir != pdFALSE )
			{
				FF_Device_GetDirEnt( xHandler.pcPath, &( xDirEntry ) );
			}
		}
		#endif

		/* Despite the warning output by MSVC - it is not possible to get here
		if xDirEntry has not been initialised. */
		pxStatBuffer->st_size = xDirEntry.ulFileSize;
		pxStatBuffer->st_ino = xDirEntry.ulObjectCluster;
		pxStatBuffer->st_dev = ( short ) xHandler.xFSIndex;

		#if( ffconfigTIME_SUPPORT == 1 )
		{
			pxStatBuffer->st_atime = ( unsigned long ) prvFileTime( &( xDirEntry.xAccessedTime ) );
			pxStatBuffer->st_mtime = ( unsigned long ) prvFileTime( &( xDirEntry.xModifiedTime ) );
			pxStatBuffer->st_ctime = ( unsigned long ) prvFileTime( &( xDirEntry.xCreateTime ) );
		}
		#endif
	}

	stdioSET_ERRNO( prvFFErrorToErrno( xError ) );

	if( FF_isERR( xError ) == pdFALSE )
	{
		iResult = 0;
	}
	else
	{
		iResult = -1;
	}

	return iResult;
}  /* ff_stat() */
/*-----------------------------------------------------------*/

#if(  ffconfigHAS_CWD == 1 )

	int ff_chdir( const char *pcDirectoryName )
	{
	int iResult, iLength, iValid = pdFALSE;
	WorkingDirectory_t *pxDir = NULL;

		/* Not all paths set an errno. */
		stdioSET_ERRNO( 0 );

		/* Is there a file system mounted? */
		if( FF_FS_Count() != 0 )
		{
			/* In case a CWD is used, get the absolute path. */
			pcDirectoryName = prvABSPath( pcDirectoryName );
			pxDir = pxFindCWD();

			if( pxDir == NULL )
			{
				/* Store the errno to thread local storage. */
				stdioSET_ERRNO( pdFREERTOS_ERRNO_ENOMEM );

				/* Return -1 for error as per normal chdir() semantics. */
				iResult = -1;
			}
			else
			{
				/* The CWD will be stored without a trailing '/'.  If "/"
				happens to be the CWD, it will be stored as an empty string. */
				iLength = strlen( pcDirectoryName );

				/* Knock off the trailing / if one exits - being careful not to
				remove the trailing slash if this is the root directory. */
				if( ( iLength > 1 ) && ( pxDir->pcFileName[ iLength - 1 ] == '/' ) )
				{
					pxDir->pcFileName[ iLength - 1 ] = '\0';
				}

				stdioSET_ERRNO( pdFREERTOS_ERRNO_ENOENT );

				/* Does the directory exist? */
				if( strcmp( pcDirectoryName, "/" ) == 0 )
				{
					/* Moving to the root - which exists. */
					iValid = pdTRUE;
				}
				else if( ff_finddir( pxDir->pcFileName ) != pdFALSE )
				{
					iValid = pdTRUE;
				}
			}
		}

		if( iValid == pdTRUE )
		{
			/* The generated name becomes the CWD.  No need to test for overflow
			as pcPath and pcFileName are the same size. */
			strcpy( pxDir->pcCWD, pxDir->pcFileName );

			/* chdir returns 0 for success. */
			iResult = FF_ERR_NONE;
		}
		else
		{
			/* Return -1 for error as per normal chdir() semantics. */
			iResult = -1;
		}

		return iResult;
	}

#endif /* ffconfigHAS_CWD == 1 */
/*-----------------------------------------------------------*/

#if(  ffconfigHAS_CWD == 1 )

	char *ff_getcwd( char *pcBuffer, size_t xBufferLength )
	{
	WorkingDirectory_t *pxDir = pxFindCWD();

		stdioSET_ERRNO( 0 );

		if( ( pxDir == NULL ) || ( pxDir->pcCWD[0] == '\0' ) )
		{
			if( xBufferLength > strlen( "/" ) )
			{
				strncpy( pcBuffer, "/", xBufferLength );
			}
			else
			{
				pcBuffer = NULL;
			}
		}
		else
		{
			if( strlen( pxDir->pcCWD ) < xBufferLength )
			{
				strncpy( pcBuffer, pxDir->pcCWD, xBufferLength );
			}
			else
			{
				pcBuffer = NULL;
			}
		}

		return pcBuffer;
	}

#endif	/* ffconfigHAS_CWD */
/*-----------------------------------------------------------*/

int ff_findfirst( const char *pcPath, FF_FindData_t *pxFindData )
{
int iIsRootDir, iReturn;
const char *pcDirectory;

	iReturn = 0;

	memset( pxFindData, '\0', sizeof( *pxFindData ) );

	pxFindData->pcFileName = pxFindData->xDirectoryEntry.pcFileName;

	/* In case a CWD is used, get the absolute path. */
	pcDirectory = prvABSPath( pcPath );

	if( ( pcDirectory[ 0 ] == '/' ) && ( pcDirectory[ 1 ] == 0x00 ) )
	{
		iIsRootDir = pdTRUE;
	}
	else
	{
		iIsRootDir = pdFALSE;
	}

		/* Find the i/o manager that can handle this path. */
	if( FF_FS_Find( pcDirectory, &( pxFindData->xDirectoryHandler ) ) == pdFALSE )
	{
		if( ( iIsRootDir == pdFALSE ) || ( FF_FS_Count() == 0 ) )
		{
			stdioSET_ERRNO( prvFFErrorToErrno( ( FF_Error_t ) ( FF_ERR_NULL_POINTER | FF_FINDFIRST ) ) );
			iReturn = -1;
		}
	}

	/* Check no errors before continuing. */
	if( iReturn == 0 )
	{
		#if( ffconfigDEV_SUPPORT != 0 )
		{
			pxFindData->bIsDeviceDir = xCheckDevicePath( pcDirectory );
		}
		#endif

		if( iIsRootDir != pdFALSE )
		{
			/* A listing of the root directory will include pseudo entries
			such as /ram /nand. */
			pxFindData->xDirectoryHandler.xFSIndex = FF_FS_Count();

			/* Only add '.' */
			pxFindData->xDirectoryHandler.u.bits.bAddDotEntries = stdioDIR_ENTRY_DOT_1;
		}
		else
		{
			/* This is the root of a sub file system, add "." and ".." */
			pxFindData->xDirectoryHandler.u.bits.bAddDotEntries = stdioDIR_ENTRY_DOT_1 | stdioDIR_ENTRY_DOT_2;
		}

		pxFindData->xDirectoryHandler.u.bits.bIsValid = pdTRUE;
		iReturn = ff_findnext( pxFindData );
	}
	else
	{
		/* errno has already been set. */
	}

	return iReturn;
}
/*-----------------------------------------------------------*/

int ff_findnext( FF_FindData_t *pxFindData )
{
FF_Error_t xError;
#if( ffconfigTIME_SUPPORT != 0 )
	BaseType_t xSetTime = 0;
#endif	/* ffconfigTIME_SUPPORT */


	if( pxFindData->xDirectoryHandler.u.bits.bIsValid == pdFALSE )
	{
		xError = ( FF_Error_t ) ( FF_ERR_DIR_INVALID_PARAMETER | FF_FINDNEXT );
		FF_PRINTF("ff_findnext: xDirectoryHandler not valid\n" );
	}
	else
	{
		xError = ( FF_Error_t ) ( FF_ERR_DIR_END_OF_DIR | FF_FINDNEXT );
		if( pxFindData->xDirectoryHandler.pxManager != NULL )
		{
			if( pxFindData->xDirectoryHandler.u.bits.bFirstCalled == pdFALSE )
			{
				pxFindData->xDirectoryHandler.u.bits.bFirstCalled = pdTRUE;
				xError = FF_FindFirst( pxFindData->xDirectoryHandler.pxManager, &( pxFindData->xDirectoryEntry ),
					pxFindData->xDirectoryHandler.pcPath );
			}
			else if( pxFindData->xDirectoryHandler.u.bits.bEndOfDir == pdFALSE )
			{
				xError = FF_FindNext( pxFindData->xDirectoryHandler.pxManager, &( pxFindData->xDirectoryEntry ) );
			}

			if( FF_GETERROR( xError ) == FF_ERR_DIR_END_OF_DIR )
			{
				/* Stop further calls to FF_FindNext(). */
				pxFindData->xDirectoryHandler.u.bits.bEndOfDir = pdTRUE;
			}

			#if( ffconfigDEV_SUPPORT != 0 )
			{
				if( pxFindData->bIsDeviceDir != pdFALSE )
				{
					FF_Device_GetDirEnt( pxFindData->xDirectoryHandler.pcPath, &( pxFindData->xDirectoryEntry ) );
				}
			}
			#endif
		}

		if( FF_isERR( xError ) == pdFALSE )
		{
			/* If an entry is found, see if it is a dot-entry.  Dot-entries
			("." and "..") need a time-stamp. */
			if( pxFindData->xDirectoryEntry.pcFileName[ 0 ] == '.' )
			{
				if( ( pxFindData->xDirectoryEntry.pcFileName[ 1 ] == '.' ) &&
					( pxFindData->xDirectoryEntry.pcFileName[ 2 ] == '\0' ) )
				{
					/* This is a directory "..". Clear the flag for DOT_2. */
					pxFindData->xDirectoryHandler.u.bits.bAddDotEntries &= stdioDIR_ENTRY_DOT_1;
					#if( ffconfigTIME_SUPPORT != 0 )
					{
						/* The dot-entries do not have a proper time stamp, add
						it here. */
						xSetTime = pdTRUE;
					}
					#endif	/* ffconfigTIME_SUPPORT */
				}
				else if( pxFindData->xDirectoryEntry.pcFileName[ 1 ] == '\0' )
				{
					/* This is a directory ".". Clear the flag for DOT_1. */
					pxFindData->xDirectoryHandler.u.bits.bAddDotEntries &= stdioDIR_ENTRY_DOT_2;
					#if( ffconfigTIME_SUPPORT != 0 )
					{
						xSetTime = pdTRUE;
					}
					#endif	/* ffconfigTIME_SUPPORT */
				}
			}
		}

		if( FF_GETERROR( xError ) == FF_ERR_DIR_END_OF_DIR )
		{
			/* No more physical entries were found.  Now see if there are FS
			entries or dot-entries to be added: */
			while( ( pxFindData->xDirectoryHandler.xFSIndex > 0 ) ||
				   ( pxFindData->xDirectoryHandler.u.bits.bAddDotEntries != 0 ) )
			{
				if( pxFindData->xDirectoryHandler.xFSIndex > 0 )
				{
				FF_SubSystem_t xSubSystem;
				int found;

					pxFindData->xDirectoryHandler.xFSIndex--;
					found = FF_FS_Get( pxFindData->xDirectoryHandler.xFSIndex, &xSubSystem );

					if( ( found == pdFALSE ) || ( xSubSystem.pcPath[ 1 ] == '\0' ) )
					{
						continue;
					}
					snprintf( pxFindData->xDirectoryEntry.pcFileName, sizeof( pxFindData->xDirectoryEntry.pcFileName ), "%s", xSubSystem.pcPath + 1 );

					if( xSubSystem.pxManager != NULL )
					{
						pxFindData->xDirectoryEntry.ulObjectCluster = xSubSystem.pxManager->xPartition.ulRootDirCluster;
					}
					else
					{
						pxFindData->xDirectoryEntry.ulObjectCluster = 0;
					}
				}
				else if( ( pxFindData->xDirectoryHandler.u.bits.bAddDotEntries & stdioDIR_ENTRY_DOT_2 ) != 0 )
				{
					strcpy( pxFindData->xDirectoryEntry.pcFileName, "..");

					/* Clear DOT_2 (keep DOT_1). */
					pxFindData->xDirectoryHandler.u.bits.bAddDotEntries &= stdioDIR_ENTRY_DOT_1;
				}
				else
				{
					strcpy( pxFindData->xDirectoryEntry.pcFileName, ".");
					pxFindData->xDirectoryHandler.u.bits.bAddDotEntries = 0;
				}

				pxFindData->xDirectoryEntry.ucAttrib = FF_FAT_ATTR_READONLY | FF_FAT_ATTR_DIR;
				pxFindData->xDirectoryEntry.ulFileSize = stdioDOT_ENTRY_FILE_SIZE;
				#if( ffconfigTIME_SUPPORT != 0 )
				{
					xSetTime = pdTRUE;
				}
				#endif	/* ffconfigTIME_SUPPORT */

				xError = FF_ERR_NONE;
				break;
			}
		}

		#if( ffconfigTIME_SUPPORT != 0 )
		{
			if( xSetTime != pdFALSE )
			{
				FF_TimeStruct_t xTimeStruct;
				time_t xSeconds;

				xSeconds = FreeRTOS_time( NULL );
				FreeRTOS_gmtime_r( &xSeconds, &xTimeStruct );

				pxFindData->xDirectoryEntry.xCreateTime.Year   = ( uint16_t ) ( xTimeStruct.tm_year + 1900 );	/* Year (e.g. 2009). */
				pxFindData->xDirectoryEntry.xCreateTime.Month  = ( uint16_t ) ( xTimeStruct.tm_mon + 1 );		/* Month (e.g. 1 = Jan, 12 = Dec). */
				pxFindData->xDirectoryEntry.xCreateTime.Day    = ( uint16_t ) xTimeStruct.tm_mday;				/* Day (1 - 31). */
				pxFindData->xDirectoryEntry.xCreateTime.Hour   = ( uint16_t ) xTimeStruct.tm_hour;				/* Hour (0 - 23). */
				pxFindData->xDirectoryEntry.xCreateTime.Minute = ( uint16_t ) xTimeStruct.tm_min;				/* Min (0 - 59). */
				pxFindData->xDirectoryEntry.xCreateTime.Second = ( uint16_t ) xTimeStruct.tm_sec;				/* Second (0 - 59). */
				pxFindData->xDirectoryEntry.xModifiedTime      = pxFindData->xDirectoryEntry.xCreateTime;		/* Date and Time Modified. */
				pxFindData->xDirectoryEntry.xAccessedTime      = pxFindData->xDirectoryEntry.xCreateTime;		/* Date of Last Access. */
			}
		}
		#endif	/* ffconfigTIME_SUPPORT */

		if( FF_GETERROR( xError ) == FF_ERR_DIR_END_OF_DIR )
		{
			/* FF_ERR_DIR_END_OF_DIR will be returned. */
			pxFindData->xDirectoryHandler.u.bits.bIsValid = 0;
		}

		pxFindData->ucAttributes = pxFindData->xDirectoryEntry.ucAttrib;
		pxFindData->ulFileSize = pxFindData->xDirectoryEntry.ulFileSize;
	}

	stdioSET_ERRNO( prvFFErrorToErrno( xError ) );

	return xError;
}
/*-----------------------------------------------------------*/

/*-----------------------------------------------------------
 * ff_isdirempty() returns 1 if a given directory is empty
 * (has no entries)
 *-----------------------------------------------------------*/
int ff_isdirempty(const char *pcPath )
{
	FF_DirHandler_t xHandler;
	int iResult;
	/* In case a CWD is used, get the absolute path */
	pcPath = prvABSPath( pcPath );
	/* Find the i/o manager which can handle this path */
	if( FF_FS_Find( pcPath, &xHandler ) == pdFALSE )
	{
		iResult = ( int ) ( FF_ERR_NULL_POINTER | FF_ISDIREMPTY );
	}
	else
	{
		iResult = FF_isDirEmpty( xHandler.pxManager, xHandler.pcPath );
	}

	/* Store the errno to thread local storage. */
	stdioSET_ERRNO( prvFFErrorToErrno( iResult ) );
	return iResult;
}
/*-----------------------------------------------------------*/

#if (ffconfig64_NUM_SUPPORT != 0 )
int64_t ff_diskfree(const char *pcPath, uint32_t *pxSectorCount )
#else
int32_t ff_diskfree(const char *pcPath, uint32_t *pxSectorCount )
#endif
{
FF_DirHandler_t xHandler;
FF_Error_t xError;
#if (ffconfig64_NUM_SUPPORT != 0 )
	#define DISKFREE_RETURN_TYPE	int64_t
	int64_t lReturn;
#else
	#define DISKFREE_RETURN_TYPE	int32_t
	int32_t lReturn;
#endif

	if( FF_FS_Find( pcPath, &xHandler ) == pdFALSE )
	{
		/* Return cluster 0 for error. */
		lReturn = 0ul;

		/* Store the errno to thread local storage. */
		stdioSET_ERRNO( pdFREERTOS_ERRNO_ENXIO );	/* No such device or address */
	}
	else
	{
		if (pxSectorCount != NULL )
		{
			*pxSectorCount = xHandler.pxManager->xPartition.ulDataSectors;
		}

		lReturn = ( DISKFREE_RETURN_TYPE ) FF_GetFreeSize( xHandler.pxManager, &xError ) / 512;

		/* Store the errno to thread local storage. */
		stdioSET_ERRNO( prvFFErrorToErrno( xError ) );
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

int ff_finddir(const char *pcPath )
{
int iResult;
FF_DirHandler_t xHandler;
FF_Error_t errCode;

	if( FF_FS_Find( pcPath, &xHandler ) == pdFALSE )
	{
		/* Return cluster 0 for error. */
		iResult = 0;
	}
	else
	{
		iResult = ( int ) FF_FindDir( xHandler.pxManager, xHandler.pcPath, ( uint16_t ) strlen( xHandler.pcPath ), &errCode );
	}

	return iResult;
}
/*-----------------------------------------------------------*/

size_t ff_filelength( FF_FILE *pxStream )
{
FF_Error_t xReturned;
uint32_t ulLength;

	xReturned = FF_GetFileSize( pxStream, &( ulLength ) );

	if( FF_isERR( xReturned ) != pdFALSE )
	{
		/* An error. */
		ulLength = ( uint32_t ) 0u;
		stdioSET_ERRNO( prvFFErrorToErrno( xReturned ) );
	}
	else
	{
		stdioSET_ERRNO( pdFREERTOS_ERRNO_NONE );
	}

	return ( size_t ) ulLength;
}
/*-----------------------------------------------------------*/

/*-----------------------------------------------------------
 * Delete a directory and, recursively, all of its contents
 *-----------------------------------------------------------*/
#if( ffconfigUSE_DELTREE != 0 )
	int ff_deltree( const char *pcDirectory )
	{
	int iResult;
	char *pcPath;

		pcPath = ( char * ) ffconfigMALLOC( ffconfigMAX_FILENAME );
		if( pcPath != NULL )
		{
			/* In case a CWD is used, get the absolute path */
			pcDirectory = prvABSPath( pcDirectory );
			snprintf (pcPath, ffconfigMAX_FILENAME, "%s", pcDirectory);
			/* This recursive function will do all the work */
			iResult = ff_deltree_recurse (pcPath);
			if( iResult >= 0 )
			{
				iResult = ff_rmdir( pcPath );
				if( iResult )
				{
					FF_PRINTF("ff_deltree(%s): %s\n", pcPath, strerror( stdioGET_ERRNO( ) ) );
				}
			}
			ffconfigFREE( pcPath );
		}
		else
		{
			iResult = -1;
			stdioSET_ERRNO( pdFREERTOS_ERRNO_ENOMEM );
		}
		return iResult;
	}
#endif /* ffconfigUSE_DELTREE */
/*-----------------------------------------------------------*/

#if( ffconfigUSE_DELTREE != 0 )
	static int ff_deltree_recurse( char *pcPath )
	{
	FF_FindData_t *pxFindData;
	BaseType_t xIsDir, xIsDotDir;
	FF_Error_t xError;
	int iResult, iNext, iNameLength, pass, iCount = 0;

		pxFindData = ( FF_FindData_t * ) ffconfigMALLOC( sizeof( *pxFindData ) );
		if( pxFindData != NULL )
		{
			iNameLength = ( int ) strlen( pcPath );
			/* The directory will be scanned 2 times.  First the sub-directories will be
			entered and their contents deleted.  In the second pass the files in the
			current directory will be removed.  In this way 'pcPath' can be constantly
			used and reused recursively which is cheaper than allocating 'ffconfigMAX_FILENAME'
			bytes within each recursion. */
			for( pass = 0; pass < 2; pass++ )
			{
				for( iResult = ff_findfirst( pcPath, pxFindData );
					 iResult == 0;
					 iResult = iNext )
				{
					xIsDir = ( pxFindData->xDirectoryEntry.ucAttrib & FF_FAT_ATTR_DIR ) != 0;
					if( ( pass == 0 ) && ( xIsDir != pdFALSE ) )
					{
					/* This entry is a directory.  Don't traverse '.' or '..' */
					xIsDotDir = 0;

						if( pxFindData->pcFileName[ 0 ] == '.' )
						{
							if( ( pxFindData->pcFileName[ 1 ] == '.' ) &&
								( pxFindData->pcFileName[ 2 ] == '\0' ) )
							{
								xIsDotDir = 2;
							}
							else if( pxFindData->pcFileName[ 1 ] == '\0' )
							{
								xIsDotDir = 1;
							}
						}
						if( xIsDotDir == 0 )
						{
							snprintf( pcPath + iNameLength, ( size_t ) ( ffconfigMAX_FILENAME - iNameLength ) , "%s%s",
								pcPath[ iNameLength - 1 ] == '/' ? "" : "/", pxFindData->pcFileName );

							/* Let pxFindData point to the next element before
							the current will get removed. */
							iNext = ff_findnext( pxFindData );

							/* Remove the contents of this directory. */
							iResult = ff_deltree_recurse( pcPath );
							if( iResult < 0 )
							{
								iCount = -1;
								break;
							}
							iCount += iResult;
							/* remove the directory itself */
							xError = ff_rmdir( pcPath );
							if( xError != 0 )
							{
								FF_PRINTF( "ff_rmdir( %s ): errno %d\n", pcPath, stdioGET_ERRNO() );
							}
							else
							{
								iCount++;
							}
						}
						else
						{
							iNext = ff_findnext( pxFindData );
						}
					}
					else if( ( pass == 1 ) && ( xIsDir == pdFALSE ) )
					{
						snprintf( pcPath + iNameLength, ( size_t ) ( ffconfigMAX_FILENAME - iNameLength ), "%s%s",
							pcPath[ iNameLength - 1 ] == '/' ? "" : "/", pxFindData->pcFileName );

						/* Let pxFindData point to the next element before
						the current will get removed. */
						iNext = ff_findnext( pxFindData );

						/* Remove a plain file. */
						xError = ff_remove( pcPath );
						if( xError != 0 )
						{
							FF_PRINTF( "ff_remove( %s ): errno %d\n", pcPath, stdioGET_ERRNO() );
						}
						else
						{
							iCount++;
						}
					}
					else
					{
						iNext = ff_findnext( pxFindData );
					}
					pcPath[ iNameLength ] = '\0';
				}

				if( FF_GETERROR( iResult ) == FF_ERR_DIR_INVALID_PATH )
				{
					break;
				}
				if( ( FF_GETERROR( iResult ) != FF_ERR_DIR_END_OF_DIR ) && ( FF_GETERROR( iResult ) != FF_ERR_FILE_INVALID_PATH ) )
				{
					FF_PRINTF( "ff_deltree_recurse[%s]: %s\n", pcPath, ( const char * ) FF_GetErrMessage( iResult ) );
				}
			}
			ffconfigFREE( pxFindData );
		}
		else
		{
			iCount = -1;
			stdioSET_ERRNO( pdFREERTOS_ERRNO_ENOMEM );
		}

		return iCount;
	}
#endif /* ffconfigUSE_DELTREE */
/*-----------------------------------------------------------*/

int prvFFErrorToErrno( FF_Error_t xError )
{
	if( FF_isERR( xError ) == pdFALSE )
	{
		return 0;
	}

	/* Store the last +FAT error code received. */
	stdioSET_FF_ERROR( xError );

	switch( FF_GETERROR( xError ) )
	{
	/* Global Error Codes. */
	case FF_ERR_NONE:							return 0;			/* No Error. */

	case FF_ERR_NULL_POINTER:					return pdFREERTOS_ERRNO_EBADF;		/* pxIOManager was NULL. */
	case FF_ERR_NOT_ENOUGH_MEMORY:				return pdFREERTOS_ERRNO_ENOMEM;		/* malloc() failed! - Could not allocate handle memory. */
	case FF_ERR_DEVICE_DRIVER_FAILED:			return pdFREERTOS_ERRNO_EIO;		/* The Block Device driver reported a FATAL error, cannot continue. */

	/* User return codes for Rd/Wr functions:. */
	case FF_ERR_IOMAN_DRIVER_BUSY:				return pdFREERTOS_ERRNO_EBUSY;		/* 10. */
	case FF_ERR_IOMAN_DRIVER_FATAL_ERROR:		return pdFREERTOS_ERRNO_EUNATCH;	/* Protocol driver not attached. */

	/* IOMAN Error Codes. */
	case FF_ERR_IOMAN_BAD_BLKSIZE:				return pdFREERTOS_ERRNO_EINVAL;		/* The provided blocksize was not a multiple of 512. */
	case FF_ERR_IOMAN_BAD_MEMSIZE:				return pdFREERTOS_ERRNO_EINVAL;		/* The memory size was not a multiple of the blocksize. */
	case FF_ERR_IOMAN_DEV_ALREADY_REGD:			return pdFREERTOS_ERRNO_EADDRINUSE;	/* Device was already registered. Use FF_UnRegister() to re-use this IOMAN with another device. */
	case FF_ERR_IOMAN_NO_MOUNTABLE_PARTITION:	return pdFREERTOS_ERRNO_ENOMEDIUM;	/* A mountable partition could not be found on the device. */
	case FF_ERR_IOMAN_INVALID_FORMAT:			return pdFREERTOS_ERRNO_EFTYPE;		/* The. */
	case FF_ERR_IOMAN_INVALID_PARTITION_NUM:	return pdFREERTOS_ERRNO_EINVAL;		/* The partition number provided was out of range. */
	case FF_ERR_IOMAN_NOT_FAT_FORMATTED:		return pdFREERTOS_ERRNO_EFTYPE;		/* The partition did not look like a FAT partition. */
	case FF_ERR_IOMAN_DEV_INVALID_BLKSIZE:		return pdFREERTOS_ERRNO_EINVAL;		/* IOMAN object BlkSize is not compatible with the blocksize of this device driver. */
	case FF_ERR_IOMAN_PARTITION_MOUNTED:		return pdFREERTOS_ERRNO_EADDRINUSE;	/* Device is in use by an actively mounted partition. Unmount the partition first. */
	case FF_ERR_IOMAN_ACTIVE_HANDLES:			return pdFREERTOS_ERRNO_EBUSY;		/* The partition cannot be unmounted until all active file handles are closed. (There may also be active handles on the cache). */
	case FF_ERR_IOMAN_GPT_HEADER_CORRUPT:		return pdFREERTOS_ERRNO_EBADE;		/* The GPT partition table appears to be corrupt, refusing to mount. */
	case FF_ERR_IOMAN_NOT_ENOUGH_FREE_SPACE:	return pdFREERTOS_ERRNO_ENOSPC;		/* 22. */
	case FF_ERR_IOMAN_OUT_OF_BOUNDS_READ:		return pdFREERTOS_ERRNO_ESPIPE;		/* 23, return 'Illegal seek'. */
	case FF_ERR_IOMAN_OUT_OF_BOUNDS_WRITE:		return pdFREERTOS_ERRNO_ESPIPE;		/* 24. */
	case FF_ERR_IOMAN_DRIVER_NOMEDIUM:			return pdFREERTOS_ERRNO_ENOMEDIUM;	/* The medium (e.g. SD-card) has been extracted. */

	/* File Error Codes                         30 +. */
	case FF_ERR_FILE_ALREADY_OPEN:				return pdFREERTOS_ERRNO_EALREADY;	/* File is in use. */
	case FF_ERR_FILE_NOT_FOUND:					return pdFREERTOS_ERRNO_ENOENT;		/* File was not found. */
	case FF_ERR_FILE_OBJECT_IS_A_DIR:			return pdFREERTOS_ERRNO_EISDIR;		/* Tried to FF_Open() a Directory. */
	case FF_ERR_FILE_IS_READ_ONLY:				return pdFREERTOS_ERRNO_EROFS;		/* Tried to FF_Open() a file marked read only. */
	case FF_ERR_FILE_INVALID_PATH:				return pdFREERTOS_ERRNO_ENOTDIR;	/* The path of the file was not found. */
	case FF_ERR_FILE_NOT_OPENED_IN_WRITE_MODE:	return pdFREERTOS_ERRNO_EACCES;		/* 35. */
	case FF_ERR_FILE_NOT_OPENED_IN_READ_MODE:	return pdFREERTOS_ERRNO_EACCES;		/* 36. */
	case FF_ERR_FILE_EXTEND_FAILED:				return pdFREERTOS_ERRNO_ENOSPC;		/* Could not extend the file. */
	case FF_ERR_FILE_DESTINATION_EXISTS:		return pdFREERTOS_ERRNO_EEXIST;		/* 38. */
	case FF_ERR_FILE_SOURCE_NOT_FOUND:			return pdFREERTOS_ERRNO_ENOENT;		/* 39. */
	case FF_ERR_FILE_DIR_NOT_FOUND:				return pdFREERTOS_ERRNO_ENOENT;		/* 40. */
	case FF_ERR_FILE_COULD_NOT_CREATE_DIRENT:	return pdFREERTOS_ERRNO_EIO;		/* 41. */
	case FF_ERR_FILE_BAD_HANDLE:				return pdFREERTOS_ERRNO_EBADF;		/* A file handle was invalid. */
	case FF_ERR_FILE_MEDIA_REMOVED:				return pdFREERTOS_ERRNO_ENODEV;		/* File handle got invalid because media was removed. */
	case FF_ERR_FILE_SEEK_INVALID_POSITION:		return pdFREERTOS_ERRNO_ESPIPE;		/* Illegal position, outside the file's space */
	case FF_ERR_FILE_SEEK_INVALID_ORIGIN:		return pdFREERTOS_ERRNO_EINVAL;		/* Seeking beyond end of file. */

	/* Directory Error Codes                    50 +. */
	case FF_ERR_DIR_OBJECT_EXISTS:				return pdFREERTOS_ERRNO_EEXIST;		/* A file or folder of the same name already exists in the current directory. */
	case FF_ERR_DIR_DIRECTORY_FULL:				return pdFREERTOS_ERRNO_ENOSPC;		/* No more items could be added to the directory. */
	case FF_ERR_DIR_END_OF_DIR:					return pdFREERTOS_ERRNO_ENMFILE;	/*/. */
	case FF_ERR_DIR_NOT_EMPTY:					return pdFREERTOS_ERRNO_ENOTEMPTY;	/* Cannot delete a directory that contains files or folders. */
	case FF_ERR_DIR_INVALID_PATH:				return pdFREERTOS_ERRNO_EINVAL;		/* Could not find the directory specified by the path. */
	case FF_ERR_DIR_CANT_EXTEND_ROOT_DIR:		return pdFREERTOS_ERRNO_ENOSPC;		/* Can't extend the root dir. */
	case FF_ERR_DIR_EXTEND_FAILED:				return pdFREERTOS_ERRNO_ENOSPC;		/* Not enough space to extend the directory. */
	case FF_ERR_DIR_NAME_TOO_LONG:				return pdFREERTOS_ERRNO_ENAMETOOLONG;/* Name exceeds the number of allowed characters for a filename. */

	/* Fat Error Codes                          70 +. */
	case FF_ERR_FAT_NO_FREE_CLUSTERS:			return pdFREERTOS_ERRNO_ENOSPC;		/* No more free space is available on the disk. */

	/* UNICODE Error Codes                      100 +. */
	case FF_ERR_UNICODE_INVALID_CODE:			return pdFREERTOS_ERRNO_EBADE;		/* An invalid Unicode character was provided!. */
	case FF_ERR_UNICODE_DEST_TOO_SMALL:			return pdFREERTOS_ERRNO_ENOBUFS;	/* Not enough space in the UTF-16 buffer to encode the entire sequence as UTF-16. */
	case FF_ERR_UNICODE_INVALID_SEQUENCE:		return pdFREERTOS_ERRNO_EILSEQ;		/* An invalid UTF-16 sequence was encountered. */
	case FF_ERR_UNICODE_CONVERSION_EXCEEDED:	return pdFREERTOS_ERRNO_ENAMETOOLONG;/* Filename exceeds MAX long-filename length when converted to UTF-16. */
	}

	return pdFREERTOS_ERRNO_EFAULT;
}
/*-----------------------------------------------------------*/

#if( ffconfigHAS_CWD == 1 )

	void ff_free_CWD_space( void )
	{
	WorkingDirectory_t *pxSpace;

		/* Obtain the CWD used by the current task. */
		pxSpace = ( WorkingDirectory_t * ) pvTaskGetThreadLocalStoragePointer( NULL, stdioCWD_THREAD_LOCAL_OFFSET );
		if( pxSpace != NULL )
		{
			vTaskSetThreadLocalStoragePointer( NULL, stdioCWD_THREAD_LOCAL_OFFSET, ( void * ) NULL );
			ffconfigFREE( pxSpace );
		}
	}

#endif /* ffconfigHAS_CWD */
/*-----------------------------------------------------------*/

#if( ffconfigHAS_CWD == 1 )

	static WorkingDirectory_t *pxFindCWD( void )
	{
	WorkingDirectory_t *pxReturn;

		/* Obtain the CWD used by the current task. */
		pxReturn = ( WorkingDirectory_t * ) pvTaskGetThreadLocalStoragePointer( NULL, stdioCWD_THREAD_LOCAL_OFFSET );

		if( pxReturn == NULL )
		{
			/* This task does not yet have a WorkingDirectory_t structure - create and
			initialise one now. */
			pxReturn = ( WorkingDirectory_t * ) ffconfigMALLOC( sizeof( WorkingDirectory_t ) );

			if( pxReturn != NULL )
			{
				pxReturn->pcCWD[ 0 ] = '\0';
				vTaskSetThreadLocalStoragePointer( NULL, stdioCWD_THREAD_LOCAL_OFFSET, ( void * ) pxReturn );
			}
		}

		return pxReturn;
	}

#endif /* ffconfigHAS_CWD */
/*-----------------------------------------------------------*/

#if( ffconfigHAS_CWD == 1 )

	static const char *prvProcessRelativePaths( const char *pcPath )
	{
	const char *pcReturn;
	char *pcChar, *pcTokenStart = NULL, *pcFollowingToken, cPreviousChar = 0x00;
	BaseType_t xByte;

		/* Scan the string looking for a relative path. */
		pcReturn = pcPath;
		pcChar = ( char * ) pcReturn;

		configASSERT( pcPath );

		while( *pcChar != 0x00 )
		{
			if( *pcChar == '.' )
			{
				/* A potential relative path was found.  Is this a "." or a "..". */
				if( *( pcChar + 1 ) == '.' )
				{
					/* Nothing can be done if this is at the start of the string. */
					if( pcTokenStart != NULL )
					{
						/* A ".." was found.  Where does the next token start? */
						pcFollowingToken = pcChar + 2;

						if( *pcFollowingToken == '/' )
						{
							/* The next token starts after the "../" */
							pcFollowingToken += sizeof( char );
						}

						/* Remove the ".." and the previous token. */
						xByte = 0;
						while( pcFollowingToken[ xByte ] != 0x00 )
						{
							pcTokenStart[ xByte ] = pcFollowingToken[ xByte ];
							xByte++;
						}

						/* Terminate. */
						pcTokenStart[ xByte ] = 0x00;

						/* The pointer to the previous token will now be wrong if
						there are multiple if "../.." appears in the string.  So
						reset the variables to continue scanning. */
						pcChar = ( char * ) pcReturn;
						cPreviousChar = 0x00;
						pcTokenStart = NULL;
						continue;
					}
				}
				else
				{
					/* A "." was found.  Remove it. */
				}
			}

			if( cPreviousChar == '/' )
			{
				/* This is the start of a new token. */
				pcTokenStart = pcChar;
			}

			cPreviousChar = *pcChar;
			pcChar++;
		}

		/* Make sure there is no / on the end of the string, being careful not to
		remove the / at the beginning of the string. */
		if( *( pcChar - 1 ) == '/' )
		{
			if( ( pcChar - 1 ) != pcReturn )
			{
				*( pcChar - 1 ) = 0x00;
			}
		}

		return pcReturn;
	}

#endif /* ffconfigHAS_CWD */
/*-----------------------------------------------------------*/

#if( ffconfigHAS_CWD == 1 )

	/*static*/ const char *prvABSPath( const char *pcPath )
	{
	char *pcReturn;
	WorkingDirectory_t *pxWorkingDirectory = pxFindCWD();

		configASSERT( pxWorkingDirectory );

		if( ( pcPath[ 0 ] ) == '/' )
		{
			/* If the path starts with a slash it does not start with a relative
			path.  Copy the string into a thread local buffer so it can be
			manipulated without risk of attempting to write to read only
			memory. */
			snprintf( pxWorkingDirectory->pcFileName, sizeof( pxWorkingDirectory->pcFileName ), "%s", pcPath );
			pcReturn = pxWorkingDirectory->pcFileName;
		}
		else
		{
			/* Insert the working directory into the front of the path. */
			if( pxWorkingDirectory->pcCWD[ 1 ] == 0x00 )
			{
				/* In the root, so don't add a '/' between the CWD and the
				file name. */
				snprintf( pxWorkingDirectory->pcFileName, sizeof( pxWorkingDirectory->pcFileName ), "/%s", pcPath );
			}
			else
			{
				snprintf( pxWorkingDirectory->pcFileName, sizeof( pxWorkingDirectory->pcFileName ), "%s/%s", pxWorkingDirectory->pcCWD, pcPath );
			}

			pcReturn = pxWorkingDirectory->pcFileName;
		}

		/* Make any adjustments necessitated by relative paths. */
		prvProcessRelativePaths( pcReturn );

		return pcReturn;
	}

#endif /* ffconfigHAS_CWD */

#if( ffconfigTIME_SUPPORT == 1 )

	static uint32_t prvFileTime( FF_SystemTime_t *pxTime )
	{
	FF_TimeStruct_t xTime;
	time_t xReturn;

		xTime.tm_sec = pxTime->Second;
		xTime.tm_min = pxTime->Minute;
		xTime.tm_hour = pxTime->Hour;
		xTime.tm_mday = pxTime->Day;
		xTime.tm_mon = pxTime->Month - 1;
		xTime.tm_year = pxTime->Year - 1900;

		xReturn = FreeRTOS_mktime( &xTime );

		return xReturn;
	}

#endif
/*-----------------------------------------------------------*/


