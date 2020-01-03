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
 *	@file		ff_file.h
 *	@ingroup	FILEIO
 **/
#ifndef _FF_FILE_H_
#define _FF_FILE_H_

#ifndef PLUS_FAT_H
	#error this header will be included from "ff_headers.h"
#endif

#define FF_SEEK_SET	0
#define FF_SEEK_CUR	1
#define FF_SEEK_END	2

#if( ffconfigOPTIMISE_UNALIGNED_ACCESS != 0 )
	#define FF_BUFSTATE_INVALID				0x00	/* Data in file handle buffer is invalid. */
	#define FF_BUFSTATE_VALID				0x01	/* Valid data in pBuf (Something has been read into it). */
	#define FF_BUFSTATE_WRITTEN				0x02	/* Data was written into pBuf, this must be saved when leaving sector. */
#endif

#if( ffconfigDEV_SUPPORT != 0 )
struct xDEV_NODE
{
	uint8_t
		ucIsDevice;
};
#endif

typedef struct _FF_FILE
{
	FF_IOManager_t *pxIOManager;			/* Ioman Pointer! */
	uint32_t ulFileSize;			/* File's Size. */
	uint32_t ulObjectCluster;		/* File's Start Cluster. */
	uint32_t ulChainLength;			/* Total Length of the File's cluster chain. */
	uint32_t ulCurrentCluster;		/* Prevents FAT Thrashing. */
	uint32_t ulAddrCurrentCluster;	/* Address of the current cluster. */
	uint32_t ulEndOfChain;			/* Address of the last cluster in the chain. */
	uint32_t ulFilePointer;			/* Current Position Pointer. */
	uint32_t ulDirCluster;			/* Cluster Number that the Dirent is in. */
	uint32_t ulValidFlags;			/* Handle validation flags. */

#if( ffconfigOPTIMISE_UNALIGNED_ACCESS != 0 )
	uint8_t *pucBuffer;				/* A buffer for providing fast unaligned access. */
	uint8_t ucState;				/* State information about the buffer. */
#endif
	uint8_t ucMode;					/* Mode that File Was opened in. */
	uint16_t usDirEntry;			/* Dirent Entry Number describing this file. */

#if( ffconfigDEV_SUPPORT != 0 )
	struct SFileCache *pxDevNode;
#endif
	struct _FF_FILE *pxNext;		/* Pointer to the next file object in the linked list. */
} FF_FILE;

#define FF_VALID_FLAG_INVALID	0x00000001
#define FF_VALID_FLAG_DELETED	0x00000002

/*---------- PROTOTYPES */
/* PUBLIC (Interfaces): */

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	FF_FILE *FF_Open( FF_IOManager_t *pxIOManager, const FF_T_WCHAR *path, uint8_t Mode, FF_Error_t *pError );
	BaseType_t FF_isDirEmpty( FF_IOManager_t *pxIOManager, const FF_T_WCHAR *Path );
	FF_Error_t FF_RmFile( FF_IOManager_t *pxIOManager, const FF_T_WCHAR *path );
	FF_Error_t FF_RmDir( FF_IOManager_t *pxIOManager, const FF_T_WCHAR *path );
	FF_Error_t FF_Move( FF_IOManager_t *pxIOManager, const FF_T_WCHAR *szSourceFile, const FF_T_WCHAR *szDestinationFile,
		BaseType_t bDeleteIfExists );
#else	/* ffconfigUNICODE_UTF16_SUPPORT */
	FF_FILE *FF_Open( FF_IOManager_t *pxIOManager, const char *path, uint8_t Mode, FF_Error_t *pError );
	BaseType_t FF_isDirEmpty( FF_IOManager_t *pxIOManager, const char *Path );
	FF_Error_t FF_RmFile( FF_IOManager_t *pxIOManager, const char *path );
	FF_Error_t FF_RmDir( FF_IOManager_t *pxIOManager, const char *path );
	FF_Error_t FF_Move( FF_IOManager_t *pxIOManager, const char *szSourceFile, const char *szDestinationFile,
		BaseType_t bDeleteIfExists );
#endif	/* ffconfigUNICODE_UTF16_SUPPORT */

#if( ffconfigTIME_SUPPORT != 0 )
	enum {
		ETimeCreate = 1,
		ETimeMod = 2,
		ETimeAccess = 4,
		ETimeAll = 7
	};
	FF_Error_t FF_SetFileTime( FF_FILE *pFile, FF_SystemTime_t *pxTime, UBaseType_t uxWhat );
	#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
		FF_Error_t FF_SetTime( FF_IOManager_t *pxIOManager, const FF_T_WCHAR *path, FF_SystemTime_t *pxTime, UBaseType_t uxWhat );
	#else
		FF_Error_t FF_SetTime( FF_IOManager_t *pxIOManager, const char *path, FF_SystemTime_t *pxTime, UBaseType_t uxWhat );
	#endif	/* ffconfigUNICODE_UTF16_SUPPORT */
#endif	/* ffconfigTIME_SUPPORT */

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	FF_Error_t FF_SetPerm( FF_IOManager_t *pxIOManager, const FF_T_WCHAR *path, UBaseType_t aPerm );
#else
	FF_Error_t FF_SetPerm( FF_IOManager_t *pxIOManager, const char *path, UBaseType_t aPerm );
#endif

FF_Error_t FF_SetEof( FF_FILE *pFile );

FF_Error_t FF_Close( FF_FILE *pFile );
int32_t FF_GetC( FF_FILE *pFile );
int32_t FF_GetLine( FF_FILE *pFile, char *szLine, uint32_t ulLimit );
int32_t FF_Read( FF_FILE *pFile, uint32_t ElementSize, uint32_t Count, uint8_t *buffer );
int32_t FF_Write( FF_FILE *pFile, uint32_t ElementSize, uint32_t Count, uint8_t *buffer );
BaseType_t FF_isEOF( FF_FILE *pFile );
int32_t FF_BytesLeft( FF_FILE *pFile ); /* Returns # of bytes left to read. */

/* FF_FileSize is an earlier version of FF_GetFileSize(). For files
equal to or larger than 2GB, the return value is negative.
Function is deprecated. Please use FF_GetFileSize(). */
int32_t FF_FileSize( FF_FILE *pFile ); /* Returns # of bytes in a file. */

/* Use the following function in case files may get larger than 2  GB.
Writes the size of a file to the parameter.
Returns 0 or error code. */
FF_Error_t FF_GetFileSize( FF_FILE *pFile, uint32_t *pulSize );

FF_Error_t FF_Seek( FF_FILE *pFile, int32_t Offset, BaseType_t xOrigin  );
int32_t FF_PutC( FF_FILE *pFile, uint8_t Value );

static portINLINE uint32_t FF_Tell( FF_FILE *pFile )
{
	return pFile ? pFile->ulFilePointer : 0;
}

uint8_t	FF_GetModeBits( const char *Mode );

FF_Error_t FF_CheckValid( FF_FILE *pFile );   /* Check if pFile is a valid FF_FILE pointer. */

#if( ffconfigREMOVABLE_MEDIA != 0 )
	int32_t FF_Invalidate( FF_IOManager_t *pxIOManager ); /* Invalidate all handles belonging to pxIOManager. */
#endif

/* Private : */

#endif
