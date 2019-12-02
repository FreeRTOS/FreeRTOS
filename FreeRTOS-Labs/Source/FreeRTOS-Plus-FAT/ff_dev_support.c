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

#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "portable.h"

#include "ff_headers.h"
#include "ff_devices.h"

#ifndef ARRAY_SIZE
#	define	ARRAY_SIZE( x )	( int )( sizeof( x ) / sizeof( x )[ 0 ] )
#endif

#if( ffconfigDEV_SUPPORT == 0 )
	#error No use to include this module if ffconfigDEV_SUPPORT is disabled
#endif /* ffconfigDEV_SUPPORT == 0 */

struct SFileCache
{
	char pcFileName[16];
	uint32_t ulFileLength;
	uint32_t ulFilePointer;
};

struct SFileCache xFiles[ 16 ];

enum eCACHE_ACTION
{
	eCACHE_LOOKUP,
	eCACHE_ADD,
	eCACHE_REMOVE,
};

const char pcDevicePath[] = ffconfigDEV_PATH;

struct SFileCache *pxFindFile( const char *pcFname, enum eCACHE_ACTION eAction )
{
BaseType_t xIndex, xFreeIndex = -1;
struct SFileCache *pxResult = NULL;

	for( xIndex = 0; xIndex < ARRAY_SIZE( xFiles ); xIndex++ )
	{
		if( xFiles[ xIndex ].pcFileName[ 0 ] == '\0' )
		{
			if( xFreeIndex < 0 )
			{
				xFreeIndex = xIndex;
			}
		}
		else if( strcmp( xFiles[ xIndex ].pcFileName, pcFname ) == 0 )
		{
			if( eAction == eCACHE_REMOVE )
			{
				xFiles[ xIndex ].pcFileName[ 0 ] = '\0';
			}

			pxResult = xFiles + xIndex;
			break;
		}
	}

	if( ( pxResult == NULL ) && ( eAction == eCACHE_ADD ) && ( xFreeIndex >= 0 ) )
	{
		pxResult = xFiles + xFreeIndex;
		snprintf( pxResult->pcFileName, sizeof( pxResult->pcFileName ), "%s", pcFname );
		pxResult->ulFileLength = 0;
		pxResult->ulFilePointer = 0;
	}

	return pxResult;
}

BaseType_t xCheckDevicePath( const char *pcPath )
{
BaseType_t xDevLength;
BaseType_t xPathLength;
BaseType_t xIsDevice;

	xDevLength = sizeof( pcDevicePath ) - 1;
	xPathLength = strlen( pcPath );

	/* System "/dev" should not match with "/device/etc". */
	if( ( xPathLength >= xDevLength ) &&
		( memcmp( pcDevicePath, pcPath, xDevLength ) == 0 ) &&
		( ( pcPath[ xDevLength ] == '\0' ) || ( pcPath[ xDevLength ] == '/' ) ) )
	{
		xIsDevice = FF_DEV_CHAR_DEV;
	}
	else
	{
		xIsDevice = FF_DEV_NO_DEV;
	}

	return xIsDevice;
}

BaseType_t FF_Device_Open( const char *pcPath, FF_FILE *pxStream )
{
uint8_t ucIsDevice;

	ucIsDevice = xCheckDevicePath( pcPath );
	if( ucIsDevice != pdFALSE )
	{
	const char *pcBaseName = pcPath;

		if( memcmp( pcBaseName, pcDevicePath, sizeof( pcDevicePath ) - 1 ) == 0 )
		{
			pcBaseName = pcBaseName + sizeof( pcDevicePath );
		}

		pxStream->pxDevNode = pxFindFile( pcBaseName, eCACHE_ADD );
		if( pxStream->pxDevNode != NULL )
		{
			pxStream->pxDevNode->ulFilePointer = 0;
			if( ( pxStream->ucMode & ( FF_MODE_WRITE | FF_MODE_APPEND | FF_MODE_CREATE ) ) == 0 )
			{
				pxStream->ulFileSize = pxStream->pxDevNode->ulFileLength;
			}
		}
	}

	return ucIsDevice;
}

void FF_Device_Close( FF_FILE * pxStream )
{
	if( pxStream->pxDevNode != NULL )
	{
		pxStream->ulFileSize = 0ul;
		pxStream->ulFilePointer = 0ul;
	}
}

size_t FF_Device_Read( void *pvBuf, size_t lSize, size_t lCount, FF_FILE * pxStream )
{
	lCount *= lSize;
	return lCount;
}

size_t FF_Device_Write( const void *pvBuf, size_t lSize, size_t lCount, FF_FILE * pxStream )
{
	lCount *= lSize;

	if( pxStream->pxDevNode != NULL )
	{

		pxStream->pxDevNode->ulFilePointer += lCount;
		if( pxStream->pxDevNode->ulFileLength < pxStream->pxDevNode->ulFilePointer )
		{
			pxStream->pxDevNode->ulFileLength = pxStream->pxDevNode->ulFilePointer;
		}
	}
	return lCount;
}

int FF_Device_Seek( FF_FILE *pxStream, long lOffset, int iWhence )
{
	if( pxStream->pxDevNode != NULL )
	{
		if( iWhence == FF_SEEK_SET )
		{
			pxStream->pxDevNode->ulFilePointer = lOffset;
		}
		else if( iWhence == FF_SEEK_END )
		{
			pxStream->pxDevNode->ulFilePointer = pxStream->pxDevNode->ulFileLength - lOffset;
		}
	}

	return 0;
}

int FF_Device_GetDirEnt( const char *pcPath, FF_DirEnt_t *pxDirEnt )
{
BaseType_t xIsDotDir = 0;
	if( pxDirEnt->pcFileName[ 0 ] == '.' )
	{
		if( ( pxDirEnt->pcFileName[ 1 ] == '.' ) &&
			( pxDirEnt->pcFileName[ 2 ] == '\0' ) )
		{
			xIsDotDir = 2;
		}
		else if( pxDirEnt->pcFileName[ 1 ] == '\0' )
		{
			xIsDotDir = 1;
		}
	}
	if( xIsDotDir == 0 )
	{
	struct SFileCache *pxDevNode;

		pxDevNode = pxFindFile( pxDirEnt->pcFileName, eCACHE_LOOKUP );

		pxDirEnt->ucIsDeviceDir = FF_DEV_CHAR_DEV;
		if( pxDevNode != NULL )
		{
			pxDirEnt->ulFileSize = pxDevNode->ulFileLength;
		}
		else if( pxDirEnt->ulFileSize < 2048 )
		{
			pxDirEnt->ulFileSize = 2048;
		}
	}

	return 1024;
}

