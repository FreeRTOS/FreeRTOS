/*
 * FreeRTOS+TCP V2.0.1
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS Protocol includes. */
#include "FreeRTOS_HTTP_commands.h"
#include "FreeRTOS_TCP_server.h"
#include "FreeRTOS_server_private.h"

/* Remove the whole file if HTTP is not supported. */
#if( ipconfigUSE_HTTP == 1 )

/* FreeRTOS+FAT includes. */
#include "ff_stdio.h"

#ifndef HTTP_SERVER_BACKLOG
	#define HTTP_SERVER_BACKLOG			( 12 )
#endif

#ifndef USE_HTML_CHUNKS
	#define USE_HTML_CHUNKS				( 0 )
#endif

#if !defined( ARRAY_SIZE )
	#define ARRAY_SIZE(x) ( BaseType_t ) (sizeof( x ) / sizeof( x )[ 0 ] )
#endif

/* Some defines to make the code more readbale */
#define pcCOMMAND_BUFFER	pxClient->pxParent->pcCommandBuffer
#define pcNEW_DIR			pxClient->pxParent->pcNewDir
#define pcFILE_BUFFER		pxClient->pxParent->pcFileBuffer

#ifndef ipconfigHTTP_REQUEST_CHARACTER
	#define ipconfigHTTP_REQUEST_CHARACTER		'?'
#endif

/*_RB_ Need comment block, although fairly self evident. */
static void prvFileClose( HTTPClient_t *pxClient );
static BaseType_t prvProcessCmd( HTTPClient_t *pxClient, BaseType_t xIndex );
static const char *pcGetContentsType( const char *apFname );
static BaseType_t prvOpenURL( HTTPClient_t *pxClient );
static BaseType_t prvSendFile( HTTPClient_t *pxClient );
static BaseType_t prvSendReply( HTTPClient_t *pxClient, BaseType_t xCode );

static const char pcEmptyString[1] = { '\0' };

typedef struct xTYPE_COUPLE
{
	const char *pcExtension;
	const char *pcType;
} TypeCouple_t;

static TypeCouple_t pxTypeCouples[ ] =
{
	{ "html", "text/html" },
	{ "css",  "text/css" },
	{ "js",   "text/javascript" },
	{ "png",  "image/png" },
	{ "jpg",  "image/jpeg" },
	{ "gif",  "image/gif" },
	{ "txt",  "text/plain" },
	{ "mp3",  "audio/mpeg3" },
	{ "wav",  "audio/wav" },
	{ "flac", "audio/ogg" },
	{ "pdf",  "application/pdf" },
	{ "ttf",  "application/x-font-ttf" },
	{ "ttc",  "application/x-font-ttf" }
};

void vHTTPClientDelete( TCPClient_t *pxTCPClient )
{
HTTPClient_t *pxClient = ( HTTPClient_t * ) pxTCPClient;

	/* This HTTP client stops, close / release all resources. */
	if( pxClient->xSocket != FREERTOS_NO_SOCKET )
	{
		FreeRTOS_FD_CLR( pxClient->xSocket, pxClient->pxParent->xSocketSet, eSELECT_ALL );
		FreeRTOS_closesocket( pxClient->xSocket );
		pxClient->xSocket = FREERTOS_NO_SOCKET;
	}
	prvFileClose( pxClient );
}
/*-----------------------------------------------------------*/

static void prvFileClose( HTTPClient_t *pxClient )
{
	if( pxClient->pxFileHandle != NULL )
	{
		FreeRTOS_printf( ( "Closing file: %s\n", pxClient->pcCurrentFilename ) );
		ff_fclose( pxClient->pxFileHandle );
		pxClient->pxFileHandle = NULL;
	}
}
/*-----------------------------------------------------------*/

static BaseType_t prvSendReply( HTTPClient_t *pxClient, BaseType_t xCode )
{
struct xTCP_SERVER *pxParent = pxClient->pxParent;
BaseType_t xRc;

	/* A normal command reply on the main socket (port 21). */
	char *pcBuffer = pxParent->pcFileBuffer;

	xRc = snprintf( pcBuffer, sizeof( pxParent->pcFileBuffer ),
		"HTTP/1.1 %d %s\r\n"
#if	USE_HTML_CHUNKS
		"Transfer-Encoding: chunked\r\n"
#endif
		"Content-Type: %s\r\n"
		"Connection: keep-alive\r\n"
		"%s\r\n",
		( int ) xCode,
		webCodename (xCode),
		pxParent->pcContentsType[0] ? pxParent->pcContentsType : "text/html",
		pxParent->pcExtraContents );

	pxParent->pcContentsType[0] = '\0';
	pxParent->pcExtraContents[0] = '\0';

	xRc = FreeRTOS_send( pxClient->xSocket, ( const void * ) pcBuffer, xRc, 0 );
	pxClient->bits.bReplySent = pdTRUE_UNSIGNED;

	return xRc;
}
/*-----------------------------------------------------------*/

static BaseType_t prvSendFile( HTTPClient_t *pxClient )
{
size_t uxSpace;
size_t uxCount;
BaseType_t xRc = 0;

	if( pxClient->bits.bReplySent == pdFALSE_UNSIGNED )
	{
		pxClient->bits.bReplySent = pdTRUE_UNSIGNED;

		strcpy( pxClient->pxParent->pcContentsType, pcGetContentsType( pxClient->pcCurrentFilename ) );
		snprintf( pxClient->pxParent->pcExtraContents, sizeof( pxClient->pxParent->pcExtraContents ),
			"Content-Length: %d\r\n", ( int ) pxClient->uxBytesLeft );

		/* "Requested file action OK". */
		xRc = prvSendReply( pxClient, WEB_REPLY_OK );
	}

	if( xRc >= 0 ) do
	{
		uxSpace = FreeRTOS_tx_space( pxClient->xSocket );

		if( pxClient->uxBytesLeft < uxSpace )
		{
			uxCount = pxClient->uxBytesLeft;
		}
		else
		{
			uxCount = uxSpace;
		}

		if( uxCount > 0u )
		{
			if( uxCount > sizeof( pxClient->pxParent->pcFileBuffer ) )
			{
				uxCount = sizeof( pxClient->pxParent->pcFileBuffer );
			}
			ff_fread( pxClient->pxParent->pcFileBuffer, 1, uxCount, pxClient->pxFileHandle );
			pxClient->uxBytesLeft -= uxCount;

			xRc = FreeRTOS_send( pxClient->xSocket, pxClient->pxParent->pcFileBuffer, uxCount, 0 );
			if( xRc < 0 )
			{
				break;
			}
		}
	} while( uxCount > 0u );

	if( pxClient->uxBytesLeft == 0u )
	{
		/* Writing is ready, no need for further 'eSELECT_WRITE' events. */
		FreeRTOS_FD_CLR( pxClient->xSocket, pxClient->pxParent->xSocketSet, eSELECT_WRITE );
		prvFileClose( pxClient );
	}
	else
	{
		/* Wake up the TCP task as soon as this socket may be written to. */
		FreeRTOS_FD_SET( pxClient->xSocket, pxClient->pxParent->xSocketSet, eSELECT_WRITE );
	}

	return xRc;
}
/*-----------------------------------------------------------*/

static BaseType_t prvOpenURL( HTTPClient_t *pxClient )
{
BaseType_t xRc;
char pcSlash[ 2 ];

	pxClient->bits.ulFlags = 0;

	#if( ipconfigHTTP_HAS_HANDLE_REQUEST_HOOK != 0 )
	{
		if( strchr( pxClient->pcUrlData, ipconfigHTTP_REQUEST_CHARACTER ) != NULL )
		{
		size_t xResult;

			xResult = uxApplicationHTTPHandleRequestHook( pxClient->pcUrlData, pxClient->pcCurrentFilename, sizeof( pxClient->pcCurrentFilename ) );
			if( xResult > 0 )
			{
				strcpy( pxClient->pxParent->pcContentsType, "text/html" );
				snprintf( pxClient->pxParent->pcExtraContents, sizeof( pxClient->pxParent->pcExtraContents ),
					"Content-Length: %d\r\n", ( int ) xResult );
				xRc = prvSendReply( pxClient, WEB_REPLY_OK );	/* "Requested file action OK" */
				if( xRc > 0 )
				{
					xRc = FreeRTOS_send( pxClient->xSocket, pxClient->pcCurrentFilename, xResult, 0 );
				}
				/* Although against the coding standard of FreeRTOS, a return is
				done here  to simplify this conditional code. */
				return xRc;
			}
		}
	}
	#endif /* ipconfigHTTP_HAS_HANDLE_REQUEST_HOOK */

	if( pxClient->pcUrlData[ 0 ] != '/' )
	{
		/* Insert a slash before the file name. */
		pcSlash[ 0 ] = '/';
		pcSlash[ 1 ] = '\0';
	}
	else
	{
		/* The browser provided a starting '/' already. */
		pcSlash[ 0 ] = '\0';
	}
	snprintf( pxClient->pcCurrentFilename, sizeof( pxClient->pcCurrentFilename ), "%s%s%s",
		pxClient->pcRootDir,
		pcSlash,
		pxClient->pcUrlData);

	pxClient->pxFileHandle = ff_fopen( pxClient->pcCurrentFilename, "rb" );

	FreeRTOS_printf( ( "Open file '%s': %s\n", pxClient->pcCurrentFilename,
		pxClient->pxFileHandle != NULL ? "Ok" : strerror( stdioGET_ERRNO() ) ) );

	if( pxClient->pxFileHandle == NULL )
	{
		/* "404 File not found". */
		xRc = prvSendReply( pxClient, WEB_NOT_FOUND );
	}
	else
	{
		pxClient->uxBytesLeft = ( size_t ) pxClient->pxFileHandle->ulFileSize;
		xRc = prvSendFile( pxClient );
	}

	return xRc;
}
/*-----------------------------------------------------------*/

static BaseType_t prvProcessCmd( HTTPClient_t *pxClient, BaseType_t xIndex )
{
BaseType_t xResult = 0;

	/* A new command has been received. Process it. */
	switch( xIndex )
	{
	case ECMD_GET:
		xResult = prvOpenURL( pxClient );
		break;

	case ECMD_HEAD:
	case ECMD_POST:
	case ECMD_PUT:
	case ECMD_DELETE:
	case ECMD_TRACE:
	case ECMD_OPTIONS:
	case ECMD_CONNECT:
	case ECMD_PATCH:
	case ECMD_UNK:
		{
			FreeRTOS_printf( ( "prvProcessCmd: Not implemented: %s\n",
				xWebCommands[xIndex].pcCommandName ) );
		}
		break;
	}

	return xResult;
}
/*-----------------------------------------------------------*/

BaseType_t xHTTPClientWork( TCPClient_t *pxTCPClient )
{
BaseType_t xRc;
HTTPClient_t *pxClient = ( HTTPClient_t * ) pxTCPClient;

	if( pxClient->pxFileHandle != NULL )
	{
		prvSendFile( pxClient );
	}

	xRc = FreeRTOS_recv( pxClient->xSocket, ( void * )pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), 0 );

	if( xRc > 0 )
	{
	BaseType_t xIndex;
	const char *pcEndOfCmd;
	const struct xWEB_COMMAND *curCmd;
	char *pcBuffer = pcCOMMAND_BUFFER;

		if( xRc < ( BaseType_t ) sizeof( pcCOMMAND_BUFFER ) )
		{
			pcBuffer[ xRc ] = '\0';
		}
		while( xRc && ( pcBuffer[ xRc - 1 ] == 13 || pcBuffer[ xRc - 1 ] == 10 ) )
		{
			pcBuffer[ --xRc ] = '\0';
		}
		pcEndOfCmd = pcBuffer + xRc;

		curCmd = xWebCommands;

		/* Pointing to "/index.html HTTP/1.1". */
		pxClient->pcUrlData = pcBuffer;

		/* Pointing to "HTTP/1.1". */
		pxClient->pcRestData = pcEmptyString;

		/* Last entry is "ECMD_UNK". */
		for( xIndex = 0; xIndex < WEB_CMD_COUNT - 1; xIndex++, curCmd++ )
		{
		BaseType_t xLength;

			xLength = curCmd->xCommandLength;
			if( ( xRc >= xLength ) && ( memcmp( curCmd->pcCommandName, pcBuffer, xLength ) == 0 ) )
			{
			char *pcLastPtr;

				pxClient->pcUrlData += xLength + 1;
				for( pcLastPtr = (char *)pxClient->pcUrlData; pcLastPtr < pcEndOfCmd; pcLastPtr++ )
				{
					char ch = *pcLastPtr;
					if( ( ch == '\0' ) || ( strchr( "\n\r \t", ch ) != NULL ) )
					{
						*pcLastPtr = '\0';
						pxClient->pcRestData = pcLastPtr + 1;
						break;
					}
				}
				break;
			}
		}

		if( xIndex < ( WEB_CMD_COUNT - 1 ) )
		{
			xRc = prvProcessCmd( pxClient, xIndex );
		}
	}
	else if( xRc < 0 )
	{
		/* The connection will be closed and the client will be deleted. */
		FreeRTOS_printf( ( "xHTTPClientWork: rc = %ld\n", xRc ) );
	}
	return xRc;
}
/*-----------------------------------------------------------*/

static const char *pcGetContentsType (const char *apFname)
{
	const char *slash = NULL;
	const char *dot = NULL;
	const char *ptr;
	const char *pcResult = "text/html";
	BaseType_t x;

	for( ptr = apFname; *ptr; ptr++ )
	{
		if (*ptr == '.') dot = ptr;
		if (*ptr == '/') slash = ptr;
	}
	if( dot > slash )
	{
		dot++;
		for( x = 0; x < ARRAY_SIZE( pxTypeCouples ); x++ )
		{
			if( strcasecmp( dot, pxTypeCouples[ x ].pcExtension ) == 0 )
			{
				pcResult = pxTypeCouples[ x ].pcType;
				break;
			}
		}
	}
	return pcResult;
}

#endif /* ipconfigUSE_HTTP */

