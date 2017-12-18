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

 /*
	Some code which is common to TCP servers like HTTP and FTP
*/

#ifndef FREERTOS_SERVER_PRIVATE_H
#define	FREERTOS_SERVER_PRIVATE_H

#define FREERTOS_NO_SOCKET		NULL

/* FreeRTOS+FAT */
#include "ff_stdio.h"

/* Each HTTP server has 1, at most 2 sockets */
#define	HTTP_SOCKET_COUNT	2

/*
 * ipconfigTCP_COMMAND_BUFFER_SIZE sets the size of:
 *     pcCommandBuffer': a buffer to receive and send TCP commands
 *
 * ipconfigTCP_FILE_BUFFER_SIZE sets the size of:
 *     pcFileBuffer'   : a buffer to access the file system: read or write data.
 *
 * The buffers are both used for FTP as well as HTTP.
 */

#ifndef ipconfigTCP_COMMAND_BUFFER_SIZE
	#define ipconfigTCP_COMMAND_BUFFER_SIZE	( 2048 )
#endif

#ifndef ipconfigTCP_FILE_BUFFER_SIZE
	#define ipconfigTCP_FILE_BUFFER_SIZE	( 2048 )
#endif

struct xTCP_CLIENT;

typedef BaseType_t ( * FTCPWorkFunction ) ( struct xTCP_CLIENT * /* pxClient */ );
typedef void ( * FTCPDeleteFunction ) ( struct xTCP_CLIENT * /* pxClient */ );

#define	TCP_CLIENT_FIELDS \
	enum eSERVER_TYPE eType; \
	struct xTCP_SERVER *pxParent; \
	Socket_t xSocket; \
	const char *pcRootDir; \
	FTCPWorkFunction fWorkFunction; \
	FTCPDeleteFunction fDeleteFunction; \
	struct xTCP_CLIENT *pxNextClient

typedef struct xTCP_CLIENT
{
	/* This define contains fields which must come first within each of the client structs */
	TCP_CLIENT_FIELDS;
	/* --- Keep at the top  --- */

} TCPClient_t;

struct xHTTP_CLIENT
{
	/* This define contains fields which must come first within each of the client structs */
	TCP_CLIENT_FIELDS;
	/* --- Keep at the top  --- */

	const char *pcUrlData;
	const char *pcRestData;
	char pcCurrentFilename[ ffconfigMAX_FILENAME ];
	size_t uxBytesLeft;
	FF_FILE *pxFileHandle;
	union {
		struct {
			uint32_t
				bReplySent : 1;
		};
		uint32_t ulFlags;
	} bits;
};

typedef struct xHTTP_CLIENT HTTPClient_t;

struct xFTP_CLIENT
{
	/* This define contains fields which must come first within each of the client structs */
	TCP_CLIENT_FIELDS;
	/* --- Keep at the top  --- */

	uint32_t ulRestartOffset;
	uint32_t ulRecvBytes;
	size_t uxBytesLeft;	/* Bytes left to send */
	uint32_t ulClientIP;
	TickType_t xStartTime;
	uint16_t usClientPort;
	Socket_t xTransferSocket;
	BaseType_t xTransType;
	BaseType_t xDirCount;
	FF_FindData_t xFindData;
	FF_FILE *pxReadHandle;
	FF_FILE *pxWriteHandle;
	char pcCurrentDir[ ffconfigMAX_FILENAME ];
	char pcFileName[ ffconfigMAX_FILENAME ];
	char pcConnectionAck[ 128 ];
	char pcClientAck[ 128 ];
	union {
		struct {
			uint32_t
				bHelloSent : 1,
				bLoggedIn : 1,
				bStatusUser : 1,
				bInRename : 1,
				bReadOnly : 1;
		};
		uint32_t ulFTPFlags;
	} bits;
	union {
		struct {
			uint32_t
				bIsListen : 1,			/* pdTRUE for passive data connections (using list()). */
				bDirHasEntry : 1,		/* pdTRUE if ff_findfirst() was successful. */
				bClientConnected : 1,	/* pdTRUE after connect() or accept() has succeeded. */
				bEmptyFile : 1,			/* pdTRUE if a connection-without-data was received. */
				bHadError : 1;			/* pdTRUE if a transfer got aborted because of an error. */
		};
		uint32_t ulConnFlags;
	} bits1;
};

typedef struct xFTP_CLIENT FTPClient_t;

BaseType_t xHTTPClientWork( TCPClient_t *pxClient );
BaseType_t xFTPClientWork( TCPClient_t *pxClient );

void vHTTPClientDelete( TCPClient_t *pxClient );
void vFTPClientDelete( TCPClient_t *pxClient );

BaseType_t xMakeAbsolute( struct xFTP_CLIENT *pxClient, char *pcBuffer, BaseType_t xBufferLength, const char *pcFileName );
BaseType_t xMakeRelative( FTPClient_t *pxClient, char *pcBuffer, BaseType_t xBufferLength, const char *pcFileName );

struct xTCP_SERVER
{
	SocketSet_t xSocketSet;
	/* A buffer to receive and send TCP commands, either HTTP of FTP. */
	char pcCommandBuffer[ ipconfigTCP_COMMAND_BUFFER_SIZE ];
	/* A buffer to access the file system: read or write data. */
	char pcFileBuffer[ ipconfigTCP_FILE_BUFFER_SIZE ];

	#if( ipconfigUSE_FTP != 0 )
		char pcNewDir[ ffconfigMAX_FILENAME ];
	#endif
	#if( ipconfigUSE_HTTP != 0 )
		char pcContentsType[40];	/* Space for the msg: "text/javascript" */
		char pcExtraContents[40];	/* Space for the msg: "Content-Length: 346500" */
	#endif
	BaseType_t xServerCount;
	TCPClient_t *pxClients;
	struct xSERVER
	{
		enum eSERVER_TYPE eType;		/* eSERVER_HTTP | eSERVER_FTP */
		const char *pcRootDir;
		Socket_t xSocket;
	} xServers[ 1 ];
};

#endif /* FREERTOS_SERVER_PRIVATE_H */
