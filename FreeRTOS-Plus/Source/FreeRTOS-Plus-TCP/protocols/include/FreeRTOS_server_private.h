/*
 * FreeRTOS+TCP Labs Build 160919 (C) 2016 Real Time Engineers ltd.
 * Authors include Hein Tibosch and Richard Barry
 *
 *******************************************************************************
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 ***                                                                         ***
 ***                                                                         ***
 ***   FREERTOS+TCP IS STILL IN THE LAB (mainly because the FTP and HTTP     ***
 ***   demos have a dependency on FreeRTOS+FAT, which is only in the Labs    ***
 ***   download):                                                            ***
 ***                                                                         ***
 ***   FreeRTOS+TCP is functional and has been used in commercial products   ***
 ***   for some time.  Be aware however that we are still refining its       ***
 ***   design, the source code does not yet quite conform to the strict      ***
 ***   coding and style standards mandated by Real Time Engineers ltd., and  ***
 ***   the documentation and testing is not necessarily complete.            ***
 ***                                                                         ***
 ***   PLEASE REPORT EXPERIENCES USING THE SUPPORT RESOURCES FOUND ON THE    ***
 ***   URL: http://www.FreeRTOS.org/contact  Active early adopters may, at   ***
 ***   the sole discretion of Real Time Engineers Ltd., be offered versions  ***
 ***   under a license other than that described below.                      ***
 ***                                                                         ***
 ***                                                                         ***
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 *******************************************************************************
 *
 * FreeRTOS+TCP can be used under two different free open source licenses.  The
 * license that applies is dependent on the processor on which FreeRTOS+TCP is
 * executed, as follows:
 *
 * If FreeRTOS+TCP is executed on one of the processors listed under the Special
 * License Arrangements heading of the FreeRTOS+TCP license information web
 * page, then it can be used under the terms of the FreeRTOS Open Source
 * License.  If FreeRTOS+TCP is used on any other processor, then it can be used
 * under the terms of the GNU General Public License V2.  Links to the relevant
 * licenses follow:
 *
 * The FreeRTOS+TCP License Information Page: http://www.FreeRTOS.org/tcp_license
 * The FreeRTOS Open Source License: http://www.FreeRTOS.org/license
 * The GNU General Public License Version 2: http://www.FreeRTOS.org/gpl-2.0.txt
 *
 * FreeRTOS+TCP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+TCP unless you agree that you use the software 'as is'.
 * FreeRTOS+TCP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/plus
 * http://www.FreeRTOS.org/labs
 *
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
