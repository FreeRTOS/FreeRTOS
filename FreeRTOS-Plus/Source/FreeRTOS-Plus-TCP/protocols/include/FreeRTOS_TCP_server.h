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
	Some code which is common to TCP servers like HTTP en FTP
*/

#ifndef FREERTOS_TCP_SERVER_H
#define	FREERTOS_TCP_SERVER_H

#ifdef __cplusplus
extern "C" {
#endif

#ifndef	FTP_SERVER_USES_RELATIVE_DIRECTORY
	#define	FTP_SERVER_USES_RELATIVE_DIRECTORY		0
#endif

enum eSERVER_TYPE
{
	eSERVER_NONE,
	eSERVER_HTTP,
	eSERVER_FTP,
};

struct xFTP_CLIENT;

#if( ipconfigFTP_HAS_RECEIVED_HOOK != 0 )
	extern void vApplicationFTPReceivedHook( const char *pcFileName, uint32_t ulSize, struct xFTP_CLIENT *pxFTPClient );
	extern void vFTPReplyMessage( struct xFTP_CLIENT *pxFTPClient, const char *pcMessage );
#endif /* ipconfigFTP_HAS_RECEIVED_HOOK != 0 */

#if( ipconfigFTP_HAS_USER_PASSWORD_HOOK != 0 )
	/*
	 * Function is called when a user name has been submitted.
	 * The function may return a string such as: "331 Please enter your password"
	 * or return NULL to use the default reply.
	 */
	extern const char *pcApplicationFTPUserHook( const char *pcUserName );
#endif /* ipconfigFTP_HAS_USER_PASSWORD_HOOK */

#if( ipconfigFTP_HAS_USER_PASSWORD_HOOK != 0 )
	/*
	 * Function is called when a password was received.
	 * Return positive value to allow the user
	 */
	extern BaseType_t xApplicationFTPPasswordHook( const char *pcUserName, const char *pcPassword );
#endif /* ipconfigFTP_HAS_USER_PASSWORD_HOOK */

#if( ipconfigFTP_HAS_USER_PROPERTIES_HOOK != 0 )
	/*
	 * The FTP server is asking for user-specific properties
	 */
	typedef struct
	{
		uint16_t usPortNumber;	/* For reference only. Host-endian. */
		const char *pcRootDir;
		BaseType_t xReadOnly;
	}
	FTPUserProperties_t;
	extern void vApplicationFTPUserPropertiesHook( const char *pcUserName, FTPUserProperties_t *pxProperties );
#endif /* ipconfigFTP_HAS_USER_PASSWORD_HOOK */

#if( ipconfigHTTP_HAS_HANDLE_REQUEST_HOOK != 0 )
	/*
	 * A GET request is received containing a special character,
	 * usually a question mark.
	 * const char *pcURLData;	// A request, e.g. "/request?limit=75"
	 * char *pcBuffer;			// Here the answer can be written
	 * size_t uxBufferLength;	// Size of the buffer
	 *
	 */
	extern size_t uxApplicationHTTPHandleRequestHook( const char *pcURLData, char *pcBuffer, size_t uxBufferLength );
#endif /* ipconfigHTTP_HAS_HANDLE_REQUEST_HOOK */

struct xSERVER_CONFIG
{
	enum eSERVER_TYPE eType;		/* eSERVER_HTTP | eSERVER_FTP */
	BaseType_t xPortNumber;			/* e.g. 80, 8080, 21 */
	BaseType_t xBackLog;			/* e.g. 10, maximum number of connected TCP clients */
	const char * const pcRootDir;	/* Treat this directory as the root directory */
};

struct xTCP_SERVER;
typedef struct xTCP_SERVER TCPServer_t;

TCPServer_t *FreeRTOS_CreateTCPServer( const struct xSERVER_CONFIG *pxConfigs, BaseType_t xCount );
void FreeRTOS_TCPServerWork( TCPServer_t *pxServer, TickType_t xBlockingTime );

#if( ipconfigSUPPORT_SIGNALS != 0 )
	/* FreeRTOS_TCPServerWork() calls select().
	The two functions below provide a possibility to interrupt
	the call to select(). After the interruption, resume
	by calling FreeRTOS_TCPServerWork() again. */
	BaseType_t FreeRTOS_TCPServerSignal( TCPServer_t *pxServer );
	BaseType_t FreeRTOS_TCPServerSignalFromISR( TCPServer_t *pxServer, BaseType_t *pxHigherPriorityTaskWoken );
#endif

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* FREERTOS_TCP_SERVER_H */
