/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*
 * A basic TFTP server that can currently only be used to receive files, and not
 * send files.  This is a slim implementation intended for use in boot loaders
 * and other applications that require over the air reception of files.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS+FAT includes. */
#include "ff_stdio.h"

#if( ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND != 1 )
	#error ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND must be set to one to use this TFTP server.
#endif

#if( configTICK_RATE_HZ > 1000 )
	#error The TFTP server uses the pdMS_TO_TICKS() macro, so configTICK_RATE_HZ must be less than or equal to 1000
#endif

#ifndef ipconfigTFTP_TIME_OUT_MS
	#define ipconfigTFTP_TIME_OUT_MS	( 10000 )
#endif

#ifndef ipconfigTFTP_MAX_RETRIES
	#define ipconfigTFTP_MAX_RETRIES	( 6 )
#endif

/* Standard/expected TFTP port number. */
#define tftpPORT_NUMBER 				( ( uint16_t ) 69 )

/* Offset to the file name within the frame. */
#define tftpFILE_NAME_OFFSET	( 2 )

/* Number of bytes in the Ack message. */
#define tftpACK_MESSAGE_LENGTH 4

/* Files are sent in fixed length blocks of 512 (the original maximum). */
#define tftpMAX_DATA_LENGTH	( ( size_t ) 512 )

/* Standard TFTP opcodes. */
typedef enum
{
	eReadRequest = 1,
	eWriteRequest,
	eData,
	eAck,
	eError
} eTFTPOpcode_t;

/* Error codes from the RFC. */
typedef enum
{
	eFileNotFound = 1,
	eAccessViolation,
	eDiskFull,
	eIllegalTFTPOperation,
	eUnknownTransferID,
	eFileAlreadyExists
} eTFTPErrorCode_t;

/* Header used in data transfer packets. */
#include "pack_struct_start.h"
struct DataPacketHeader
{
	uint16_t usOpcode;
	uint16_t usBlockNumber;
}
#include "pack_struct_end.h"
typedef struct DataPacketHeader TFTPBlockNumberHeader_t;

/*
 * Manages a single TFTP connection at a time.
 */
static void prvSimpleTFTPServerTask( void *pvParameters );

/*
 * Manage the reception of a file.  If the file is received correctly then
 * return pdPASS, otherwise return pdFAIL.
 */
static BaseType_t prvReceiveFile( FF_FILE *pxFile, struct freertos_sockaddr *pxClient  );

/*
 * Send an error frame to the client.
 */
static void prvSendTFTPError( Socket_t xSocket, struct freertos_sockaddr *pxClient, eTFTPErrorCode_t eErrorCode );

/*
 * Check a received write request contains a potentially valid file name string,
 * and is a binary mode transfer.  If so return a pointer to the file name with
 * the write request packet received from the network, otherwise return NULL.
 */
static const char* prvValidateWriteRequest( Socket_t xSocket, struct freertos_sockaddr *pxClient, uint8_t *pucUDPPayloadBuffer );

/*
 * Called after a valid write request has been received to first check the file
 * does not already exist, and if the file does not exist, create the file ready
 * to be written.  If the file did already exist, or if the file could not be
 * created, then NULL is returned - otherwise a handle to the created file is
 * returned.
 */
static FF_FILE* prvValidateFileToWrite( Socket_t xSocket, struct freertos_sockaddr *pxClient, const char *pcFileName );

/*
 * Send an acknowledgement packet to pxClient with block number usBlockNumber.
 */
static void prvSendAcknowledgement( Socket_t xSocket, struct freertos_sockaddr *pxClient, uint16_t usBlockNumber );

/* The index for the error string below MUST match the value of the applicable
eTFTPErrorCode_t error code value. */
static const char *cErrorStrings[] =
{
	NULL, /* Not valid. */
	"File not found.",
	"Access violation.",
	"Disk full or allocation exceeded.",
	"Illegal TFTP operation.",
	"Unknown transfer ID.",
	"File already exists.",
	"No such user."
};

/*-----------------------------------------------------------*/

void vStartTFTPServerTask( uint16_t usStackSize, UBaseType_t uxPriority )
{
	/* A single server task is created.  Currently this is only capable of
	managing one TFTP transfer at a time. */
	xTaskCreate( prvSimpleTFTPServerTask, "TFTPd", usStackSize, NULL, uxPriority, NULL );
}
/*-----------------------------------------------------------*/

static void prvSimpleTFTPServerTask( void *pvParameters )
{
int32_t lBytes;
uint8_t *pucUDPPayloadBuffer;
struct freertos_sockaddr xClient, xBindAddress;
uint32_t xClientLength = sizeof( xClient ), ulIPAddress;
Socket_t xTFTPListeningSocket;
const char *pcFileName;
FF_FILE *pxFile;

	/* Just to prevent compiler warnings. */
	( void ) pvParameters;

	/* Attempt to open the socket.  The receive block time defaults to the max
	delay, so there is no need to set that separately. */
	xTFTPListeningSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
	configASSERT( xTFTPListeningSocket != FREERTOS_INVALID_SOCKET );

	/* Bind to the standard TFTP port. */
	FreeRTOS_GetAddressConfiguration( &ulIPAddress, NULL, NULL, NULL );
	xBindAddress.sin_addr = ulIPAddress;
	xBindAddress.sin_port = FreeRTOS_htons( tftpPORT_NUMBER );
	FreeRTOS_bind( xTFTPListeningSocket, &xBindAddress, sizeof( xBindAddress ) );

	for( ;; )
	{
		/* Look for the start of a new transfer on the TFTP port.  ulFlags has
		the zero copy bit set (FREERTOS_ZERO_COPY) indicating to the stack that
		a reference to the received data should be passed out to this task using
		the second parameter to the FreeRTOS_recvfrom() call.  When this is done
		the IP stack is no longer responsible for releasing the buffer, and the
		task *must* return the buffer to the stack when it is no longer
		needed. */
		lBytes = FreeRTOS_recvfrom( xTFTPListeningSocket, ( void * ) &pucUDPPayloadBuffer, 0, FREERTOS_ZERO_COPY, &xClient, &xClientLength );

		if( lBytes >= 0 )
		{
			/* Could this be a new write request?  The opcode is contained in
			the first two bytes of the received data. */
			if( ( pucUDPPayloadBuffer[ 0 ] == ( uint8_t ) 0 ) && ( pucUDPPayloadBuffer[ 1 ] == ( uint8_t ) eWriteRequest ) )
			{
				/* If the write request is valid pcFileName will get set to
				point to the file name within pucWriteRequestBuffer - otherwise
				an appropriate error will be sent on xTFTPListeningSocket. */
				pcFileName = prvValidateWriteRequest( xTFTPListeningSocket, &xClient, pucUDPPayloadBuffer );

				if( pcFileName != NULL )
				{
					/* If the file does not already exist, and can be created,
					then xFile will get set to the file's open handle.
					Otherwise an appropriate error will be sent on
					xTFTPListeningSocket. */
					pxFile = prvValidateFileToWrite( xTFTPListeningSocket, &xClient, pcFileName );

					if( pxFile != NULL )
					{
						/* Manage reception of the file. */
						prvReceiveFile( pxFile, &xClient );
					}
				}
			}
			else
			{
				/* Not a transfer ID handled by this server. */
				prvSendTFTPError( xTFTPListeningSocket, &xClient, eUnknownTransferID );
			}

			/* The buffer was received using zero copy, so *must* be freed. */
			FreeRTOS_ReleaseUDPPayloadBuffer( pucUDPPayloadBuffer );
		}
	}
}
/*-----------------------------------------------------------*/

static BaseType_t prvReceiveFile( FF_FILE *pxFile, struct freertos_sockaddr *pxClient )
{
BaseType_t xReturn = pdPASS, xRetries = 0;
uint16_t usExpectedBlockNumber;
Socket_t xTFTPRxSocket = FREERTOS_INVALID_SOCKET;
TickType_t xRxTimeout = pdMS_TO_TICKS( ipconfigTFTP_TIME_OUT_MS );
int32_t lBytes;
uint8_t *pucFileBuffer;
struct freertos_sockaddr xClient;
uint32_t xClientLength = sizeof( xClient );
TFTPBlockNumberHeader_t *pxHeader;
size_t xBlocksWritten, xBytesOfFileDataReceived = tftpMAX_DATA_LENGTH;
const size_t xBlocksToWrite = 1;

	/* The file is open for writing, now create the socket on which the file
	will be received from the client.  Note the socket is not bound	here - so
	will be automatically bound to a port number selected by the IP stack when
	it is used for the first time. */
	xTFTPRxSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );

	if( xTFTPRxSocket != FREERTOS_INVALID_SOCKET )
	{
		/* The socket's Rx block time is set to the user configurable timeout
		value. */
		FreeRTOS_setsockopt( xTFTPRxSocket, 0, FREERTOS_SO_RCVTIMEO, &xRxTimeout, sizeof( xRxTimeout ) );

		/* Acknowledge the write request so the client starts to send the file.
		The first acknowledgment does not have a corresponding block number so
		the special case block number 0 is used. */
		usExpectedBlockNumber = 0;

		do
		{
			/* The acknowledgment sent here may be a duplicate if the last call
			to FreeRTOS_recvfrom() timee out. */
			prvSendAcknowledgement( xTFTPRxSocket, pxClient, usExpectedBlockNumber );

			/* Wait for next data packet.  Zero copy is used so it is the
			responsibility of this task to free the received data once it is no
			longer required. */
			lBytes = FreeRTOS_recvfrom( xTFTPRxSocket, ( void * ) &pucFileBuffer, 0, FREERTOS_ZERO_COPY, &xClient, &xClientLength );

			if( lBytes == 0 )
			{
				/* Timed out. */
				FreeRTOS_printf( ( "Error: Timeout.\n" ) );
				xRetries++;

				if( xRetries > ipconfigTFTP_MAX_RETRIES )
				{
					FreeRTOS_printf( ( "Error: Retry limit exceeded.\n" ) );
					xReturn = pdFAIL;
				}
			}
			else
			{
				/* Data received.  It is expected to be the next sequential
				block. */
				usExpectedBlockNumber++;
				pxHeader = ( TFTPBlockNumberHeader_t * ) pucFileBuffer;
				pxHeader->usOpcode = FreeRTOS_ntohs( pxHeader->usOpcode );
				pxHeader->usBlockNumber = FreeRTOS_ntohs( pxHeader->usBlockNumber );

				/* Is the data as expected and from the expected IP address and
				port? */
				if( ( pxHeader->usOpcode == ( uint16_t ) eData ) 		 &&
					( pxHeader->usBlockNumber == usExpectedBlockNumber ) &&
					( pxClient->sin_addr == xClient.sin_addr ) 			 &&
					( pxClient->sin_port == xClient.sin_port ) )
				{
					/* Everything in the packet other than the header is file
					data. */
					xBytesOfFileDataReceived = ( size_t ) lBytes - sizeof( TFTPBlockNumberHeader_t );
					FreeRTOS_printf( ( "Received %d bytes of file data.\n", ( int ) xBytesOfFileDataReceived ) );

					/* Ack the data then write the data to the file. */
					prvSendAcknowledgement( xTFTPRxSocket, pxClient, usExpectedBlockNumber );

					/* The data is located by jumping over the header. */
					/*_RB_ Is it ok to write 0 bytes? */
					xBlocksWritten = ff_fwrite( pucFileBuffer + sizeof( TFTPBlockNumberHeader_t ),
												xBytesOfFileDataReceived,
												xBlocksToWrite,
												pxFile );

					if( xBlocksWritten != xBlocksToWrite )
					{
						/* File could not be written. */
						prvSendTFTPError( xTFTPRxSocket, pxClient, eDiskFull );
						xReturn = pdFAIL;
					}

					/* Start to receive the next block. */
					xRetries = 0;
				}
				else
				{
					prvSendTFTPError( xTFTPRxSocket, pxClient, eIllegalTFTPOperation );
					xReturn = pdFAIL;
				}

				/* pucFileBuffer was obtained using zero copy mode, so the
				buffer must be freed now its contents have been written to the
				disk. */
				FreeRTOS_ReleaseUDPPayloadBuffer( pucFileBuffer );
			}

		  /* Until a disk write fails, or the maximum number of retries is
		  exceeded, or fewer bytes than tftpMAX_DATA_LENGTH are received (which
		  indicates the end of the file). */
		} while( ( xReturn != pdFAIL ) && ( xBytesOfFileDataReceived == tftpMAX_DATA_LENGTH ) );

		FreeRTOS_printf( ( "Closing connection.\n" ) );
		FreeRTOS_closesocket( xTFTPRxSocket );
	}
	else
	{
		/* An error could be returned here, but it is probably cleaner to just
		time out as the error would have to be sent via the listening socket
		outside of this function. */
		FreeRTOS_printf( ( "Could not create socket to receive file.\n" ) );
	}

	ff_fclose( pxFile );

	return xReturn;
}
/*-----------------------------------------------------------*/

void prvSendAcknowledgement( Socket_t xSocket, struct freertos_sockaddr *pxClient, uint16_t usBlockNumber )
{
/* Small fixed size buffer, so not much to be gained by using the zero copy
interface, just send the buffer directly. */
TFTPBlockNumberHeader_t xAckMessage;

	xAckMessage.usOpcode = FreeRTOS_htons( ( ( uint16_t ) eAck ) );
	xAckMessage.usBlockNumber = FreeRTOS_htons( usBlockNumber );
	FreeRTOS_sendto( xSocket, ( void * ) &xAckMessage, tftpACK_MESSAGE_LENGTH, 0, pxClient, sizeof( struct freertos_sockaddr ) );
}
/*-----------------------------------------------------------*/

static FF_FILE* prvValidateFileToWrite( Socket_t xSocket, struct freertos_sockaddr *pxClient, const char *pcFileName )
{
FF_FILE *pxFile;

	FreeRTOS_printf( ( "Write request for %s received\n", pcFileName ) );

	/* The file cannot be received if it already exists.  Attempt to open the
	file in read mode to see if it exists. */
	pxFile = ff_fopen( pcFileName, "r" );

	if( pxFile != NULL )
	{
		/* Can't receive a new file without deleting the old one first. */
		ff_fclose( pxFile );
		pxFile = NULL;
		prvSendTFTPError( xSocket, pxClient, eFileAlreadyExists );
	}
	else
	{
		/* The file does not already exist.  Attempt to open the file in write
		mode, which will cause it to be created. */
		pxFile = ff_fopen( pcFileName, "w" );

		if( pxFile == NULL )
		{
			/* The file cannot be created. */
			prvSendTFTPError( xSocket, pxClient, eAccessViolation );
		}
	}

	return pxFile;
}
/*-----------------------------------------------------------*/

static const char* prvValidateWriteRequest( Socket_t xSocket, struct freertos_sockaddr *pxClient, uint8_t *pucUDPPayloadBuffer )
{
char *pcFileName;
BaseType_t x;
const char *pcOctedMode = "octet";

	/* pcFileName is set to point to the file name which is inside the write
	request frame, so its important not to free the frame until the operation is
	over.  The start of the file name string is after the opcode, so two bytes
	into the packet. */
	pcFileName = ( char * ) &( pucUDPPayloadBuffer[ tftpFILE_NAME_OFFSET ] );

	/* Sanity check the file name. */
	for( x = 0; x < ffconfigMAX_FILENAME; x++ )
	{
		if( pcFileName[ x ] == 0x00 )
		{
			/* The end of the string was located. */
			break;
		}
		else if( ( pcFileName[ x ] < ' ' ) || ( pcFileName[ x ] > '~' ) )
		{
			/* Not a valid file name character. */
			pcFileName = NULL;
			break;
		}
		else
		{
			/* Just a character in the file name. */
		}
	}

	if( pcFileName != NULL )
	{
		/* Only binary transfers are supported, indicated by an 'octet' mode
		string following the file name. +1 to move past the null terminator to
		the start of the next string. */
		x++;
		if( strcmpi( pcOctedMode, ( const char * ) &( pucUDPPayloadBuffer[ tftpFILE_NAME_OFFSET + x ] ) ) != 0 )
		{
			/* Not the expected mode. */
			prvSendTFTPError( xSocket, pxClient, eIllegalTFTPOperation );
			pcFileName = NULL;
		}
	}
	else
	{
		prvSendTFTPError( xSocket, pxClient, eFileNotFound );
	}

	return pcFileName;
}
/*-----------------------------------------------------------*/

static void prvSendTFTPError( Socket_t xSocket, struct freertos_sockaddr *pxClient, eTFTPErrorCode_t eErrorCode )
{
uint8_t *pucUDPPayloadBuffer = NULL;
const size_t xFixedSizePart = ( size_t ) 5; /* 2 byte opcode, plus two byte error code, plus string terminating 0. */
const size_t xNumberOfErrorStrings = sizeof( cErrorStrings ) / sizeof( char * );
size_t xErrorCode = ( size_t ) eErrorCode, xTotalLength = 0; /* Only initialised to keep compiler quiet. */
const char *pcErrorString = NULL;
int32_t lReturned;

	/* The total size of the packet to be sent depends on the length of the
	error string. */
	if( xErrorCode < xNumberOfErrorStrings )
	{
		pcErrorString = cErrorStrings[ xErrorCode ];

		/* This task is going to send using the zero copy interface.  The data
		being sent is therefore written directly into a buffer that is passed
		into, rather than copied into, the FreeRTOS_sendto() function.  First
		obtain a buffer of adequate length from the IP stack into which the
		error packet will be written.  Although a max delay is used, the actual
		delay will be capped to ipconfigMAX_SEND_BLOCK_TIME_TICKS. */
		xTotalLength = strlen( pcErrorString ) + xFixedSizePart;
		pucUDPPayloadBuffer = ( uint8_t * ) FreeRTOS_GetUDPPayloadBuffer( xTotalLength, portMAX_DELAY );
	}

	if( pucUDPPayloadBuffer != NULL )
	{
		FreeRTOS_printf( ( "Error: %s\n", pcErrorString ) );

		/* Create error packet: Opcode. */
		pucUDPPayloadBuffer[ 0 ] = 0;
		pucUDPPayloadBuffer[ 1 ] = ( uint8_t ) eError;

		/* Create error packet: Error code. */
		pucUDPPayloadBuffer[ 2 ] = 0;
		pucUDPPayloadBuffer[ 3 ] = ( uint8_t ) eErrorCode;

		/* Create error packet: Error string. */
		strcpy( ( ( char * ) &( pucUDPPayloadBuffer[ 4 ] ) ), pcErrorString );

		/* Pass the buffer into the send function.  ulFlags has the
		FREERTOS_ZERO_COPY bit set so the IP stack will take control of the
		buffer rather than copy data out of the buffer. */
		lReturned = FreeRTOS_sendto( xSocket,  						/* The socket to which the error frame is sent. */
									( void * ) pucUDPPayloadBuffer, /* A pointer to the the data being sent. */
									xTotalLength, 					/* The length of the data being sent. */
									FREERTOS_ZERO_COPY, 			/* ulFlags with the FREERTOS_ZERO_COPY bit set. */
									pxClient, 			/* Where the data is being sent. */
									sizeof( *pxClient ) );

		if( lReturned == 0 )
		{
			/* The send operation failed, so this task is still responsible
			for the buffer obtained from the IP stack.  To ensure the buffer
			is not lost it must either be used again, or, as in this case,
			returned to the IP stack using FreeRTOS_ReleaseUDPPayloadBuffer(). */
			FreeRTOS_ReleaseUDPPayloadBuffer( ( void * ) pucUDPPayloadBuffer );
		}
		else
		{
			/* The send was successful so the IP stack is now managing the
			buffer pointed to by pucUDPPayloadBuffer, and the IP stack will
			return the buffer once it has been sent. */
		}
	}
}


