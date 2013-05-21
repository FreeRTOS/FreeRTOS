/*
 * FreeRTOS+UDP V1.0.0 (C) 2013 Real Time Engineers ltd.
 *
 * This file is part of the FreeRTOS+UDP distribution.  The FreeRTOS+UDP license
 * terms are different to the FreeRTOS license terms.
 *
 * FreeRTOS+UDP uses a dual license model that allows the software to be used 
 * under a standard GPL open source license, or a commercial license.  The 
 * standard GPL license (unlike the modified GPL license under which FreeRTOS 
 * itself is distributed) requires that all software statically linked with 
 * FreeRTOS+UDP is also distributed under the same GPL V2 license terms.  
 * Details of both license options follow:
 *
 * - Open source licensing -
 * FreeRTOS+UDP is a free download and may be used, modified, evaluated and
 * distributed without charge provided the user adheres to version two of the
 * GNU General Public License (GPL) and does not remove the copyright notice or
 * this text.  The GPL V2 text is available on the gnu.org web site, and on the
 * following URL: http://www.FreeRTOS.org/gpl-2.0.txt.
 *
 * - Commercial licensing -
 * Businesses and individuals that for commercial or other reasons cannot comply
 * with the terms of the GPL V2 license must obtain a commercial license before 
 * incorporating FreeRTOS+UDP into proprietary software for distribution in any 
 * form.  Commercial licenses can be purchased from http://shop.freertos.org/udp 
 * and do not require any source files to be changed.
 *
 * FreeRTOS+UDP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+UDP unless you agree that you use the software 'as is'.
 * FreeRTOS+UDP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/udp
 *
 */

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_Sockets.h"
#include "NetworkInterface.h"
#include "IPTraceMacroDefaults.h"

/* Exclude the entire file if DNS is not enabled. */
#if ipconfigUSE_DNS != 0

#if( ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN )
	#define dnsOUTGOING_FLAGS				0x0001 /* Standard query. */
	#define dnsTYPE							0x0100 /* A record (host address. */
	#define dnsCLASS						0x0100 /* IN */
	#define dnsDNS_PORT						0x3500
	#define dnsONE_QUESTION					0x0100
	#define dnsRX_FLAGS_MASK				0x0f80 /* The bits of interest in the flags field of incoming DNS messages. */
	#define dnsEXPECTED_RX_FLAGS			0x0080 /* Should be a response, without any errors. */
#else
	#define dnsDNS_PORT						0x35
	#define dnsONE_QUESTION					0x01
	#define dnsFLAG_QUERY_RESPONSE_BIT		0x8000
	#define dnsFLAG_OPERATION_CODE_BITS		0x7800
	#define dnsFLAG_TRUNCATION_BIT			0x0200
	#define dnsFLAG_RESPONSE_CODE_BITS		0x000f
	#define dnsOUTGOING_FLAGS				0x0100 /* Standard query. */
	#define dnsTYPE							0x0001 /* A record (host address. */
	#define dnsCLASS						0x0001 /* IN */
	#define dnsRX_FLAGS_MASK				0x800f /* The bits of interest in the flags field of incoming DNS messages. */
	#define dnsEXPECTED_RX_FLAGS			0x8000 /* Should be a response, without any errors. */
#endif /* ipconfigBYTE_ORDER */

/* The maximum number of times a DNS request should be sent out if a response
is not received, before giving up. */
#define dnsMAX_REQUEST_ATTEMPTS		5

/* If the top two bits in the first character of a name field are set then the
name field is an offset to the string, rather than the string itself. */
#define dnsNAME_IS_OFFSET			( ( uint8_t ) 0xc0 )

/*
 * Create a socket and bind it to the standard DNS port number.  Return the
 * the created socket - or NULL if the socket could not be created or bound.
 */
static xSocket_t prvCreateDNSSocket( void );

/*
 * Create the DNS message in the zero copy buffer passed in the first parameter.
 */
static size_t prvCreateDNSMessage( uint8_t *pucUDPPayloadBuffer, const uint8_t *pcHostName, uint16_t usIdentifier );

/*
 * Simple routine that jumps over the NAME field of a resource record.
 */
static uint8_t *prvSkipNameField( uint8_t *pucByte );

/*
 * Process a response packet from a DNS server.
 */
static uint32_t prvParseDNSReply( uint8_t *pucUDPPayloadBuffer, uint16_t usIdentifier );

/*-----------------------------------------------------------*/

#include "pack_struct_start.h"
struct xDNSMessage
{
	uint16_t usIdentifier;
	uint16_t usFlags;
	uint16_t usQuestions;
	uint16_t usAnswers;
	uint16_t usAuthorityRRs;
	uint16_t usAdditionalRRs;
}
#include "pack_struct_end.h"
typedef struct xDNSMessage xDNSMessage_t;

/*-----------------------------------------------------------*/

uint32_t FreeRTOS_gethostbyname( const uint8_t *pcHostName )
{
static uint16_t usIdentifier = 0;
struct freertos_sockaddr xAddress;
static xSocket_t xDNSSocket = NULL;
uint32_t ulIPAddress = 0UL;
uint8_t *pucUDPPayloadBuffer;
static uint32_t ulAddressLength;
portBASE_TYPE xAttempt;
int32_t lBytes;
size_t xPayloadLength;
const size_t xExpectedPayloadLength = sizeof( xDNSMessage_t ) + strlen( ( const char * const ) pcHostName ) + sizeof( uint16_t ) + sizeof( uint16_t ) + 2; /* Two for the count of characters in the first subdomain part, and the string end byte */

	if( xDNSSocket == NULL )
	{
		xDNSSocket = prvCreateDNSSocket();
	}

	if( xDNSSocket != NULL )
	{
		/* Generate a unique identifier for this query. */
		usIdentifier++;

		for( xAttempt = 0; xAttempt < dnsMAX_REQUEST_ATTEMPTS; xAttempt++ )
		{
			/* Get a buffer.  This uses a maximum delay, but the delay will be
			capped to ipconfigMAX_SEND_BLOCK_TIME_TICKS so the return value
			still needs to be tested. */
			pucUDPPayloadBuffer = ( uint8_t * ) FreeRTOS_GetUDPPayloadBuffer( xExpectedPayloadLength, portMAX_DELAY );
			if( pucUDPPayloadBuffer != NULL )
			{
				/* Create the message in the obtained buffer. */
				xPayloadLength = prvCreateDNSMessage( pucUDPPayloadBuffer, pcHostName, usIdentifier );
				iptraceSENDING_DNS_REQUEST();

				/* Obtain the DNS server address. */
				FreeRTOS_GetAddressConfiguration( NULL, NULL, NULL, &ulIPAddress );

				/* Send the DNS message. */
				xAddress.sin_addr = ulIPAddress;
				xAddress.sin_port = dnsDNS_PORT;
				ulIPAddress = 0;

				if( FreeRTOS_sendto( xDNSSocket, pucUDPPayloadBuffer, xPayloadLength, FREERTOS_ZERO_COPY, &xAddress, sizeof( xAddress ) ) != 0 )
				{
					/* Wait for the reply. */
					lBytes = FreeRTOS_recvfrom( xDNSSocket, &pucUDPPayloadBuffer, 0, FREERTOS_ZERO_COPY, &xAddress, &ulAddressLength );

					if( lBytes > 0 )
					{
						/* The reply was received.  Process it. */
						ulIPAddress = prvParseDNSReply( pucUDPPayloadBuffer, usIdentifier );

						/* Finished with the buffer.  The zero copy interface
						is being used, so the buffer must be freed by the
						task. */
						FreeRTOS_ReleaseUDPPayloadBuffer( ( void * ) pucUDPPayloadBuffer );

						if( ulIPAddress != 0 )
						{
							/* All done. */
							break;
						}
					}
				}
				else
				{
					/* The message was not sent so the stack will not be
					releasing the zero copy - it must be released here. */
					FreeRTOS_ReleaseUDPPayloadBuffer( ( void * ) pucUDPPayloadBuffer );
				}
			}
		}
	}

	return ulIPAddress;
}
/*-----------------------------------------------------------*/

static size_t prvCreateDNSMessage( uint8_t *pucUDPPayloadBuffer, const uint8_t *pcHostName, uint16_t usIdentifier )
{
xDNSMessage_t *pxDNSMessageHeader;
uint8_t *pucStart, *pucByte;
const uint16_t usARecordType = dnsTYPE, usClass = dnsCLASS;
static const xDNSMessage_t xDefaultPartDNSHeader =
{
	0,					/* The identifier will be overwritten. */
	dnsOUTGOING_FLAGS,	/* Flags set for standard query. */
	dnsONE_QUESTION,	/* One question is being asked. */
	0,					/* No replies are included. */
	0,					/* No authorities. */
	0					/* No additional authorities. */
};

	/* Copy in the const part of the header. */
	memcpy( ( void * ) pucUDPPayloadBuffer, ( void * ) &xDefaultPartDNSHeader, sizeof( xDefaultPartDNSHeader ) );

	/* Write in a unique identifier. */
	pxDNSMessageHeader = ( xDNSMessage_t * ) pucUDPPayloadBuffer;
	pxDNSMessageHeader->usIdentifier = usIdentifier;

	/* Create the resource record at the end of the header.  First
	find the end of the header. */
	pucStart = pucUDPPayloadBuffer + sizeof( xDefaultPartDNSHeader );

	/* Leave a gap for the first length bytes. */
	pucByte = pucStart + 1;

	/* Copy in the host name. */
	strcpy( ( char * ) pucByte, ( const char * ) pcHostName );

	/* Mark the end of the string. */
	pucByte += strlen( ( const char * ) pcHostName );
	*pucByte = 0x00;

	/* Walk the string to replace the '.' characters with byte counts.
	pucStart holds the address of the byte count.  Walking the string
	starts after the byte count position. */
	pucByte = pucStart;

	do
	{
		pucByte++;

		while( ( *pucByte != 0x00 ) && ( *pucByte != '.' ) )
		{
			pucByte++;
		}

		/* Fill in the byte count, then move the pucStart pointer up to
		the found byte position. */
		*pucStart = ( uint8_t ) ( ( uint32_t ) pucByte - ( uint32_t ) pucStart );
		( *pucStart )--;

		pucStart = pucByte;

	} while( *pucByte != 0x00 );

	/* Finish off the record. */
	pucByte++;
	memcpy( ( void * ) pucByte, &usARecordType, sizeof( uint16_t ) );
	pucByte += sizeof( uint16_t );
	memcpy( ( void * ) pucByte, &usClass, sizeof( uint16_t ) );
	pucByte += sizeof( uint16_t );

	/* Return the total size of the generated message, which is the space from
	the last written byte to the beginning of the buffer. */
	return ( ( uint32_t ) pucByte - ( uint32_t ) pucUDPPayloadBuffer );
}
/*-----------------------------------------------------------*/

static uint8_t *prvSkipNameField( uint8_t *pucByte )
{
	/* Determine if the name is the fully coded name, or an offset to the name
	elsewhere in the message. */
	if( ( *pucByte & dnsNAME_IS_OFFSET ) == dnsNAME_IS_OFFSET )
	{
		/* Jump over the two byte offset. */
		pucByte += sizeof( uint16_t );

	}
	else
	{
		/* pucByte points to the full name.  Walk over the string. */
		while( *pucByte != 0x00 )
		{
			/* The number of bytes to jump for each name section is stored in the byte
			before the name section. */
			pucByte += ( *pucByte + 1 );
		}

		pucByte++;
	}

	return pucByte;
}
/*-----------------------------------------------------------*/

static uint32_t prvParseDNSReply( uint8_t *pucUDPPayloadBuffer, uint16_t usIdentifier )
{
xDNSMessage_t *pxDNSMessageHeader;
uint32_t ulIPAddress = 0UL;
uint8_t *pucByte;
uint16_t x, usDataLength;
const uint16_t usARecordType = dnsTYPE;

	pxDNSMessageHeader = ( xDNSMessage_t * ) pucUDPPayloadBuffer;

	if( pxDNSMessageHeader->usIdentifier == usIdentifier )
	{
		if( ( pxDNSMessageHeader->usFlags & dnsRX_FLAGS_MASK ) == dnsEXPECTED_RX_FLAGS )
		{
			/* Start at the first byte after the header. */
			pucByte = pucUDPPayloadBuffer + sizeof( xDNSMessage_t );

			/* Skip any question records. */
			pxDNSMessageHeader->usQuestions = FreeRTOS_ntohs( pxDNSMessageHeader->usQuestions );
			for( x = 0; x < pxDNSMessageHeader->usQuestions; x++ )
			{
				/* Skip the variable length name field. */
				pucByte = prvSkipNameField( pucByte );

				/* Skip the type and class fields. */
				pucByte += sizeof( uint32_t );
			}

			/* Search through the answers records. */
			pxDNSMessageHeader->usAnswers = FreeRTOS_ntohs( pxDNSMessageHeader->usAnswers );
			for( x = 0; x < pxDNSMessageHeader->usAnswers; x++ )
			{
				pucByte = prvSkipNameField( pucByte );

				/* Is the type field that of an A record? */
				if( memcmp( ( void * ) pucByte, ( void * ) &usARecordType, sizeof( uint16_t ) ) == 0 )
				{
					/* This is the required record.  Skip the type, class, and
					time to live fields, plus the first byte of the data
					length. */
					pucByte += ( sizeof( uint32_t ) + sizeof( uint32_t ) + sizeof( uint8_t ) );

					/* Sanity check the data length. */
					if( *pucByte == sizeof( uint32_t ) )
					{
						/* Skip the second byte of the length. */
						pucByte++;

						/* Copy the IP address out of the record. */
						memcpy( ( void * ) &ulIPAddress, ( void * ) pucByte, sizeof( uint32_t ) );
					}

					break;
				}
				else
				{
					/* Skip the type, class and time to live fields. */
					pucByte += ( sizeof( uint32_t ) + sizeof( uint32_t ) );

					/* Determine the length of the data in the field. */
					memcpy( ( void * ) &usDataLength, ( void * ) pucByte, sizeof( uint16_t ) );
					usDataLength = FreeRTOS_ntohs( usDataLength );

					/* Jump over the data lenth bytes, and the data itself. */
					pucByte += usDataLength + sizeof( uint16_t );
				}
			}
		}
	}

	return ulIPAddress;
}
/*-----------------------------------------------------------*/

static xSocket_t prvCreateDNSSocket( void )
{
static xSocket_t xSocket = NULL;
struct freertos_sockaddr xAddress;
portBASE_TYPE xReturn;
portTickType xTimeoutTime = 200 / portTICK_RATE_MS;

	/* This must be the first time this function has been called.  Create
	the socket. */
	xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );

	/* Auto bind the port. */
	xAddress.sin_port = 0;
	xReturn = FreeRTOS_bind( xSocket, &xAddress, sizeof( xAddress ) );

	/* Check the bind was successful, and clean up if not. */
	if( xReturn != 0 )
	{
		FreeRTOS_closesocket( xSocket );
		xSocket = NULL;
	}
	else
	{
		/* Set the send and receive timeouts. */
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, ( void * ) &xTimeoutTime, sizeof( portTickType ) );
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_SNDTIMEO, ( void * ) &xTimeoutTime, sizeof( portTickType ) );
	}

	return xSocket;
}

#endif /* ipconfigUSE_DNS != 0 */


