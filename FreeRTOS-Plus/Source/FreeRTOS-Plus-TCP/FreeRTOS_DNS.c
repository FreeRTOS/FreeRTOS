/*
 * FreeRTOS+TCP V2.2.0
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "list.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DNS.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"
#include "IPTraceMacroDefaults.h"

/* Exclude the entire file if DNS is not enabled. */
#if( ipconfigUSE_DNS != 0 )

#if( ipconfigBYTE_ORDER == pdFREERTOS_LITTLE_ENDIAN )
	#define dnsDNS_PORT				0x3500u
	#define dnsONE_QUESTION			0x0100u
	#define dnsOUTGOING_FLAGS		0x0001u     /* Standard query. */
	#define dnsRX_FLAGS_MASK		0x0f80u     /* The bits of interest in the flags field of incoming DNS messages. */
	#define dnsEXPECTED_RX_FLAGS	0x0080u     /* Should be a response, without any errors. */
#else
	#define dnsDNS_PORT				0x0035u
	#define dnsONE_QUESTION			0x0001u
	#define dnsOUTGOING_FLAGS		0x0100u     /* Standard query. */
	#define dnsRX_FLAGS_MASK		0x800fu     /* The bits of interest in the flags field of incoming DNS messages. */
	#define dnsEXPECTED_RX_FLAGS	0x8000u     /* Should be a response, without any errors. */

#endif /* ipconfigBYTE_ORDER */

/* The maximum number of times a DNS request should be sent out if a response
is not received, before giving up. */
#ifndef ipconfigDNS_REQUEST_ATTEMPTS
	#define ipconfigDNS_REQUEST_ATTEMPTS    5
#endif

/* If the top two bits in the first character of a name field are set then the
name field is an offset to the string, rather than the string itself. */
#define dnsNAME_IS_OFFSET					 ( ( uint8_t ) 0xc0 )

/* NBNS flags. */
#define dnsNBNS_FLAGS_RESPONSE				 0x8000u
#define dnsNBNS_FLAGS_OPCODE_MASK			 0x7800u
#define dnsNBNS_FLAGS_OPCODE_QUERY			 0x0000u
#define dnsNBNS_FLAGS_OPCODE_REGISTRATION	 0x2800u

/* Host types. */
#define dnsTYPE_A_HOST						 0x01u
#define dnsCLASS_IN							 0x01u

/* LLMNR constants. */
#define dnsLLMNR_TTL_VALUE					 300000uL
#define dnsLLMNR_FLAGS_IS_REPONSE			 0x8000u

/* NBNS constants. */
#define dnsNBNS_TTL_VALUE					 3600uL /* 1 hour valid */
#define dnsNBNS_TYPE_NET_BIOS				 0x0020u
#define dnsNBNS_CLASS_IN					 0x01u
#define dnsNBNS_NAME_FLAGS					 0x6000u
#define dnsNBNS_ENCODED_NAME_LENGTH			 32

/* If the queried NBNS name matches with the device's name,
the query will be responded to with these flags: */
#define dnsNBNS_QUERY_RESPONSE_FLAGS		 ( 0x8500u )

/* Flag DNS parsing errors in situations where an IPv4 address is the return
type. */
#define dnsPARSE_ERROR						 0uL

/*
 * Create a socket and bind it to the standard DNS port number.  Return the
 * the created socket - or NULL if the socket could not be created or bound.
 */
static Socket_t prvCreateDNSSocket( void );

/*
 * Create the DNS message in the zero copy buffer passed in the first parameter.
 */
static size_t prvCreateDNSMessage( uint8_t *pucUDPPayloadBuffer,
								   const char *pcHostName,
								   TickType_t uxIdentifier );

/*
 * Simple routine that jumps over the NAME field of a resource record.
 */
static uint8_t * prvSkipNameField( uint8_t *pucByte,
								   size_t uxSourceLen );

/*
 * Process a response packet from a DNS server.
 * The parameter 'xExpected' indicates whether the identifier in the reply
 * was expected, and thus if the DNS cache may be updated with the reply.
 */
static uint32_t prvParseDNSReply( uint8_t *pucUDPPayloadBuffer,
								  size_t uxBufferLength,
								  BaseType_t xExpected );

/*
 * Prepare and send a message to a DNS server.  'uxReadTimeOut_ticks' will be passed as
 * zero, in case the user has supplied a call-back function.
 */
static uint32_t prvGetHostByName( const char *pcHostName,
								  TickType_t uxIdentifier,
								  TickType_t uxReadTimeOut_ticks );

/*
 * The NBNS and the LLMNR protocol share this reply function.
 */
#if( ( ipconfigUSE_NBNS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) )
	static void prvReplyDNSMessage( NetworkBufferDescriptor_t *pxNetworkBuffer,
									BaseType_t lNetLength );
#endif

#if( ipconfigUSE_NBNS == 1 )
	static portINLINE void prvTreatNBNS( uint8_t *pucUDPPayloadBuffer,
										 size_t uxBufferLength,
										 uint32_t ulIPAddress );
#endif /* ipconfigUSE_NBNS */


#if( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )
	static uint8_t * prvReadNameField( uint8_t *pucByte,
									   size_t uxSourceLen,
									   char *pcName,
									   size_t uxLen );
#endif /* ipconfigUSE_DNS_CACHE || ipconfigDNS_USE_CALLBACKS */

#if( ipconfigUSE_DNS_CACHE == 1 )
	static void prvProcessDNSCache( const char *pcName,
									uint32_t *pulIP,
									uint32_t ulTTL,
									BaseType_t xLookUp );

	typedef struct xDNS_CACHE_TABLE_ROW
	{
		uint32_t ulIPAddress;                         /* The IP address of an ARP cache entry. */
		char pcName[ ipconfigDNS_CACHE_NAME_LENGTH ]; /* The name of the host */
		uint32_t ulTTL;                               /* Time-to-Live (in seconds) from the DNS server. */
		uint32_t ulTimeWhenAddedInSeconds;
	} DNSCacheRow_t;

	static DNSCacheRow_t xDNSCache[ ipconfigDNS_CACHE_ENTRIES ];

	void FreeRTOS_dnsclear()
	{
		memset( xDNSCache, 0x0, sizeof( xDNSCache ) );
	}
#endif /* ipconfigUSE_DNS_CACHE == 1 */

#if( ipconfigUSE_LLMNR == 1 )
	const MACAddress_t xLLMNR_MacAdress = { { 0x01, 0x00, 0x5e, 0x00, 0x00, 0xfc } };
#endif /* ipconfigUSE_LLMNR == 1 */

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
typedef struct xDNSMessage DNSMessage_t;

/* A DNS query consists of a header, as described in 'struct xDNSMessage'
It is followed by 1 or more queries, each one consisting of a name and a tail,
with two fields: type and class
*/
#include "pack_struct_start.h"
struct xDNSTail
{
	uint16_t usType;
	uint16_t usClass;
}
#include "pack_struct_end.h"
typedef struct xDNSTail DNSTail_t;

/* DNS answer record header. */
#include "pack_struct_start.h"
struct xDNSAnswerRecord
{
	uint16_t usType;
	uint16_t usClass;
	uint32_t ulTTL;
	uint16_t usDataLength;
}
#include "pack_struct_end.h"
typedef struct xDNSAnswerRecord DNSAnswerRecord_t;

#if( ipconfigUSE_LLMNR == 1 )

	#include "pack_struct_start.h"
	struct xLLMNRAnswer
	{
		uint8_t ucNameCode;
		uint8_t ucNameOffset;   /* The name is not repeated in the answer, only the offset is given with "0xc0 <offs>" */
		uint16_t usType;
		uint16_t usClass;
		uint32_t ulTTL;
		uint16_t usDataLength;
		uint32_t ulIPAddress;
	}
	#include "pack_struct_end.h"
	typedef struct xLLMNRAnswer LLMNRAnswer_t;

#endif /* ipconfigUSE_LLMNR == 1 */

#if( ipconfigUSE_NBNS == 1 )

	#include "pack_struct_start.h"
	struct xNBNSRequest
	{
		uint16_t usRequestId;
		uint16_t usFlags;
		uint16_t ulRequestCount;
		uint16_t usAnswerRSS;
		uint16_t usAuthRSS;
		uint16_t usAdditionalRSS;
		uint8_t ucNameSpace;
		uint8_t ucName[ dnsNBNS_ENCODED_NAME_LENGTH ];
		uint8_t ucNameZero;
		uint16_t usType;
		uint16_t usClass;
	}
	#include "pack_struct_end.h"
	typedef struct xNBNSRequest NBNSRequest_t;

	#include "pack_struct_start.h"
	struct xNBNSAnswer
	{
		uint16_t usType;
		uint16_t usClass;
		uint32_t ulTTL;
		uint16_t usDataLength;
		uint16_t usNbFlags;     /* NetBIOS flags 0x6000 : IP-address, big-endian */
		uint32_t ulIPAddress;
	}
	#include "pack_struct_end.h"
	typedef struct xNBNSAnswer NBNSAnswer_t;

	#endif /* ipconfigUSE_NBNS == 1 */

/*-----------------------------------------------------------*/

#if( ipconfigUSE_DNS_CACHE == 1 )
	uint32_t FreeRTOS_dnslookup( const char *pcHostName )
	{
	uint32_t ulIPAddress = 0uL;

		prvProcessDNSCache( pcHostName, &ulIPAddress, 0, pdTRUE );
		return ulIPAddress;
	}
#endif /* ipconfigUSE_DNS_CACHE == 1 */
/*-----------------------------------------------------------*/

#if( ipconfigDNS_USE_CALLBACKS == 1 )

	typedef struct xDNS_Callback
	{
		TickType_t uxRemaningTime;		/* Timeout in ms */
		FOnDNSEvent pCallbackFunction;	/* Function to be called when the address has been found or when a timeout has beeen reached */
		TimeOut_t uxTimeoutState;
		void *pvSearchID;
		struct xLIST_ITEM xListItem;
		char pcName[ 1 ];
	} DNSCallback_t;

	static List_t xCallbackList;

	/* Define FreeRTOS_gethostbyname() as a normal blocking call. */
	uint32_t FreeRTOS_gethostbyname( const char *pcHostName )
	{
		return FreeRTOS_gethostbyname_a( pcHostName, ( FOnDNSEvent ) NULL, ( void * ) NULL, 0 );
	}
	/*-----------------------------------------------------------*/

	/* Initialise the list of call-back structures. */
	void vDNSInitialise( void );
	void vDNSInitialise( void )
	{
		vListInitialise( &xCallbackList );
	}
	/*-----------------------------------------------------------*/

	/* Iterate through the list of call-back structures and remove
	old entries which have reached a timeout.
	As soon as the list hase become empty, the DNS timer will be stopped
	In case pvSearchID is supplied, the user wants to cancel a DNS request
	*/
	void vDNSCheckCallBack( void *pvSearchID );
	void vDNSCheckCallBack( void *pvSearchID )
	{
	const ListItem_t *pxIterator;
	const MiniListItem_t * xEnd = ( const MiniListItem_t * ) listGET_END_MARKER( &xCallbackList );

		vTaskSuspendAll();
		{
			for( pxIterator  = ( const ListItem_t * ) listGET_NEXT( xEnd );
				 pxIterator != ( const ListItem_t * ) xEnd;
				 )
			{
			DNSCallback_t *pxCallback = ( DNSCallback_t * ) listGET_LIST_ITEM_OWNER( pxIterator );

				/* Move to the next item because we might remove this item */
				pxIterator = ( const ListItem_t * ) listGET_NEXT( pxIterator );

				if( ( pvSearchID != NULL ) && ( pvSearchID == pxCallback->pvSearchID ) )
				{
					uxListRemove( &pxCallback->xListItem );
					vPortFree( pxCallback );
				}
				else if( xTaskCheckForTimeOut( &pxCallback->uxTimeoutState, &pxCallback->uxRemaningTime ) != pdFALSE )
				{
					pxCallback->pCallbackFunction( pxCallback->pcName, pxCallback->pvSearchID, 0 );
					uxListRemove( &pxCallback->xListItem );
					vPortFree( ( void * ) pxCallback );
				}
			}
		}
		xTaskResumeAll();

		if( listLIST_IS_EMPTY( &xCallbackList ) )
		{
			vIPSetDnsTimerEnableState( pdFALSE );
		}
	}
	/*-----------------------------------------------------------*/

	void FreeRTOS_gethostbyname_cancel( void *pvSearchID )
	{
		/* _HT_ Should better become a new API call to have the IP-task remove the callback */
		vDNSCheckCallBack( pvSearchID );
	}
	/*-----------------------------------------------------------*/

	/* FreeRTOS_gethostbyname_a() was called along with callback parameters.
	Store them in a list for later reference. */
	static void vDNSSetCallBack( const char *pcHostName,
								 void *pvSearchID,
								 FOnDNSEvent pCallbackFunction,
								 TickType_t uxTimeout,
								 TickType_t uxIdentifier );
	static void vDNSSetCallBack( const char *pcHostName,
								 void *pvSearchID,
								 FOnDNSEvent pCallbackFunction,
								 TickType_t uxTimeout,
								 TickType_t uxIdentifier )
	{
	size_t lLength = strlen( pcHostName );
	DNSCallback_t *pxCallback = ( DNSCallback_t * ) pvPortMalloc( sizeof( *pxCallback ) + lLength );

		/* Translate from ms to number of clock ticks. */
		uxTimeout /= portTICK_PERIOD_MS;

		if( pxCallback != NULL )
		{
			if( listLIST_IS_EMPTY( &xCallbackList ) )
			{
				/* This is the first one, start the DNS timer to check for timeouts */
				vIPReloadDNSTimer( FreeRTOS_min_uint32( 1000U, uxTimeout ) );
			}

			strcpy( pxCallback->pcName, pcHostName );
			pxCallback->pCallbackFunction = pCallbackFunction;
			pxCallback->pvSearchID = pvSearchID;
			pxCallback->uxRemaningTime = uxTimeout;
			vTaskSetTimeOutState( &pxCallback->uxTimeoutState );
			listSET_LIST_ITEM_OWNER( &( pxCallback->xListItem ), ( void * ) pxCallback );
			listSET_LIST_ITEM_VALUE( &( pxCallback->xListItem ), uxIdentifier );
			vTaskSuspendAll();
			{
				vListInsertEnd( &xCallbackList, &pxCallback->xListItem );
			}
			xTaskResumeAll();
		}
	}
	/*-----------------------------------------------------------*/

	/* A DNS reply was received, see if there is any matching entry and
	call the handler.  Returns pdTRUE if uxIdentifier was recognised. */
	static BaseType_t xDNSDoCallback( TickType_t uxIdentifier,
									  const char *pcName,
									  uint32_t ulIPAddress );
	static BaseType_t xDNSDoCallback( TickType_t uxIdentifier,
									  const char *pcName,
									  uint32_t ulIPAddress )
	{
	BaseType_t xResult = pdFALSE;
	const ListItem_t *pxIterator;
	const MiniListItem_t * xEnd = ( const MiniListItem_t * ) listGET_END_MARKER( &xCallbackList );

		vTaskSuspendAll();
		{
			for( pxIterator  = ( const ListItem_t * ) listGET_NEXT( xEnd );
				 pxIterator != ( const ListItem_t * ) xEnd;
				 pxIterator  = ( const ListItem_t * ) listGET_NEXT( pxIterator ) )
			{
				/* The cast will take away the 'configLIST_VOLATILE' */
				if( uxIdentifier == ( TickType_t ) listGET_LIST_ITEM_VALUE( pxIterator ) )
				{
				DNSCallback_t *pxCallback = ( DNSCallback_t * ) listGET_LIST_ITEM_OWNER( pxIterator );

					pxCallback->pCallbackFunction( pcName, pxCallback->pvSearchID, ulIPAddress );
					uxListRemove( &pxCallback->xListItem );
					vPortFree( pxCallback );

					if( listLIST_IS_EMPTY( &xCallbackList ) )
					{
						/* The list of outstanding requests is empty. No need for periodic polling. */
						vIPSetDnsTimerEnableState( pdFALSE );
					}

					xResult = pdTRUE;
					break;
				}
			}
		}
		xTaskResumeAll();
		return xResult;
	}

#endif /* ipconfigDNS_USE_CALLBACKS == 1 */
/*-----------------------------------------------------------*/

#if( ipconfigDNS_USE_CALLBACKS == 0 )
	uint32_t FreeRTOS_gethostbyname( const char *pcHostName )
#else
	uint32_t FreeRTOS_gethostbyname_a( const char *pcHostName,
									   FOnDNSEvent pCallback,
									   void *pvSearchID,
									   TickType_t uxTimeout )
#endif
{
uint32_t ulIPAddress = 0uL;
TickType_t uxReadTimeOut_ticks = ipconfigDNS_RECEIVE_BLOCK_TIME_TICKS;
TickType_t uxIdentifier = 0u;
BaseType_t xHasRandom = pdFALSE;

	if( pcHostName != NULL )
	{
		/* If the supplied hostname is IP address, convert it to uint32_t
		and return. */
		#if( ipconfigINCLUDE_FULL_INET_ADDR == 1 )
		{
			ulIPAddress = FreeRTOS_inet_addr( pcHostName );
		}
		#endif /* ipconfigINCLUDE_FULL_INET_ADDR == 1 */

		/* If a DNS cache is used then check the cache before issuing another DNS
		request. */
		#if( ipconfigUSE_DNS_CACHE == 1 )
		{
			if( ulIPAddress == 0uL )
			{
				ulIPAddress = FreeRTOS_dnslookup( pcHostName );

				if( ulIPAddress != 0 )
				{
					FreeRTOS_debug_printf( ( "FreeRTOS_gethostbyname: found '%s' in cache: %lxip\n", pcHostName, ulIPAddress ) );
				}
				else
				{
					/* prvGetHostByName will be called to start a DNS lookup. */
				}
			}
		}
		#endif /* ipconfigUSE_DNS_CACHE == 1 */

		/* Generate a unique identifier. */
		if( ulIPAddress == 0uL )
		{
		uint32_t ulNumber;

			xHasRandom = xApplicationGetRandomNumber( &( ulNumber ) );
			/* DNS identifiers are 16-bit. */
			uxIdentifier = ( TickType_t ) ( ulNumber & 0xffffu );
			/* ipconfigRAND32() may not return a non-zero value. */
		}

		#if( ipconfigDNS_USE_CALLBACKS == 1 )
		{
			if( pCallback != NULL )
			{
				if( ulIPAddress == 0uL )
				{
					/* The user has provided a callback function, so do not block on recvfrom() */
					if( xHasRandom != pdFALSE )
					{
						uxReadTimeOut_ticks = 0u;
						vDNSSetCallBack( pcHostName, pvSearchID, pCallback, uxTimeout, uxIdentifier );
					}
				}
				else
				{
					/* The IP address is known, do the call-back now. */
					pCallback( pcHostName, pvSearchID, ulIPAddress );
				}
			}
		}
		#endif /* if ( ipconfigDNS_USE_CALLBACKS == 1 ) */

		if( ( ulIPAddress == 0uL ) && ( xHasRandom != pdFALSE ) )
		{
			ulIPAddress = prvGetHostByName( pcHostName, uxIdentifier, uxReadTimeOut_ticks );
		}
	}
	return ulIPAddress;
}
/*-----------------------------------------------------------*/

static uint32_t prvGetHostByName( const char *pcHostName,
								  TickType_t uxIdentifier,
								  TickType_t uxReadTimeOut_ticks )
{
struct freertos_sockaddr xAddress;
Socket_t xDNSSocket;
uint32_t ulIPAddress = 0uL;
uint8_t *pucUDPPayloadBuffer;
uint32_t ulAddressLength = sizeof( struct freertos_sockaddr );
BaseType_t xAttempt;
int32_t lBytes;
size_t uxPayloadLength, uxExpectedPayloadLength;
TickType_t uxWriteTimeOut_ticks = ipconfigDNS_SEND_BLOCK_TIME_TICKS;

#if( ipconfigUSE_LLMNR == 1 )
	BaseType_t bHasDot = pdFALSE;
#endif /* ipconfigUSE_LLMNR == 1 */

	/* If LLMNR is being used then determine if the host name includes a '.' -
	if not then LLMNR can be used as the lookup method. */
	#if( ipconfigUSE_LLMNR == 1 )
	{
	const char *pucPtr;

		for( pucPtr = pcHostName; *pucPtr; pucPtr++ )
		{
			if( *pucPtr == '.' )
			{
				bHasDot = pdTRUE;
				break;
			}
		}
	}
	#endif /* ipconfigUSE_LLMNR == 1 */

	/* Two is added at the end for the count of characters in the first
	subdomain part and the string end byte. */
	uxExpectedPayloadLength = sizeof( DNSMessage_t ) + strlen( pcHostName ) + sizeof( uint16_t ) + sizeof( uint16_t ) + 2u;

	xDNSSocket = prvCreateDNSSocket();

	if( xDNSSocket != NULL )
	{
		FreeRTOS_setsockopt( xDNSSocket, 0, FREERTOS_SO_SNDTIMEO, ( void * ) &uxWriteTimeOut_ticks, sizeof( TickType_t ) );
		FreeRTOS_setsockopt( xDNSSocket, 0, FREERTOS_SO_RCVTIMEO, ( void * ) &uxReadTimeOut_ticks,  sizeof( TickType_t ) );

		for( xAttempt = 0; xAttempt < ipconfigDNS_REQUEST_ATTEMPTS; xAttempt++ )
		{
			/* Get a buffer.  This uses a maximum delay, but the delay will be
			capped to ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS so the return value
			still needs to be tested. */
			pucUDPPayloadBuffer = ( uint8_t * ) FreeRTOS_GetUDPPayloadBuffer( uxExpectedPayloadLength, portMAX_DELAY );

			if( pucUDPPayloadBuffer != NULL )
			{
				/* Create the message in the obtained buffer. */
				uxPayloadLength = prvCreateDNSMessage( pucUDPPayloadBuffer, pcHostName, uxIdentifier );

				iptraceSENDING_DNS_REQUEST();

				/* Obtain the DNS server address. */
				FreeRTOS_GetAddressConfiguration( NULL, NULL, NULL, &ulIPAddress );

				/* Send the DNS message. */
#if( ipconfigUSE_LLMNR == 1 )
				if( bHasDot == pdFALSE )
				{
					/* Use LLMNR addressing. */
					( ( DNSMessage_t * ) pucUDPPayloadBuffer )->usFlags = 0;
					xAddress.sin_addr = ipLLMNR_IP_ADDR; /* Is in network byte order. */
					xAddress.sin_port = FreeRTOS_ntohs( ipLLMNR_PORT );
				}
				else
#endif
				{
					/* Use DNS server. */
					xAddress.sin_addr = ulIPAddress;
					xAddress.sin_port = dnsDNS_PORT;
				}

				ulIPAddress = 0uL;

				if( FreeRTOS_sendto( xDNSSocket, pucUDPPayloadBuffer, uxPayloadLength, FREERTOS_ZERO_COPY, &xAddress, sizeof( xAddress ) ) != 0 )
				{
					/* Wait for the reply. */
					lBytes = FreeRTOS_recvfrom( xDNSSocket, &pucUDPPayloadBuffer, 0, FREERTOS_ZERO_COPY, &xAddress, &ulAddressLength );

					if( lBytes > 0 )
					{
					BaseType_t xExpected;
					DNSMessage_t *pxDNSMessageHeader = ( DNSMessage_t * ) pucUDPPayloadBuffer;

						/* See if the identifiers match. */
						if( uxIdentifier == ( TickType_t ) pxDNSMessageHeader->usIdentifier )
						{
							xExpected = pdTRUE;
						}
						else
						{
							/* The reply was not expected. */
							xExpected = pdFALSE;
						}

						/* The reply was received.  Process it. */
					#if( ipconfigDNS_USE_CALLBACKS == 0 )
						/* It is useless to analyse the unexpected reply
						unless asynchronous look-ups are enabled. */
						if( xExpected != pdFALSE )
					#endif /* ipconfigDNS_USE_CALLBACKS == 0 */
						{
							ulIPAddress = prvParseDNSReply( pucUDPPayloadBuffer, ( size_t ) lBytes, xExpected );
						}

						/* Finished with the buffer.  The zero copy interface
						is being used, so the buffer must be freed by the
						task. */
						FreeRTOS_ReleaseUDPPayloadBuffer( ( void * ) pucUDPPayloadBuffer );

						if( ulIPAddress != 0uL )
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

			if( uxReadTimeOut_ticks == 0u )
			{
				/* This DNS lookup is asynchronous, using a call-back:
				send the request only once. */
				break;
			}
		}

		/* Finished with the socket. */
		FreeRTOS_closesocket( xDNSSocket );
	}

	return ulIPAddress;
}
/*-----------------------------------------------------------*/

static size_t prvCreateDNSMessage( uint8_t *pucUDPPayloadBuffer,
								   const char *pcHostName,
								   TickType_t uxIdentifier )
{
DNSMessage_t *pxDNSMessageHeader;
uint8_t *pucStart, *pucByte;
DNSTail_t *pxTail;
static const DNSMessage_t xDefaultPartDNSHeader =
{
	0,                 /* The identifier will be overwritten. */
	dnsOUTGOING_FLAGS, /* Flags set for standard query. */
	dnsONE_QUESTION,   /* One question is being asked. */
	0,                 /* No replies are included. */
	0,                 /* No authorities. */
	0                  /* No additional authorities. */
};

	/* Copy in the const part of the header. */
	memcpy( ( void * ) pucUDPPayloadBuffer, ( void * ) &xDefaultPartDNSHeader, sizeof( xDefaultPartDNSHeader ) );

	/* Write in a unique identifier. */
	pxDNSMessageHeader = ( DNSMessage_t * ) pucUDPPayloadBuffer;
	pxDNSMessageHeader->usIdentifier = ( uint16_t ) uxIdentifier;

	/* Create the resource record at the end of the header.  First
	find the end of the header. */
	pucStart = pucUDPPayloadBuffer + sizeof( xDefaultPartDNSHeader );

	/* Leave a gap for the first length bytes. */
	pucByte = pucStart + 1;

	/* Copy in the host name. */
	strcpy( ( char * ) pucByte, pcHostName );

	/* Mark the end of the string. */
	pucByte += strlen( pcHostName );
	*pucByte = 0x00u;

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

	pxTail = ( DNSTail_t * ) ( pucByte + 1 );

	vSetField16( pxTail, DNSTail_t, usType, dnsTYPE_A_HOST ); /* Type A: host */
	vSetField16( pxTail, DNSTail_t, usClass, dnsCLASS_IN );   /* 1: Class IN */

	/* Return the total size of the generated message, which is the space from
	the last written byte to the beginning of the buffer. */
	return ( ( uint32_t ) pucByte - ( uint32_t ) pucUDPPayloadBuffer + 1 ) + sizeof( *pxTail );
}
/*-----------------------------------------------------------*/

#if( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )

	static uint8_t * prvReadNameField( uint8_t *pucByte,
									   size_t uxSourceLen,
									   char *pcName,
									   size_t uxDestLen )
	{
	size_t uxNameLen = 0;
	BaseType_t xCount;

		if( 0 == uxSourceLen )
		{
			return NULL;
		}

		/* Determine if the name is the fully coded name, or an offset to the name
		elsewhere in the message. */
		if( ( *pucByte & dnsNAME_IS_OFFSET ) == dnsNAME_IS_OFFSET )
		{
			/* Jump over the two byte offset. */
			if( uxSourceLen > sizeof( uint16_t ) )
			{
				pucByte += sizeof( uint16_t );
			}
			else
			{
				pucByte = NULL;
			}
		}
		else
		{
			/* pucByte points to the full name. Walk over the string. */
			while( ( NULL != pucByte ) && ( *pucByte != 0x00u ) && ( uxSourceLen > 1u ) )
			{
				/* If this is not the first time through the loop, then add a
				separator in the output. */
				if( ( uxNameLen > 0 ) && ( uxNameLen < ( uxDestLen - 1u ) ) )
				{
					pcName[ uxNameLen++ ] = '.';
				}

				/* Process the first/next sub-string. */
				for( xCount = *( pucByte++ ), uxSourceLen--;
					 xCount-- && uxSourceLen > 1u;
					 pucByte++, uxSourceLen-- )
				{
					if( uxNameLen < uxDestLen - 1u )
					{
						pcName[ uxNameLen++ ] = *( ( char * ) pucByte );
					}
					else
					{
						/* DNS name is too big for the provided buffer. */
						pucByte = NULL;
						break;
					}
				}
			}

			/* Confirm that a fully formed name was found. */
			if( NULL != pucByte )
			{
				if( 0x00 == *pucByte )
				{
					pucByte++;
					uxSourceLen--;
					pcName[ uxNameLen++ ] = '\0';
				}
				else
				{
					pucByte = NULL;
				}
			}
		}

		return pucByte;
	}
#endif /* ipconfigUSE_DNS_CACHE || ipconfigDNS_USE_CALLBACKS */
/*-----------------------------------------------------------*/

static uint8_t * prvSkipNameField( uint8_t *pucByte,
								   size_t uxSourceLen )
{
size_t uxChunkLength;

	if( 0u == uxSourceLen )
	{
		return NULL;
	}

	/* Determine if the name is the fully coded name, or an offset to the name
	elsewhere in the message. */
	if( ( *pucByte & dnsNAME_IS_OFFSET ) == dnsNAME_IS_OFFSET )
	{
		/* Jump over the two byte offset. */
		if( uxSourceLen > sizeof( uint16_t ) )
		{
			pucByte += sizeof( uint16_t );
		}
		else
		{
			pucByte = NULL;
		}
	}
	else
	{
		/* pucByte points to the full name. Walk over the string. */
		while( ( *pucByte != 0x00u ) && ( uxSourceLen > 1u ) )
		{
			uxChunkLength = *pucByte + 1u;

			if( uxSourceLen > uxChunkLength )
			{
				uxSourceLen -= uxChunkLength;
				pucByte += uxChunkLength;
			}
			else
			{
				pucByte = NULL;
				break;
			}
		}

		/* Confirm that a fully formed name was found. */
		if( NULL != pucByte )
		{
			if( 0x00u == *pucByte )
			{
				pucByte++;
			}
			else
			{
				pucByte = NULL;
			}
		}
	}

	return pucByte;
}
/*-----------------------------------------------------------*/

/* The function below will only be called :
when ipconfigDNS_USE_CALLBACKS == 1
when ipconfigUSE_LLMNR == 1
for testing purposes, by the module iot_test_freertos_tcp.c
*/
uint32_t ulDNSHandlePacket( NetworkBufferDescriptor_t *pxNetworkBuffer )
{
DNSMessage_t *pxDNSMessageHeader;
size_t uxPayloadSize;

    /* Only proceed if the payload length indicated in the header
    appears to be valid. */
    if( pxNetworkBuffer->xDataLength >= sizeof( UDPPacket_t ) )
    {
        uxPayloadSize = pxNetworkBuffer->xDataLength - sizeof( UDPPacket_t );

        if( uxPayloadSize >= sizeof( DNSMessage_t ) )
        {
            pxDNSMessageHeader =
                ( DNSMessage_t * ) ( pxNetworkBuffer->pucEthernetBuffer + sizeof( UDPPacket_t ) );

            /* The parameter pdFALSE indicates that the reply was not expected. */
            prvParseDNSReply( ( uint8_t * ) pxDNSMessageHeader,
                uxPayloadSize,
                pdFALSE );
        }
    }

	/* The packet was not consumed. */
	return pdFAIL;
}
/*-----------------------------------------------------------*/

#if( ipconfigUSE_NBNS == 1 )

	uint32_t ulNBNSHandlePacket( NetworkBufferDescriptor_t * pxNetworkBuffer )
	{
	UDPPacket_t *pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
	uint8_t *pucUDPPayloadBuffer = pxNetworkBuffer->pucEthernetBuffer + sizeof( UDPPacket_t );
	size_t uxPayloadSize = pxNetworkBuffer->xDataLength - sizeof( UDPPacket_t );

		/* The network buffer data length has already been set to the
		length of the UDP payload. */
		prvTreatNBNS( pucUDPPayloadBuffer,
					  uxPayloadSize,
					  pxUDPPacket->xIPHeader.ulSourceIPAddress );

		/* The packet was not consumed. */
		return pdFAIL;
	}

#endif /* ipconfigUSE_NBNS */
/*-----------------------------------------------------------*/

static uint32_t prvParseDNSReply( uint8_t *pucUDPPayloadBuffer,
								  size_t uxBufferLength,
								  BaseType_t xExpected )
{
DNSMessage_t *pxDNSMessageHeader;
DNSAnswerRecord_t *pxDNSAnswerRecord;
uint32_t ulIPAddress = 0uL;
#if( ipconfigUSE_LLMNR == 1 )
	char *pcRequestedName = NULL;
#endif
uint8_t *pucByte;
size_t uxSourceBytesRemaining;
uint16_t x, usDataLength, usQuestions;
BaseType_t xDoStore = xExpected;
#if( ipconfigUSE_LLMNR == 1 )
	uint16_t usType = 0, usClass = 0;
#endif
#if( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )
	char pcName[ ipconfigDNS_CACHE_NAME_LENGTH ] = "";
#endif

	/* Ensure that the buffer is of at least minimal DNS message length. */
	if( uxBufferLength < sizeof( DNSMessage_t ) )
	{
		return dnsPARSE_ERROR;
	}

	uxSourceBytesRemaining = uxBufferLength;

	/* Parse the DNS message header. */
	pxDNSMessageHeader = ( DNSMessage_t * ) pucUDPPayloadBuffer;

	/* Introduce a do {} while (0) to allow the use of breaks. */
	do
	{
		/* Start at the first byte after the header. */
		pucByte = pucUDPPayloadBuffer + sizeof( DNSMessage_t );
		uxSourceBytesRemaining -= sizeof( DNSMessage_t );

		/* Skip any question records. */
		usQuestions = FreeRTOS_ntohs( pxDNSMessageHeader->usQuestions );

		for( x = 0; x < usQuestions; x++ )
		{
			#if( ipconfigUSE_LLMNR == 1 )
			{
				if( x == 0 )
				{
					pcRequestedName = ( char * ) pucByte;
				}
			}
			#endif

#if( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )
			if( x == 0 )
			{
				pucByte = prvReadNameField( pucByte,
											uxSourceBytesRemaining,
											pcName,
											sizeof( pcName ) );

				/* Check for a malformed response. */
				if( NULL == pucByte )
				{
					return dnsPARSE_ERROR;
				}

				uxSourceBytesRemaining = ( pucUDPPayloadBuffer + uxBufferLength ) - pucByte;
			}
			else
#endif /* ipconfigUSE_DNS_CACHE || ipconfigDNS_USE_CALLBACKS */
			{
				/* Skip the variable length pcName field. */
				pucByte = prvSkipNameField( pucByte,
											uxSourceBytesRemaining );

				/* Check for a malformed response. */
				if( NULL == pucByte )
				{
					return dnsPARSE_ERROR;
				}

				uxSourceBytesRemaining = ( size_t )
					( pucUDPPayloadBuffer + uxBufferLength - pucByte );
			}

			/* Check the remaining buffer size. */
			if( uxSourceBytesRemaining >= sizeof( uint32_t ) )
			{
				#if( ipconfigUSE_LLMNR == 1 )
				{
					/* usChar2u16 returns value in host endianness. */
					usType = usChar2u16( pucByte );
					usClass = usChar2u16( pucByte + 2 );
				}
				#endif /* ipconfigUSE_LLMNR */

				/* Skip the type and class fields. */
				pucByte += sizeof( uint32_t );
				uxSourceBytesRemaining -= sizeof( uint32_t );
			}
			else
			{
				/* Malformed response. */
				return dnsPARSE_ERROR;
			}
		}

		/* Search through the answer records. */
		pxDNSMessageHeader->usAnswers = FreeRTOS_ntohs( pxDNSMessageHeader->usAnswers );

		if( ( pxDNSMessageHeader->usFlags & dnsRX_FLAGS_MASK ) == dnsEXPECTED_RX_FLAGS )
		{
			for( x = 0; x < pxDNSMessageHeader->usAnswers; x++ )
			{
				pucByte = prvSkipNameField( pucByte,
											uxSourceBytesRemaining );

				/* Check for a malformed response. */
				if( NULL == pucByte )
				{
					return dnsPARSE_ERROR;
				}

				uxSourceBytesRemaining = ( size_t )
					( pucUDPPayloadBuffer + uxBufferLength - pucByte );

				/* Is there enough data for an IPv4 A record answer and, if so,
				is this an A record? */
				if( ( uxSourceBytesRemaining >= ( sizeof( DNSAnswerRecord_t ) + sizeof( uint32_t ) ) ) &&
					( usChar2u16( pucByte ) == dnsTYPE_A_HOST ) )
				{
					/* This is the required record type and is of sufficient size. */
					pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) pucByte;

					/* Sanity check the data length of an IPv4 answer. */
					if( FreeRTOS_ntohs( pxDNSAnswerRecord->usDataLength ) == sizeof( uint32_t ) )
					{
						/* Copy the IP address out of the record. */
						memcpy( &ulIPAddress,
								pucByte + sizeof( DNSAnswerRecord_t ),
								sizeof( uint32_t ) );

						#if( ipconfigDNS_USE_CALLBACKS == 1 )
						{
							/* See if any asynchronous call was made to FreeRTOS_gethostbyname_a() */
							if( xDNSDoCallback( ( TickType_t ) pxDNSMessageHeader->usIdentifier, pcName, ulIPAddress ) != pdFALSE )
							{
								/* This device has requested this DNS look-up.
								The result may be stored in the DNS cache. */
								xDoStore = pdTRUE;
							}
						}
						#endif /* ipconfigDNS_USE_CALLBACKS == 1 */
						#if( ipconfigUSE_DNS_CACHE == 1 )
						{
							/* The reply will only be stored in the DNS cache when the
							request was issued by this device. */
							if( xDoStore != pdFALSE )
							{
								prvProcessDNSCache( pcName, &ulIPAddress, pxDNSAnswerRecord->ulTTL, pdFALSE );
							}

							/* Show what has happened. */
							FreeRTOS_printf( ( "DNS[0x%04X]: The answer to '%s' (%xip) will%s be stored\n",
											   ( unsigned ) pxDNSMessageHeader->usIdentifier,
											   pcName,
											   ( unsigned ) FreeRTOS_ntohl( ulIPAddress ),
											   ( xDoStore != 0 ) ? "" : " NOT" ) );
						}
						#endif /* ipconfigUSE_DNS_CACHE */
					}

					pucByte += sizeof( DNSAnswerRecord_t ) + sizeof( uint32_t );
					uxSourceBytesRemaining -= ( sizeof( DNSAnswerRecord_t ) + sizeof( uint32_t ) );
					break;
				}
				else if( uxSourceBytesRemaining >= sizeof( DNSAnswerRecord_t ) )
				{
					/* It's not an A record, so skip it. Get the header location
					and then jump over the header. */
					pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) pucByte;
					pucByte += sizeof( DNSAnswerRecord_t );
					uxSourceBytesRemaining -= sizeof( DNSAnswerRecord_t );

					/* Determine the length of the answer data from the header. */
					usDataLength = FreeRTOS_ntohs( pxDNSAnswerRecord->usDataLength );

					/* Jump over the answer. */
					if( uxSourceBytesRemaining >= usDataLength )
					{
						pucByte += usDataLength;
						uxSourceBytesRemaining -= usDataLength;
					}
					else
					{
						/* Malformed response. */
						return dnsPARSE_ERROR;
					}
				}
			}
		}

#if( ipconfigUSE_LLMNR == 1 )
		else if( usQuestions && ( usType == dnsTYPE_A_HOST ) && ( usClass == dnsCLASS_IN ) )
		{
			/* If this is not a reply to our DNS request, it might an LLMNR
			request. */
			if( xApplicationDNSQueryHook( ( pcRequestedName + 1 ) ) )
			{
			int16_t usLength;
			NetworkBufferDescriptor_t *pxNewBuffer = NULL;
			NetworkBufferDescriptor_t *pxNetworkBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( pucUDPPayloadBuffer );
			LLMNRAnswer_t *pxAnswer;

				if( ( xBufferAllocFixedSize == pdFALSE ) && ( pxNetworkBuffer != NULL ) )
				{
				BaseType_t xDataLength = uxBufferLength + sizeof( UDPHeader_t ) + sizeof( EthernetHeader_t ) + sizeof( IPHeader_t );

					/* Set the size of the outgoing packet. */
					pxNetworkBuffer->xDataLength = xDataLength;
					pxNewBuffer = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, xDataLength + sizeof( LLMNRAnswer_t ) );

					if( pxNewBuffer != NULL )
					{
					BaseType_t xOffset1, xOffset2;

						xOffset1 = ( BaseType_t ) ( pucByte - pucUDPPayloadBuffer );
						xOffset2 = ( BaseType_t ) ( ( ( uint8_t * ) pcRequestedName ) - pucUDPPayloadBuffer );

						pxNetworkBuffer = pxNewBuffer;
						pucUDPPayloadBuffer = pxNetworkBuffer->pucEthernetBuffer + ipUDP_PAYLOAD_OFFSET_IPv4;

						pucByte = pucUDPPayloadBuffer + xOffset1;
						pcRequestedName = ( char * ) ( pucUDPPayloadBuffer + xOffset2 );
						pxDNSMessageHeader = ( DNSMessage_t * ) pucUDPPayloadBuffer;
					}
					else
					{
						/* Just to indicate that the message may not be answered. */
						pxNetworkBuffer = NULL;
					}
				}

				if( pxNetworkBuffer != NULL )
				{
					pxAnswer = ( LLMNRAnswer_t * ) pucByte;

					/* We leave 'usIdentifier' and 'usQuestions' untouched */
					vSetField16( pxDNSMessageHeader, DNSMessage_t, usFlags, dnsLLMNR_FLAGS_IS_REPONSE ); /* Set the response flag */
					vSetField16( pxDNSMessageHeader, DNSMessage_t, usAnswers, 1 );                       /* Provide a single answer */
					vSetField16( pxDNSMessageHeader, DNSMessage_t, usAuthorityRRs, 0 );                  /* No authority */
					vSetField16( pxDNSMessageHeader, DNSMessage_t, usAdditionalRRs, 0 );                 /* No additional info */

					pxAnswer->ucNameCode = dnsNAME_IS_OFFSET;
					pxAnswer->ucNameOffset = ( uint8_t ) ( pcRequestedName - ( char * ) pucUDPPayloadBuffer );

					vSetField16( pxAnswer, LLMNRAnswer_t, usType, dnsTYPE_A_HOST ); /* Type A: host */
					vSetField16( pxAnswer, LLMNRAnswer_t, usClass, dnsCLASS_IN );   /* 1: Class IN */
					vSetField32( pxAnswer, LLMNRAnswer_t, ulTTL, dnsLLMNR_TTL_VALUE );
					vSetField16( pxAnswer, LLMNRAnswer_t, usDataLength, 4 );
					vSetField32( pxAnswer, LLMNRAnswer_t, ulIPAddress, FreeRTOS_ntohl( *ipLOCAL_IP_ADDRESS_POINTER ) );

					usLength = ( int16_t ) ( sizeof( *pxAnswer ) + ( size_t ) ( pucByte - pucUDPPayloadBuffer ) );

					prvReplyDNSMessage( pxNetworkBuffer, usLength );

					if( pxNewBuffer != NULL )
					{
						vReleaseNetworkBufferAndDescriptor( pxNewBuffer );
					}
				}
			}
		}
#endif /* ipconfigUSE_LLMNR == 1 */
	} while( 0 );

	if( xExpected == pdFALSE )
	{
		/* Do not return a valid IP-address in case the reply was not expected. */
		ulIPAddress = 0uL;
	}

	return ulIPAddress;
}
/*-----------------------------------------------------------*/

#if( ipconfigUSE_NBNS == 1 )

	static void prvTreatNBNS( uint8_t *pucUDPPayloadBuffer,
							  size_t uxBufferLength,
							  uint32_t ulIPAddress )
	{
	uint16_t usFlags, usType, usClass;
	uint8_t *pucSource, *pucTarget;
	uint8_t ucByte;
	uint8_t ucNBNSName[ 17 ];

		/* Check for minimum buffer size. */
		if( uxBufferLength < sizeof( NBNSRequest_t ) )
		{
			return;
		}

		/* Read the request flags in host endianness. */
		usFlags = usChar2u16( pucUDPPayloadBuffer + offsetof( NBNSRequest_t, usFlags ) );

		if( ( usFlags & dnsNBNS_FLAGS_OPCODE_MASK ) == dnsNBNS_FLAGS_OPCODE_QUERY )
		{
			usType  = usChar2u16( pucUDPPayloadBuffer + offsetof( NBNSRequest_t, usType ) );
			usClass = usChar2u16( pucUDPPayloadBuffer + offsetof( NBNSRequest_t, usClass ) );

			/* Not used for now */
			( void ) usClass;

			/* For NBNS a name is 16 bytes long, written with capitals only.
			Make sure that the copy is terminated with a zero. */
			pucTarget = ucNBNSName + sizeof( ucNBNSName ) - 2;
			pucTarget[ 1 ] = '\0';

			/* Start with decoding the last 2 bytes. */
			pucSource = pucUDPPayloadBuffer + ( offsetof( NBNSRequest_t, ucName ) + ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) );

			for( ;; )
			{
				ucByte = ( uint8_t ) ( ( ( pucSource[ 0 ] - 0x41 ) << 4 ) | ( pucSource[ 1 ] - 0x41 ) );

				/* Make sure there are no trailing spaces in the name. */
				if( ( ucByte == ' ' ) && ( pucTarget[ 1 ] == '\0' ) )
				{
					ucByte = '\0';
				}

				*pucTarget = ucByte;

				if( pucTarget == ucNBNSName )
				{
					break;
				}

				pucTarget -= 1;
				pucSource -= 2;
			}

			#if( ipconfigUSE_DNS_CACHE == 1 )
			{
				if( ( usFlags & dnsNBNS_FLAGS_RESPONSE ) != 0 )
				{
					/* If this is a response from another device,
					add the name to the DNS cache */
					prvProcessDNSCache( ( char * ) ucNBNSName, &ulIPAddress, 0, pdFALSE );
				}
			}
			#else
			{
				/* Avoid compiler warnings. */
				( void ) ulIPAddress;
			}
			#endif /* ipconfigUSE_DNS_CACHE */

			if( ( ( usFlags & dnsNBNS_FLAGS_RESPONSE ) == 0 ) &&
				( usType == dnsNBNS_TYPE_NET_BIOS ) &&
				( xApplicationDNSQueryHook( ( const char * ) ucNBNSName ) != pdFALSE ) )
			{
			uint16_t usLength;
			DNSMessage_t *pxMessage;
			NBNSAnswer_t *pxAnswer;

				/* Someone is looking for a device with ucNBNSName,
				prepare a positive reply. */
				NetworkBufferDescriptor_t *pxNetworkBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( pucUDPPayloadBuffer );

				if( ( xBufferAllocFixedSize == pdFALSE ) && ( pxNetworkBuffer != NULL ) )
				{
				NetworkBufferDescriptor_t *pxNewBuffer;

					/* The field xDataLength was set to the total length of the UDP packet,
					i.e. the payload size plus sizeof( UDPPacket_t ). */
					pxNewBuffer = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, pxNetworkBuffer->xDataLength + sizeof( NBNSAnswer_t ) );

					if( pxNewBuffer != NULL )
					{
						pucUDPPayloadBuffer = pxNewBuffer->pucEthernetBuffer + sizeof( UDPPacket_t );
						pxNetworkBuffer = pxNewBuffer;
					}
					else
					{
						/* Just prevent that a reply will be sent */
						pxNetworkBuffer = NULL;
					}
				}

				/* Should not occur: pucUDPPayloadBuffer is part of a xNetworkBufferDescriptor */
				if( pxNetworkBuffer != NULL )
				{
					pxMessage = ( DNSMessage_t * ) pucUDPPayloadBuffer;

					/* As the fields in the structures are not word-aligned, we have to
					copy the values byte-by-byte using macro's vSetField16() and vSetField32() */
					vSetField16( pxMessage, DNSMessage_t, usFlags, dnsNBNS_QUERY_RESPONSE_FLAGS ); /* 0x8500 */
					vSetField16( pxMessage, DNSMessage_t, usQuestions, 0 );
					vSetField16( pxMessage, DNSMessage_t, usAnswers, 1 );
					vSetField16( pxMessage, DNSMessage_t, usAuthorityRRs, 0 );
					vSetField16( pxMessage, DNSMessage_t, usAdditionalRRs, 0 );

					pxAnswer = ( NBNSAnswer_t * ) ( pucUDPPayloadBuffer + offsetof( NBNSRequest_t, usType ) );

					vSetField16( pxAnswer, NBNSAnswer_t, usType, usType );            /* Type */
					vSetField16( pxAnswer, NBNSAnswer_t, usClass, dnsNBNS_CLASS_IN ); /* Class */
					vSetField32( pxAnswer, NBNSAnswer_t, ulTTL, dnsNBNS_TTL_VALUE );
					vSetField16( pxAnswer, NBNSAnswer_t, usDataLength, 6 );           /* 6 bytes including the length field */
					vSetField16( pxAnswer, NBNSAnswer_t, usNbFlags, dnsNBNS_NAME_FLAGS );
					vSetField32( pxAnswer, NBNSAnswer_t, ulIPAddress, FreeRTOS_ntohl( *ipLOCAL_IP_ADDRESS_POINTER ) );

					usLength = ( uint16_t ) ( offsetof( NBNSRequest_t, usType ) + sizeof( NBNSAnswer_t ) );

					prvReplyDNSMessage( pxNetworkBuffer, usLength );
				}
			}
		}
	}

#endif /* ipconfigUSE_NBNS */
/*-----------------------------------------------------------*/

static Socket_t prvCreateDNSSocket( void )
{
Socket_t xSocket = NULL;
struct freertos_sockaddr xAddress;
BaseType_t xReturn;

	/* This must be the first time this function has been called.  Create
	the socket. */
	xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );

	/* Auto bind the port. */
	xAddress.sin_port = 0u;
	xReturn = FreeRTOS_bind( xSocket, &xAddress, sizeof( xAddress ) );

	/* Check the bind was successful, and clean up if not. */
	if( xReturn != 0 )
	{
		FreeRTOS_closesocket( xSocket );
		xSocket = NULL;
	}
	else
	{
		/* The send and receive timeouts will be set later on. */
	}

	return xSocket;
}
/*-----------------------------------------------------------*/

#if( ( ipconfigUSE_NBNS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) )

	static void prvReplyDNSMessage( NetworkBufferDescriptor_t *pxNetworkBuffer,
									BaseType_t lNetLength )
	{
	UDPPacket_t *pxUDPPacket;
	IPHeader_t *pxIPHeader;
	UDPHeader_t *pxUDPHeader;

		pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
		pxIPHeader = &pxUDPPacket->xIPHeader;
		pxUDPHeader = &pxUDPPacket->xUDPHeader;
		/* HT: started using defines like 'ipSIZE_OF_xxx' */
		pxIPHeader->usLength			   = FreeRTOS_htons( lNetLength + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER );
		/* HT:endian: should not be translated, copying from packet to packet */
		pxIPHeader->ulDestinationIPAddress = pxIPHeader->ulSourceIPAddress;
		pxIPHeader->ulSourceIPAddress	   = *ipLOCAL_IP_ADDRESS_POINTER;
		pxIPHeader->ucTimeToLive		   = ipconfigUDP_TIME_TO_LIVE;
		pxIPHeader->usIdentification	   = FreeRTOS_htons( usPacketIdentifier );
		usPacketIdentifier++;
		pxUDPHeader->usLength			   = FreeRTOS_htons( lNetLength + ipSIZE_OF_UDP_HEADER );
		vFlip_16( pxUDPPacket->xUDPHeader.usSourcePort, pxUDPPacket->xUDPHeader.usDestinationPort );

		/* Important: tell NIC driver how many bytes must be sent */
		pxNetworkBuffer->xDataLength = ( size_t ) ( lNetLength + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER + ipSIZE_OF_ETH_HEADER );

		#if( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
		{
			/* calculate the IP header checksum */
			pxIPHeader->usHeaderChecksum = 0x00;
			pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0uL, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipSIZE_OF_IPv4_HEADER );
			pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );

			/* calculate the UDP checksum for outgoing package */
			usGenerateProtocolChecksum( ( uint8_t* ) pxUDPPacket, pxNetworkBuffer->xDataLength, pdTRUE );
		}
		#endif

		/* This function will fill in the eth addresses and send the packet */
		vReturnEthernetFrame( pxNetworkBuffer, pdFALSE );
	}

#endif /* ipconfigUSE_NBNS == 1 || ipconfigUSE_LLMNR == 1 */
/*-----------------------------------------------------------*/

#if( ipconfigUSE_DNS_CACHE == 1 )

	static void prvProcessDNSCache( const char *pcName,
									uint32_t *pulIP,
									uint32_t ulTTL,
									BaseType_t xLookUp )
	{
	BaseType_t x;
	BaseType_t xFound = pdFALSE;
	uint32_t ulCurrentTimeSeconds = ( xTaskGetTickCount() / portTICK_PERIOD_MS ) / 1000;
	static BaseType_t xFreeEntry = 0;
		configASSERT(pcName);

		/* For each entry in the DNS cache table. */
		for( x = 0; x < ipconfigDNS_CACHE_ENTRIES; x++ )
		{
			if( xDNSCache[ x ].pcName[ 0 ] == 0 )
			{
				continue;
			}

			if( 0 == strcmp( xDNSCache[ x ].pcName, pcName ) )
			{
				/* Is this function called for a lookup or to add/update an IP address? */
				if( xLookUp != pdFALSE )
				{
					/* Confirm that the record is still fresh. */
					if( ulCurrentTimeSeconds < ( xDNSCache[ x ].ulTimeWhenAddedInSeconds + FreeRTOS_ntohl( xDNSCache[ x ].ulTTL ) ) )
					{
						*pulIP = xDNSCache[ x ].ulIPAddress;
					}
					else
					{
						/* Age out the old cached record. */
						xDNSCache[ x ].pcName[ 0 ] = 0;
					}
				}
				else
				{
					xDNSCache[ x ].ulIPAddress = *pulIP;
					xDNSCache[ x ].ulTTL = ulTTL;
					xDNSCache[ x ].ulTimeWhenAddedInSeconds = ulCurrentTimeSeconds;
				}

				xFound = pdTRUE;
				break;
			}
		}

		if( xFound == pdFALSE )
		{
			if( xLookUp != pdFALSE )
			{
				*pulIP = 0;
			}
			else
			{
				/* Add or update the item. */
				if( strlen( pcName ) < ipconfigDNS_CACHE_NAME_LENGTH )
				{
					strcpy( xDNSCache[ xFreeEntry ].pcName, pcName );

					xDNSCache[ xFreeEntry ].ulIPAddress = *pulIP;
					xDNSCache[ xFreeEntry ].ulTTL = ulTTL;
					xDNSCache[ xFreeEntry ].ulTimeWhenAddedInSeconds = ulCurrentTimeSeconds;

					xFreeEntry++;

					if( xFreeEntry == ipconfigDNS_CACHE_ENTRIES )
					{
						xFreeEntry = 0;
					}
				}
			}
		}

		if( ( xLookUp == 0 ) || ( *pulIP != 0 ) )
		{
			FreeRTOS_debug_printf( ( "prvProcessDNSCache: %s: '%s' @ %lxip\n", xLookUp ? "look-up" : "add", pcName, FreeRTOS_ntohl( *pulIP ) ) );
		}
	}

#endif /* ipconfigUSE_DNS_CACHE */

#endif /* ipconfigUSE_DNS != 0 */

/*-----------------------------------------------------------*/

/* Provide access to private members for testing. */
#ifdef AMAZON_FREERTOS_ENABLE_UNIT_TESTS
	#include "iot_freertos_tcp_test_access_dns_define.h"
#endif

