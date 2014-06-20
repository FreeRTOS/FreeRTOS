/*
 * FreeRTOS+UDP V1.0.3 (C) 2014 Real Time Engineers ltd.
 * All rights reserved
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
#include "semphr.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"
#include "NetworkBufferManagement.h"

/* Sanity check the UDP payload length setting is compatible with the
fragmentation setting. */
#if ipconfigCAN_FRAGMENT_OUTGOING_PACKETS == 1
	#if ( ( ipMAX_UDP_PAYLOAD_LENGTH % 8 ) != 0 )
		#error ( ipconfigNETWORK_MTU - 28 ) must be divisible by 8 when fragmentation is used
	#endif /* ipMAX_UDP_PAYLOAD_LENGTH */
#endif /* ipconfigFRAGMENT_OUTGOING_PACKETS */

/* The ItemValue of the sockets xBoundSocketListItem member holds the socket's
port number. */
#define socketSET_SOCKET_ADDRESS( pxSocket, usPort ) listSET_LIST_ITEM_VALUE( ( &( ( pxSocket )->xBoundSocketListItem ) ), ( usPort ) )
#define socketGET_SOCKET_ADDRESS( pxSocket ) listGET_LIST_ITEM_VALUE( ( &( ( pxSocket )->xBoundSocketListItem ) ) )

/* xWaitingPacketSemaphore is not created until the socket is bound, so can be
tested to see if bind() has been called. */
#define socketSOCKET_IS_BOUND( pxSocket ) ( ( BaseType_t ) pxSocket->xWaitingPacketSemaphore )

/* If FreeRTOS_sendto() is called on a socket that is not bound to a port
number then, depending on the FreeRTOSIPConfig.h settings, it might be that a
port number is automatically generated for the socket.  Automatically generated
port numbers will be between socketAUTO_PORT_ALLOCATION_START_NUMBER and
0xffff. */
#define socketAUTO_PORT_ALLOCATION_START_NUMBER ( ( uint16_t ) 0xc000 )

/* When the automatically generated port numbers overflow, the next value used
is not set back to socketAUTO_PORT_ALLOCATION_START_NUMBER because it is likely
that the first few automatically generated ports will still be in use.  Instead
it is reset back to the value defined by this constant. */
#define socketAUTO_PORT_ALLOCATION_RESET_NUMBER ( ( uint16_t ) 0xc100 )

/* The number of octets that make up an IP address. */
#define socketMAX_IP_ADDRESS_OCTETS		4
/*-----------------------------------------------------------*/

/*
 * Allocate the next port number from the private allocation range.
 */
static uint16_t prvGetPrivatePortNumber( void );

/*
 * Return the list itme from within pxList that has an item value of
 * xWantedItemValue.  If there is no such list item return NULL.
 */
xListItem * pxListFindListItemWithValue( xList *pxList, TickType_t xWantedItemValue );

/*-----------------------------------------------------------*/

typedef struct XSOCKET
{
	xSemaphoreHandle xWaitingPacketSemaphore;
	xList xWaitingPacketsList;
	xListItem xBoundSocketListItem; /* Used to reference the socket from a bound sockets list. */
	TickType_t xReceiveBlockTime;
	TickType_t xSendBlockTime;
	uint8_t ucSocketOptions;
	#if ipconfigSUPPORT_SELECT_FUNCTION == 1
		xQueueHandle xSelectQueue;
	#endif
} xFreeRTOS_Socket_t;


/* The list that contains mappings between sockets and port numbers.  Accesses
to this list must be protected by critical sections of one kind or another. */
static xList xBoundSocketsList;

/*-----------------------------------------------------------*/

xSocket_t FreeRTOS_socket( BaseType_t xDomain, BaseType_t xType, BaseType_t xProtocol )
{
xFreeRTOS_Socket_t *pxSocket;

	/* Only UDP on Ethernet is currently supported. */
	configASSERT( xDomain == FREERTOS_AF_INET );
	configASSERT( xType == FREERTOS_SOCK_DGRAM );
	configASSERT( xProtocol == FREERTOS_IPPROTO_UDP );
	configASSERT( listLIST_IS_INITIALISED( &xBoundSocketsList ) );

	/* Allocate the structure that will hold the socket information. */
	pxSocket = ( xFreeRTOS_Socket_t * ) pvPortMalloc( sizeof( xFreeRTOS_Socket_t ) );

	if( pxSocket == NULL )
	{
		pxSocket = ( xFreeRTOS_Socket_t * ) FREERTOS_INVALID_SOCKET;
		iptraceFAILED_TO_CREATE_SOCKET();
	}
	else
	{
		/* Initialise the socket's members.  The semaphore will be created if
		the socket is bound to an address, for now the pointer to the semaphore
		is just set to NULL to show it has not been created. */
		pxSocket->xWaitingPacketSemaphore = NULL;
		vListInitialise( &( pxSocket->xWaitingPacketsList ) );
		vListInitialiseItem( &( pxSocket->xBoundSocketListItem ) );
		listSET_LIST_ITEM_OWNER( &( pxSocket->xBoundSocketListItem ), ( void * ) pxSocket );
		pxSocket->xSendBlockTime = ( TickType_t ) 0;
		pxSocket->xReceiveBlockTime = portMAX_DELAY;
		pxSocket->ucSocketOptions = FREERTOS_SO_UDPCKSUM_OUT;
		#if ipconfigSUPPORT_SELECT_FUNCTION == 1
			pxSocket->xSelectQueue = NULL;
		#endif
	}

	/* Remove compiler warnings in the case the configASSERT() is not defined. */
	( void ) xDomain;
	( void ) xType;
	( void ) xProtocol;

	return ( xSocket_t ) pxSocket;
}
/*-----------------------------------------------------------*/

#if ipconfigSUPPORT_SELECT_FUNCTION == 1

	xSocketSet_t FreeRTOS_CreateSocketSet( UBaseType_t uxEventQueueLength )
	{
	xQueueHandle xSelectQueue;

		/* Create the queue into which the address of sockets that are
		available to read are posted. */
		xSelectQueue = xQueueCreate( uxEventQueueLength, sizeof( xSocket_t ) );

		return ( xSocketSet_t ) xSelectQueue;
	}

#endif /* ipconfigSUPPORT_SELECT_FUNCTION */
/*-----------------------------------------------------------*/

#if ipconfigSUPPORT_SELECT_FUNCTION == 1

	BaseType_t FreeRTOS_FD_SET( xSocket_t xSocket, xSocketSet_t xSocketSet )
	{
	xFreeRTOS_Socket_t *pxSocket = ( xFreeRTOS_Socket_t * ) xSocket;
	BaseType_t xReturn = pdFALSE;
	UBaseType_t uxMessagesWaiting;

		configASSERT( xSocket );

		/* Is the socket already a member of a select group? */
		if( pxSocket->xSelectQueue == NULL )
		{
			taskENTER_CRITICAL();
			{
				/* Are there packets queued on the socket already? */
				uxMessagesWaiting = uxQueueMessagesWaiting( pxSocket->xWaitingPacketSemaphore );

				/* Are there enough notification spaces in the select queue for the
				number of packets already queued on the socket? */
				if( uxQueueSpacesAvailable( ( xQueueHandle ) xSocketSet ) >= uxMessagesWaiting )
				{
					/* Store a pointer to the select group in the socket for
					future reference. */
					pxSocket->xSelectQueue = ( xQueueHandle ) xSocketSet;

					while( uxMessagesWaiting > 0 )
					{
						/* Add notifications of the number of packets that are
						already queued on the socket to the select queue. */
						xQueueSendFromISR( pxSocket->xSelectQueue, &pxSocket, NULL );
						uxMessagesWaiting--;
					}

					xReturn = pdPASS;
				}
			}
			taskEXIT_CRITICAL();
		}

		return xReturn;
	}

#endif /* ipconfigSUPPORT_SELECT_FUNCTION */
/*-----------------------------------------------------------*/

#if ipconfigSUPPORT_SELECT_FUNCTION == 1

	BaseType_t FreeRTOS_FD_CLR( xSocket_t xSocket, xSocketSet_t xSocketSet )
	{
	xFreeRTOS_Socket_t *pxSocket = ( xFreeRTOS_Socket_t * ) xSocket;
	BaseType_t xReturn;

		/* Is the socket a member of the select group? */
		if( pxSocket->xSelectQueue == ( xQueueHandle ) xSocketSet )
		{
			/* The socket is no longer a member of the select group. */
			pxSocket->xSelectQueue = NULL;
			xReturn = pdPASS;
		}
		else
		{
			xReturn = pdFAIL;
		}

		return xReturn;
	}

#endif /* ipconfigSUPPORT_SELECT_FUNCTION */
/*-----------------------------------------------------------*/

#if ipconfigSUPPORT_SELECT_FUNCTION == 1

	xSocket_t FreeRTOS_select( xSocketSet_t xSocketSet, TickType_t xBlockTimeTicks )
	{
	xFreeRTOS_Socket_t *pxSocket;

		/* Wait for a socket to be ready to read. */
		if( xQueueReceive( ( xQueueHandle ) xSocketSet, &pxSocket, xBlockTimeTicks ) != pdPASS )
		{
			pxSocket = NULL;
		}

		return ( xSocket_t ) pxSocket;
	}

#endif /* ipconfigSUPPORT_SELECT_FUNCTION */
/*-----------------------------------------------------------*/

int32_t FreeRTOS_recvfrom( xSocket_t xSocket, void *pvBuffer, size_t xBufferLength, uint32_t ulFlags, struct freertos_sockaddr *pxSourceAddress, socklen_t *pxSourceAddressLength )
{
xNetworkBufferDescriptor_t *pxNetworkBuffer;
int32_t lReturn;
xFreeRTOS_Socket_t *pxSocket;

	pxSocket = ( xFreeRTOS_Socket_t * ) xSocket;

	/* The function prototype is designed to maintain the expected Berkeley
	sockets standard, but this implementation does not use all the parameters. */
	( void ) pxSourceAddressLength;

	if( socketSOCKET_IS_BOUND( pxSocket ) != pdFALSE )
	{
		/* The semaphore is given when received data is queued on the socket. */
		if( xSemaphoreTake( pxSocket->xWaitingPacketSemaphore, pxSocket->xReceiveBlockTime ) == pdPASS )
		{
			taskENTER_CRITICAL();
			{
				configASSERT( ( listCURRENT_LIST_LENGTH( &( pxSocket->xWaitingPacketsList ) ) > 0U ) );

				/* The owner of the list item is the network buffer. */
				pxNetworkBuffer = ( xNetworkBufferDescriptor_t * ) listGET_OWNER_OF_HEAD_ENTRY( &( pxSocket->xWaitingPacketsList ) );

				/* Remove the network buffer from the list of buffers waiting to
				be processed by the socket. */
				uxListRemove( &( pxNetworkBuffer->xBufferListItem ) );
			}
			taskEXIT_CRITICAL();

			if( ( ulFlags & FREERTOS_ZERO_COPY ) == 0 )
			{
				/* The zero copy flag is not set.  Truncate the length if it
				won't fit in the provided buffer. */
				if( pxNetworkBuffer->xDataLength > xBufferLength )
				{
					iptraceRECVFROM_DISCARDING_BYTES( ( xBufferLength - pxNetworkBuffer->xDataLength ) );
					pxNetworkBuffer->xDataLength = xBufferLength;
				}

				/* Copy the received data into the provided buffer, then
				release the network buffer. */
				memcpy( pvBuffer, ( void * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipUDP_PAYLOAD_OFFSET ] ), pxNetworkBuffer->xDataLength );
				vNetworkBufferRelease( pxNetworkBuffer );
			}
			else
			{
				/* The zero copy flag was set.  pvBuffer is not a buffer into
				which the received data can be copied, but a pointer that must
				be set to point to the buffer in which the received data has
				already been placed. */
				*( ( void** ) pvBuffer ) = ( void * ) ( &( pxNetworkBuffer->pucEthernetBuffer[ ipUDP_PAYLOAD_OFFSET ] ) );
			}

			/* The returned value is the data length, which may have been
			capped to the receive buffer size. */
			lReturn = ( int32_t ) pxNetworkBuffer->xDataLength;

			if( pxSourceAddress != NULL )
			{
				pxSourceAddress->sin_port = pxNetworkBuffer->usPort;
				pxSourceAddress->sin_addr = pxNetworkBuffer->ulIPAddress;
			}
		}
		else
		{
			lReturn = FREERTOS_EWOULDBLOCK;
			iptraceRECVFROM_TIMEOUT();
		}
	}
	else
	{
		lReturn = FREERTOS_EINVAL;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

#if ipconfigCAN_FRAGMENT_OUTGOING_PACKETS == 1

	int32_t FreeRTOS_sendto( xSocket_t xSocket, const void *pvBuffer, size_t xTotalDataLength, uint32_t ulFlags, const struct freertos_sockaddr *pxDestinationAddress, socklen_t xDestinationAddressLength )
	{
	xNetworkBufferDescriptor_t *pxNetworkBuffer;
	xIPFragmentParameters_t *pxFragmentParameters;
	size_t xBytesToSend, xBytesRemaining;
	xIPStackEvent_t xStackTxEvent = { eStackTxEvent, NULL };
	extern xQueueHandle xNetworkEventQueue;
	uint8_t *pucBuffer;
	xTimeOutType xTimeOut;
	TickType_t xTicksToWait;
	uint16_t usFragmentOffset;
	xFreeRTOS_Socket_t *pxSocket;

		pxSocket = ( xFreeRTOS_Socket_t * ) xSocket;

		/* The function prototype is designed to maintain the expected Berkeley
		sockets standard, but this implementation does not use all the
		parameters. */
		( void ) xDestinationAddressLength;
		configASSERT( xNetworkEventQueue );
		configASSERT( pvBuffer );

		xBytesRemaining = xTotalDataLength;

		if( socketSOCKET_IS_BOUND( pxSocket ) == pdFALSE )
		{
			/* If the socket is not already bound to an address, bind it now.
			Passing NULL as the address parameter tells FreeRTOS_bind() to select
			the address to bind to. */
			FreeRTOS_bind( xSocket, NULL, 0 );
		}

		if( socketSOCKET_IS_BOUND( pxSocket ) != pdFALSE )
		{
			/* pucBuffer will be reset if this send turns out to be a zero copy
			send because in that case pvBuffer is actually a pointer to an
			xUserData_t structure, not the UDP payload. */
			pucBuffer = ( uint8_t * ) pvBuffer;
			vTaskSetTimeOutState( &xTimeOut );
			xTicksToWait = pxSocket->xSendBlockTime;

			/* The data being transmitted will be sent in
			ipMAX_UDP_PAYLOAD_LENGTH chunks if xDataLength is greater than the
			network buffer payload size.  Loop until all the data is sent. */
			while( xBytesRemaining > 0 )
			{
				if( xBytesRemaining > ipMAX_UDP_PAYLOAD_LENGTH )
				{
					/* Cap the amount being sent in this packet to the maximum
					UDP payload size.  This will be a multiple of 8 already,
					removing the need to check in the code. */
					xBytesToSend = ipMAX_UDP_PAYLOAD_LENGTH;
				}
				else
				{
					/* Send all remaining bytes - which may well be the total
					number of bytes if the packet was not chopped up. */
					xBytesToSend = xBytesRemaining;
				}

				/* If the zero copy flag is set, then the data is already in a
				network buffer.  Otherwise, get a new network buffer. */
				if( ( ulFlags & FREERTOS_ZERO_COPY ) == 0 )
				{
					if( xTaskCheckForTimeOut( &xTimeOut, &xTicksToWait ) == pdTRUE )
					{
						xTicksToWait = 0;
					}

					pxNetworkBuffer = pxNetworkBufferGet( xBytesToSend + sizeof( xUDPPacket_t ), xTicksToWait );
				}
				else
				{
					if( xTotalDataLength > ipMAX_UDP_PAYLOAD_LENGTH )
					{
						/* The packet needs fragmenting, but zero copy buffers
						cannot be fragmented. */
						pxNetworkBuffer = NULL;
					}
					else
					{
						/* When zero copy is used, pvBuffer is a pointer to the
						payload of a buffer that has already been obtained from the
						stack.  Obtain the network buffer pointer from the buffer. */
						pucBuffer = ( uint8_t * ) pvBuffer;
						pucBuffer -= ( ipBUFFER_PADDING + sizeof( xUDPPacket_t ) );
						pxNetworkBuffer = * ( ( xNetworkBufferDescriptor_t ** ) pucBuffer );
					}
				}

				if( pxNetworkBuffer != NULL )
				{
					/* Use the part of the network buffer that will be completed
					by the IP layer as temporary storage to pass extra
					information required by the IP layer. */
					pxFragmentParameters = ( xIPFragmentParameters_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipFRAGMENTATION_PARAMETERS_OFFSET ] );
					pxFragmentParameters->ucSocketOptions = pxSocket->ucSocketOptions;

					if( xBytesRemaining > ipMAX_UDP_PAYLOAD_LENGTH )
					{
						/* The packet is being chopped up, and more data will
						follow. */
						pxFragmentParameters->ucSocketOptions = ( pxSocket->ucSocketOptions | FREERTOS_NOT_LAST_IN_FRAGMENTED_PACKET );
					}

					if( xTotalDataLength > ipMAX_UDP_PAYLOAD_LENGTH )
					{
						/* Let the IP layer know this packet has been chopped up,
						and supply the IP layer with any addition information it
						needs to make sense of it. */
						pxFragmentParameters->ucSocketOptions |= FREERTOS_FRAGMENTED_PACKET;
						usFragmentOffset = ( uint16_t ) ( xTotalDataLength - xBytesRemaining );
						pxFragmentParameters->usFragmentedPacketOffset = usFragmentOffset;
						pxFragmentParameters->usFragmentLength = ( uint16_t ) xBytesToSend;
					}
					else
					{
						usFragmentOffset = 0;
					}

					/* Write the payload into the packet.  The IP layer is
					queried to find where in the IP payload the data should be
					written.  This is because the necessary offset is different
					for the first packet, because the first packet leaves space
					for a UDP header.  Note that this changes usFragmentOffset
					from the offset in the entire UDP packet, to the offset
					in the IP packet. */
					if( ( ulFlags & FREERTOS_ZERO_COPY ) == 0 )
					{
						/* Only copy the data if it is not already in the
						expected location. */
						usFragmentOffset = ipGET_UDP_PAYLOAD_OFFSET_FOR_FRAGMENT( usFragmentOffset );
						memcpy( ( void * ) &( pxNetworkBuffer->pucEthernetBuffer[ usFragmentOffset ] ), ( void * ) pucBuffer, xBytesToSend );
					}
					pxNetworkBuffer->xDataLength = xTotalDataLength;
					pxNetworkBuffer->usPort = pxDestinationAddress->sin_port;
					pxNetworkBuffer->usBoundPort = ( uint16_t ) socketGET_SOCKET_ADDRESS( pxSocket );
					pxNetworkBuffer->ulIPAddress = pxDestinationAddress->sin_addr;

					/* Tell the networking task that the packet needs sending. */
					xStackTxEvent.pvData = pxNetworkBuffer;

					if( xTaskCheckForTimeOut( &xTimeOut, &xTicksToWait ) == pdTRUE )
					{
						xTicksToWait = 0;
					}

					if( xQueueSendToBack( xNetworkEventQueue, &xStackTxEvent, xTicksToWait ) != pdPASS )
					{
						/* If the buffer was allocated in this function, release it. */
						if( ( ulFlags & FREERTOS_ZERO_COPY ) == 0 )
						{
							vNetworkBufferRelease( pxNetworkBuffer );
						}
						iptraceSTACK_TX_EVENT_LOST( ipSTACK_TX_EVENT );
						break;
					}

					/* Adjust counters ready to either exit the loop, or send
					another chunk of data. */
					xBytesRemaining -= xBytesToSend;
					pucBuffer += xBytesToSend;
				}
				else
				{
					/* If errno was available, errno would be set to
					FREERTOS_ENOPKTS.  As it is, the function must return the
					number of transmitted bytes, so the calling function knows how
					much data was actually sent. */
					break;
				}
			}
		}

		return ( xTotalDataLength - xBytesRemaining );
	} /* Tested */

#else /* ipconfigCAN_FRAGMENT_OUTGOING_PACKETS */

	int32_t FreeRTOS_sendto( xSocket_t xSocket, const void *pvBuffer, size_t xTotalDataLength, uint32_t ulFlags, const struct freertos_sockaddr *pxDestinationAddress, socklen_t xDestinationAddressLength )
	{
	xNetworkBufferDescriptor_t *pxNetworkBuffer;
	xIPStackEvent_t xStackTxEvent = { eStackTxEvent, NULL };
	extern xQueueHandle xNetworkEventQueue;
	xTimeOutType xTimeOut;
	TickType_t xTicksToWait;
	int32_t lReturn = 0;
	xFreeRTOS_Socket_t *pxSocket;
	uint8_t *pucBuffer;

		pxSocket = ( xFreeRTOS_Socket_t * ) xSocket;

		/* The function prototype is designed to maintain the expected Berkeley
		sockets standard, but this implementation does not use all the
		parameters. */
		( void ) xDestinationAddressLength;
		configASSERT( xNetworkEventQueue );
		configASSERT( pvBuffer );

		if( xTotalDataLength <= ipMAX_UDP_PAYLOAD_LENGTH )
		{
			if( socketSOCKET_IS_BOUND( pxSocket ) == pdFALSE )
			{
				/* If the socket is not already bound to an address, bind it now.
				Passing NULL as the address parameter tells FreeRTOS_bind() to
				select the address to bind to. */
				FreeRTOS_bind( pxSocket, NULL, 0 );
			}

			if( socketSOCKET_IS_BOUND( pxSocket ) != pdFALSE )
			{
				xTicksToWait = pxSocket->xSendBlockTime;

				if( ( ulFlags & FREERTOS_ZERO_COPY ) == 0 )
				{
					/* Zero copy is not set, so obtain a network buffer into
					which the payload will be copied. */
					vTaskSetTimeOutState( &xTimeOut );
					pxNetworkBuffer = pxNetworkBufferGet( xTotalDataLength + sizeof( xUDPPacket_t ), xTicksToWait );

					if( pxNetworkBuffer != NULL )
					{
						memcpy( ( void * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipUDP_PAYLOAD_OFFSET ] ), ( void * ) pvBuffer, xTotalDataLength );

						if( xTaskCheckForTimeOut( &xTimeOut, &xTicksToWait ) == pdTRUE )
						{
							/* The entire block time has been used up. */
							xTicksToWait = 0;
						}
					}
				}
				else
				{
					/* When zero copy is used, pvBuffer is a pointer to the
					payload of a buffer that has already been obtained from the
					stack.  Obtain the network buffer pointer from the buffer. */
					pucBuffer = ( uint8_t * ) pvBuffer;
					pucBuffer -= ( ipBUFFER_PADDING + sizeof( xUDPPacket_t ) );
					pxNetworkBuffer = * ( ( xNetworkBufferDescriptor_t ** ) pucBuffer );
				}

				if( pxNetworkBuffer != NULL )
				{
					pxNetworkBuffer->xDataLength = xTotalDataLength;
					pxNetworkBuffer->usPort = pxDestinationAddress->sin_port;
					pxNetworkBuffer->usBoundPort = ( uint16_t ) socketGET_SOCKET_ADDRESS( pxSocket );
					pxNetworkBuffer->ulIPAddress = pxDestinationAddress->sin_addr;

					/* The socket options are passed to the IP layer in the
					space that will eventually get used by the Ethernet header. */
					pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] = pxSocket->ucSocketOptions;

					/* Tell the networking task that the packet needs sending. */
					xStackTxEvent.pvData = pxNetworkBuffer;

					if( xQueueSendToBack( xNetworkEventQueue, &xStackTxEvent, xTicksToWait ) != pdPASS )
					{
						/* If the buffer was allocated in this function, release it. */
						if( ( ulFlags & FREERTOS_ZERO_COPY ) == 0 )
						{
							vNetworkBufferRelease( pxNetworkBuffer );
						}
						iptraceSTACK_TX_EVENT_LOST( ipSTACK_TX_EVENT );
					}
					else
					{
						lReturn = ( int32_t ) xTotalDataLength;
					}
				}
				else
				{
					/* If errno was available, errno would be set to
					FREERTOS_ENOPKTS.  As it is, the function must return the
					number of transmitted bytes, so the calling function knows how
					much data was actually sent. */
					iptraceNO_BUFFER_FOR_SENDTO();
				}
			}
			else
			{
				iptraceSENDTO_SOCKET_NOT_BOUND();
			}
		}
		else
		{
			/* The data is longer than the available buffer space.  Setting
			ipconfigCAN_FRAGMENT_OUTGOING_PACKETS to 1 may allow this packet
			to be sent. */
			iptraceSENDTO_DATA_TOO_LONG();
		}

		return lReturn;
	} /* Tested */

#endif /* ipconfigCAN_FRAGMENT_OUTGOING_PACKETS */
/*-----------------------------------------------------------*/

BaseType_t FreeRTOS_bind( xSocket_t xSocket, struct freertos_sockaddr * pxAddress, socklen_t xAddressLength )
{
BaseType_t xReturn = 0; /* In Berkeley sockets, 0 means pass for bind(). */
xFreeRTOS_Socket_t *pxSocket;
#if ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND == 1
	struct freertos_sockaddr xAddress;
#endif /* ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND */

	pxSocket = ( xFreeRTOS_Socket_t * ) xSocket;

	/* The function prototype is designed to maintain the expected Berkeley
	sockets standard, but this implementation does not use all the parameters. */
	( void ) xAddressLength;

	configASSERT( xSocket );
	configASSERT( xSocket != FREERTOS_INVALID_SOCKET );

	#if ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND == 1
	{
		/* pxAddress will be NULL if sendto() was called on a socket without the
		socket being bound to an address.  In this case, automatically allocate
		an address to the socket.  There is a very tiny chance that the allocated
		port will already be in use - if that is the case, then the check below
		[pxListFindListItemWithValue()] will result in an error being returned. */
		if( pxAddress == NULL )
		{
			pxAddress = &xAddress;
			pxAddress->sin_port = prvGetPrivatePortNumber();
		}
	}
	#endif /* ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND == 1 */

	/* Sockets must be bound before calling FreeRTOS_sendto() if
	ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND is not set to 1. */
	configASSERT( pxAddress );

	if( pxAddress != NULL )
	{
		if( pxAddress->sin_port == 0 )
		{
			pxAddress->sin_port = prvGetPrivatePortNumber();
		}

		vTaskSuspendAll();
		{
			/* Check to ensure the port is not already in use. */
			if( pxListFindListItemWithValue( &xBoundSocketsList, ( TickType_t ) pxAddress->sin_port ) != NULL )
			{
				xReturn = FREERTOS_EADDRINUSE;
			}
		}
		xTaskResumeAll();

		/* Check that xReturn has not been set before continuing. */
		if( xReturn == 0 )
		{
			if( pxSocket->xWaitingPacketSemaphore == NULL )
			{
				/* Create the semaphore used to count the number of packets that
				are queued on this socket. */
				pxSocket->xWaitingPacketSemaphore = xSemaphoreCreateCounting( ipconfigNUM_NETWORK_BUFFERS, 0 );

				if( pxSocket->xWaitingPacketSemaphore != NULL )
				{
					/* Allocate the port number to the socket. */
					socketSET_SOCKET_ADDRESS( pxSocket, pxAddress->sin_port );
					taskENTER_CRITICAL();
					{
						/* Add the socket to the list of bound ports. */
						vListInsertEnd( &xBoundSocketsList, &( pxSocket->xBoundSocketListItem ) );
					}
					taskEXIT_CRITICAL();
				}
				else
				{
					/* Out of memory. */
					xReturn = FREERTOS_ENOBUFS;
				}
			}
			else
			{
				/* The socket is already bound. */
				xReturn = FREERTOS_EINVAL;
			}
		}
	}
	else
	{
		xReturn = FREERTOS_EADDRNOTAVAIL;
	}

	if( xReturn != 0 )
	{
		iptraceBIND_FAILED( xSocket, ( FreeRTOS_ntohs( pxAddress->sin_port ) ) );
	}

	return xReturn;
} /* Tested */
/*-----------------------------------------------------------*/

BaseType_t FreeRTOS_closesocket( xSocket_t xSocket )
{
xNetworkBufferDescriptor_t *pxNetworkBuffer;
xFreeRTOS_Socket_t *pxSocket;

	pxSocket = ( xFreeRTOS_Socket_t * ) xSocket;

	configASSERT( pxSocket );
	configASSERT( pxSocket != FREERTOS_INVALID_SOCKET );

	/* Socket must be unbound first, to ensure no more packets are queued on
	it. */
	if( socketSOCKET_IS_BOUND( pxSocket ) != pdFALSE )
	{
		taskENTER_CRITICAL();
		{
			uxListRemove( &( pxSocket->xBoundSocketListItem ) );
		}
		taskEXIT_CRITICAL();
	}

	/* Now the socket is not bound the list of waiting packets can be
	drained. */
	if( pxSocket->xWaitingPacketSemaphore != NULL )
	{
		while( listCURRENT_LIST_LENGTH( &( pxSocket->xWaitingPacketsList ) ) > 0U )
		{
			pxNetworkBuffer = ( xNetworkBufferDescriptor_t * ) listGET_OWNER_OF_HEAD_ENTRY( &( pxSocket->xWaitingPacketsList ) );
			uxListRemove( &( pxNetworkBuffer->xBufferListItem ) );
			vNetworkBufferRelease( pxNetworkBuffer );
		}
		vSemaphoreDelete( pxSocket->xWaitingPacketSemaphore );
	}

	vPortFree( pxSocket );

	return 0;
} /* Tested */
/*-----------------------------------------------------------*/

void FreeRTOS_SocketsInit( void )
{
	vListInitialise( &xBoundSocketsList );
}
/*-----------------------------------------------------------*/

BaseType_t FreeRTOS_setsockopt( xSocket_t xSocket, int32_t lLevel, int32_t lOptionName, const void *pvOptionValue, size_t xOptionLength )
{
/* The standard Berkeley function returns 0 for success. */
BaseType_t xReturn = 0;
BaseType_t lOptionValue;
xFreeRTOS_Socket_t *pxSocket;

	pxSocket = ( xFreeRTOS_Socket_t * ) xSocket;

	/* The function prototype is designed to maintain the expected Berkeley
	sockets standard, but this implementation does not use all the parameters. */
	( void ) lLevel;
	( void ) xOptionLength;

	configASSERT( xSocket );

	switch( lOptionName )
	{
		case FREERTOS_SO_RCVTIMEO	:
			/* Receive time out. */
			pxSocket->xReceiveBlockTime = *( ( TickType_t * ) pvOptionValue );
			break;

		case FREERTOS_SO_SNDTIMEO	:
			/* The send time out is capped for the reason stated in the comments
			where ipconfigMAX_SEND_BLOCK_TIME_TICKS is defined in
			FreeRTOSIPConfig.h (assuming an official configuration file is being
			used. */
			pxSocket->xSendBlockTime = *( ( TickType_t * ) pvOptionValue );
			if( pxSocket->xSendBlockTime > ipconfigMAX_SEND_BLOCK_TIME_TICKS )
			{
				pxSocket->xSendBlockTime = ipconfigMAX_SEND_BLOCK_TIME_TICKS;
			}
			break;

		case FREERTOS_SO_UDPCKSUM_OUT :
			/* Turn calculating of the UDP checksum on/off for this socket. */
			lOptionValue = ( BaseType_t ) pvOptionValue;

			if( lOptionValue == 0 )
			{
				pxSocket->ucSocketOptions &= ~FREERTOS_SO_UDPCKSUM_OUT;
			}
			else
			{
				pxSocket->ucSocketOptions |= FREERTOS_SO_UDPCKSUM_OUT;
			}
			break;

		default :
			/* No other options are handled. */
			xReturn = FREERTOS_ENOPROTOOPT;
			break;
	}

	return xReturn;
} /* Tested */
/*-----------------------------------------------------------*/

BaseType_t xProcessReceivedUDPPacket( xNetworkBufferDescriptor_t *pxNetworkBuffer, uint16_t usPort )
{
xListItem *pxListItem;
BaseType_t xReturn = pdPASS;
xFreeRTOS_Socket_t *pxSocket;
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	vTaskSuspendAll();
	{
		/* See if there is a list item associated with the port number on the
		list of bound sockets. */
		pxListItem = pxListFindListItemWithValue( &xBoundSocketsList, ( TickType_t ) usPort );
	}
	xTaskResumeAll();

	if( pxListItem != NULL )
	{
		/* The owner of the list item is the socket itself. */
		pxSocket = ( xFreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxListItem );

		vTaskSuspendAll();
		{
			#if( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
			{
				/* Is the socket a member of a select() group? */
				if( pxSocket->xSelectQueue != NULL )
				{
					/* Can the select group be notified that the socket is
					ready to be read? */
					if( xQueueSendFromISR( pxSocket->xSelectQueue, &pxSocket, &xHigherPriorityTaskWoken ) != pdPASS )
					{
						/* Could not notify the select group. */
						xReturn = pdFAIL;
						iptraceFAILED_TO_NOTIFY_SELECT_GROUP( pxSocket );
					}
				}
			}
			#endif

			if( xReturn == pdPASS )
			{
				taskENTER_CRITICAL();
				{
					/* Add the network packet to the list of packets to be
					processed by the socket. */
					vListInsertEnd( &( pxSocket->xWaitingPacketsList ), &( pxNetworkBuffer->xBufferListItem ) );
				}
				taskEXIT_CRITICAL();

				/* The socket's counting semaphore records how many packets are
				waiting	to be processed by the socket. */
				xSemaphoreGiveFromISR( pxSocket->xWaitingPacketSemaphore, &xHigherPriorityTaskWoken );
			}
		}
		if( xTaskResumeAll() == pdFALSE )
		{
			if( xHigherPriorityTaskWoken != pdFALSE )
			{
				taskYIELD();
			}
		}
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static uint16_t prvGetPrivatePortNumber( void )
{
static uint16_t usNextPortToUse = socketAUTO_PORT_ALLOCATION_START_NUMBER - 1;
uint16_t usReturn;

	/* Assign the next port in the range. */
	taskENTER_CRITICAL();
	{
		usNextPortToUse++;

		/* Has it overflowed? */
		if( usNextPortToUse == 0U )
		{
			/* Don't go right back to the start of the dynamic/private port
			range numbers as any persistent sockets are likely to have been
			create first so the early port numbers may still be in use. */
			usNextPortToUse = socketAUTO_PORT_ALLOCATION_RESET_NUMBER;
		}

		usReturn = FreeRTOS_htons( usNextPortToUse );
	}
	taskEXIT_CRITICAL();

	return usReturn;
} /* Tested */
/*-----------------------------------------------------------*/

xListItem * pxListFindListItemWithValue( xList *pxList, TickType_t xWantedItemValue )
{
xListItem *pxIterator, *pxReturn;

	pxReturn = NULL;
	for( pxIterator = ( xListItem * ) pxList->xListEnd.pxNext; pxIterator != ( xListItem* ) &( pxList->xListEnd ); pxIterator = ( xListItem * ) pxIterator->pxNext )
	{
		if( pxIterator->xItemValue == xWantedItemValue )
		{
			pxReturn = pxIterator;
			break;
		}
	}

	return pxReturn;
} /* Tested */
/*-----------------------------------------------------------*/

#if ipconfigINCLUDE_FULL_INET_ADDR == 1

	uint32_t FreeRTOS_inet_addr( const char *pcIPAddress )
	{
	const uint8_t ucDecimalBase = 10;
	uint8_t ucOctet[ socketMAX_IP_ADDRESS_OCTETS ];
	const char *pcPointerOnEntering;
	uint32_t ulReturn = 0UL, ulOctetNumber, ulValue;
	BaseType_t xResult = pdPASS;

		for( ulOctetNumber = 0; ulOctetNumber < socketMAX_IP_ADDRESS_OCTETS; ulOctetNumber++ )
		{
			ulValue = 0;
			pcPointerOnEntering = pcIPAddress;

			while( ( *pcIPAddress >= ( uint8_t ) '0' ) && ( *pcIPAddress <= ( uint8_t ) '9' ) )
			{
				/* Move previous read characters into the next decimal
				position. */
				ulValue *= ucDecimalBase;

				/* Add the binary value of the ascii character. */
				ulValue += ( *pcIPAddress - ( uint8_t ) '0' );

				/* Move to next character in the string. */
				pcIPAddress++;
			}

			/* Check characters were read. */
			if( pcIPAddress == pcPointerOnEntering )
			{
				xResult = pdFAIL;
			}

			/* Check the value fits in an 8-bit number. */
			if( ulValue > 0xffUL )
			{
				xResult = pdFAIL;
			}
			else
			{
				ucOctet[ ulOctetNumber ] = ( uint8_t ) ulValue;

				/* Check the next character is as expected. */
				if( ulOctetNumber < ( socketMAX_IP_ADDRESS_OCTETS - 1 ) )
				{
					if( *pcIPAddress != ( uint8_t ) '.' )
					{
						xResult = pdFAIL;
					}
					else
					{
						/* Move past the dot. */
						pcIPAddress++;
					}
				}
			}

			if( xResult == pdFAIL )
			{
				/* No point going on. */
				break;
			}
		}

		if( *pcIPAddress != ( uint8_t ) 0x00 )
		{
			/* Expected the end of the string. */
			xResult = pdFAIL;
		}

		if( ulOctetNumber != socketMAX_IP_ADDRESS_OCTETS )
		{
			/* Didn't read enough octets. */
			xResult = pdFAIL;
		}

		if( xResult == pdPASS )
		{
			ulReturn = FreeRTOS_inet_addr_quick( ucOctet[ 0 ], ucOctet[ 1 ], ucOctet[ 2 ], ucOctet[ 3 ] );
		}

		return ulReturn;
	}

#endif /* ipconfigINCLUDE_FULL_INET_ADDR */
/*-----------------------------------------------------------*/

