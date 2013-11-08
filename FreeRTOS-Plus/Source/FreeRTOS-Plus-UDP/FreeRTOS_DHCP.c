/*
 * FreeRTOS+UDP V1.0.2 (C) 2013 Real Time Engineers ltd.
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
#include "timers.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_DHCP.h"
#include "FreeRTOS_Sockets.h"
#include "NetworkInterface.h"
#include "IPTraceMacroDefaults.h"

/* Exclude the entire file if DHCP is not enabled. */
#if ipconfigUSE_DHCP != 0

#if ( ipconfigUSE_DHCP != 0 ) && ( ipconfigNETWORK_MTU < 586 )
	/* DHCP must be able to receive an options field of 312 bytes, the fixed
	part of the DHCP packet is 240 bytes, and the IP/UDP headers take 28 bytes. */
	#error ipconfigNETWORK_MTU needs to be at least 586 to use DHCP (588 if ipconfigCAN_FRAGMENT_OUTGOING_PACKETS is set to 1)
#endif

/* Parameter widths in the DHCP packet. */
#define dhcpCLIENT_HARDWARE_ADDRESS_LENGTH		16
#define dhcpSERVER_HOST_NAME_LENGTH				64
#define dhcpBOOT_FILE_NAME_LENGTH 				128

/* Timer parameters.  Windows simulator times are much shorter because simulated
time is not real time. */
#ifdef _WINDOWS_
	#define dhcpINITIAL_DHCP_TX_PERIOD			( 100 / portTICK_RATE_MS )
	#define dhcpINITIAL_TIMER_PERIOD			( 10 / portTICK_RATE_MS )
	#define dhcpMAX_TIME_TO_WAIT_FOR_ACK		( 200 / portTICK_RATE_MS )
#else
	#define dhcpINITIAL_DHCP_TX_PERIOD			( 5000 / portTICK_RATE_MS )
	#define dhcpINITIAL_TIMER_PERIOD			( 250 / portTICK_RATE_MS )
	#define dhcpMAX_TIME_TO_WAIT_FOR_ACK		( 5000 / portTICK_RATE_MS )
#endif /* _WINDOWS_ */

/* Codes of interest found in the DHCP options field. */
#define dhcpSUBNET_MASK_OPTION_CODE				( 1 )
#define dhcpGATEWAY_OPTION_CODE					( 3 )
#define hdcpDNS_SERVER_OPTIONS_CODE				( 6 )
#define dhcpMESSAGE_TYPE_OPTION_CODE			( 53 )
#define dhcpLEASE_TIME_OPTION_CODE				( 51 )
#define dhcpCLIENT_IDENTIFIER_OPTION_CODE		( 61 )
#define dhcpPARAMETER_REQUEST_OPTION_CODE		( 55 )
#define dhcpREQUEST_IP_ADDRESS_OPTION_CODE		( 50 )
#define dhcpSERVER_IP_ADDRESS_OPTION_CODE		( 54 )

/* The four DHCP message types of interest. */
#define dhcpMESSAGE_TYPE_DISCOVER				( 1 )
#define dhcpMESSAGE_TYPE_OFFER					( 2 )
#define dhcpMESSAGE_TYPE_REQUEST				( 3 )
#define dhcpMESSAGE_TYPE_ACK					( 5 )
#define dhcpMESSAGE_TYPE_NACK					( 6 )

/* Offsets into the transmitted DHCP options fields at which various parameters
are located. */
#define dhcpCLIENT_IDENTIFIER_OFFSET			( 5 )
#define dhcpREQUESTED_IP_ADDRESS_OFFSET			( 13 )
#define dhcpDHCP_SERVER_IP_ADDRESS_OFFSET		( 19 )

/* Values used in the DHCP packets. */
#define dhcpREQUEST_OPCODE						( 1 )
#define dhcpREPLY_OPCODE						( 2 )
#define dhcpADDRESS_TYPE_ETHERNET				( 1 )
#define dhcpETHERNET_ADDRESS_LENGTH				( 6 )

/* If a lease time is not received, use the default of two days. */
#define dhcpDEFAULT_LEASE_TIME					( ( 48UL * 60UL * 60UL * 1000UL ) / portTICK_RATE_MS ) /* 48 hours in ticks. */

/* Don't allow the lease time to be too short. */
#define dhcpMINIMUM_LEASE_TIME					( 60000UL / portTICK_RATE_MS )	/* 60 seconds in ticks. */

/* Marks the end of the variable length options field in the DHCP packet. */
#define dhcpOPTION_END_BYTE 0xff

/* Offset into a DHCP message at which the first byte of the options is
located. */
#define dhcpFIRST_OPTION_BYTE_OFFSET			( 0xf0 )

/* When walking the variable length options field, the following value is used
to ensure the walk has not gone past the end of the valid options.  2 bytes is
made up of the length byte, and minimum one byte value. */
#define dhcpMAX_OPTION_LENGTH_OF_INTEREST		( 2L )

/* Standard DHCP port numbers and magic cookie value. */
#if( ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN )
	#define dhcpCLIENT_PORT 0x4400
	#define dhcpSERVER_PORT 0x4300
	#define dhcpCOOKIE		0x63538263
	#define dhcpBROADCAST	0x0080
#else
	#define dhcpCLIENT_PORT 0x0044
	#define dhcpSERVER_PORT 0x0043
	#define dhcpCOOKIE		0x63825363
	#define dhcpBROADCAST	0x8000
#endif /* ipconfigBYTE_ORDER */

#include "pack_struct_start.h"
struct xDHCPMessage
{
	uint8_t ucOpcode;
	uint8_t ucAddressType;
	uint8_t ucAddressLength;
	uint8_t ucHops;
	uint32_t ulTransactionID;
	uint16_t usElapsedTime;
	uint16_t usFlags;
	uint32_t ulClientIPAddress_ciaddr;
	uint32_t ulYourIPAddress_yiaddr;
	uint32_t ulServerIPAddress_siaddr;
	uint32_t ulRelayAgentIPAddress_giaddr;
	uint8_t ucClientHardwareAddress[ dhcpCLIENT_HARDWARE_ADDRESS_LENGTH ];
	uint8_t ucServerHostName[ dhcpSERVER_HOST_NAME_LENGTH ];
	uint8_t ucBootFileName[ dhcpBOOT_FILE_NAME_LENGTH ];
	uint32_t ulDHCPCookie;
	uint8_t ucFirstOptionByte;
}
#include "pack_struct_end.h"
typedef struct xDHCPMessage xDHCPMessage_t;

/* DHCP state machine states. */
typedef enum
{
	eWaitingSendFirstDiscover = 0,	/* Initial state.  Send a discover the first time it is called, and reset all timers. */
	eWaitingOffer,					/* Either resend the discover, or, if the offer is forthcoming, send a request. */
	eWaitingAcknowledge,			/* Either resend the request. */
	eLeasedAddress,					/* Resend the request at the appropriate time to renew the lease. */
	eNotUsingLeasedAddress			/* DHCP failed, and a default IP address is being used. */
} eDHCPState_t;

/*
 * Generate a DHCP discover message and send it on the DHCP socket.
 */
static void prvSendDHCPDiscover( xMACAddress_t *pxMACAddress );

/*
 * Interpret message received on the DHCP socket.
 */
static portBASE_TYPE prvProcessDHCPReplies( uint8_t ucExpectedMessageType, xMACAddress_t *pxMACAddress, xNetworkAddressingParameters_t *pxNetworkAddressing );

/*
 * Generate a DHCP request packet, and send it on the DHCP socket.
 */
static void prvSendDHCPRequest( xMACAddress_t *pxMACAddress );

/*
 * Prepare to start a DHCP transaction.  This initialises some state variables
 * and creates the DHCP socket if necessary.
 */
static void prvInitialiseDHCP( void );

/*
 * Creates the part of outgoing DHCP messages that are common to all outgoing
 * DHCP messages.
 */
static uint8_t *prvCreatePartDHCPMessage( struct freertos_sockaddr *pxAddress, xMACAddress_t *pxMACAddress, uint8_t ucOpcode, const uint8_t * const pucOptionsArray, size_t xOptionsArraySize );

/*
 * Create the DHCP socket, if it has not been created already.
 */
static void prvCreateDHCPSocket( void );

/*-----------------------------------------------------------*/

/* The timer used to drive the DHCP state machine. */
static xTimerHandle xDHCPTimer = NULL;

/* The UDP socket used for all incoming and outgoing DHCP traffic. */
static xSocket_t xDHCPSocket = NULL;

/* Hold information in between steps in the DHCP state machine. */
static uint32_t ulTransactionId = 0UL, ulOfferedIPAddress = 0UL, ulDHCPServerAddress = 0UL, ulLeaseTime = 0;

/* Hold information on the current timer state. */
static portTickType xDHCPTxTime = 0x00, xDHCPTxPeriod = 0x00;

/* Maintains the DHCP state machine state. */
static eDHCPState_t eDHCPState = eWaitingSendFirstDiscover;

/*-----------------------------------------------------------*/

void vDHCPProcess( portBASE_TYPE xReset, xMACAddress_t *pxMACAddress, uint32_t *pulIPAddress, xNetworkAddressingParameters_t *pxNetworkAddressing )
{
	if( xReset != pdFALSE )
	{
		eDHCPState = eWaitingSendFirstDiscover;
	}

	switch( eDHCPState )
	{
		case eWaitingSendFirstDiscover :

			/* Initial state.  Create the DHCP socket, timer, etc. if they
			have not already been created. */
			prvInitialiseDHCP();
			*pulIPAddress = 0UL;

			/* Send the first discover request. */
			if( xDHCPSocket != NULL )
			{
				xDHCPTxTime = xTaskGetTickCount();
				prvSendDHCPDiscover( pxMACAddress );
				eDHCPState = eWaitingOffer;
			}
			break;

		case eWaitingOffer :

			/* Look for offers coming in. */
			if( prvProcessDHCPReplies( dhcpMESSAGE_TYPE_OFFER, pxMACAddress, pxNetworkAddressing ) == pdPASS )
			{
				/* An offer has been made, generate the request. */
				xDHCPTxTime = xTaskGetTickCount();
				xDHCPTxPeriod = dhcpINITIAL_DHCP_TX_PERIOD;
				prvSendDHCPRequest( pxMACAddress );
				eDHCPState = eWaitingAcknowledge;
			}
			else
			{
				/* Is it time to send another Discover? */
				if( ( xTaskGetTickCount() - xDHCPTxTime ) > xDHCPTxPeriod )
				{
					/* Increase the time period, and if it has not got to the
					point of giving up - send another discovery. */
					xDHCPTxPeriod <<= 1;
					if( xDHCPTxPeriod <= ipconfigMAXIMUM_DISCOVER_TX_PERIOD )
					{
						ulTransactionId++;
						xDHCPTxTime = xTaskGetTickCount();
						prvSendDHCPDiscover( pxMACAddress );
					}
					else
					{
						/* Revert to static IP address. */
						taskENTER_CRITICAL();
						{
							*pulIPAddress = pxNetworkAddressing->ulDefaultIPAddress;
							iptraceDHCP_REQUESTS_FAILED_USING_DEFAULT_IP_ADDRESS( pxNetworkAddressing->ulDefaultIPAddress );
						}
						taskEXIT_CRITICAL();
						eDHCPState = eNotUsingLeasedAddress;
						xTimerStop( xDHCPTimer, ( portTickType ) 0 );

						#if ipconfigUSE_NETWORK_EVENT_HOOK == 1
						{
							vApplicationIPNetworkEventHook( eNetworkUp );
						}
						#endif

						/* Static configuration is being used, so the network is now up. */
						#if ipconfigFREERTOS_PLUS_NABTO == 1
						{
							/* Return value is used in configASSERT() inside the 
							function. */
							( void ) xStartNabtoTask();
						}
						#endif /* ipconfigFREERTOS_PLUS_NABTO */

						/* Close socket to ensure packets don't queue on it. */
						FreeRTOS_closesocket( xDHCPSocket );
						xDHCPSocket = NULL;
					}
				}
			}
			break;

		case eWaitingAcknowledge :

			/* Look for acks coming in. */
			if( prvProcessDHCPReplies( dhcpMESSAGE_TYPE_ACK, pxMACAddress, pxNetworkAddressing ) == pdPASS )
			{
				/* DHCP completed.  The IP address can now be used, and the
				timer set to the lease timeout time. */
				*pulIPAddress = ulOfferedIPAddress;
				eDHCPState = eLeasedAddress;

				#if ipconfigUSE_NETWORK_EVENT_HOOK == 1
				{
					vApplicationIPNetworkEventHook( eNetworkUp );
				}
				#endif

				/* Static configuration is being used, so the network is now 
				up. */
				#if ipconfigFREERTOS_PLUS_NABTO == 1
				{
					/* Return value is used in configASSERT() inside the 
					function. */
					( void ) xStartNabtoTask();
				}
				#endif /* ipconfigFREERTOS_PLUS_NABTO */

				/* Close socket to ensure packets don't queue on it. */
				FreeRTOS_closesocket( xDHCPSocket );
				xDHCPSocket = NULL;

				if( ulLeaseTime == 0UL )
				{
					ulLeaseTime = dhcpDEFAULT_LEASE_TIME;
				}
				else if( ulLeaseTime < dhcpMINIMUM_LEASE_TIME )
				{
					ulLeaseTime = dhcpMINIMUM_LEASE_TIME;
				}
				else
				{
					/* The lease time is already valid. */
				}

				xTimerChangePeriod( xDHCPTimer, ulLeaseTime, portMAX_DELAY );
			}
			else
			{
				/* Is it time to send another Discover? */
				if( ( xTaskGetTickCount() - xDHCPTxTime ) > xDHCPTxPeriod )
				{
					/* Increase the time period, and if it has not got to the
					point of giving up - send another request. */
					xDHCPTxPeriod <<= 1;
					if( xDHCPTxPeriod <= ipconfigMAXIMUM_DISCOVER_TX_PERIOD )
					{
						xDHCPTxTime = xTaskGetTickCount();
						prvSendDHCPRequest( pxMACAddress );
					}
					else
					{
						/* Give up, start again. */
						eDHCPState = eWaitingSendFirstDiscover;
					}
				}
			}
			break;

		case eLeasedAddress :

			/* Resend the request at the appropriate time to renew the lease. */
			prvCreateDHCPSocket();
			if( xDHCPSocket != NULL )
			{
				xDHCPTxTime = xTaskGetTickCount();
				xDHCPTxPeriod = dhcpINITIAL_DHCP_TX_PERIOD;
				prvSendDHCPRequest( pxMACAddress );
				eDHCPState = eWaitingAcknowledge;
			}
			xTimerChangePeriod( xDHCPTimer, dhcpINITIAL_TIMER_PERIOD, portMAX_DELAY );
			break;

		case eNotUsingLeasedAddress:
			xTimerStop( xDHCPTimer, ( portTickType ) 0 );
			break;
	}
}
/*-----------------------------------------------------------*/

static void prvCreateDHCPSocket( void )
{
struct freertos_sockaddr xAddress;
portBASE_TYPE xReturn;
portTickType xTimeoutTime = 0;

	/* Create the socket, if it has not already been created. */
	if( xDHCPSocket == NULL )
	{
		xDHCPSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
		configASSERT( ( xDHCPSocket != FREERTOS_INVALID_SOCKET ) );

		/* Ensure the Rx and Tx timeouts are zero as the DHCP executes in the
		context of the IP task. */
		FreeRTOS_setsockopt( xDHCPSocket, 0, FREERTOS_SO_RCVTIMEO, ( void * ) &xTimeoutTime, sizeof( portTickType ) );
		FreeRTOS_setsockopt( xDHCPSocket, 0, FREERTOS_SO_SNDTIMEO, ( void * ) &xTimeoutTime, sizeof( portTickType ) );

		/* Bind to the standard DHCP client port. */
		xAddress.sin_port = dhcpCLIENT_PORT;
		xReturn = FreeRTOS_bind( xDHCPSocket, &xAddress, sizeof( xAddress ) );
		configASSERT( xReturn == 0 );

		/* Remove compiler warnings if configASSERT() is not defined. */
		( void ) xReturn;
	}
}
/*-----------------------------------------------------------*/

static void prvInitialiseDHCP( void )
{
extern void vIPFunctionsTimerCallback( xTimerHandle xTimer );

	/* Initialise the parameters that will be set by the DHCP process. */
	if( ulTransactionId == 0 )
	{
		ulTransactionId = ipconfigRAND32();
	}
	else
	{
		ulTransactionId++;
	}
	ulOfferedIPAddress = 0UL;
	ulDHCPServerAddress = 0UL;
	xDHCPTxPeriod = dhcpINITIAL_DHCP_TX_PERIOD;

	/* Create the DHCP socket if it has not already been created. */
	prvCreateDHCPSocket();

	if( xDHCPTimer == NULL )
	{
		xDHCPTimer = xTimerCreate( ( const signed char * const ) "DHCP", dhcpINITIAL_TIMER_PERIOD, pdTRUE, ( void * ) eDHCPEvent, vIPFunctionsTimerCallback );
		configASSERT( xDHCPTimer );
		xTimerStart( xDHCPTimer, portMAX_DELAY );
	}
	else
	{
		xTimerChangePeriod( xDHCPTimer, dhcpINITIAL_TIMER_PERIOD, portMAX_DELAY );
	}
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvProcessDHCPReplies( uint8_t ucExpectedMessageType, xMACAddress_t *pxMACAddress, xNetworkAddressingParameters_t *pxNetworkAddressing )
{
uint8_t *pucUDPPayload, *pucLastByte;
struct freertos_sockaddr xClient;
uint32_t xClientLength = sizeof( xClient );
int32_t lBytes;
xDHCPMessage_t *pxDHCPMessage;
uint8_t *pucByte, ucOptionCode, ucLength;
uint32_t ulProcessed;
portBASE_TYPE xReturn = pdFALSE;
const uint32_t ulMandatoryOptions = 2; /* DHCP server address, and the correct DHCP message type must be present in the options. */

	lBytes = FreeRTOS_recvfrom( xDHCPSocket, ( void * ) &pucUDPPayload, 0, FREERTOS_ZERO_COPY, &xClient, &xClientLength );

	if( lBytes > 0 )
	{
		/* Map a DHCP structure onto the received data. */
		pxDHCPMessage = ( xDHCPMessage_t * ) ( pucUDPPayload );

		/* Sanity check. */
		if( ( pxDHCPMessage->ulDHCPCookie == dhcpCOOKIE ) && ( pxDHCPMessage->ucOpcode == dhcpREPLY_OPCODE ) && ( pxDHCPMessage->ulTransactionID == ulTransactionId ) )
		{
			if( memcmp( ( void * ) &( pxDHCPMessage->ucClientHardwareAddress ), ( void * ) pxMACAddress, sizeof( xMACAddress_t ) ) == 0 )
			{
				/* None of the essential options have been processed yet. */
				ulProcessed = 0;

				/* Walk through the options until the dhcpOPTION_END_BYTE byte
				is found, taking care not to walk off the end of the options. */
				pucByte = &( pxDHCPMessage->ucFirstOptionByte );
				pucLastByte = &( pucUDPPayload[ lBytes - dhcpMAX_OPTION_LENGTH_OF_INTEREST ] );
				while( ( *pucByte != dhcpOPTION_END_BYTE ) && ( pucByte < pucLastByte ) )
				{
					ucOptionCode = *pucByte;
					pucByte++;
					ucLength = *pucByte;
					pucByte++;

					switch( ucOptionCode )
					{
						case dhcpMESSAGE_TYPE_OPTION_CODE	:

							if( *pucByte == ucExpectedMessageType )
							{
								/* The message type is the message type the
								state machine is expecting. */
								ulProcessed++;
							}
							else if( *pucByte == dhcpMESSAGE_TYPE_NACK )
							{
								if( ucExpectedMessageType == dhcpMESSAGE_TYPE_ACK )
								{
									/* Start again. */
									eDHCPState = eWaitingSendFirstDiscover;
								}
							}
							else
							{
								/* Don't process other message types. */
							}
							break;

						case dhcpSUBNET_MASK_OPTION_CODE :

							if( ucLength == sizeof( uint32_t ) )
							{
								memcpy( ( void * ) &( pxNetworkAddressing->ulNetMask ), ( void * ) pucByte, ( size_t ) ucLength );
							}
							break;

						case dhcpGATEWAY_OPTION_CODE :

							if( ucLength == sizeof( uint32_t ) )
							{
								/* ulProcessed is not incremented in this case
								because the gateway is not essential. */
								memcpy( ( void * ) &( pxNetworkAddressing->ulGatewayAddress ), ( void * ) pucByte, ( size_t ) ucLength );
							}
							break;

						case hdcpDNS_SERVER_OPTIONS_CODE :

							/* ulProcessed is not incremented in this case
							because the DNS server is not essential.  Only the
							first DNS server address is taken. */
							memcpy( ( void * ) &( pxNetworkAddressing->ulDNSServerAddress ), ( void * ) pucByte, sizeof( uint32_t ) );
							break;

						case dhcpSERVER_IP_ADDRESS_OPTION_CODE :

							if( ucLength == sizeof( uint32_t ) )
							{
								if( ucExpectedMessageType == dhcpMESSAGE_TYPE_OFFER )
								{
									/* Offers state the replying server. */
									ulProcessed++;
									memcpy( ( void * ) &ulDHCPServerAddress, ( void * ) pucByte, ( size_t ) ucLength );
								}
								else
								{
									/* The ack must come from the expected server. */
									if( memcmp( ( void * ) &ulDHCPServerAddress, ( void * ) pucByte, ( size_t ) ucLength ) == 0 )
									{
										ulProcessed++;
									}
								}
							}
							break;

						case dhcpLEASE_TIME_OPTION_CODE :

							if( ucLength == sizeof( &ulLeaseTime ) )
							{
								/* ulProcessed is not incremented in this case
								because the lease time is not essential. */
								memcpy( ( void * ) &ulLeaseTime, ( void * ) pucByte, ( size_t ) ucLength );
								ulLeaseTime = FreeRTOS_ntohl( ulLeaseTime );

								/* Convert the lease time to milliseconds
								(*1000) then ticks (/portTICK_RATE_MS). */
								ulLeaseTime *= ( 1000UL / portTICK_RATE_MS );

								/* Divide the lease time to ensure a renew
								request is sent before the lease actually
								expires. */
								ulLeaseTime >>= 1UL;
							}
							break;

						default :

							/* Not interested in this field. */

							break;
					}

					/* Jump over the data to find the next option code. */
					if( ucLength == 0 )
					{
						break;
					}
					else
					{
						pucByte += ucLength;
					}
				}

				/* Were all the mandatory options received? */
				if( ulProcessed == ulMandatoryOptions )
				{
					ulOfferedIPAddress = pxDHCPMessage->ulYourIPAddress_yiaddr;
					xReturn = pdPASS;
				}
			}
		}

		FreeRTOS_ReleaseUDPPayloadBuffer( ( void * ) pucUDPPayload );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static uint8_t *prvCreatePartDHCPMessage( struct freertos_sockaddr *pxAddress, xMACAddress_t *pxMACAddress, uint8_t ucOpcode, const uint8_t * const pucOptionsArray, size_t xOptionsArraySize )
{
xDHCPMessage_t *pxDHCPMessage;
const size_t xRequiredBufferSize = sizeof( xDHCPMessage_t ) + xOptionsArraySize;
uint8_t *pucUDPPayloadBuffer;

	/* Get a buffer.  This uses a maximum delay, but the delay will be capped
	to ipconfigMAX_SEND_BLOCK_TIME_TICKS so the return value still needs to be
	test. */
	do
	{
	}while( ( pucUDPPayloadBuffer = ( uint8_t * ) FreeRTOS_GetUDPPayloadBuffer( xRequiredBufferSize, portMAX_DELAY ) ) == NULL );

	pxDHCPMessage = ( xDHCPMessage_t * ) pucUDPPayloadBuffer;

	/* Most fields need to be zero. */
	memset( ( void * ) pxDHCPMessage, 0x00, sizeof( xDHCPMessage_t ) );

	/* Create the message. */
	pxDHCPMessage->ucOpcode = ucOpcode;
	pxDHCPMessage->ucAddressType = dhcpADDRESS_TYPE_ETHERNET;
	pxDHCPMessage->ucAddressLength = dhcpETHERNET_ADDRESS_LENGTH;
	pxDHCPMessage->ulTransactionID = ulTransactionId;
	pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;
	pxDHCPMessage->usFlags = dhcpBROADCAST;
	memcpy( ( void * ) &( pxDHCPMessage->ucClientHardwareAddress[ 0 ] ), ( void * ) pxMACAddress, sizeof( xMACAddress_t ) );

	/* Copy in the const part of the options options. */
	memcpy( ( void * ) &( pucUDPPayloadBuffer[ dhcpFIRST_OPTION_BYTE_OFFSET ] ), ( void * ) pucOptionsArray, xOptionsArraySize );

	/* Map in the client identifier. */
	memcpy( ( void * ) &( pucUDPPayloadBuffer[ dhcpFIRST_OPTION_BYTE_OFFSET + dhcpCLIENT_IDENTIFIER_OFFSET ] ), ( void * ) pxMACAddress, sizeof( xMACAddress_t ) );

	/* Set the addressing. */
	pxAddress->sin_addr = ipBROADCAST_IP_ADDRESS;
	pxAddress->sin_port = ( uint16_t ) dhcpSERVER_PORT;

	return pucUDPPayloadBuffer;
}
/*-----------------------------------------------------------*/

static void prvSendDHCPRequest( xMACAddress_t *pxMACAddress )
{
uint8_t *pucUDPPayloadBuffer;
struct freertos_sockaddr xAddress;
static const uint8_t ucDHCPRequestOptions[] =
{
	/* Do not change the ordering without also changing
	dhcpCLIENT_IDENTIFIER_OFFSET, dhcpREQUESTED_IP_ADDRESS_OFFSET and
	dhcpDHCP_SERVER_IP_ADDRESS_OFFSET. */
	dhcpMESSAGE_TYPE_OPTION_CODE, 1, dhcpMESSAGE_TYPE_REQUEST,		/* Message type option. */
	dhcpCLIENT_IDENTIFIER_OPTION_CODE, 6, 0, 0, 0, 0, 0, 0,			/* Client identifier. */
	dhcpREQUEST_IP_ADDRESS_OPTION_CODE, 4, 0, 0, 0, 0,				/* The IP address being requested. */
	dhcpSERVER_IP_ADDRESS_OPTION_CODE, 4, 0, 0, 0, 0,				/* The IP address of the DHCP server. */
	dhcpOPTION_END_BYTE
};

	pucUDPPayloadBuffer = prvCreatePartDHCPMessage( &xAddress, pxMACAddress, dhcpREQUEST_OPCODE, ucDHCPRequestOptions, sizeof( ucDHCPRequestOptions ) );

	/* Copy in the IP address being requested. */
	memcpy( ( void * ) &( pucUDPPayloadBuffer[ dhcpFIRST_OPTION_BYTE_OFFSET + dhcpREQUESTED_IP_ADDRESS_OFFSET ] ), ( void * ) &ulOfferedIPAddress, sizeof( ulOfferedIPAddress ) );

	/* Copy in the address of the DHCP server being used. */
	memcpy( ( void * ) &( pucUDPPayloadBuffer[ dhcpFIRST_OPTION_BYTE_OFFSET + dhcpDHCP_SERVER_IP_ADDRESS_OFFSET ] ), ( void * ) &ulDHCPServerAddress, sizeof( ulDHCPServerAddress ) );

	iptraceSENDING_DHCP_REQUEST();
	if( FreeRTOS_sendto( xDHCPSocket, pucUDPPayloadBuffer, ( sizeof( xDHCPMessage_t ) + sizeof( ucDHCPRequestOptions ) ), FREERTOS_ZERO_COPY, &xAddress, sizeof( xAddress ) ) == 0 )
	{
		/* The packet was not successfully queued for sending and must be
		returned to the stack. */
		FreeRTOS_ReleaseUDPPayloadBuffer( pucUDPPayloadBuffer );
	}
}
/*-----------------------------------------------------------*/

static void prvSendDHCPDiscover( xMACAddress_t *pxMACAddress )
{
uint8_t *pucUDPPayloadBuffer;
struct freertos_sockaddr xAddress;
static const uint8_t ucDHCPDiscoverOptions[] =
{
	/* Do not change the ordering without also changing dhcpCLIENT_IDENTIFIER_OFFSET. */
	dhcpMESSAGE_TYPE_OPTION_CODE, 1, dhcpMESSAGE_TYPE_DISCOVER,					/* Message type option. */
	dhcpCLIENT_IDENTIFIER_OPTION_CODE, 6, 0, 0, 0, 0, 0, 0,						/* Client identifier. */
	dhcpPARAMETER_REQUEST_OPTION_CODE, 3, dhcpSUBNET_MASK_OPTION_CODE, dhcpGATEWAY_OPTION_CODE, hdcpDNS_SERVER_OPTIONS_CODE,	/* Parameter request option. */
	dhcpOPTION_END_BYTE
};

	pucUDPPayloadBuffer = prvCreatePartDHCPMessage( &xAddress, pxMACAddress, dhcpREQUEST_OPCODE, ucDHCPDiscoverOptions, sizeof( ucDHCPDiscoverOptions ) );

	iptraceSENDING_DHCP_DISCOVER();
	if( FreeRTOS_sendto( xDHCPSocket, pucUDPPayloadBuffer, ( sizeof( xDHCPMessage_t ) + sizeof( ucDHCPDiscoverOptions ) ), FREERTOS_ZERO_COPY, &xAddress, sizeof( xAddress ) ) == 0 )
	{
		/* The packet was not successfully queued for sending and must be
		returned to the stack. */
		FreeRTOS_ReleaseUDPPayloadBuffer( pucUDPPayloadBuffer );
	}
}
/*-----------------------------------------------------------*/

#endif /* ipconfigUSE_DHCP != 0 */


