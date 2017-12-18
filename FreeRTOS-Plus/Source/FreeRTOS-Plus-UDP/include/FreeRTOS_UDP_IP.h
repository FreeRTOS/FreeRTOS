/*
 * FreeRTOS+UDP V1.0.4
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

#ifndef FREERTOS_IP_H
#define FREERTOS_IP_H

/* Use in FreeRTOSIPConfig.h. */
#define FREERTOS_LITTLE_ENDIAN	0
#define FREERTOS_BIG_ENDIAN		1

/* Application level configuration options. */
#include "FreeRTOSIPConfig.h"
#include "FreeRTOSIPConfigDefaults.h"
#include "IPTraceMacroDefaults.h"

/* The number of octets in the MAC and IP addresses respectively. */
#define ipMAC_ADDRESS_LENGTH_BYTES ( 6 )
#define ipIP_ADDRESS_LENGTH_BYTES ( 4 )

#include "pack_struct_start.h"
struct xMAC_ADDRESS
{
	uint8_t ucBytes[ ipMAC_ADDRESS_LENGTH_BYTES ];
}
#include "pack_struct_end.h"
typedef struct xMAC_ADDRESS xMACAddress_t;

typedef enum eNETWORK_EVENTS
{
	eNetworkUp,		/* The network is configured. */
	eNetworkDown	/* The network connection has been lost. */
} eIPCallbackEvent_t;

typedef enum ePING_REPLY_STATUS
{
	eSuccess = 0,		/* A correct reply has been received for an outgoing ping. */
	eInvalidChecksum,	/* A reply was received for an outgoing ping but the checksum of the reply was incorrect. */
	eInvalidData		/* A reply was received to an outgoing ping but the payload of the reply was not correct. */
} ePingReplyStatus_t;

/* Endian related definitions. */
#if( ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN )

	uint16_t FreeRTOS_htons( uint16_t usIn );
	uint32_t FreeRTOS_htonl( uint32_t ulIn );

#else

	#define FreeRTOS_htons( x ) ( x )
	#define FreeRTOS_htonl( x ) ( x )

#endif /* ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN */

#define FreeRTOS_ntohs( x ) FreeRTOS_htons( x )
#define FreeRTOS_ntohl( x ) FreeRTOS_htonl( x )

/**
 * FULL, UP-TO-DATE AND MAINTAINED REFERENCE DOCUMENTATION FOR ALL THESE
 * FUNCTIONS IS AVAILABLE ON THE FOLLOWING URL:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/FreeRTOS_UDP_API_Functions.shtml
 */
BaseType_t FreeRTOS_IPInit( const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ], const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ], const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ], const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ], const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] );
void * FreeRTOS_GetUDPPayloadBuffer( size_t xRequestedSizeBytes, TickType_t xBlockTimeTicks );
void FreeRTOS_GetAddressConfiguration( uint32_t *pulIPAddress, uint32_t *pulNetMask, uint32_t *pulGatewayAddress, uint32_t *pulDNSServerAddress );
BaseType_t FreeRTOS_SendPingRequest( uint32_t ulIPAddress, size_t xNumberOfBytesToSend, TickType_t xBlockTimeTicks );
void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent );
void vApplicationPingReplyHook( ePingReplyStatus_t eStatus, uint16_t usIdentifier );
void FreeRTOS_ReleaseUDPPayloadBuffer( void *pvBuffer );
uint8_t * FreeRTOS_GetMACAddress( void );

#if ( ipconfigFREERTOS_PLUS_NABTO == 1 )
	BaseType_t xStartNabtoTask( void );
#endif

#endif /* FREERTOS_IP_H */













