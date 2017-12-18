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

#ifndef FREERTOS_IP_PRIVATE_H
#define FREERTOS_IP_PRIVATE_H

/* Application level configuration options. */
#include "FreeRTOSIPConfig.h"
#include "IPTraceMacroDefaults.h"

typedef struct xNetworkAddressingParameters
{
	uint32_t ulDefaultIPAddress;
	uint32_t ulNetMask;
	uint32_t ulGatewayAddress;
	uint32_t ulDNSServerAddress;
} xNetworkAddressingParameters_t;


/*-----------------------------------------------------------*/
/* Protocol headers.                                         */
/*-----------------------------------------------------------*/

#include "pack_struct_start.h"
struct xETH_HEADER
{
	xMACAddress_t xDestinationAddress;
	xMACAddress_t xSourceAddress;
	uint16_t usFrameType;
}
#include "pack_struct_end.h"
typedef struct xETH_HEADER xEthernetHeader_t;

#include "pack_struct_start.h"
struct xARP_HEADER
{
	uint16_t usHardwareType;
	uint16_t usProtocolType;
	uint8_t ucHardwareAddressLength;
	uint8_t ucProtocolAddressLength;
	uint16_t usOperation;
	xMACAddress_t xSenderHardwareAddress;
	uint32_t ulSenderProtocolAddress;
	xMACAddress_t xTargetHardwareAddress;
	uint32_t ulTargetProtocolAddress;
}
#include "pack_struct_end.h"
typedef struct xARP_HEADER xARPHeader_t;

#include "pack_struct_start.h"
struct xIP_HEADER
{
	uint8_t ucVersionHeaderLength;
	uint8_t ucDifferentiatedServicesCode;
	uint16_t usLength;
	uint16_t usIdentification;
	uint16_t usFragmentOffset;
	uint8_t ucTimeToLive;
	uint8_t ucProtocol;
	uint16_t usHeaderChecksum;
	uint32_t ulSourceIPAddress;
	uint32_t ulDestinationIPAddress;
}
#include "pack_struct_end.h"
typedef struct xIP_HEADER xIPHeader_t;
#define ipSIZE_OF_IP_HEADER 20

#include "pack_struct_start.h"
struct xICMP_HEADER
{
	uint8_t ucTypeOfMessage;
	uint8_t ucTypeOfService;
	uint16_t usChecksum;
	uint16_t usIdentifier;
	uint16_t usSequenceNumber;
}
#include "pack_struct_end.h"
typedef struct xICMP_HEADER xICMPHeader_t;

#include "pack_struct_start.h"
struct xUDP_HEADER
{
	uint16_t usSourcePort;
	uint16_t usDestinationPort;
	uint16_t usLength;
	uint16_t usChecksum;
}
#include "pack_struct_end.h"
typedef struct xUDP_HEADER xUDPHeader_t;
#define ipSIZE_OF_UDP_HEADER 8

#include "pack_struct_start.h"
struct xPSEUDO_HEADER
{
	uint32_t ulSourceAddress;
	uint32_t ulDestinationAddress;
	uint8_t ucZeros;
	uint8_t ucProtocol;
	uint16_t usUDPLength;
}
#include "pack_struct_end.h"
typedef struct xPSEUDO_HEADER xPseudoHeader_t;

/*-----------------------------------------------------------*/
/* Nested protocol packets.                                  */
/*-----------------------------------------------------------*/

#include "pack_struct_start.h"
struct xARP_PACKET
{
	xEthernetHeader_t xEthernetHeader;
	xARPHeader_t xARPHeader;
}
#include "pack_struct_end.h"
typedef struct xARP_PACKET xARPPacket_t;

#include "pack_struct_start.h"
struct xIP_PACKET
{
	xEthernetHeader_t xEthernetHeader;
	xIPHeader_t xIPHeader;
}
#include "pack_struct_end.h"
typedef struct xIP_PACKET xIPPacket_t;

#include "pack_struct_start.h"
struct xICMP_PACKET
{
	xEthernetHeader_t xEthernetHeader;
	xIPHeader_t xIPHeader;
	xICMPHeader_t xICMPHeader;
}
#include "pack_struct_end.h"
typedef struct xICMP_PACKET xICMPPacket_t;

#include "pack_struct_start.h"
struct xUDP_PACKET
{
	xEthernetHeader_t xEthernetHeader;
	xIPHeader_t xIPHeader;
	xUDPHeader_t xUDPHeader;
}
#include "pack_struct_end.h"
typedef struct xUDP_PACKET xUDPPacket_t;

/* Dimensions the buffers that are filled by received Ethernet frames. */
#define ipETHERNET_CRC_BYTES					( 4UL )
#define ipETHERNET_OPTIONAL_802_1Q_TAG_BYTES	( 4UL )
#define ipTOTAL_ETHERNET_FRAME_SIZE				( ipconfigNETWORK_MTU + sizeof( xEthernetHeader_t ) + ipETHERNET_CRC_BYTES + ipETHERNET_OPTIONAL_802_1Q_TAG_BYTES )

/* The maximum UDP payload length. */
#define ipMAX_UDP_PAYLOAD_LENGTH ( ( ipconfigNETWORK_MTU - ipSIZE_OF_IP_HEADER ) - ipSIZE_OF_UDP_HEADER )

typedef enum
{
	eReleaseBuffer = 0,		/* Processing the frame did not find anything to do - just release the buffer. */
	eProcessBuffer,			/* An Ethernet frame has a valid address - continue process its contents. */
	eReturnEthernetFrame,	/* The Ethernet frame contains an ARP or ICMP packet that can be returned to its source. */
	eFrameConsumed			/* Processing the Ethernet packet contents resulted in the payload being sent to the stack. */
} eFrameProcessingResult_t;

typedef enum
{
	eNetworkDownEvent = 0,	/* The network interface has been lost and/or needs [re]connecting. */
	eEthernetRxEvent,	/* The network interface has queued a received Ethernet frame. */
	eARPTimerEvent,		/* The ARP timer expired. */
	eStackTxEvent,		/* The software stack has queued a packet to transmit. */
	eDHCPEvent			/* Process the DHCP state machine. */
} eIPEvent_t;

typedef struct IP_TASK_COMMANDS
{
	eIPEvent_t eEventType;
	void *pvData;
} xIPStackEvent_t;

#define ipBROADCAST_IP_ADDRESS 0xffffffffUL

/* Offset into the Ethernet frame that is used to temporarily store information
on the fragmentation status of the packet being sent.  The value is important,
as it is past the location into which the destination address will get placed. */
#define ipFRAGMENTATION_PARAMETERS_OFFSET		( 6 )
#define ipSOCKET_OPTIONS_OFFSET					( 6 )

/* Only used when outgoing fragmentation is being used (FreeRTOSIPConfig.h
setting. */
#define ipGET_UDP_PAYLOAD_OFFSET_FOR_FRAGMENT( usFragmentOffset ) ( ( ( usFragmentOffset ) == 0 ) ? ipUDP_PAYLOAD_OFFSET : ipIP_PAYLOAD_OFFSET )

/* The offset into a UDP packet at which the UDP data (payload) starts. */
#define ipUDP_PAYLOAD_OFFSET	( sizeof( xUDPPacket_t ) )

/* The offset into an IP packet into which the IP data (payload) starts. */
#define ipIP_PAYLOAD_OFFSET		( sizeof( xIPPacket_t ) )

/* Space left at the beginning of a network buffer storage area to store a
pointer back to the network buffer.  Should be a multiple of 8 to ensure
8 byte alignment is maintained on architectures that require it. */
#define ipBUFFER_PADDING		( 8 )

#include "pack_struct_start.h"
struct xUDP_IP_FRACMENT_PARAMETERS
{
	uint8_t ucSocketOptions;
	uint8_t ucPadFor16BitAlignment;
	uint16_t usFragmentedPacketOffset;
	uint16_t usFragmentLength;
	uint16_t usPayloadChecksum;
}
#include "pack_struct_end.h"
typedef struct xUDP_IP_FRACMENT_PARAMETERS xIPFragmentParameters_t;

#if( ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN )

	/* Ethernet frame types. */
	#define ipARP_TYPE	( 0x0608U )
	#define ipIP_TYPE	( 0x0008U )

	/* ARP related definitions. */
	#define ipARP_PROTOCOL_TYPE ( 0x0008U )
	#define ipARP_HARDWARE_TYPE_ETHERNET ( 0x0100U )
	#define ipARP_REQUEST ( 0x0100 )
	#define ipARP_REPLY ( 0x0200 )

#else

	/* Ethernet frame types. */
	#define ipARP_TYPE	( 0x0806U )
	#define ipIP_TYPE	( 0x0800U )

	/* ARP related definitions. */
	#define ipARP_PROTOCOL_TYPE ( 0x0800U )
	#define ipARP_HARDWARE_TYPE_ETHERNET ( 0x0001U )
	#define ipARP_REQUEST ( 0x0001 )
	#define ipARP_REPLY ( 0x0002 )

#endif /* ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN */

/* The structure used to store buffers and pass them around the network stack.
Buffers can be in use by the stack, in use by the network interface hardware
driver, or free (not in use). */
typedef struct xNETWORK_BUFFER
{
	xListItem xBufferListItem; 		/* Used to reference the buffer form the free buffer list or a socket. */
	uint32_t ulIPAddress;			/* Source or destination IP address, depending on usage scenario. */
	uint8_t *pucEthernetBuffer; 	/* Pointer to the start of the Ethernet frame. */
	size_t xDataLength; 			/* Starts by holding the total Ethernet frame length, then the UDP payload length. */
	uint16_t usPort;				/* Source or destination port, depending on usage scenario. */
	uint16_t usBoundPort;			/* The port to which a transmitting socket is bound. */
} xNetworkBufferDescriptor_t;

void vNetworkBufferRelease( xNetworkBufferDescriptor_t * const pxNetworkBuffer );

/*
 * A version of FreeRTOS_GetReleaseNetworkBuffer() that can be called from an
 * interrupt.  If a non zero value is returned, then the calling ISR should
 * perform a context switch before exiting the ISR.
 */
BaseType_t FreeRTOS_ReleaseFreeNetworkBufferFromISR( void );

/*
 * Create a message that contains a command to initialise the network interface.
 * This is used during initialisation, and at any time the network interface
 * goes down thereafter.  The network interface hardware driver is responsible
 * for sending the message that contains the network interface down command/
 * event.
 *
 * Only use the FreeRTOS_NetworkDownFromISR() version if the function is to be
 * called from an interrupt service routine.  If FreeRTOS_NetworkDownFromISR()
 * returns a non-zero value then a context switch should be performed ebfore
 * the interrupt is exited.
 */
void FreeRTOS_NetworkDown( void );
BaseType_t FreeRTOS_NetworkDownFromISR( void );

/*
 * Inspect an Ethernet frame to see if it contains data that the stack needs to
 * process.  eProcessBuffer is returned if the frame should be processed by the
 * stack.  eReleaseBuffer is returned if the frame should be discarded.
 */
eFrameProcessingResult_t eConsiderFrameForProcessing( const uint8_t * const pucEthernetBuffer );

#if( ipconfigINCLUDE_TEST_CODE == 1 )
	UBaseType_t uxGetNumberOfFreeNetworkBuffers( void );
#endif /* ipconfigINCLUDE_TEST_CODE */

/* Socket related private functions. */
BaseType_t xProcessReceivedUDPPacket( xNetworkBufferDescriptor_t *pxNetworkBuffer, uint16_t usPort );
void FreeRTOS_SocketsInit( void );

/* If FreeRTOS+NABTO is included then include the prototype of the function that
creates the Nabto task. */
#if( ipconfigFREERTOS_PLUS_NABTO == 1 )
	void vStartNabtoTask( void );
#endif


#endif /* FREERTOS_IP_PRIVATE_H */













