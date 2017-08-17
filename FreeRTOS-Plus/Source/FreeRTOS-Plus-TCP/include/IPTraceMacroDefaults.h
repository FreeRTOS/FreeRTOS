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

/* This file provides default (empty) implementations for any IP trace macros
that are not defined by the user.  See
http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Trace.html */

#ifndef UDP_TRACE_MACRO_DEFAULTS_H
#define UDP_TRACE_MACRO_DEFAULTS_H

#ifndef iptraceNETWORK_DOWN
	#define iptraceNETWORK_DOWN()
#endif

#ifndef iptraceNETWORK_BUFFER_RELEASED
	#define iptraceNETWORK_BUFFER_RELEASED( pxBufferAddress )
#endif

#ifndef iptraceNETWORK_BUFFER_OBTAINED
	#define iptraceNETWORK_BUFFER_OBTAINED( pxBufferAddress )
#endif

#ifndef iptraceNETWORK_BUFFER_OBTAINED_FROM_ISR
	#define iptraceNETWORK_BUFFER_OBTAINED_FROM_ISR( pxBufferAddress )
#endif

#ifndef iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER
	#define iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER()
#endif

#ifndef iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER_FROM_ISR
	#define iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER_FROM_ISR()
#endif

#ifndef iptraceCREATING_ARP_REQUEST
	#define iptraceCREATING_ARP_REQUEST( ulIPAddress )
#endif

#ifndef iptraceARP_TABLE_ENTRY_WILL_EXPIRE
	#define iptraceARP_TABLE_ENTRY_WILL_EXPIRE( ulIPAddress )
#endif

#ifndef iptraceARP_TABLE_ENTRY_EXPIRED
	#define iptraceARP_TABLE_ENTRY_EXPIRED( ulIPAddress )
#endif

#ifndef iptraceARP_TABLE_ENTRY_CREATED
	#define iptraceARP_TABLE_ENTRY_CREATED( ulIPAddress, ucMACAddress )
#endif

#ifndef iptraceSENDING_UDP_PACKET
	#define iptraceSENDING_UDP_PACKET( ulIPAddress )
#endif

#ifndef iptracePACKET_DROPPED_TO_GENERATE_ARP
	#define iptracePACKET_DROPPED_TO_GENERATE_ARP( ulIPAddress )
#endif

#ifndef iptraceICMP_PACKET_RECEIVED
	#define iptraceICMP_PACKET_RECEIVED()
#endif

#ifndef iptraceSENDING_PING_REPLY
	#define iptraceSENDING_PING_REPLY( ulIPAddress )
#endif

#ifndef traceARP_PACKET_RECEIVED
	#define traceARP_PACKET_RECEIVED()
#endif

#ifndef iptracePROCESSING_RECEIVED_ARP_REPLY
	#define iptracePROCESSING_RECEIVED_ARP_REPLY( ulIPAddress )
#endif

#ifndef iptraceSENDING_ARP_REPLY
	#define iptraceSENDING_ARP_REPLY( ulIPAddress )
#endif

#ifndef iptraceFAILED_TO_CREATE_SOCKET
	#define iptraceFAILED_TO_CREATE_SOCKET()
#endif

#ifndef iptraceFAILED_TO_CREATE_EVENT_GROUP
	#define iptraceFAILED_TO_CREATE_EVENT_GROUP()
#endif

#ifndef iptraceRECVFROM_DISCARDING_BYTES
	#define iptraceRECVFROM_DISCARDING_BYTES( xNumberOfBytesDiscarded )
#endif

#ifndef iptraceETHERNET_RX_EVENT_LOST
	#define iptraceETHERNET_RX_EVENT_LOST()
#endif

#ifndef iptraceSTACK_TX_EVENT_LOST
	#define iptraceSTACK_TX_EVENT_LOST( xEvent )
#endif

#ifndef iptraceNETWORK_EVENT_RECEIVED
	#define iptraceNETWORK_EVENT_RECEIVED( eEvent )
#endif

#ifndef iptraceBIND_FAILED
	#define iptraceBIND_FAILED( xSocket, usPort )
#endif

#ifndef iptraceDHCP_REQUESTS_FAILED_USING_DEFAULT_IP_ADDRESS
	#define iptraceDHCP_REQUESTS_FAILED_USING_DEFAULT_IP_ADDRESS( ulIPAddress )
#endif

#ifndef iptraceSENDING_DHCP_DISCOVER
	#define iptraceSENDING_DHCP_DISCOVER()
#endif

#ifndef iptraceSENDING_DHCP_REQUEST
	#define iptraceSENDING_DHCP_REQUEST()
#endif

#ifndef iptraceDHCP_SUCCEDEED
	#define iptraceDHCP_SUCCEDEED( address )
#endif

#ifndef iptraceNETWORK_INTERFACE_TRANSMIT
	#define iptraceNETWORK_INTERFACE_TRANSMIT()
#endif

#ifndef iptraceNETWORK_INTERFACE_RECEIVE
	#define iptraceNETWORK_INTERFACE_RECEIVE()
#endif

#ifndef iptraceSENDING_DNS_REQUEST
	#define iptraceSENDING_DNS_REQUEST()
#endif

#ifndef	iptraceWAITING_FOR_TX_DMA_DESCRIPTOR
	#define iptraceWAITING_FOR_TX_DMA_DESCRIPTOR()
#endif

#ifndef ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS
	#define ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS 0
#endif

#ifndef iptraceFAILED_TO_NOTIFY_SELECT_GROUP
	#define iptraceFAILED_TO_NOTIFY_SELECT_GROUP( xSocket )
#endif

#ifndef pvPortMallocSocket
	#define pvPortMallocSocket(xSize) pvPortMalloc( ( xSize ) )
#endif

#ifndef iptraceRECVFROM_TIMEOUT
	#define iptraceRECVFROM_TIMEOUT()
#endif

#ifndef iptraceRECVFROM_INTERRUPTED
	#define iptraceRECVFROM_INTERRUPTED()
#endif

#ifndef iptraceNO_BUFFER_FOR_SENDTO
	#define iptraceNO_BUFFER_FOR_SENDTO()
#endif

#ifndef iptraceSENDTO_SOCKET_NOT_BOUND
	#define iptraceSENDTO_SOCKET_NOT_BOUND()
#endif

#ifndef iptraceSENDTO_DATA_TOO_LONG
	#define iptraceSENDTO_DATA_TOO_LONG()
#endif

#endif /* UDP_TRACE_MACRO_DEFAULTS_H */
