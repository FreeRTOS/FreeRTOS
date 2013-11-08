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

/* This file provides default (empty) implementations for any IP trace macros
that are not defined by the user.  See
http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/UDP_IP_Trace.shtml */

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

#ifndef iptraceRECVFROM_TIMEOUT
	#define iptraceRECVFROM_TIMEOUT()
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
