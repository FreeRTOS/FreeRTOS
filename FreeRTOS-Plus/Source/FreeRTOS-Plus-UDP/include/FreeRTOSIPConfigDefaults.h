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

#ifndef FREERTOS_DEFAULT_IP_CONFIG_H
#define FREERTOS_DEFAULT_IP_CONFIG_H

/* This file provides default values for configuration options that are missing
from the FreeRTOSIPConfig.h configuration header file. */

#ifndef ipconfigUSE_NETWORK_EVENT_HOOK
	#define ipconfigUSE_NETWORK_EVENT_HOOK 0
#endif

#ifndef ipconfigMAX_SEND_BLOCK_TIME_TICKS
	#define ipconfigMAX_SEND_BLOCK_TIME_TICKS ( 20 / portTICK_RATE_MS )
#endif

#ifndef ipconfigARP_CACHE_ENTRIES
	#define ipconfigARP_CACHE_ENTRIES		10
#endif

#ifndef ipconfigMAX_ARP_RETRANSMISSIONS
	#define ipconfigMAX_ARP_RETRANSMISSIONS ( 5 )
#endif

#ifndef ipconfigMAX_ARP_AGE
	#define ipconfigMAX_ARP_AGE			150
#endif

#ifndef ipconfigINCLUDE_FULL_INET_ADDR
	#define ipconfigINCLUDE_FULL_INET_ADDR	1
#endif

#ifndef ipconfigNUM_NETWORK_BUFFERS
	#define ipconfigNUM_NETWORK_BUFFERS		45
#endif

#ifndef ipconfigEVENT_QUEUE_LENGTH
	#define ipconfigEVENT_QUEUE_LENGTH		( ipconfigNUM_NETWORK_BUFFERS + 5 )
#endif

#ifndef ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND
	#define ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND 1
#endif

#ifndef updconfigIP_TIME_TO_LIVE
	#define updconfigIP_TIME_TO_LIVE		128
#endif

#ifndef ipconfigCAN_FRAGMENT_OUTGOING_PACKETS
	#define ipconfigCAN_FRAGMENT_OUTGOING_PACKETS 0
#endif

#ifndef ipconfigNETWORK_MTU
	#define ipconfigNETWORK_MTU 1500
#endif

#ifndef ipconfigUSE_DHCP
	#define ipconfigUSE_DHCP	1
#endif

#ifndef ipconfigMAXIMUM_DISCOVER_TX_PERIOD
	#ifdef _WINDOWS_
		#define ipconfigMAXIMUM_DISCOVER_TX_PERIOD		( 999 / portTICK_RATE_MS )
	#else
		#define ipconfigMAXIMUM_DISCOVER_TX_PERIOD		( 30000 / portTICK_RATE_MS )
	#endif /* _WINDOWS_ */
#endif /* ipconfigMAXIMUM_DISCOVER_TX_PERIOD */

#ifndef ipconfigUSE_DNS
	#define ipconfigUSE_DNS		1
#endif

#ifndef ipconfigREPLY_TO_INCOMING_PINGS
	#define ipconfigREPLY_TO_INCOMING_PINGS				1
#endif

#ifndef ipconfigSUPPORT_OUTGOING_PINGS
	#define ipconfigSUPPORT_OUTGOING_PINGS				0
#endif

#ifndef updconfigLOOPBACK_ETHERNET_PACKETS
	#define updconfigLOOPBACK_ETHERNET_PACKETS	0
#endif

#ifndef ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES
	#define ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES 1
#endif

#ifndef ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES
	#define ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES	1
#endif

#ifndef configINCLUDE_TRACE_RELATED_CLI_COMMANDS
	#define ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS 0
#else
	#define ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS configINCLUDE_TRACE_RELATED_CLI_COMMANDS
#endif

#ifndef ipconfigFREERTOS_PLUS_NABTO
	#define ipconfigFREERTOS_PLUS_NABTO 0
#endif

#ifndef ipconfigNABTO_TASK_STACK_SIZE
	#define ipconfigNABTO_TASK_STACK_SIZE ( configMINIMAL_STACK_SIZE * 2 )
#endif

#ifndef ipconfigNABTO_TASK_PRIORITY
	#define ipconfigNABTO_TASK_PRIORITY	 ( ipconfigUDP_TASK_PRIORITY + 1 )
#endif

#ifndef ipconfigSUPPORT_SELECT_FUNCTION
	#define ipconfigSUPPORT_SELECT_FUNCTION 0
#endif

#endif /* FREERTOS_DEFAULT_IP_CONFIG_H */
