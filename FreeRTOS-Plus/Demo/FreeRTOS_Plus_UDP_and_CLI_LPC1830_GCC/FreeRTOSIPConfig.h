/*
 * FreeRTOS+UDP V1.0.1 (C) 2013 Real Time Engineers ltd.
 * All rights reserved
 *
 * FreeRTOS+UDP is an add-on component to FreeRTOS.  It is not, in itself, part
 * of the FreeRTOS kernel.  FreeRTOS+UDP is licensed separately from FreeRTOS,
 * and uses a different license to FreeRTOS.  FreeRTOS+UDP uses a dual license
 * model, information on which is provided below:
 *
 * - Open source licensing -
 * FreeRTOS+UDP is a free download and may be used, modified and distributed
 * without charge provided the user adheres to version two of the GNU General
 * Public license (GPL) and does not remove the copyright notice or this text.
 * The GPL V2 text is available on the gnu.org web site, and on the following
 * URL: http://www.FreeRTOS.org/gpl-2.0.txt
 *
 * - Commercial licensing -
 * Businesses and individuals who wish to incorporate FreeRTOS+UDP into
 * proprietary software for redistribution in any form must first obtain a
 * (very) low cost commercial license - and in-so-doing support the maintenance,
 * support and further development of the FreeRTOS+UDP product.  Commercial
 * licenses can be obtained from http://shop.freertos.org and do not require any
 * source files to be changed.
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
 * http://www.FreeRTOS.org/FreeRTOS-Plus
 *
 */

/*****************************************************************************
 *
 * See the following URL for configuration information.
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/UDP_IP_Configuration.shtml
 *
 *****************************************************************************/

#ifndef FREERTOS_IP_CONFIG_H
#define FREERTOS_IP_CONFIG_H

/* The IP stack executes it its own task (although any application task can make
use of its services through the published sockets API). ipconfigUDP_TASK_PRIORITY
sets the priority of the task that executes the IP stack.  The priority is a
standard FreeRTOS task priority so can take any value from 0 (the lowest
priority) to (configMAX_PRIORITIES - 1) (the highest priority).
configMAX_PRIORITIES is a standard FreeRTOS configuration parameter defined in
FreeRTOSConfig.h, not FreeRTOSIPConfig.h. Consideration needs to be given as to
the priority assigned to the task executing the IP stack relative to the
priority assigned to tasks that use the IP stack. */
#define ipconfigUDP_TASK_PRIORITY			( configMAX_PRIORITIES - 2 )

/* The size, in words (not bytes), of the stack allocated to the FreeRTOS+UDP
task.  This setting is less important when the FreeRTOS Win32 simulator is used
as the Win32 simulator only stores a fixed amount of information on the task
stack.  FreeRTOS includes optional stack overflow detection, see:
http://www.freertos.org/Stacks-and-stack-overflow-checking.html */
#define ipconfigUDP_TASK_STACK_SIZE_WORDS	( configMINIMAL_STACK_SIZE * 3 )

/* ipconfigRAND32() is called by the IP stack to generate a random number that
is then used as a DHCP transaction number.  Random number generation is performed
via this macro to allow applications to use their own random number generation
method.  For example, it might be possible to generate a random number by
sampling noise on an analogue input. */
#define ipconfigRAND32()	1

/* If ipconfigUSE_NETWORK_EVENT_HOOK is set to 1 then FreeRTOS+UDP will call the
network event hook at the appropriate times.  If ipconfigUSE_NETWORK_EVENT_HOOK
is not set to 1 then the network event hook will never be called.  See
http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/API/vApplicationIPNetworkEventHook.shtml
*/
#define ipconfigUSE_NETWORK_EVENT_HOOK 1

/* Sockets have a send block time attribute.  If FreeRTOS_sendto() is called but
a network buffer cannot be obtained then the calling task is held in the Blocked
state (so other tasks can continue to executed) until either a network buffer
becomes available or the send block time expires.  If the send block time expires
then the send operation is aborted.  The maximum allowable send block time is
capped to the value set by ipconfigMAX_SEND_BLOCK_TIME_TICKS.  Capping the
maximum allowable send block time prevents prevents a deadlock occurring when
all the network buffers are in use and the tasks that process (and subsequently
free) the network buffers are themselves blocked waiting for a network buffer.
ipconfigMAX_SEND_BLOCK_TIME_TICKS is specified in RTOS ticks.  A time in
milliseconds can be converted to a time in ticks by dividing the time in
milliseconds by portTICK_RATE_MS. */
#define ipconfigMAX_SEND_BLOCK_TIME_TICKS ( 20 / portTICK_RATE_MS )

/* If ipconfigUSE_DHCP is 1 then FreeRTOS+UDP will attempt to retrieve an IP
address, netmask, DNS server address and gateway address from a DHCP server.  If
ipconfigUSE_DHCP is 0 then FreeRTOS+UDP will use a static IP address.  The
stack will revert to using the static IP address even when ipconfigUSE_DHCP is
set to 1 if a valid configuration cannot be obtained from a DHCP server for any
reason.  The static configuration used is that passed into the stack by the
FreeRTOS_IPInit() function call. */
#define ipconfigUSE_DHCP	1

/* When ipconfigUSE_DHCP is set to 1, DHCP requests will be sent out at
increasing time intervals until either a reply is received from a DHCP server
and accepted, or the interval between transmissions reaches
ipconfigMAXIMUM_DISCOVER_TX_PERIOD.  The IP stack will revert to using the
static IP address passed as a parameter to FreeRTOS_IPInit() if the
re-transmission time interval reaches ipconfigMAXIMUM_DISCOVER_TX_PERIOD without
a DHCP reply being received. */
#ifdef _WINDOWS_
	/* The windows simulated time is not real time so the max delay is much
	shorter. */
	#define ipconfigMAXIMUM_DISCOVER_TX_PERIOD		( 999 / portTICK_RATE_MS )
#else
	#define ipconfigMAXIMUM_DISCOVER_TX_PERIOD		( 120000 / portTICK_RATE_MS )
#endif /* _WINDOWS_ */

/* The ARP cache is a table that maps IP addresses to MAC addresses.  The IP
stack can only send a UDP message to a remove IP address if it knowns the MAC
address associated with the IP address, or the MAC address of the router used to
contact the remote IP address.  When a UDP message is received from a remote IP
address the MAC address and IP address are added to the ARP cache.  When a UDP
message is sent to a remote IP address that does not already appear in the ARP
cache then the UDP message is replaced by a ARP message that solicits the
required MAC address information.  ipconfigARP_CACHE_ENTRIES defines the maximum
number of entries that can exist in the ARP table at any one time. */
#define ipconfigARP_CACHE_ENTRIES		6

/* ARP requests that do not result in an ARP response will be re-transmitted a
maximum of ipconfigMAX_ARP_RETRANSMISSIONS times before the ARP request is
aborted. */
#define ipconfigMAX_ARP_RETRANSMISSIONS ( 5 )

/* ipconfigMAX_ARP_AGE defines the maximum time between an entry in the ARP
table being created or refreshed and the entry being removed because it is stale.
New ARP requests are sent for ARP cache entries that are nearing their maximum
age.  ipconfigMAX_ARP_AGE is specified in tens of seconds, so a value of 150 is
equal to 1500 seconds (or 25 minutes). */
#define ipconfigMAX_ARP_AGE			150

/* Implementing FreeRTOS_inet_addr() necessitates the use of string handling
routines, which are relatively large.  To save code space the full
FreeRTOS_inet_addr() implementation is made optional, and a smaller and faster
alternative called FreeRTOS_inet_addr_quick() is provided.  FreeRTOS_inet_addr()
takes an IP in decimal dot format (for example, "192.168.0.1") as its parameter.
FreeRTOS_inet_addr_quick() takes an IP address as four separate numerical octets
(for example, 192, 168, 0, 1) as its parameters.  If
ipconfigINCLUDE_FULL_INET_ADDR is set to 1 then both FreeRTOS_inet_addr() and
FreeRTOS_indet_addr_quick() are available.  If ipconfigINCLUDE_FULL_INET_ADDR is
not set to 1 then only FreeRTOS_indet_addr_quick() is available. */
#define ipconfigINCLUDE_FULL_INET_ADDR	1

/* ipconfigNUM_NETWORK_BUFFERS defines the total number of network buffer that
are available to the IP stack.  The total number of network buffers is limited
to ensure the total amount of RAM that can be consumed by the IP stack is capped
to a pre-determinable value. */
#define ipconfigNUM_NETWORK_BUFFERS		10

/* A FreeRTOS queue is used to send events from application tasks to the IP
stack.  ipconfigEVENT_QUEUE_LENGTH sets the maximum number of events that can
be queued for processing at any one time.  The event queue must be a minimum of
5 greater than the total number of network buffers. */
#define ipconfigEVENT_QUEUE_LENGTH		( ipconfigNUM_NETWORK_BUFFERS + 5 )

/* The address of a socket is the combination of its IP address and its port
number.  FreeRTOS_bind() is used to manually allocate a port number to a socket
(to 'bind' the socket to a port), but manual binding is not normally necessary
for client sockets (those sockets that initiate outgoing connections rather than
wait for incoming connections on a known port number).  If
ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND is set to 1 then calling
FreeRTOS_sendto() on a socket that has not yet been bound will result in the IP
stack automatically binding the socket to a port number from the range
socketAUTO_PORT_ALLOCATION_START_NUMBER to 0xffff.  If
ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND is set to 0 then calling FreeRTOS_sendto()
on a socket that has not yet been bound will result in the send operation being
aborted. */
#define ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND 1

/* Defines the Time To Live (TTL) values used in outgoing UDP packets. */
#define updconfigIP_TIME_TO_LIVE		128

/* If ipconfigCAN_FRAGMENT_OUTGOING_PACKETS is set to 1 then UDP packets that
contain more data than will fit in a single network frame will be fragmented
across multiple IP packets.  Also see the ipconfigNETWORK_MTU setting.  If
ipconfigCAN_FRAGMENT_OUTGOING_PACKETS is 1 then (ipconfigNETWORK_MTU - 28) must
be divisible by 8.  Setting ipconfigCAN_FRAGMENT_OUTGOING_PACKETS to 1 will
increase both the code size and execution time. */
#define ipconfigCAN_FRAGMENT_OUTGOING_PACKETS 0

/* The MTU is the maximum number of bytes the payload of a network frame can
contain.  For normal Ethernet V2 frames the maximum MTU is 1500.  Setting a
lower value can save RAM, depending on the buffer management scheme used.  If
ipconfigCAN_FRAGMENT_OUTGOING_PACKETS is 1 then (ipconfigNETWORK_MTU - 28) must
be divisible by 8. */
#define ipconfigNETWORK_MTU 586

/* Set ipconfigUSE_DNS to 1 to include a basic DNS client/resolver.  DNS is used
through the FreeRTOS_gethostbyname() API function. */
#define ipconfigUSE_DNS		1

/* If ipconfigREPLY_TO_INCOMING_PINGS is set to 1 then the IP stack will
generate replies to incoming ICMP echo (ping) requests. */
#define ipconfigREPLY_TO_INCOMING_PINGS				1

/* If ipconfigSUPPORT_OUTGOING_PINGS is set to 1 then the
FreeRTOS_SendPingRequest() API function is available. */
#define ipconfigSUPPORT_OUTGOING_PINGS				1

/* Used for stack testing only, and must be implemented in the network
interface. */
#define updconfigLOOPBACK_ETHERNET_PACKETS	0

/* If ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES is set to 1 then Ethernet frames
that are not in Ethernet II format will be dropped.  This option is included for
potential future IP stack developments. */
#define ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES 1

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1 then it is the
responsibility of the Ethernet interface to filter out packets that are of no
interest.  If the Ethernet interface does not implement this functionality, then
set ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES to 0 to have the IP stack
perform the filtering instead (it is much less efficient for the stack to do it
because the packet will already have been passed into the stack).  If the
Ethernet driver does all the necessary filtering in hardware then software
filtering can be removed by using a value other than 1 or 0. */
#define ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES	2

/* The example IP trace macros are included here so the definitions are
available in all the FreeRTOS+UDP source files. */
#include "DemoIPTrace.h"

#endif /* FREERTOS_IP_CONFIG_H */
