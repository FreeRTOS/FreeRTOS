/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

/* lwIP core includes */
#include "lwip/opt.h"
#include "lwip/sys.h"
#include "lwip/timers.h"
#include "lwip/debug.h"
#include "lwip/stats.h"
#include "lwip/init.h"
#include "lwip/tcpip.h"
#include "lwip/netif.h"
#include "lwip/tcp.h"
#include "lwip/udp.h"
#include "lwip/dns.h"
#include "lwip/dhcp.h"
#include "lwip/autoip.h"

/* lwIP netif includes */
#include "netif/etharp.h"

/* applications includes */
#include "apps/httpserver_raw/httpd.h"
#include "apps/httpserver/httpserver-netconn.h"
#include "apps/netio/netio.h"
#include "apps/netbios/netbios.h"
#include "apps/ping/ping.h"
#include "apps/rtp/rtp.h"
#include "apps/sntp/sntp.h"
#include "apps/chargen/chargen.h"
#include "apps/shell/shell.h"
#include "apps/tcpecho/tcpecho.h"
#include "apps/udpecho/udpecho.h"
#include "apps/tcpecho_raw/echo.h"
#include "apps/socket_examples/socket_examples.h"

/* include the port-dependent configuration */
#include "lwipcfg_msvc.h"

static struct netif netif;

static void apps_init( void );

#define ssiTASK_STATS_INDEX			0
#define ssiRUN_TIME_STATS_INDEX		1


/*
 * The SSI handler callback function passed to lwIP.
 */
static unsigned short uslwIPAppsSSIHandler( int iIndex, char *pcBuffer, int iBufferLength );


/* The SSI strings that are embedded in the served html files. */
static const char *pccSSITags[] = 
{
	"rtos_stats",
	"run_stats"
};


/* Called from the TCP/IP thread. */
void lwIPAppsInit( void *pvArgument )
{
ip_addr_t ipaddr, netmask, gw;
extern err_t ethernetif_init( struct netif *netif );

	( void ) pvArgument;

	ip_addr_set_zero( &gw );
	ip_addr_set_zero( &ipaddr );
	ip_addr_set_zero( &netmask );

	LWIP_PORT_INIT_GW(&gw);
	LWIP_PORT_INIT_IPADDR(&ipaddr);
	LWIP_PORT_INIT_NETMASK(&netmask);
	printf("Starting lwIP, local interface IP is %s\n", ip_ntoa(&ipaddr));

	netif_set_default(netif_add(&netif, &ipaddr, &netmask, &gw, NULL, ethernetif_init, tcpip_input));

	#if LWIP_NETIF_STATUS_CALLBACK
		netif_set_status_callback(&netif, status_callback);
	#endif /* LWIP_NETIF_STATUS_CALLBACK */
	#if LWIP_NETIF_LINK_CALLBACK
		netif_set_link_callback(&netif, link_callback);
	#endif /* LWIP_NETIF_LINK_CALLBACK */

	netif_set_up( &netif );
	apps_init();
	http_set_ssi_handler( uslwIPAppsSSIHandler, pccSSITags, sizeof( pccSSITags ) / sizeof( char * ) );
}
/*-----------------------------------------------------------*/

/* This function initializes applications */
static void apps_init( void )
{
	/* Taken from the lwIP example code. */
	
	#if LWIP_DNS_APP && LWIP_DNS
		/* wait until the netif is up (for dhcp, autoip or ppp) */
		sys_timeout(5000, dns_dorequest, NULL);
	#endif /* LWIP_DNS_APP && LWIP_DNS */

	#if LWIP_CHARGEN_APP && LWIP_SOCKET
		chargen_init();
	#endif /* LWIP_CHARGEN_APP && LWIP_SOCKET */

	#if LWIP_PING_APP && LWIP_RAW && LWIP_ICMP
		ping_init();
	#endif /* LWIP_PING_APP && LWIP_RAW && LWIP_ICMP */

	#if LWIP_NETBIOS_APP && LWIP_UDP
		netbios_init();
	#endif /* LWIP_NETBIOS_APP && LWIP_UDP */

	#if LWIP_HTTPD_APP && LWIP_TCP
	{
		#ifdef LWIP_HTTPD_APP_NETCONN
			http_server_netconn_init();
		#else /* LWIP_HTTPD_APP_NETCONN */
			httpd_init();
		#endif /* LWIP_HTTPD_APP_NETCONN */
	}
	#endif /* LWIP_HTTPD_APP && LWIP_TCP */

	#if LWIP_NETIO_APP && LWIP_TCP
		netio_init();
	#endif /* LWIP_NETIO_APP && LWIP_TCP */

	#if LWIP_RTP_APP && LWIP_SOCKET && LWIP_IGMP
		rtp_init();
	#endif /* LWIP_RTP_APP && LWIP_SOCKET && LWIP_IGMP */

	#if LWIP_SNTP_APP && LWIP_SOCKET
		sntp_init();
	#endif /* LWIP_SNTP_APP && LWIP_SOCKET */

	#if LWIP_SHELL_APP && LWIP_NETCONN
		shell_init();
	#endif /* LWIP_SHELL_APP && LWIP_NETCONN */

	#if LWIP_TCPECHO_APP
		#if LWIP_NETCONN && defined(LWIP_TCPECHO_APP_NETCONN)
			tcpecho_init();
		#else /* LWIP_NETCONN && defined(LWIP_TCPECHO_APP_NETCONN) */
			echo_init();
		#endif
	#endif /* LWIP_TCPECHO_APP && LWIP_NETCONN */

	#if LWIP_UDPECHO_APP && LWIP_NETCONN
		udpecho_init();
	#endif /* LWIP_UDPECHO_APP && LWIP_NETCONN */
	
	#if LWIP_SOCKET_EXAMPLES_APP && LWIP_SOCKET
		socket_examples_init();
	#endif /* LWIP_SOCKET_EXAMPLES_APP && LWIP_SOCKET */
}
/*-----------------------------------------------------------*/

static unsigned short uslwIPAppsSSIHandler( int iIndex, char *pcBuffer, int iBufferLength )
{
static unsigned int uiUpdateCount = 0;
static char cUpdateString[ 200 ];
extern char *pcMainGetTaskStatusMessage( void );

	( void ) iBufferLength;

	/* The SSI handler function that generates text depending on the index of
	the SSI tag encountered. */
	
	switch( iIndex )
	{
		case ssiTASK_STATS_INDEX :
			vTaskList( pcBuffer );
			break;

		case ssiRUN_TIME_STATS_INDEX :
			vTaskGetRunTimeStats( pcBuffer );
			break;
	}

	uiUpdateCount++;
	sprintf( cUpdateString, "\r\n\r\n%u\r\nStatus - %s", uiUpdateCount, pcMainGetTaskStatusMessage() );
	strcat( pcBuffer, cUpdateString );
	return strlen( pcBuffer );
}

