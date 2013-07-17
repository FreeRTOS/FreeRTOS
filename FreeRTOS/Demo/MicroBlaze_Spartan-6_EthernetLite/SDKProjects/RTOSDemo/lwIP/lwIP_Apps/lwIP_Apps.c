/*
    FreeRTOS V7.5.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* Standard includes. */
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* lwIP core includes */
#include "lwip/opt.h"
#include "lwip/tcpip.h"

/* lwIP netif includes */
#include "netif/etharp.h"

/* applications includes */
#include "apps/httpserver_raw/httpd.h"

/* The constants that define the IP address, net mask, gateway address and MAC
address are located at the bottom of FreeRTOSConfig.h. */
#define LWIP_PORT_INIT_IPADDR(addr)   IP4_ADDR((addr), configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3 )
#define LWIP_PORT_INIT_GW(addr)       IP4_ADDR((addr), configGW_IP_ADDR0, configGW_IP_ADDR1, configGW_IP_ADDR2, configGW_IP_ADDR3 )
#define LWIP_PORT_INIT_NETMASK(addr)  IP4_ADDR((addr), configNET_MASK0,configNET_MASK1,configNET_MASK2,configNET_MASK3)
#define LWIP_MAC_ADDR_BASE            { configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5 }

/* Definitions of the various SSI callback functions within the pccSSITags 
array.  If pccSSITags is updated, then these definitions must also be updated. */
#define ssiTASK_STATS_INDEX			0
#define ssiRUN_TIME_STATS_INDEX		1

/*
 * The SSI handler callback function passed to lwIP.
 */
static unsigned short uslwIPAppsSSIHandler( int iIndex, char *pcBuffer, int iBufferLength );

/*-----------------------------------------------------------*/

/* The SSI strings that are embedded in the served html files.  If this array
is changed, then the index position defined by the #defines such as 
ssiTASK_STATS_INDEX above must also be updated. */
static const char *pccSSITags[] = 
{
	"rtos_stats",
	"run_stats"
};

/*-----------------------------------------------------------*/

/* Called from the TCP/IP thread. */
void lwIPAppsInit( void *pvArgument )
{
ip_addr_t xIPAddr, xNetMask, xGateway;
extern err_t ethernetif_init( struct netif *xNetIf );
static struct netif xNetIf;

	( void ) pvArgument;

	/* Set up the network interface. */
	ip_addr_set_zero( &xGateway );
	ip_addr_set_zero( &xIPAddr );
	ip_addr_set_zero( &xNetMask );

	LWIP_PORT_INIT_GW(&xGateway);
	LWIP_PORT_INIT_IPADDR(&xIPAddr);
	LWIP_PORT_INIT_NETMASK(&xNetMask);

	netif_set_default( netif_add( &xNetIf, &xIPAddr, &xNetMask, &xGateway, NULL, ethernetif_init, tcpip_input ) );
	netif_set_up( &xNetIf );

	/* Initialise the raw http server. */
	httpd_init();

	/* Install the server side include handler. */
	http_set_ssi_handler( uslwIPAppsSSIHandler, pccSSITags, sizeof( pccSSITags ) / sizeof( char * ) );
}
/*-----------------------------------------------------------*/

static unsigned short uslwIPAppsSSIHandler( int iIndex, char *pcBuffer, int iBufferLength )
{
static unsigned int uiUpdateCount = 0;
static char cUpdateString[ 200 ];
extern char *pcMainGetTaskStatusMessage( void );

	/* Unused parameter. */
	( void ) iBufferLength;

	/* The SSI handler function that generates text depending on the index of
	the SSI tag encountered. */
	
	switch( iIndex )
	{
		case ssiTASK_STATS_INDEX :
			vTaskList( ( signed char * ) pcBuffer );
			break;

		case ssiRUN_TIME_STATS_INDEX :
			vTaskGetRunTimeStats( ( signed char * ) pcBuffer );
			break;
	}

	/* Include a count of the number of times an SSI function has been executed
	in the returned string. */
	uiUpdateCount++;
	sprintf( cUpdateString, "\r\n\r\n%u\r\nStatus - %s", uiUpdateCount, pcMainGetTaskStatusMessage() );
	strcat( pcBuffer, cUpdateString );
	return strlen( pcBuffer );
}

