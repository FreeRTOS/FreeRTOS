/*
    FreeRTOS V8.2.2 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

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
#include "lwip/inet.h"
#include "lwip/dhcp.h"

/* applications includes */
#include "apps/httpserver_raw_from_lwIP_download/httpd.h"

/* include the port-dependent configuration */
#include "lwipcfg_msvc.h"

/* Dimensions the cTxBuffer array - which is itself used to hold replies from 
command line commands.  cTxBuffer is a shared buffer, so protected by the 
xTxBufferMutex mutex. */
#define lwipappsTX_BUFFER_SIZE	1024

/* The maximum time to block waiting to obtain the xTxBufferMutex to become
available. */
#define lwipappsMAX_TIME_TO_WAIT_FOR_TX_BUFFER_MS	( 100 / portTICK_RATE_MS )

/* Definitions of the various SSI callback functions within the pccSSITags 
array.  If pccSSITags is updated, then these definitions must also be updated. */
#define ssiTASK_STATS_INDEX			0
#define ssiRUN_TIME_STATS_INDEX		1

/*-----------------------------------------------------------*/

/*
 * The function that implements the lwIP based sockets command interpreter
 * server.
 */
extern void vBasicSocketsCommandInterpreterTask( void *pvParameters );

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

/* Semaphore used to guard the Tx buffer. */
static xSemaphoreHandle xTxBufferMutex = NULL;

/* The Tx buffer itself.  This is used to hold the text generated by the 
execution of command line commands, and (hopefully) the execution of 
server side include callbacks.  It is a shared buffer so protected by the
xTxBufferMutex mutex.  pcLwipAppsBlockingGetTxBuffer() and 
vLwipAppsReleaseTxBuffer() are provided to obtain and release the 
xTxBufferMutex respectively.  pcLwipAppsBlockingGetTxBuffer() must be used with
caution as it has the potential to block. */
static signed char cTxBuffer[ lwipappsTX_BUFFER_SIZE ];

/*-----------------------------------------------------------*/

void vStatusCallback( struct netif *pxNetIf )
{
char pcMessage[20];
struct in_addr* pxIPAddress;

	if( netif_is_up( pxNetIf ) != 0 )
	{
		strcpy( pcMessage, "IP=" );
		pxIPAddress = ( struct in_addr* ) &( pxNetIf->ip_addr );
		strcat( pcMessage, inet_ntoa( ( *pxIPAddress ) ) );
		xil_printf( pcMessage );
	}
	else
	{
		xil_printf( "Network is down" );
	}
}

/* Called from the TCP/IP thread. */
void lwIPAppsInit( void *pvArgument )
{
ip_addr_t xIPAddr, xNetMask, xGateway;
extern err_t xemacpsif_init( struct netif *netif );
extern void xemacif_input_thread( void *netif );
static struct netif xNetIf;

	( void ) pvArgument;

	/* Set up the network interface. */
	ip_addr_set_zero( &xGateway );
	ip_addr_set_zero( &xIPAddr );
	ip_addr_set_zero( &xNetMask );

	LWIP_PORT_INIT_GW(&xGateway);
	LWIP_PORT_INIT_IPADDR( &xIPAddr );
	LWIP_PORT_INIT_NETMASK(&xNetMask);

	/* Set mac address */
	xNetIf.hwaddr_len = 6;
	xNetIf.hwaddr[ 0 ] = configMAC_ADDR0;
	xNetIf.hwaddr[ 1 ] = configMAC_ADDR1;
	xNetIf.hwaddr[ 2 ] = configMAC_ADDR2;
	xNetIf.hwaddr[ 3 ] = configMAC_ADDR3;
	xNetIf.hwaddr[ 4 ] = configMAC_ADDR4;
	xNetIf.hwaddr[ 5 ] = configMAC_ADDR5;

	netif_set_default( netif_add( &xNetIf, &xIPAddr, &xNetMask, &xGateway, ( void * ) XPAR_XEMACPS_0_BASEADDR, xemacpsif_init, tcpip_input ) );
	netif_set_status_callback( &xNetIf, vStatusCallback );
	#if LWIP_DHCP
	{
		dhcp_start( &xNetIf );
	}
	#else
	{
		netif_set_up( &xNetIf );
	}
	#endif

	/* Install the server side include handler. */
	http_set_ssi_handler( uslwIPAppsSSIHandler, pccSSITags, sizeof( pccSSITags ) / sizeof( char * ) );

	/* Create the mutex used to ensure mutual exclusive access to the Tx 
	buffer. */
	xTxBufferMutex = xSemaphoreCreateMutex();
	configASSERT( xTxBufferMutex );

	/* Create the httpd server from the standard lwIP code.  This demonstrates
	use of the lwIP raw API. */
	httpd_init();

	sys_thread_new( "lwIP_In", xemacif_input_thread, &xNetIf, configMINIMAL_STACK_SIZE, configMAC_INPUT_TASK_PRIORITY );

	/* Create the FreeRTOS defined basic command server.  This demonstrates use
	of the lwIP sockets API. */
	xTaskCreate( vBasicSocketsCommandInterpreterTask, "CmdInt", configMINIMAL_STACK_SIZE * 5, NULL, configCLI_TASK_PRIORITY, NULL );
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
			vTaskList( pcBuffer );
			break;

		case ssiRUN_TIME_STATS_INDEX :
			vTaskGetRunTimeStats( pcBuffer );
			break;
	}

	/* Include a count of the number of times an SSI function has been executed
	in the returned string. */
	uiUpdateCount++;
	sprintf( cUpdateString, "\r\n\r\n%u\r\nStatus - %s", uiUpdateCount, pcMainGetTaskStatusMessage() );
	strcat( pcBuffer, cUpdateString );

	return strlen( pcBuffer );
}
/*-----------------------------------------------------------*/

signed char *pcLwipAppsBlockingGetTxBuffer( void )
{
signed char *pcReturn;

	/* Attempt to obtain the semaphore that guards the Tx buffer. */
	if( xSemaphoreTakeRecursive( xTxBufferMutex, lwipappsMAX_TIME_TO_WAIT_FOR_TX_BUFFER_MS ) == pdFAIL )
	{
		/* The semaphore could not be obtained before timing out. */
		pcReturn = NULL;
	}
	else
	{
		/* The semaphore was obtained successfully.  Return a pointer to the
		Tx buffer. */
		pcReturn = cTxBuffer;
	}

	return pcReturn;
}
/*-----------------------------------------------------------*/

void vLwipAppsReleaseTxBuffer( void )
{
	/* Finished with the Tx buffer.  Return the mutex. */
	xSemaphoreGiveRecursive( xTxBufferMutex );
}



