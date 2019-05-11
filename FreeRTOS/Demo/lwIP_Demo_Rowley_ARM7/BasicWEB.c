/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/*
	Implements a simplistic WEB server.  Every time a connection is made and
	data is received a dynamic page that shows the current TCP/IP statistics
	is generated and returned.  The connection is then closed.

	This file was adapted from a FreeRTOS lwIP slip demo supplied by a third
	party.
*/

/*
	Changes from V3.2.2

	+ Changed the page returned by the lwIP WEB server demo to display the
	  task status table rather than the TCP/IP statistics.
*/


/* Standard includes. */
#include <stdio.h>
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Demo includes. */
#include "BasicWEB.h"
#include "SAM7_EMAC.h"

/* lwIP includes. */
#include "lwip/api.h"
#include "lwip/tcpip.h"
#include "lwip/memp.h"
#include "lwip/stats.h"
#include "netif/loopif.h"

/* The size of the buffer in which the dynamic WEB page is created. */
#define webMAX_PAGE_SIZE	2048

/* Standard GET response. */
#define webHTTP_OK	"HTTP/1.0 200 OK\r\nContent-type: text/html\r\n\r\n"

/* The port on which we listen. */
#define webHTTP_PORT		( 80 )

/* Delay on close error. */
#define webSHORT_DELAY		( 10 )

/* Format of the dynamic page that is returned on each connection. */
#define webHTML_START \
"<html>\
<head>\
</head>\
<BODY onLoad=\"window.setTimeout(&quot;location.href='index.html'&quot;,1000)\"bgcolor=\"#CCCCff\">\
\r\nPage Hits = "

#define webHTML_END \
"\r\n</pre>\
\r\n</BODY>\
</html>"

/*------------------------------------------------------------*/

/*
 * Process an incoming connection on port 80.
 *
 * This simply checks to see if the incoming data contains a GET request, and
 * if so sends back a single dynamically created page.  The connection is then
 * closed.  A more complete implementation could create a task for each
 * connection.
 */
static void vProcessConnection( struct netconn *pxNetCon );

/*------------------------------------------------------------*/

static void vProcessConnection( struct netconn *pxNetCon )
{
static char cDynamicPage[ webMAX_PAGE_SIZE ], cPageHits[ 11 ];
struct netbuf *pxRxBuffer;
char *pcRxString;
unsigned short usLength;
static unsigned long ulPageHits = 0;

	/* We expect to immediately get data. */
	pxRxBuffer = netconn_recv( pxNetCon );

	if( pxRxBuffer != NULL )
	{
		/* Where is the data? */
		netbuf_data( pxRxBuffer, ( void * ) &pcRxString, &usLength );

		/* Is this a GET?  We don't handle anything else. */
		if( !strncmp( pcRxString, "GET", 3 ) )
		{
			pcRxString = cDynamicPage;

			/* Update the hit count. */
			ulPageHits++;
			sprintf( cPageHits, "%lu", ulPageHits );

			/* Write out the HTTP OK header. */
            netconn_write(pxNetCon, webHTTP_OK, (u16_t)strlen( webHTTP_OK ), NETCONN_COPY );

			/* Generate the dynamic page...

			... First the page header. */
			strcpy( cDynamicPage, webHTML_START );
			/* ... Then the hit count... */
			strcat( cDynamicPage, cPageHits );
			strcat( cDynamicPage, "<p><pre>Task          State  Priority  Stack	#<br>************************************************<br>" );
			/* ... Then the list of tasks and their status... */
			vTaskList( cDynamicPage + strlen( cDynamicPage ) );
			/* ... Finally the page footer. */
			strcat( cDynamicPage, webHTML_END );

			/* Write out the dynamically generated page. */
			netconn_write(pxNetCon, cDynamicPage, (u16_t)strlen( cDynamicPage ), NETCONN_COPY );
		}

		netbuf_delete( pxRxBuffer );
	}

	netconn_close( pxNetCon );
}
/*------------------------------------------------------------*/

void vlwIPInit( void )
{
    /* Initialize lwIP and its interface layer. */
	sys_init();
	mem_init();
	memp_init();
	pbuf_init();
	netif_init();
	ip_init();
	tcpip_init( NULL, NULL );
}
/*------------------------------------------------------------*/

void vBasicWEBServer( void *pvParameters )
{
struct netconn *pxHTTPListener, *pxNewConnection;
struct ip_addr xIpAddr, xNetMast, xGateway;
extern err_t ethernetif_init( struct netif *netif );
static struct netif EMAC_if;

	/* Parameters are not used - suppress compiler error. */
	( void ) pvParameters;


	/* Create and configure the EMAC interface. */
	IP4_ADDR(&xIpAddr,emacIPADDR0,emacIPADDR1,emacIPADDR2,emacIPADDR3);
	IP4_ADDR(&xNetMast,emacNET_MASK0,emacNET_MASK1,emacNET_MASK2,emacNET_MASK3);
	IP4_ADDR(&xGateway,emacGATEWAY_ADDR0,emacGATEWAY_ADDR1,emacGATEWAY_ADDR2,emacGATEWAY_ADDR3);
	netif_add(&EMAC_if, &xIpAddr, &xNetMast, &xGateway, NULL, ethernetif_init, tcpip_input);

	/* make it the default interface */
    netif_set_default(&EMAC_if);

	/* bring it up */
    netif_set_up(&EMAC_if);

	/* Create a new tcp connection handle */

 	pxHTTPListener = netconn_new( NETCONN_TCP );
	netconn_bind(pxHTTPListener, NULL, webHTTP_PORT );
	netconn_listen( pxHTTPListener );

	/* Loop forever */
	for( ;; )
	{
		/* Wait for connection. */
		pxNewConnection = netconn_accept(pxHTTPListener);

		if(pxNewConnection != NULL)
		{
			/* Service connection. */
			vProcessConnection( pxNewConnection );
			while( netconn_delete( pxNewConnection ) != ERR_OK )
			{
				vTaskDelay( webSHORT_DELAY );
			}
		}
	}
}


