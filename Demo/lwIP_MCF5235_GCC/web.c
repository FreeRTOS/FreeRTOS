/*
    FreeRTOS V4.6.1 - copyright (C) 2003-2006 Richard Barry.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License** as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    FreeRTOS is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with FreeRTOS; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    A special exception to the GPL can be applied should you wish to distribute
    a combined work that includes FreeRTOS, without being obliged to provide
    the source code for any proprietary components.  See the licensing section
    of http://www.FreeRTOS.org for full details of how and when the exception
    can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/

/*
    Implements a simplistic WEB server.  Every time a connection is made and
    data is received a dynamic page that shows the current TCP/IP statistics
    is generated and returned.  The connection is then closed.

    This file was adapted from a FreeRTOS lwIP slip demo supplied by a third
    party.
*/

/* ------------------------ System includes ------------------------------- */
#include <stdio.h>
#include <string.h>

/* ------------------------ FreeRTOS includes ----------------------------- */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* ------------------------ lwIP includes --------------------------------- */
#include "lwip/api.h"
#include "lwip/tcpip.h"
#include "lwip/memp.h"
#include "lwip/stats.h"
#include "netif/loopif.h"

/* ------------------------ Project includes ------------------------------ */
#include "mcf5xxx.h"
#include "mcf523x.h"
#include "netif/fec.h"

#include "web.h"

/* ------------------------ Defines --------------------------------------- */
/* The size of the buffer in which the dynamic WEB page is created. */
#define webMAX_PAGE_SIZE        ( 2048 )

/* Standard GET response. */
#define webHTTP_OK  "HTTP/1.0 200 OK\r\nContent-type: text/html\r\n\r\n"

/* The port on which we listen. */
#define webHTTP_PORT            ( 80 )

/* Delay on close error. */
#define webSHORT_DELAY          ( 10 )

/* Format of the dynamic page that is returned on each connection. */
#define webHTML_START \
"<html>\
<head>\
</head>\
<BODY onLoad=\"window.setTimeout(&quot;location.href='index.html'&quot;,1000)\"bgcolor=\"#CCCCff\">\
\r\nPage Hits = "

#define webHTML_END \
"\r\n" \
"FreeRTOS MCF5235 port (c) 2006 by Christian Walter &lt;wolti@sil.at&gt;\r\n" \
"</pre>\r\n" \
"</BODY>\r\n" \
"</html>"

/* ------------------------ Prototypes ------------------------------------ */
static void     vProcessConnection( struct netconn *pxNetCon );

/*------------------------------------------------------------*/

/*
 * Process an incoming connection on port 80.
 *
 * This simply checks to see if the incoming data contains a GET request, and
 * if so sends back a single dynamically created page.  The connection is then
 * closed.  A more complete implementation could create a task for each
 * connection.
 */
static void
vProcessConnection( struct netconn *pxNetCon )
{
    static portCHAR cDynamicPage[webMAX_PAGE_SIZE], cPageHits[11];
    struct netbuf  *pxRxBuffer;
    portCHAR       *pcRxString;
    unsigned portSHORT usLength;
    static unsigned portLONG ulPageHits = 0;

    /* We expect to immediately get data. */
    pxRxBuffer = netconn_recv( pxNetCon );

    if( pxRxBuffer != NULL )
    {
        /* Where is the data? */
        netbuf_data( pxRxBuffer, ( void * )&pcRxString, &usLength );

        /* Is this a GET?  We don't handle anything else. */
        if( !strncmp( pcRxString, "GET", 3 ) )
        {
            pcRxString = cDynamicPage;

            /* Update the hit count. */
            ulPageHits++;
            sprintf( cPageHits, "%lu", ulPageHits );

            /* Write out the HTTP OK header. */
            netconn_write( pxNetCon, webHTTP_OK, ( u16_t ) strlen( webHTTP_OK ), NETCONN_COPY );

            /* Generate the dynamic page...

               ... First the page header. */
            strcpy( cDynamicPage, webHTML_START );
            /* ... Then the hit count... */
            strcat( cDynamicPage, cPageHits );
            strcat( cDynamicPage,
                    "<p><pre>Task          State  Priority  Stack #<br>************************************************<br>" );
            /* ... Then the list of tasks and their status... */
            vTaskList( ( signed portCHAR * )cDynamicPage + strlen( cDynamicPage ) );
            /* ... Finally the page footer. */
            strcat( cDynamicPage, webHTML_END );

            /* Write out the dynamically generated page. */
            netconn_write( pxNetCon, cDynamicPage, ( u16_t ) strlen( cDynamicPage ), NETCONN_COPY );
        }

        netbuf_delete( pxRxBuffer );
    }

    netconn_close( pxNetCon );
}

/*------------------------------------------------------------*/

void
vlwIPInit( void )
{
    /* Initialize lwIP and its interface layer. */
    sys_init(  );
    mem_init(  );
    memp_init(  );
    pbuf_init(  );
    netif_init(  );
    ip_init(  );
    tcpip_init( NULL, NULL );
}

/*------------------------------------------------------------*/

void
vBasicWEBServer( void *pvParameters )
{
    struct netconn *pxHTTPListener, *pxNewConnection;
    struct ip_addr  xIpAddr, xNetMast, xGateway;
    static struct netif fec523x_if;

    /* Parameters are not used - suppress compiler error. */
    ( void )pvParameters;

    /* Create and configure the EMAC interface. */
    IP4_ADDR( &xIpAddr, 10, 0, 10, 2 );
    IP4_ADDR( &xNetMast, 255, 255, 255, 0 );
    IP4_ADDR( &xGateway, 10, 0, 10, 1 );
    netif_add( &fec523x_if, &xIpAddr, &xNetMast, &xGateway, NULL, mcf523xfec_init, tcpip_input );

    /* make it the default interface */
    netif_set_default( &fec523x_if );

    /* bring it up */
    netif_set_up( &fec523x_if );

    /* Create a new tcp connection handle */
    pxHTTPListener = netconn_new( NETCONN_TCP );
    netconn_bind( pxHTTPListener, NULL, webHTTP_PORT );
    netconn_listen( pxHTTPListener );

    /* Loop forever */
    for( ;; )
    {
        /* Wait for connection. */
        pxNewConnection = netconn_accept( pxHTTPListener );

        if( pxNewConnection != NULL )
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
