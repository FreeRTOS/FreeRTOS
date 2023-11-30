/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief Basic WEB Server for AVR32 UC3.
 *
 * - Compiler:           GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 *****************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


/*
  Implements a simplistic WEB server.  Every time a connection is made and
  data is received a dynamic page that shows the current FreeRTOS.org kernel
  statistics is generated and returned.  The connection is then closed.

  This file was adapted from a FreeRTOS lwIP slip demo supplied by a third
  party.
*/

#if (HTTP_USED == 1)


/* Standard includes. */
#include <stdio.h>
#include <string.h>

#include "conf_eth.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"
#include "partest.h"
#include "serial.h"

/* Demo includes. */
/* Demo app includes. */
#include "portmacro.h"

/* lwIP includes. */
#include "lwip/api.h"
#include "lwip/tcpip.h"
#include "lwip/memp.h"
#include "lwip/stats.h"
#include "netif/loopif.h"

/* ethernet includes */
#include "ethernet.h"

/*! The size of the buffer in which the dynamic WEB page is created. */
#define webMAX_PAGE_SIZE	512

/*! Standard GET response. */
#define webHTTP_OK	"HTTP/1.0 200 OK\r\nContent-type: text/html\r\n\r\n"

/*! The port on which we listen. */
#define webHTTP_PORT		( 80 )

/*! Delay on close error. */
#define webSHORT_DELAY		( 10 )

/*! Format of the dynamic page that is returned on each connection. */
#define webHTML_START \
"<html>\
<head>\
</head>\
<BODY onLoad=\"window.setTimeout(&quot;location.href='index.html'&quot;,1000)\" bgcolor=\"#FFFFFF\" text=\"#2477E6\">\
\r\nPage Hits = "

#define webHTML_END \
"\r\n</pre>\
\r\n</font></BODY>\
</html>"

char cDynamicPage[ webMAX_PAGE_SIZE ];
char cPageHits[ 11 ];


/*! Function to process the current connection */
static void prvweb_ParseHTMLRequest( struct netconn *pxNetCon );


/*! \brief WEB server main task
 *         check for incoming connection and process it
 *
 *  \param pvParameters   Input. Not Used.
 *
 */
portTASK_FUNCTION( vBasicWEBServer, pvParameters )
{
struct netconn *pxHTTPListener, *pxNewConnection;

	/* Create a new tcp connection handle */
	pxHTTPListener = netconn_new( NETCONN_TCP );
	netconn_bind(pxHTTPListener, NULL, webHTTP_PORT );
	netconn_listen( pxHTTPListener );

	/* Loop forever */
	for( ;; )
	{
		/* Wait for a first connection. */
		pxNewConnection = netconn_accept(pxHTTPListener);
		vParTestSetLED(webCONN_LED, pdTRUE);

		if(pxNewConnection != NULL)
		{
			prvweb_ParseHTMLRequest(pxNewConnection);
		}/* end if new connection */

		vParTestSetLED(webCONN_LED, pdFALSE);

	} /* end infinite loop */
}


/*! \brief parse the incoming request
 *         parse the HTML request and send file
 *
 *  \param pxNetCon   Input. The netconn to use to send and receive data.
 *
 */
static void prvweb_ParseHTMLRequest( struct netconn *pxNetCon )
{
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
			sprintf( cPageHits, "%d", (int)ulPageHits );

			/* Write out the HTTP OK header. */
			netconn_write( pxNetCon, webHTTP_OK, (u16_t) strlen( webHTTP_OK ), NETCONN_COPY );

			/* Generate the dynamic page... First the page header. */
			strcpy( cDynamicPage, webHTML_START );

			/* ... Then the hit count... */
			strcat( cDynamicPage, cPageHits );
			strcat( cDynamicPage, "<p><pre>Task          State  Priority  Stack	#<br>************************************************<br>" );

			/* ... Then the list of tasks and their status... */
			vTaskList( cDynamicPage + strlen( cDynamicPage ) );

			/* ... Finally the page footer. */
			strcat( cDynamicPage, webHTML_END );

			/* Write out the dynamically generated page. */
			netconn_write( pxNetCon, cDynamicPage, (u16_t) strlen( cDynamicPage ), NETCONN_COPY );
		}
		netbuf_delete( pxRxBuffer );
	}

	netconn_close( pxNetCon );
	netconn_delete( pxNetCon );
}

#endif

