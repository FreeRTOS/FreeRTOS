/*
 * Modified from an original work that is Copyright (c) 2001-2003, Adam Dunkels.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote
 *    products derived from this software without specific prior
 *    written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
 * GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * This file is part of the uIP TCP/IP stack.
 *
 * $Id: main.c,v 1.10.2.4 2003/10/21 21:27:51 adam Exp $
 *
 */

/* Standard includes. */
#include <stdlib.h>
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "semphr.h"
#include "task.h"

/* Demo app includes. */
#include "SAM7_EMAC.h"

/* uIP includes. */
#undef HTONS
#include "uip.h"
#include "uip_arp.h"
#include "tapdev.h"
#include "httpd.h"

/* The start of the uIP buffer, which will contain the frame headers. */
#define pucUIP_Buffer ( ( struct uip_eth_hdr * ) &uip_buf[ 0 ] )

/* uIP update frequencies. */
#define RT_CLOCK_SECOND		( configTICK_RATE_HZ  )
#define uipARP_FREQUENCY	( 20 )
#define uipMAX_BLOCK_TIME	( RT_CLOCK_SECOND / 4 )

/*-----------------------------------------------------------*/

void vuIP_TASK( void *pvParameters )
{
/* The semaphore used by the EMAC ISR to indicate that an Rx frame is ready
for processing. */
SemaphoreHandle_t xSemaphore = NULL;
portBASE_TYPE xARPTimer;
unsigned portBASE_TYPE uxPriority;
static volatile TickType_t xStartTime, xCurrentTime;

	/* Initialize the uIP TCP/IP stack. */
	uip_init();
	uip_arp_init();
	
	/* Initialize the HTTP server. */
	httpd_init();

	/* Initialise the local timers. */
	xStartTime = xTaskGetTickCount();
	xARPTimer = 0;

	/* Initialise the EMAC.  A semaphore will be returned when this is
	successful. This routine contains code that polls status bits.  If the
	Ethernet cable is not plugged in then this can take a considerable time.
	To prevent this starving lower priority tasks of processing time we
	lower our priority prior to the call, then raise it back again once the
	initialisation is complete. */
	uxPriority = uxTaskPriorityGet( NULL );
	vTaskPrioritySet( NULL, tskIDLE_PRIORITY );
	while( xSemaphore == NULL )
	{
		xSemaphore = xEMACInit();
	}
	vTaskPrioritySet( NULL, uxPriority );

	for( ;; )
	{
		/* Let the network device driver read an entire IP packet
		into the uip_buf. If it returns > 0, there is a packet in the
		uip_buf buffer. */
		uip_len = ulEMACPoll();

		/* Was a packet placed in the uIP buffer? */
		if( uip_len > 0 )
		{
			/* A packet is present in the uIP buffer. We call the
			appropriate ARP functions depending on what kind of packet we
			have received. If the packet is an IP packet, we should call
			uip_input() as well. */
			if( pucUIP_Buffer->type == htons( UIP_ETHTYPE_IP ) )
			{
				uip_arp_ipin();
				uip_input();

				/* If the above function invocation resulted in data that
				should be sent out on the network, the global variable
				uip_len is set to a value > 0. */
				if( uip_len > 0 )
				{
					uip_arp_out();
					lEMACSend();
				}
			}
			else if( pucUIP_Buffer->type == htons( UIP_ETHTYPE_ARP ) )
			{
				uip_arp_arpin();

				/* If the above function invocation resulted in data that
				should be sent out on the network, the global variable
				uip_len is set to a value > 0. */	
				if( uip_len > 0 )
				{	
					lEMACSend();
				}
			}
		}
		else
		{
			/* The poll function returned 0, so no packet was
			received. Instead we check if it is time that we do the
			periodic processing. */
			xCurrentTime = xTaskGetTickCount();

			if( ( xCurrentTime - xStartTime ) >= RT_CLOCK_SECOND )
			{
				portBASE_TYPE i;

				/* Reset the timer. */
				xStartTime = xCurrentTime;

				/* Periodic check of all connections. */
				for( i = 0; i < UIP_CONNS; i++ )
				{
					uip_periodic( i );

					/* If the above function invocation resulted in data that
					should be sent out on the network, the global variable
					uip_len is set to a value > 0. */					
					if( uip_len > 0 )
					{
						uip_arp_out();
						lEMACSend();
					}
				}

				#if UIP_UDP
					for( i = 0; i < UIP_UDP_CONNS; i++ )
					{
						uip_udp_periodic( i );

						/* If the above function invocation resulted in data that
						should be sent out on the network, the global variable
						uip_len is set to a value > 0. */
						if( uip_len > 0 )
						{
							uip_arp_out();
							tapdev_send();
						}
					}
				#endif /* UIP_UDP */

				/* Periodically call the ARP timer function. */
				if( ++xARPTimer == uipARP_FREQUENCY )
				{	
					uip_arp_timer();
					xARPTimer = 0;
				}
			}
			else
			{				
				/* We did not receive a packet, and there was no periodic
				processing to perform.  Block for a fixed period.  If a packet
				is received during this period we will be woken by the ISR
				giving us the Semaphore. */
				xSemaphoreTake( xSemaphore, uipMAX_BLOCK_TIME );
			}
		}
	}
}
/*-----------------------------------------------------------------------------------*/





