/*
 * FreeRTOS Kernel V10.2.0
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

/* Standard includes. */
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* uip includes. */
#include "net/uip.h"
#include "net/uip_arp.h"
#include "apps/httpd/httpd.h"
#include "sys/timer.h"
#include "net/clock-arch.h"
#include "emac.h"

/* Demo includes. */
#include "ParTest.h"

/* The buffer used by the uIP stack to both receive and send.  In this case,
because the Ethernet driver is implemented to be zero copy - the uip_buf
variable is just a pointer to an Ethernet buffer, and not a buffer in its own
right. */
extern unsigned char *uip_buf;

/* The ARP timer and the periodic timer share a callback function, so the
respective timer IDs are used to determine which timer actually expired.  These
constants are assigned to the timer IDs. */
#define uipARP_TIMER				0
#define uipPERIODIC_TIMER			1

/* The length of the queue used to send events from timers or the Ethernet
driver to the uIP stack. */
#define uipEVENT_QUEUE_LENGTH		10

/* A block time of zero simply means "don't block". */
#define uipDONT_BLOCK				0UL

/* Shortcut to the header within the Rx buffer. */
#define xHeader ((struct uip_eth_hdr *) &uip_buf[ 0 ])

/*-----------------------------------------------------------*/

/*
 * Setup the MAC address in the MAC itself, and in the uIP stack.
 */
static void prvSetMACAddress( void );

/*
 * Perform any uIP initialisation required to ready the stack for http
 * processing.
 */
static void prvInitialise_uIP( void );

/*
 * The callback function that is assigned to both the periodic timer and the
 * ARP timer.
 */
static void prvUIPTimerCallback( TimerHandle_t xTimer );

/*
 * Port functions required by the uIP stack.
 */
clock_time_t clock_time( void );

/*-----------------------------------------------------------*/

/* The queue used to send TCP/IP events to the uIP stack. */
QueueHandle_t xEMACEventQueue = NULL;

/*-----------------------------------------------------------*/

clock_time_t clock_time( void )
{
	return xTaskGetTickCount();
}
/*-----------------------------------------------------------*/

void vuIP_Task( void *pvParameters )
{
long i;
unsigned long ulNewEvent = 0UL, ulUIP_Events = 0UL;
unsigned short usPacketLength;

	/* Just to prevent compiler warnings about the unused parameter. */
	( void ) pvParameters;

	/* Initialise the uIP stack, configuring for web server usage. */
	prvInitialise_uIP();

	/* Initialise the MAC and PHY. */
	vEMACInit();

	for( ;; )
	{
		/* Is there received data ready to be processed? */
		usPacketLength = usEMACRead();

		/* Statements to be executed if data has been received on the Ethernet. */
		if( ( usPacketLength > 0U ) && ( uip_buf != NULL ) )
		{
			uip_len = usPacketLength;

			if( xHeader->type == htons( UIP_ETHTYPE_IP ) )
			{
				uip_arp_ipin();
				uip_input();

				/* If the above function invocation resulted in data that
				should be sent out on the network, the global variable
				uip_len is set to a value > 0. */
				if( uip_len > 0 )
				{
					uip_arp_out();
					vEMACWrite();
				}
			}
			else if( xHeader->type == htons( UIP_ETHTYPE_ARP ) )
			{
				uip_arp_arpin();

				/* If the above function invocation resulted in data that
				should be sent out on the network, the global variable
				uip_len is set to a value > 0. */
				if( uip_len > 0 )
				{
					vEMACWrite();
				}
			}
		}
		else
		{
			/* Clear the RX event latched in ulUIP_Events - if one was latched. */
			ulUIP_Events &= ~uipETHERNET_RX_EVENT;
		}

		/* Statements to be executed if the TCP/IP period timer has expired. */
		if( ( ulUIP_Events & uipPERIODIC_TIMER_EVENT ) != 0UL )
		{
			ulUIP_Events &= ~uipPERIODIC_TIMER_EVENT;

			if( uip_buf != NULL )
			{
				for( i = 0; i < UIP_CONNS; i++ )
				{
					uip_periodic( i );

					/* If the above function invocation resulted in data that
					should be sent out on the network, the global variable
					uip_len is set to a value > 0. */
					if( uip_len > 0 )
					{
						uip_arp_out();
						vEMACWrite();
					}
				}
			}
		}

		/* Statements to be executed if the ARP timer has expired. */
		if( ( ulUIP_Events & uipARP_TIMER_EVENT ) != 0 )
		{
			ulUIP_Events &= ~uipARP_TIMER_EVENT;
			uip_arp_timer();
		}

		/* If all latched events have been cleared - block until another event
		occurs. */
		if( ulUIP_Events == pdFALSE )
		{
			xQueueReceive( xEMACEventQueue, &ulNewEvent, portMAX_DELAY );
			ulUIP_Events |= ulNewEvent;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSetMACAddress( void )
{
struct uip_eth_addr xAddr;

	/* Configure the MAC address in the uIP stack. */
	xAddr.addr[ 0 ] = configMAC_ADDR0;
	xAddr.addr[ 1 ] = configMAC_ADDR1;
	xAddr.addr[ 2 ] = configMAC_ADDR2;
	xAddr.addr[ 3 ] = configMAC_ADDR3;
	xAddr.addr[ 4 ] = configMAC_ADDR4;
	xAddr.addr[ 5 ] = configMAC_ADDR5;
	uip_setethaddr( xAddr );
}
/*-----------------------------------------------------------*/

static void prvInitialise_uIP( void )
{
uip_ipaddr_t xIPAddr;
TimerHandle_t xARPTimer, xPeriodicTimer;

	uip_init();
	uip_ipaddr( &xIPAddr, configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3 );
	uip_sethostaddr( &xIPAddr );
	uip_ipaddr( &xIPAddr, configNET_MASK0, configNET_MASK1, configNET_MASK2, configNET_MASK3 );
	uip_setnetmask( &xIPAddr );
	prvSetMACAddress();
	httpd_init();

	/* Create the queue used to sent TCP/IP events to the uIP stack. */
	xEMACEventQueue = xQueueCreate( uipEVENT_QUEUE_LENGTH, sizeof( unsigned long ) );

	/* Create and start the uIP timers. */
	xARPTimer = xTimerCreate( 	"ARPTimer", /* Just a name that is helpful for debugging, not used by the kernel. */
								( 10000UL / portTICK_PERIOD_MS ), /* Timer period. */
								pdTRUE, /* Autor-reload. */
								( void * ) uipARP_TIMER,
								prvUIPTimerCallback
							);

	xPeriodicTimer = xTimerCreate( 	"PeriodicTimer",
									( 500UL / portTICK_PERIOD_MS ),
									pdTRUE, /* Autor-reload. */
									( void * ) uipPERIODIC_TIMER,
									prvUIPTimerCallback
								);

	/* Sanity check that the timers were indeed created. */
	configASSERT( xARPTimer );
	configASSERT( xPeriodicTimer );
	configASSERT( xEMACEventQueue );

	/* These commands will block indefinitely until they succeed, so there is
	no point in checking their return values. */
	xTimerStart( xARPTimer, portMAX_DELAY );
	xTimerStart( xPeriodicTimer, portMAX_DELAY );
}
/*-----------------------------------------------------------*/

static void prvUIPTimerCallback( TimerHandle_t xTimer )
{
static const unsigned long ulARPTimerExpired = uipARP_TIMER_EVENT;
static const unsigned long ulPeriodicTimerExpired = uipPERIODIC_TIMER_EVENT;

	/* This is a time callback, so calls to xQueueSend() must not attempt to
	block.  As this callback is assigned to both the ARP and Periodic timers, the
	first thing to do is ascertain which timer it was that actually expired. */
	switch( ( int ) pvTimerGetTimerID( xTimer ) )
	{
		case uipARP_TIMER		:	xQueueSend( xEMACEventQueue, &ulARPTimerExpired, uipDONT_BLOCK );
									break;

		case uipPERIODIC_TIMER	:	xQueueSend( xEMACEventQueue, &ulPeriodicTimerExpired, uipDONT_BLOCK );
									break;

		default					:  	/* Should not get here. */
									break;
	}
}
/*-----------------------------------------------------------*/

void vApplicationProcessFormInput( char *pcInputString )
{
char *c;
const unsigned long ulYellowLED = 2UL;

	/* Only interested in processing form input if this is the IO page. */
	c = strstr( pcInputString, "io.shtml" );

	if( c )
	{
		/* Is there a command in the string? */
		c = strstr( pcInputString, "?" );
	    if( c )
	    {
			/* Turn the LEDs on or off in accordance with the check box status. */
			if( strstr( c, "LED0=1" ) != NULL )
			{
				/* Turn the LEDs on. */
				vParTestSetLED( ulYellowLED, pdTRUE );
			}
			else
			{
				/* Turn the LEDs off. */
				vParTestSetLED( ulYellowLED, pdFALSE );
			}
	    }
		else
		{
			/* Some browsers will only imply that a check box is off. */
			vParTestSetLED( ulYellowLED, pdFALSE );
		}
	}
}
/*-----------------------------------------------------------*/
