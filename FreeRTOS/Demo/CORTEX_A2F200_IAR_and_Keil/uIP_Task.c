/*
    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd. 
    All rights reserved

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

/* Demo includes. */
#include "ParTest.h"

/* Hardware driver includes. */
#include "mss_ethernet_mac_regs.h"
#include "mss_ethernet_mac.h"

/* The buffer used by the uIP stack to both receive and send.  In this case,
because the Ethernet driver has been modified to be zero copy - the uip_buf
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

/* How long to wait before attempting to connect the MAC again. */
#define uipINIT_WAIT    ( 100 / portTICK_RATE_MS )

/* Shortcut to the header within the Rx buffer. */
#define xHeader ((struct uip_eth_hdr *) &uip_buf[ 0 ])

/* Standard constant. */
#define uipTOTAL_FRAME_HEADER_SIZE	54

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
 * Handles Ethernet interrupt events.
 */
static void prvEMACEventListener( unsigned long ulISREvents );

/*
 * The callback function that is assigned to both the periodic timer and the
 * ARP timer.
 */
static void prvUIPTimerCallback( xTimerHandle xTimer );

/*
 * Initialise the MAC hardware.
 */
static void prvInitEmac( void );

/*
 * Write data to the Ethener.  Note that this actually writes data twice for the
 * to get around delayed ack issues when communicating with a non real-time
 * peer (for example, a Windows machine).
 */
void vEMACWrite( void );

/*
 * Port functions required by the uIP stack.
 */
clock_time_t clock_time( void );

/*-----------------------------------------------------------*/

/* The queue used to send TCP/IP events to the uIP stack. */
xQueueHandle xEMACEventQueue = NULL;

/*-----------------------------------------------------------*/

clock_time_t clock_time( void )
{
	return xTaskGetTickCount();
}
/*-----------------------------------------------------------*/

void vuIP_Task( void *pvParameters )
{
portBASE_TYPE i;
unsigned long ulNewEvent = 0UL, ulUIP_Events = 0UL;
long lPacketLength;

	/* Just to prevent compiler warnings about the unused parameter. */
	( void ) pvParameters;

	/* Initialise the uIP stack, configuring for web server usage. */
	prvInitialise_uIP();

	/* Initialise the MAC and PHY. */
	prvInitEmac();

	for( ;; )
	{
		/* Is there received data ready to be processed? */
		lPacketLength = MSS_MAC_rx_packet();

		/* Statements to be executed if data has been received on the Ethernet. */
		if( ( lPacketLength > 0 ) && ( uip_buf != NULL ) )
		{
			uip_len = ( u16_t ) lPacketLength;
			
			/* Standard uIP loop taken from the uIP manual. */
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
xTimerHandle xARPTimer, xPeriodicTimer;

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
	xARPTimer = xTimerCreate( 	( signed char * ) "ARPTimer", /* Just a name that is helpful for debugging, not used by the kernel. */
								( 10000UL / portTICK_RATE_MS ), /* Timer period. */
								pdTRUE, /* Autor-reload. */
								( void * ) uipARP_TIMER,
								prvUIPTimerCallback
							);

	xPeriodicTimer = xTimerCreate( 	( signed char * ) "PeriodicTimer",
									( 500UL / portTICK_RATE_MS ),
									pdTRUE, /* Autor-reload. */
									( void * ) uipPERIODIC_TIMER,
									prvUIPTimerCallback
								);

	/* Sanity check that the timers were indeed created. */
	configASSERT( xARPTimer );
	configASSERT( xPeriodicTimer );

	/* These commands will block indefinitely until they succeed, so there is
	no point in checking their return values. */
	xTimerStart( xARPTimer, portMAX_DELAY );
	xTimerStart( xPeriodicTimer, portMAX_DELAY );
}
/*-----------------------------------------------------------*/

static void prvEMACEventListener( unsigned long ulISREvents )
{
long lHigherPriorityTaskWoken = pdFALSE;
const unsigned long ulRxEvent = uipETHERNET_RX_EVENT;

	/* Sanity check that the event queue was indeed created. */
	configASSERT( xEMACEventQueue );

	if( ( ulISREvents & MSS_MAC_EVENT_PACKET_SEND ) != 0UL )
	{
		/* An Ethernet Tx event has occurred. */
		MSS_MAC_FreeTxBuffers();
	}

	if( ( ulISREvents & MSS_MAC_EVENT_PACKET_RECEIVED ) != 0UL )
	{
		/* An Ethernet Rx event has occurred. */
		xQueueSendFromISR( xEMACEventQueue, &ulRxEvent, &lHigherPriorityTaskWoken );
	}

	portEND_SWITCHING_ISR( lHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvInitEmac( void )
{
const unsigned char ucPHYAddress = 1;

	/* Initialise the MAC and PHY hardware. */
	MSS_MAC_init( ucPHYAddress );

	/* Register the event listener.  The Ethernet interrupt handler will call
	this listener whenever an Rx or a Tx interrupt occurs. */
	MSS_MAC_set_callback( ( MSS_MAC_callback_t ) prvEMACEventListener );

    /* Setup the EMAC and the NVIC for MAC interrupts. */
    NVIC_SetPriority( EthernetMAC_IRQn, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
    NVIC_EnableIRQ( EthernetMAC_IRQn );
}
/*-----------------------------------------------------------*/

void vEMACWrite( void )
{
const long lMaxAttempts = 10;
long lAttempt;
const portTickType xShortDelay = ( 5 / portTICK_RATE_MS );

	/* Try to send data to the Ethernet.  Keep trying for a while if data cannot
	be sent immediately.  Note that this will actually cause the data to be sent
	twice to get around delayed ACK problems when communicating with non real-
	time TCP/IP stacks (such as a Windows machine). */
	for( lAttempt = 0; lAttempt < lMaxAttempts; lAttempt++ )
	{
		if( MSS_MAC_tx_packet( uip_len ) != 0 )
		{
			break;
		}
		else
		{
			vTaskDelay( xShortDelay );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvUIPTimerCallback( xTimerHandle xTimer )
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

	/* Only interested in processing form input if this is the IO page. */
	c = strstr( pcInputString, "io.shtml" );
	
	if( c )
	{
		/* Is there a command in the string? */
		c = strstr( pcInputString, "?" );
	    if( c )
	    {
			/* Turn the LED's on or off in accordance with the check box status. */
			if( strstr( c, "LED0=1" ) != NULL )
			{
				/* Turn the LEDs on. */
				vParTestSetLED( 3, 1 );
				vParTestSetLED( 4, 1 );
			}
			else
			{
				/* Turn the LEDs off. */
				vParTestSetLED( 3, 0 );
				vParTestSetLED( 4, 0 );
			}
	    }
		else
		{
			/* Commands to turn LEDs off are not always explicit. */
			vParTestSetLED( 3, 0 );
			vParTestSetLED( 4, 0 );
		}
	}
}
/*-----------------------------------------------------------*/
