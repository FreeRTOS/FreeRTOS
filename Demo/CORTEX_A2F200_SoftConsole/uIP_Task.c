/*
    FreeRTOS V7.0.0 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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

/* The buffer used by the uIP stack to both receive and send.  This points to
one of the Ethernet buffers when its actually in use. */
extern unsigned char *uip_buf;

static const unsigned char ucMACAddress[] = { configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5 };

#define uipARP_TIMER				0
#define uipPERIODIC_TIMER			1

#define uipEVENT_QUEUE_LENGTH		10

#define uipETHERNET_RX_EVENT		0x01UL
#define	uipETHERNET_TX_EVENT		0x02UL
#define uipARP_TIMER_EVENT			0x04UL
#define uipPERIODIC_TIMER_EVENT		0x08UL
#define uipAPPLICATION_SEND_EVENT	0x10UL

#define uipDONT_BLOCK				0UL

/*-----------------------------------------------------------*/

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

static void prvUIPTimerCallback( xTimerHandle xTimer );

/*
 * Initialise the MAC hardware.
 */
static void prvInitEmac( void );

void vEMACWrite( void );

long lEMACWaitForLink( void );

/*
 * Port functions required by the uIP stack.
 */
void clock_init( void );
clock_time_t clock_time( void );

/*-----------------------------------------------------------*/

/* The queue used to send TCP/IP events to the uIP stack. */
xQueueHandle xEMACEventQueue = NULL;

static unsigned long ulUIP_Events = 0UL;

/*-----------------------------------------------------------*/

void clock_init(void)
{
	/* This is done when the scheduler starts. */
}
/*-----------------------------------------------------------*/

clock_time_t clock_time( void )
{
	return xTaskGetTickCount();
}
/*-----------------------------------------------------------*/

void vuIP_Task( void *pvParameters )
{
portBASE_TYPE i;
unsigned long ulNewEvent;

	( void ) pvParameters;

	/* Initialise the uIP stack, configuring for web server usage. */
	prvInitialise_uIP();

	/* Initialise the MAC. */
	prvInitEmac();

	for( ;; )
	{
		if( ( ulUIP_Events & uipETHERNET_TX_EVENT ) != 0UL )
		{
			ulUIP_Events &= ~uipETHERNET_TX_EVENT;
			MSS_MAC_TxBufferCompleted();
		}

		if( ( ulUIP_Events & uipETHERNET_RX_EVENT ) != 0UL )
		{
			ulUIP_Events &= ~uipETHERNET_RX_EVENT;

			/* Is there received data ready to be processed? */
			uip_len = MSS_MAC_rx_packet();

			if( ( uip_len > 0 ) && ( uip_buf != NULL ) )
			{
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
		}

		if( ( ulUIP_Events & uipPERIODIC_TIMER_EVENT ) != 0UL )
		{
			ulUIP_Events &= ~uipPERIODIC_TIMER_EVENT;

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

		/* Call the ARP timer function every 10 seconds. */
		if( ( ulUIP_Events & uipARP_TIMER_EVENT ) != 0 )
		{
			ulUIP_Events &= ~uipARP_TIMER_EVENT;
			uip_arp_timer();
		}

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
				vParTestSetLED( 7, 1 );
				vParTestSetLED( 8, 1 );
				vParTestSetLED( 9, 1 );
				vParTestSetLED( 10, 1 );
			}
			else
			{
				/* Turn the LEDs off. */
				vParTestSetLED( 7, 0 );
				vParTestSetLED( 8, 0 );
				vParTestSetLED( 9, 0 );
				vParTestSetLED( 10, 0 );
			}
	    }
		else
		{
			/* Commands to turn LEDs off are not always explicit. */
			vParTestSetLED( 7, 0 );
			vParTestSetLED( 8, 0 );
			vParTestSetLED( 9, 0 );
			vParTestSetLED( 10, 0 );
		}
	}
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
	xARPTimer = xTimerCreate( 	( const signed char * const ) "ARPTimer", /* Just a name that is helpful for debugging, not used by the kernel. */
								( 500 / portTICK_RATE_MS ), /* Timer period. */
								pdTRUE, /* Autor-reload. */
								( void * ) uipARP_TIMER,
								prvUIPTimerCallback
							);

	xPeriodicTimer = xTimerCreate( 	( const signed char * const ) "PeriodicTimer",
									( 5000 / portTICK_RATE_MS ),
									pdTRUE, /* Autor-reload. */
									( void * ) uipPERIODIC_TIMER,
									prvUIPTimerCallback
								);

	configASSERT( xARPTimer );
	configASSERT( xPeriodicTimer );

	xTimerStart( xARPTimer, portMAX_DELAY );
	xTimerStart( xPeriodicTimer, portMAX_DELAY );
}
/*-----------------------------------------------------------*/

static void prvEMACEventListener( unsigned long ulISREvents )
{
long lHigherPriorityTaskWoken = pdFALSE;
unsigned long ulUIPEvents = 0UL;

	configASSERT( xEMACEventQueue );

	if( ( ulISREvents & MSS_MAC_EVENT_PACKET_SEND ) != 0UL )
	{
		ulUIP_Events |= uipETHERNET_TX_EVENT;
	}

	if( ( ulISREvents & MSS_MAC_EVENT_PACKET_RECEIVED ) != 0UL )
	{
		/* Wake the uIP task as new data has arrived. */
		ulUIPEvents |= uipETHERNET_RX_EVENT;
	}

	if( ulUIPEvents != 0UL )
	{
		xQueueSendFromISR( xEMACEventQueue, &ulUIPEvents, &lHigherPriorityTaskWoken );
	}

	portEND_SWITCHING_ISR( lHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvInitEmac( void )
{
const unsigned char ucPHYAddress = 1;

	MSS_MAC_init( ucPHYAddress );

	MSS_MAC_set_callback( prvEMACEventListener );

    /* Setup the EMAC and the NVIC for MAC interrupts. */
    NVIC_SetPriority( EthernetMAC_IRQn, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
    NVIC_EnableIRQ( EthernetMAC_IRQn );
}
/*-----------------------------------------------------------*/

void vEMACWrite( void )
{
const long lMaxAttempts = 10;
long lAttempt;
const portTickType xShortDelay = ( 10 / portTICK_RATE_MS );

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

long lEMACWaitForLink( void )
{
long lReturn = pdFAIL;
unsigned long ulStatus;

	ulStatus = MSS_MAC_link_status();
	if( ( ulStatus & ( unsigned long ) MSS_MAC_LINK_STATUS_LINK ) != 0UL )
	{
		lReturn = pdPASS;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

static void prvUIPTimerCallback( xTimerHandle xTimer )
{
static const unsigned long ulARPTimerExpired = uipARP_TIMER_EVENT;
static const unsigned long ulPeriodicTimerExpired = uipPERIODIC_TIMER_EVENT;

	/* This is a time callback, so calls to xQueueSend() must not attempt to
	block. */
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
