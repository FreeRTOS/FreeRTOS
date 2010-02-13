/*
    FreeRTOS V6.0.2 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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
#include "semphr.h"

/* uip includes. */
#include "net/uip.h"
#include "net/uip_arp.h"
#include "apps/httpd/httpd.h"
#include "sys/timer.h"
#include "net/clock-arch.h"

/* Demo includes. */
#include "ParTest.h"

/* Hardware includes. */
#include "hwEthernet.h"

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
 * Port functions required by the uIP stack.
 */
void clock_init( void );
clock_time_t clock_time( void );

/*-----------------------------------------------------------*/

/* The semaphore used by the ISR to wake the uIP task. */
xSemaphoreHandle xEMACSemaphore = NULL;

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
uip_ipaddr_t xIPAddr;
struct timer periodic_timer, arp_timer;
extern void ( vEMAC_ISR_Wrapper )( void );

	( void ) pvParameters;

	/* Initialise the uIP stack. */
	timer_set( &periodic_timer, configTICK_RATE_HZ / 2 );
	timer_set( &arp_timer, configTICK_RATE_HZ * 10 );
	uip_init();
	uip_ipaddr( &xIPAddr, configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3 );
	uip_sethostaddr( &xIPAddr );
	uip_ipaddr( &xIPAddr, configNET_MASK0, configNET_MASK1, configNET_MASK2, configNET_MASK3 );
	uip_setnetmask( &xIPAddr );
	prvSetMACAddress();
	httpd_init();

	/* Create the semaphore used to wake the uIP task. */
	vSemaphoreCreateBinary( xEMACSemaphore );

	/* Initialise the MAC. */
	vInitEmac();

	while( lEMACWaitForLink() != pdPASS )
    {
        vTaskDelay( uipINIT_WAIT );
    }

	for( ;; )
	{
		/* Is there received data ready to be processed? */
		uip_len = ( unsigned short ) ulEMACRead();
		
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
		else
		{
			if( timer_expired( &periodic_timer ) && ( uip_buf != NULL ) )
			{
				timer_reset( &periodic_timer );
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

				/* Call the ARP timer function every 10 seconds. */
				if( timer_expired( &arp_timer ) )
				{
					timer_reset( &arp_timer );
					uip_arp_timer();
				}
			}
			else
			{
				/* We did not receive a packet, and there was no periodic
				processing to perform.  Block for a fixed period.  If a packet
				is received during this period we will be woken by the ISR
				giving us the Semaphore. */
				xSemaphoreTake( xEMACSemaphore, configTICK_RATE_HZ / 2 );
			}
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
//extern void vParTestSetLEDState( long lState );

	/* Process the form input sent by the IO page of the served HTML. */

	c = strstr( pcInputString, "?" );
    if( c )
    {
		/* Turn the FIO1 LED's on or off in accordance with the check box status. */
		if( strstr( c, "LED0=1" ) != NULL )
		{
//			vParTestSetLEDState( pdTRUE );
		}
		else
		{
//			vParTestSetLEDState( pdFALSE );
		}
    }
}

