/*
	FreeRTOS V5.4.2 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

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
#include "uip.h"
#include "uip_arp.h"
#include "httpd.h"
#include "timer.h"
#include "clock-arch.h"
#include "timer.h"

/* Demo includes. */
#include "FEC.h"
#include "partest.h"

/*-----------------------------------------------------------*/

/* Shortcut to the header within the Rx buffer. */
#define xHeader ((struct uip_eth_hdr *) &uip_buf[ 0 ])

/*-----------------------------------------------------------*/

/*
 * Port functions required by the uIP stack.
 */
clock_time_t clock_time( void );

/*-----------------------------------------------------------*/

/* The semaphore used by the ISR to wake the uIP task. */
extern xSemaphoreHandle xFECSemaphore;

/*-----------------------------------------------------------*/

clock_time_t clock_time( void )
{
	return xTaskGetTickCount();
}


void vuIP_Task( void *pvParameters )
{
portBASE_TYPE i;
uip_ipaddr_t xIPAddr;
struct timer periodic_timer, arp_timer;
extern void ( vEMAC_ISR )( void );

	/* Just to get rid of the compiler warning. */
	( void ) pvParameters;

	/* Enable/Reset the Ethernet Controller */

	/* Create the semaphore used by the ISR to wake this task. */
	vSemaphoreCreateBinary( xFECSemaphore );
	
	/* Initialise the uIP stack. */
	timer_set( &periodic_timer, configTICK_RATE_HZ / 2 );
	timer_set( &arp_timer, configTICK_RATE_HZ * 10 );
	uip_init();
	uip_ipaddr( xIPAddr, configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3 );
	uip_sethostaddr( xIPAddr );
	uip_ipaddr( xIPAddr, configNET_MASK0, configNET_MASK1, configNET_MASK2, configNET_MASK3 );
	uip_setnetmask( xIPAddr );		
	httpd_init();

	vInitFEC();

	for( ;; )
	{
		/* Is there received data ready to be processed? */
		uip_len = ( unsigned short ) ulFECRx();
		
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
					vFECTx();
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
					vFECTx();
				}
			}			
		}
		else
		{
			if( ( timer_expired( &periodic_timer ) ) && ( uip_buf != NULL ) )
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
						vFECTx();
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
				xSemaphoreTake( xFECSemaphore, configTICK_RATE_HZ / 2 );			
			}
		}
	}
}
/*-----------------------------------------------------------*/

void vApplicationProcessFormInput( portCHAR *pcInputString, portBASE_TYPE xInputLength )
{
char *c;

	/* Just to get rid of the compiler warning - other ports/demos use the parameter. */
	( void ) xInputLength;

	/* Process the form input sent by the IO page of the served HTML. */

	c = strstr( pcInputString, "?" );

    if( c )
    {
		/* Turn LED's on or off in accordance with the check box status. */
		if( strstr( c, "LED3=1" ) != NULL )
		{
			/* Turn LED 3 on. */
			vParTestSetLED( 3, 1 );
		}
		else
		{
			/* Turn LED 3 off. */
			vParTestSetLED( 3, 0 );
		}		
    }
}

