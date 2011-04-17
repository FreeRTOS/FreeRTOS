/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Hardware driver includes. */
#include "mss_ethernet_mac.h"

/* uIP includes. */
#include "net/uip.h"

static void prvEMACEventListener( unsigned long ulEvents );

#define emacPHY_ADDRESS 1

/*-----------------------------------------------------------*/

/* The buffer used by the uIP stack to both receive and send.  This points to
one of the Ethernet buffers when its actually in use. */
unsigned char *uip_buf = NULL;

const unsigned char ucMACAddress[] = { configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5 };

/*-----------------------------------------------------------*/

void vInitEmac( void )
{
unsigned long ulMACCfg;

	MSS_MAC_init( emacPHY_ADDRESS );

	ulMACCfg = MSS_MAC_get_configuration();

	ulMACCfg &= ~( MSS_MAC_CFG_STORE_AND_FORWARD | MSS_MAC_CFG_PASS_BAD_FRAMES );
	ulMACCfg |=	( MSS_MAC_CFG_RECEIVE_ALL | MSS_MAC_CFG_PROMISCUOUS_MODE | MSS_MAC_CFG_FULL_DUPLEX_MODE | MSS_MAC_CFG_TRANSMIT_THRESHOLD_MODE | MSS_MAC_CFG_THRESHOLD_CONTROL_00 );
	MSS_MAC_configure( ulMACCfg );
	MSS_MAC_set_mac_address( ( unsigned char *) ucMACAddress );
	MSS_MAC_set_callback( prvEMACEventListener );
}
/*-----------------------------------------------------------*/

void vEMACWrite( void )
{
	MSS_MAC_tx_packet( uip_buf, uip_len, 0 );
}
/*-----------------------------------------------------------*/

unsigned long ulEMACRead( void )
{
	return MSS_MAC_rx_packet( &uip_buf, ( MSS_RX_BUFF_SIZE + 4 ), 0UL );
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

static void prvEMACEventListener( unsigned long ulEvents )
{
extern xSemaphoreHandle xEMACSemaphore;
long lHigherPriorityTaskWoken = pdFALSE;

	if( xEMACSemaphore != NULL )
	{
		if( ( ulEvents & MSS_MAC_EVENT_PACKET_SEND ) != 0UL )
		{
			/* Handle send event. */
		}

		if( ( ulEvents & MSS_MAC_EVENT_PACKET_RECEIVED ) != 0UL )
		{
			/* Wake the uIP task as new data has arrived. */
			xSemaphoreGiveFromISR( xEMACSemaphore, &lHigherPriorityTaskWoken );
		}
	}

	portEND_SWITCHING_ISR( lHigherPriorityTaskWoken );
}



