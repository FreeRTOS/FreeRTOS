/*
    FreeRTOS V6.0.0 - Copyright (C) 2009 Real Time Engineers Ltd.

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

/* Library includes. */
#include "91x_lib.h"
#include "91x_enet.h"

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

/*-----------------------------------------------------------*/

/* MAC address configuration. */
#define uipMAC_ADDR0	0x00
#define uipMAC_ADDR1	0x12
#define uipMAC_ADDR2	0x13
#define uipMAC_ADDR3	0x14
#define uipMAC_ADDR4	0x15
#define uipMAC_ADDR5	0x20

/* IP address configuration. */
#define uipIP_ADDR0		172
#define uipIP_ADDR1		25
#define uipIP_ADDR2		218
#define uipIP_ADDR3		11	

/* Netmask configuration. */
#define uipNET_MASK0	255
#define uipNET_MASK1	255
#define uipNET_MASK2	255
#define uipNET_MASK3	0

/* Gateway address configuration. */
#define uipGATEWAY_ADDR0 172
#define uipGATEWAY_ADDR1 25
#define uipGATEWAY_ADDR2 218
#define uipGATEWAY_ADDR3 1

/* Shortcut to the header within the Rx buffer. */
#define xHeader ((struct uip_eth_hdr *) &uip_buf[ 0 ])

/* uIP update frequencies. */
#define uipMAX_BLOCK_TIME	(configTICK_RATE_HZ / 4)

/* Interrupt status bit definition. */
#define uipDMI_RX_CURRENT_DONE 0x8000

/* If no buffers are available, then wait this long before looking again. */
#define uipBUFFER_WAIT_DELAY	( 10 / portTICK_RATE_MS )
#define uipBUFFER_WAIT_ATTEMPTS	( 10 )

/* Standard constant. */
#define uipTOTAL_FRAME_HEADER_SIZE	54

/*-----------------------------------------------------------*/

/*
 * Send the uIP buffer to the MAC.
 */
static void prvENET_Send(void);

/*
 * Setup the MAC address in the MAC itself, and in the uIP stack.
 */
static void prvSetMACAddress( void );

/*
 * Used to return a pointer to the next buffer to be used.
 */
extern unsigned char *pcGetNextBuffer( void );

/*
 * Port functions required by the uIP stack.
 */
void clock_init( void );
clock_time_t clock_time( void );

/*-----------------------------------------------------------*/

/* The semaphore used by the ISR to wake the uIP task. */
xSemaphoreHandle xSemaphore = NULL;

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

	/* Create the semaphore used by the ISR to wake this task. */
	vSemaphoreCreateBinary( xSemaphore );
	
	/* Initialise the uIP stack. */
	timer_set( &periodic_timer, configTICK_RATE_HZ / 2 );
	timer_set( &arp_timer, configTICK_RATE_HZ * 10 );
	uip_init();
	uip_ipaddr( xIPAddr, uipIP_ADDR0, uipIP_ADDR1, uipIP_ADDR2, uipIP_ADDR3 );
	uip_sethostaddr( xIPAddr );
	uip_ipaddr( xIPAddr, uipNET_MASK0, uipNET_MASK1, uipNET_MASK2, uipNET_MASK3 );
	uip_setnetmask( xIPAddr );
	uip_ipaddr( xIPAddr, uipGATEWAY_ADDR0, uipGATEWAY_ADDR1, uipGATEWAY_ADDR2, uipGATEWAY_ADDR3 );
	uip_setdraddr( xIPAddr );	
	httpd_init();

	/* Initialise the MAC. */
	ENET_InitClocksGPIO();
	ENET_Init();
	portENTER_CRITICAL();
	{
		ENET_Start();
		prvSetMACAddress();
		VIC_Config( ENET_ITLine, VIC_IRQ, 1 );
		VIC_ITCmd( ENET_ITLine, ENABLE );	
		ENET_DMA->ISR = uipDMI_RX_CURRENT_DONE;
 		ENET_DMA->IER = uipDMI_RX_CURRENT_DONE;
	}
	portEXIT_CRITICAL();
	

	while(1)
	{
		/* Is there received data ready to be processed? */
		uip_len = ENET_HandleRxPkt( uip_buf );
		
		if( uip_len > 0 )
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
					prvENET_Send();
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
					prvENET_Send();
				}
			}
		}
		else
		{
			if( timer_expired( &periodic_timer ) )
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
						prvENET_Send();
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
				xSemaphoreTake( xSemaphore, configTICK_RATE_HZ / 2 );			
			}
		}
	}
}
/*-----------------------------------------------------------*/

static void prvENET_Send(void)
{
portBASE_TYPE i;
static unsigned char *pcTxData;

	/* Get a DMA buffer into which we can write the data to send. */
	for( i = 0; i < uipBUFFER_WAIT_ATTEMPTS; i++ )
	{
		pcTxData = pcGetNextBuffer();

		if( pcTxData )
		{
			break;
		}
		else
		{
			vTaskDelay( uipBUFFER_WAIT_DELAY );
		}
	}
	
	if( pcTxData )
	{
		/* Copy the header into the Tx buffer. */
		memcpy( ( void * ) pcTxData, ( void * ) uip_buf, uipTOTAL_FRAME_HEADER_SIZE );
		if( uip_len > uipTOTAL_FRAME_HEADER_SIZE )
		{
			memcpy( ( void * ) &( pcTxData[ uipTOTAL_FRAME_HEADER_SIZE ] ), ( void * ) uip_appdata, ( uip_len - uipTOTAL_FRAME_HEADER_SIZE ) );
		}

		ENET_TxPkt( &pcTxData, uip_len );
	}
}
/*-----------------------------------------------------------*/

void ENET_IRQHandler(void)
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Give the semaphore in case the uIP task needs waking. */
	xSemaphoreGiveFromISR( xSemaphore, &xHigherPriorityTaskWoken );
	
	/* Clear the interrupt. */
	ENET_DMA->ISR = uipDMI_RX_CURRENT_DONE;
	
	/* Switch tasks if necessary. */	
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvSetMACAddress( void )
{
struct uip_eth_addr xAddr;

	/* Configure the MAC address in the uIP stack. */
	xAddr.addr[ 0 ] = uipMAC_ADDR0;
	xAddr.addr[ 1 ] = uipMAC_ADDR1;
	xAddr.addr[ 2 ] = uipMAC_ADDR2;
	xAddr.addr[ 3 ] = uipMAC_ADDR3;
	xAddr.addr[ 4 ] = uipMAC_ADDR4;
	xAddr.addr[ 5 ] = uipMAC_ADDR5;
	uip_setethaddr( xAddr );

	/* Write the MAC address to the MAC. */	
	ENET_MAC->MAL = ( uipMAC_ADDR3 << 24 ) | ( uipMAC_ADDR2 << 16 ) | ( uipMAC_ADDR1 << 8 ) | ( uipMAC_ADDR0 );
	ENET_MAC->MAH = ( uipMAC_ADDR5 << 8 ) | ( uipMAC_ADDR4 );
}

