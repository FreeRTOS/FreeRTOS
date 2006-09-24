/*
	FreeRTOS.org V4.1.1 - Copyright (C) 2003-2006 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license
	and contact details.  Please ensure to read the configuration and relevant
	port sections of the online documentation.
	***************************************************************************
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
#define uipMAC_ADDR5	0x16

/* IP address configuration. */
#define uipIP_ADDR0		172
#define uipIP_ADDR1		25
#define uipIP_ADDR2		218
#define uipIP_ADDR3		26	

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
extern unsigned portCHAR *pcGetNextBuffer( void );

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
static unsigned portCHAR *pcTxData;

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

		/* If there is room, also copy in the application data if any. */
		if( ( uip_len > uipTOTAL_FRAME_HEADER_SIZE ) && ( uip_len <= ( ENET_BUFFER_SIZE - uipTOTAL_FRAME_HEADER_SIZE ) ) )
		{
			memcpy( ( void * ) &( pcTxData[ uipTOTAL_FRAME_HEADER_SIZE ] ), ( void * ) uip_appdata, ( uip_len - uipTOTAL_FRAME_HEADER_SIZE ) );
		}

		ENET_TxPkt( &pcTxData, uip_len );
	}
}
/*-----------------------------------------------------------*/

void ENET_IRQHandler(void)
{
portBASE_TYPE xSwitchRequired;

	/* Give the semaphore in case the uIP task needs waking. */
	xSwitchRequired = xSemaphoreGiveFromISR( xSemaphore, pdFALSE );
	
	/* Clear the interrupt. */
	ENET_DMA->ISR = uipDMI_RX_CURRENT_DONE;
	
	/* Switch tasks if necessary. */	
	portEND_SWITCHING_ISR( xSwitchRequired );
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

