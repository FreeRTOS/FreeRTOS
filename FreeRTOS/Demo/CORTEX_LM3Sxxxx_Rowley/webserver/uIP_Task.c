/*
 * FreeRTOS Kernel V10.4.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
#include "semphr.h"

#include "lcd_message.h"

/* uip includes. */
#include "hw_types.h"

#include "uip.h"
#include "uip_arp.h"
#include "httpd.h"
#include "timer.h"
#include "clock-arch.h"
#include "hw_ethernet.h"
#include "ethernet.h"
#include "hw_memmap.h"
#include "lmi_flash.h"
#include "sysctl.h"

/* Demo includes. */
#include "emac.h"
#include "partest.h"

/*-----------------------------------------------------------*/

/* IP address configuration. */
#define uipIP_ADDR0		192
#define uipIP_ADDR1		168
#define uipIP_ADDR2		0
#define uipIP_ADDR3		201

/* Netmask configuration. */
#define uipNETMASK_0	255
#define uipNETMASK_1	255
#define uipNETMASK_2	255
#define uipNETMASK_3	0

/* How long to wait before attempting to connect the MAC again. */
#define uipINIT_WAIT    100

/* Shortcut to the header within the Rx buffer. */
#define xHeader ((struct uip_eth_hdr *) &uip_buf[ 0 ])

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
 * Port functions required by the uIP stack.
 */
void clock_init( void );
clock_time_t clock_time( void );

/*-----------------------------------------------------------*/

/* The semaphore used by the ISR to wake the uIP task. */
extern SemaphoreHandle_t xEMACSemaphore;

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


void vuIP_Task( void *pvParameters )
{
portBASE_TYPE i;
uip_ipaddr_t xIPAddr;
struct timer periodic_timer, arp_timer;
extern void ( vEMAC_ISR )( void );

	/* Enable/Reset the Ethernet Controller */
	SysCtlPeripheralEnable( SYSCTL_PERIPH_ETH );
	SysCtlPeripheralReset( SYSCTL_PERIPH_ETH );

	/* Create the semaphore used by the ISR to wake this task. */
	vSemaphoreCreateBinary( xEMACSemaphore );

	/* Initialise the uIP stack. */
	timer_set( &periodic_timer, configTICK_RATE_HZ / 2 );
	timer_set( &arp_timer, configTICK_RATE_HZ * 10 );
	uip_init();
	uip_ipaddr( xIPAddr, uipIP_ADDR0, uipIP_ADDR1, uipIP_ADDR2, uipIP_ADDR3 );
	uip_sethostaddr( xIPAddr );
	uip_ipaddr( xIPAddr, uipNETMASK_0, uipNETMASK_1, uipNETMASK_2, uipNETMASK_3 );
    uip_setnetmask( xIPAddr );
	httpd_init();

	while( vInitEMAC() != pdPASS )
    {
        vTaskDelay( uipINIT_WAIT );
    }
	prvSetMACAddress();


	for( ;; )
	{
		/* Is there received data ready to be processed? */
		uip_len = uiGetEMACRxData( uip_buf );

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
				xSemaphoreTake( xEMACSemaphore, configTICK_RATE_HZ / 2 );
			}
		}
	}
}
/*-----------------------------------------------------------*/

static void prvENET_Send(void)
{
    vInitialiseSend();
    vIncrementTxLength( uip_len );
    vSendBufferToMAC();
    vInitialiseSend();
    vIncrementTxLength( uip_len );
    vSendBufferToMAC();
}
/*-----------------------------------------------------------*/

static void prvSetMACAddress( void )
{
unsigned long ulUser0, ulUser1;
unsigned char pucMACArray[8];
struct uip_eth_addr xAddr;

	/* Get the device MAC address from flash */
    FlashUserGet(&ulUser0, &ulUser1);

	/* Convert the MAC address from flash into sequence of bytes. */
    pucMACArray[0] = ((ulUser0 >>  0) & 0xff);
    pucMACArray[1] = ((ulUser0 >>  8) & 0xff);
    pucMACArray[2] = ((ulUser0 >> 16) & 0xff);
    pucMACArray[3] = ((ulUser1 >>  0) & 0xff);
    pucMACArray[4] = ((ulUser1 >>  8) & 0xff);
    pucMACArray[5] = ((ulUser1 >> 16) & 0xff);

	/* Program the MAC address. */
    EthernetMACAddrSet(ETH_BASE, pucMACArray);

	xAddr.addr[ 0 ] = pucMACArray[0];
	xAddr.addr[ 1 ] = pucMACArray[1];
	xAddr.addr[ 2 ] = pucMACArray[2];
	xAddr.addr[ 3 ] = pucMACArray[3];
	xAddr.addr[ 4 ] = pucMACArray[4];
	xAddr.addr[ 5 ] = pucMACArray[5];
	uip_setethaddr( xAddr );
}
/*-----------------------------------------------------------*/

void vApplicationProcessFormInput( char *pcInputString, portBASE_TYPE xInputLength )
{
char *c, *pcText;
static char cMessageForDisplay[ 32 ];
extern QueueHandle_t xOLEDQueue;
xOLEDMessage xOLEDMessage;

	/* Process the form input sent by the IO page of the served HTML. */

	c = strstr( pcInputString, "?" );

    if( c )
    {
		/* Turn LED's on or off in accordance with the check box status. */
		if( strstr( c, "LED0=1" ) != NULL )
		{
			vParTestSetLED( 0, 1 );
		}
		else
		{
			vParTestSetLED( 0, 0 );
		}

		/* Find the start of the text to be displayed on the LCD. */
        pcText = strstr( c, "LCD=" );
        pcText += strlen( "LCD=" );

        /* Terminate the file name for further processing within uIP. */
        *c = 0x00;

        /* Terminate the LCD string. */
        c = strstr( pcText, " " );
        if( c != NULL )
        {
            *c = 0x00;
        }

        /* Add required spaces. */
        while( ( c = strstr( pcText, "+" ) ) != NULL )
        {
            *c = ' ';
        }

        /* Write the message to the LCD. */
		strcpy( cMessageForDisplay, pcText );
		xOLEDMessage.pcMessage = cMessageForDisplay;
        xQueueSend( xOLEDQueue, &xOLEDMessage, portMAX_DELAY );
    }
}

