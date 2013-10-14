/*
 * FreeRTOS+UDP V1.0.1 (C) 2013 Real Time Engineers ltd.
 * All rights reserved
 *
 * This file is part of the FreeRTOS+UDP distribution.  The FreeRTOS+UDP license
 * terms are different to the FreeRTOS license terms.
 *
 * FreeRTOS+UDP uses a dual license model that allows the software to be used 
 * under a standard GPL open source license, or a commercial license.  The 
 * standard GPL license (unlike the modified GPL license under which FreeRTOS 
 * itself is distributed) requires that all software statically linked with 
 * FreeRTOS+UDP is also distributed under the same GPL V2 license terms.  
 * Details of both license options follow:
 *
 * - Open source licensing -
 * FreeRTOS+UDP is a free download and may be used, modified, evaluated and
 * distributed without charge provided the user adheres to version two of the
 * GNU General Public License (GPL) and does not remove the copyright notice or
 * this text.  The GPL V2 text is available on the gnu.org web site, and on the
 * following URL: http://www.FreeRTOS.org/gpl-2.0.txt.
 *
 * - Commercial licensing -
 * Businesses and individuals that for commercial or other reasons cannot comply
 * with the terms of the GPL V2 license must obtain a commercial license before 
 * incorporating FreeRTOS+UDP into proprietary software for distribution in any 
 * form.  Commercial licenses can be purchased from http://shop.freertos.org/udp 
 * and do not require any source files to be changed.
 *
 * FreeRTOS+UDP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+UDP unless you agree that you use the software 'as is'.
 * FreeRTOS+UDP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/udp
 *
 */

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Sockets.h"
#include "NetworkBufferManagement.h"

/* Hardware includes. */
#include "hwEthernet.h"

/* Demo includes. */
#include "NetworkInterface.h"

#if ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES != 1
	#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eProcessBuffer
#else
	#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/* When a packet is ready to be sent, if it cannot be sent immediately then the
task performing the transmit will block for niTX_BUFFER_FREE_WAIT
milliseconds.  It will do this a maximum of niMAX_TX_ATTEMPTS before giving
up. */
#define niTX_BUFFER_FREE_WAIT	( ( portTickType ) 2UL / portTICK_RATE_MS )
#define niMAX_TX_ATTEMPTS		( 5 )

/* The length of the queue used to send interrupt status words from the
interrupt handler to the deferred handler task. */
#define niINTERRUPT_QUEUE_LENGTH	( 10 )

/*-----------------------------------------------------------*/

/*
 * A deferred interrupt handler task that processes
 */
extern void vEMACHandlerTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue used to communicate Ethernet events with the IP task. */
extern xQueueHandle xNetworkEventQueue;

/* The semaphore used to wake the deferred interrupt handler task when an Rx
interrupt is received. */
xSemaphoreHandle xEMACRxEventSemaphore = NULL;
/*-----------------------------------------------------------*/

portBASE_TYPE xNetworkInterfaceInitialise( void )
{
portBASE_TYPE xStatus, xReturn;
extern uint8_t ucMACAddress[ 6 ];

	/* Initialise the MAC. */
	vInitEmac();

	while( lEMACWaitForLink() != pdPASS )
    {
        vTaskDelay( 20 );
    }

	vSemaphoreCreateBinary( xEMACRxEventSemaphore );
	configASSERT( xEMACRxEventSemaphore );

	/* The handler task is created at the highest possible priority to
	ensure the interrupt handler can return directly to it. */
	xTaskCreate( vEMACHandlerTask, ( const signed char * const ) "EMAC", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, NULL );
	xReturn = pdPASS;

	return xReturn;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xNetworkInterfaceOutput( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
{
extern void vEMACCopyWrite( uint8_t * pucBuffer, uint16_t usLength );

	vEMACCopyWrite( pxNetworkBuffer->pucBuffer, pxNetworkBuffer->xDataLength );

	/* Finished with the network buffer. */
	vNetworkBufferRelease( pxNetworkBuffer );

	return pdTRUE;
}
/*-----------------------------------------------------------*/


