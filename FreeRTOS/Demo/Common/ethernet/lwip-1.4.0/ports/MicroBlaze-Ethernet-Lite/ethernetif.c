/*
 * FreeRTOS Kernel V10.0.1
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* BSP includes. */
#include "xemaclite.h"
#include "xintc_l.h"

/* lwIP includes. */
#include "lwip/opt.h"
#include "lwip/def.h"
#include "lwip/mem.h"
#include "lwip/pbuf.h"
#include "lwip/sys.h"
#include <lwip/stats.h>
#include <lwip/snmp.h>
#include "netif/etharp.h"

/* Define those to better describe your network interface. */
#define IFNAME0 'e'
#define IFNAME1 'l'

/* When a packet is ready to be sent, if it cannot be sent immediately then
 * the task performing the transmit will block for netifTX_BUFFER_FREE_WAIT
 * milliseconds.  It will do this a maximum of netifMAX_TX_ATTEMPTS before
 * giving up.
 */
#define netifTX_BUFFER_FREE_WAIT	( ( TickType_t ) 2UL / portTICK_PERIOD_MS )
#define netifMAX_TX_ATTEMPTS		( 5 )

#define netifMAX_MTU 1500

struct xEthernetIf
{
	struct eth_addr *ethaddr;
	/* Add whatever per-interface state that is needed here. */
};

/*
 * Copy the received data into a pbuf.
 */
static struct pbuf *prvLowLevelInput( const unsigned char * const pucInputData, unsigned short usDataLength );

/*
 * Send data from a pbuf to the hardware.
 */
static err_t prvLowLevelOutput( struct netif *pxNetIf, struct pbuf *p );

/*
 * Perform any hardware and/or driver initialisation necessary.
 */
static void prvLowLevelInit( struct netif *pxNetIf );

/*
 * Functions that get registered as the Rx and Tx interrupt handers
 * respectively.
 */
static void prvRxHandler( void *pvNetIf );
static void prvTxHandler( void *pvUnused );


/*-----------------------------------------------------------*/

/* The instance of the xEmacLite IP being used in this driver. */
static XEmacLite xEMACInstance;

/*-----------------------------------------------------------*/

/**
 * In this function, the hardware should be initialized.
 * Called from ethernetif_init().
 *
 * @param pxNetIf the already initialized lwip network interface structure
 *		for this etherpxNetIf
 */
static void prvLowLevelInit( struct netif *pxNetIf )
{
portBASE_TYPE xStatus;
extern void vInitialisePHY( XEmacLite *xemaclitep );
unsigned portBASE_TYPE uxOriginalPriority;

	/* Hardware initialisation can take some time, so temporarily lower the
	task priority to ensure other functionality is not adversely effected.
	The priority will get raised again before this function exits. */
	uxOriginalPriority = uxTaskPriorityGet( NULL );
	vTaskPrioritySet( NULL, tskIDLE_PRIORITY );

	/* set MAC hardware address length */
	pxNetIf->hwaddr_len = ETHARP_HWADDR_LEN;

	/* set MAC hardware address */
	pxNetIf->hwaddr[ 0 ] = configMAC_ADDR0;
	pxNetIf->hwaddr[ 1 ] = configMAC_ADDR1;
	pxNetIf->hwaddr[ 2 ] = configMAC_ADDR2;
	pxNetIf->hwaddr[ 3 ] = configMAC_ADDR3;
	pxNetIf->hwaddr[ 4 ] = configMAC_ADDR4;
	pxNetIf->hwaddr[ 5 ] = configMAC_ADDR5;

	/* device capabilities */
	pxNetIf->flags = NETIF_FLAG_BROADCAST | NETIF_FLAG_ETHARP | NETIF_FLAG_LINK_UP;

	/* maximum transfer unit */
	pxNetIf->mtu = netifMAX_MTU;

	/* Broadcast capability */
	pxNetIf->flags = NETIF_FLAG_BROADCAST | NETIF_FLAG_ETHARP | NETIF_FLAG_LINK_UP;

	/* Initialize the mac */
	xStatus = XEmacLite_Initialize( &xEMACInstance, XPAR_EMACLITE_0_DEVICE_ID );

	if( xStatus == XST_SUCCESS )
	{
		/* Set mac address */
		XEmacLite_SetMacAddress( &xEMACInstance, ( Xuint8* )( pxNetIf->hwaddr ) );

		/* Flush any frames already received */
		XEmacLite_FlushReceive( &xEMACInstance );

		/* Set Rx, Tx interrupt handlers */
		XEmacLite_SetRecvHandler( &xEMACInstance, ( void * ) pxNetIf, prvRxHandler );
		XEmacLite_SetSendHandler( &xEMACInstance, NULL, prvTxHandler );

		/* Enable Rx, Tx interrupts */
		XEmacLite_EnableInterrupts( &xEMACInstance );

		/* Install the standard Xilinx library interrupt handler itself.
		*NOTE* The xPortInstallInterruptHandler() API function must be used
		for	this purpose. */
		xStatus = xPortInstallInterruptHandler( XPAR_INTC_0_EMACLITE_0_VEC_ID, ( XInterruptHandler ) XEmacLite_InterruptHandler, &xEMACInstance );

		vInitialisePHY( &xEMACInstance );

		/* Enable the interrupt in the interrupt controller.
		*NOTE* The vPortEnableInterrupt() API function must be used for this
		purpose. */
		vPortEnableInterrupt( XPAR_INTC_0_EMACLITE_0_VEC_ID );
	}

	/* Reset the task priority back to its original value. */
	vTaskPrioritySet( NULL, uxOriginalPriority );

	configASSERT( xStatus == pdPASS );
}

/**
 * This function should do the actual transmission of the packet. The packet is
 * contained in the pbuf that is passed to the function. This pbuf
 * might be chained.
 *
 * @param pxNetIf the lwip network interface structure for this etherpxNetIf
 * @param p the MAC packet to send (e.g. IP packet including MAC addresses and type)
 * @return ERR_OK if the packet could be sent
 *		 an err_t value if the packet couldn't be sent
 *
 * @note Returning ERR_MEM here if a DMA queue of your MAC is full can lead to
 *	   strange results. You might consider waiting for space in the DMA queue
 *	   to become availale since the stack doesn't retry to send a packet
 *	   dropped because of memory failure (except for the TCP timers).
 */

static err_t prvLowLevelOutput( struct netif *pxNetIf, struct pbuf *p )
{

	/* This is taken from lwIP example code and therefore does not conform
	to the FreeRTOS coding standard. */

struct pbuf *q;
static unsigned char ucBuffer[ 1520 ] __attribute__((aligned(32)));
unsigned char *pucBuffer = ucBuffer;
unsigned char *pucChar;
struct eth_hdr *pxHeader;
u16_t usTotalLength = p->tot_len - ETH_PAD_SIZE;
err_t xReturn = ERR_OK;
long x;

	( void ) pxNetIf;

	#if defined(LWIP_DEBUG) && LWIP_NETIF_TX_SINGLE_PBUF
		LWIP_ASSERT("p->next == NULL && p->len == p->tot_len", p->next == NULL && p->len == p->tot_len);
	#endif

	/* Initiate transfer. */
	if( p->len == p->tot_len ) 
	{
		/* No pbuf chain, don't have to copy -> faster. */
		pucBuffer = &( ( unsigned char * ) p->payload )[ ETH_PAD_SIZE ];
	} 
	else 
	{
		/* pbuf chain, copy into contiguous ucBuffer. */
		if( p->tot_len >= sizeof( ucBuffer ) )
		{
			LINK_STATS_INC( link.lenerr );
			LINK_STATS_INC( link.drop );
			snmp_inc_ifoutdiscards( pxNetIf );
			xReturn = ERR_BUF;
		}
		else
		{
			pucChar = ucBuffer;

			for( q = p; q != NULL; q = q->next )
			{
				/* Send the data from the pbuf to the interface, one pbuf at a
				time. The size of the data in each pbuf is kept in the ->len
				variable. */
				/* send data from(q->payload, q->len); */
				LWIP_DEBUGF( NETIF_DEBUG, ( "NETIF: send pucChar %p q->payload %p q->len %i q->next %p\n", pucChar, q->payload, ( int ) q->len, ( void* ) q->next ) );
				if( q == p )
				{
					memcpy( pucChar, &( ( char * ) q->payload )[ ETH_PAD_SIZE ], q->len - ETH_PAD_SIZE );
					pucChar += q->len - ETH_PAD_SIZE;
				}
				else
				{
					memcpy( pucChar, q->payload, q->len );
					pucChar += q->len;
				}
			}
		}
	}

	if( xReturn == ERR_OK )
	{
		for( x = 0; x < netifMAX_TX_ATTEMPTS; x++ )
		{
			xReturn =  XEmacLite_Send( &xEMACInstance, pucBuffer, ( int ) usTotalLength );
			if( xReturn == XST_SUCCESS )
			{
				break;
			}
			else
			{
				vTaskDelay( netifTX_BUFFER_FREE_WAIT );
			}
		}

		if( xReturn != XST_SUCCESS )
		{
			LINK_STATS_INC( link.memerr );
			LINK_STATS_INC( link.drop );
			snmp_inc_ifoutdiscards( pxNetIf );
			xReturn = ERR_BUF;
		}
		else
		{
			LINK_STATS_INC( link.xmit );
			snmp_add_ifoutoctets( pxNetIf, usTotalLength );
			pxHeader = ( struct eth_hdr * )p->payload;

			if( ( pxHeader->dest.addr[ 0 ] & 1 ) != 0 ) 
			{
				/* broadcast or multicast packet*/
				snmp_inc_ifoutnucastpkts( pxNetIf );
			} 
			else 
			{
				/* unicast packet */
				snmp_inc_ifoutucastpkts( pxNetIf );
			}
		}
	}

	return xReturn;
}

/**
 * Should allocate a pbuf and transfer the bytes of the incoming
 * packet from the interface into the pbuf.
 *
 * @param pxNetIf the lwip network interface structure for this etherpxNetIf
 * @return a pbuf filled with the received packet (including MAC header)
 *		 NULL on memory error
 */
static struct pbuf *prvLowLevelInput( const unsigned char * const pucInputData, unsigned short usDataLength )
{
struct pbuf *p = NULL, *q;

	if( usDataLength > 0U )
	{
		#if ETH_PAD_SIZE
			len += ETH_PAD_SIZE; /* allow room for Ethernet padding */
		#endif

		/* We allocate a pbuf chain of pbufs from the pool. */
		p = pbuf_alloc( PBUF_RAW, usDataLength, PBUF_POOL );
  
		if( p != NULL ) 
		{
			#if ETH_PAD_SIZE
				pbuf_header( p, -ETH_PAD_SIZE ); /* drop the padding word */
			#endif

			/* We iterate over the pbuf chain until we have read the entire
			* packet into the pbuf. */
			usDataLength = 0U;
			for( q = p; q != NULL; q = q->next ) 
			{
				/* Read enough bytes to fill this pbuf in the chain. The
				* available data in the pbuf is given by the q->len
				* variable.
				* This does not necessarily have to be a memcpy, you can also preallocate
				* pbufs for a DMA-enabled MAC and after receiving truncate it to the
				* actually received size. In this case, ensure the usTotalLength member of the
				* pbuf is the sum of the chained pbuf len members.
				*/
				memcpy( q->payload, &( pucInputData[ usDataLength ] ), q->len );
				usDataLength += q->len;
			}

			#if ETH_PAD_SIZE
				pbuf_header( p, ETH_PAD_SIZE ); /* reclaim the padding word */
			#endif

			LINK_STATS_INC(link.recv);
		}
	}

	return p;  
}

/**
 * Should be called at the beginning of the program to set up the
 * network interface. It calls the function prvLowLevelInit() to do the
 * actual setup of the hardware.
 *
 * This function should be passed as a parameter to pxNetIf_add().
 *
 * @param pxNetIf the lwip network interface structure for this etherpxNetIf
 * @return ERR_OK if the loopif is initialized
 *		 ERR_MEM if private data couldn't be allocated
 *		 any other err_t on error
 */
err_t ethernetif_init( struct netif *pxNetIf )
{
err_t xReturn = ERR_OK;

	/* This is taken from lwIP example code and therefore does not conform
	to the FreeRTOS coding standard. */
	
struct xEthernetIf *pxEthernetIf;

	LWIP_ASSERT( "pxNetIf != NULL", ( pxNetIf != NULL ) );
	
	pxEthernetIf = mem_malloc( sizeof( struct xEthernetIf ) );
	if( pxEthernetIf == NULL ) 
	{
		LWIP_DEBUGF(NETIF_DEBUG, ( "ethernetif_init: out of memory\n" ) );
		xReturn = ERR_MEM;
	}
	else
	{
		#if LWIP_NETIF_HOSTNAME
		{
			/* Initialize interface hostname */
			pxNetIf->hostname = "lwip";
		}
		#endif /* LWIP_NETIF_HOSTNAME */

		pxNetIf->state = pxEthernetIf;
		pxNetIf->name[ 0 ] = IFNAME0;
		pxNetIf->name[ 1 ] = IFNAME1;

		/* We directly use etharp_output() here to save a function call.
		* You can instead declare your own function an call etharp_output()
		* from it if you have to do some checks before sending (e.g. if link
		* is available...) */
		pxNetIf->output = etharp_output;
		pxNetIf->flags = NETIF_FLAG_BROADCAST | NETIF_FLAG_ETHARP | NETIF_FLAG_IGMP;
		pxNetIf->hwaddr_len = ETHARP_HWADDR_LEN;
		pxNetIf->mtu = netifMAX_MTU;
		pxNetIf->linkoutput = prvLowLevelOutput;

		pxEthernetIf->ethaddr = ( struct eth_addr * ) &( pxNetIf->hwaddr[ 0 ] );

		/* initialize the hardware */
		prvLowLevelInit( pxNetIf );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static void prvRxHandler( void *pvNetIf )
{
	/* This is taken from lwIP example code and therefore does not conform
	to the FreeRTOS coding standard. */

struct eth_hdr *pxHeader;
struct pbuf *p;
unsigned short usInputLength;
static unsigned char ucBuffer[ 1520 ] __attribute__((aligned(32)));
extern portBASE_TYPE xInsideISR;
struct netif *pxNetIf = ( struct netif * ) pvNetIf;

	XIntc_AckIntr( XPAR_ETHERNET_LITE_BASEADDR, XPAR_ETHERNET_LITE_IP2INTC_IRPT_MASK );

	/* Ensure the pbuf handling functions don't attempt to use critical
	sections. */
	xInsideISR++;

	usInputLength = ( long ) XEmacLite_Recv( &xEMACInstance, ucBuffer );

	/* move received packet into a new pbuf */
	p = prvLowLevelInput( ucBuffer, usInputLength );

	/* no packet could be read, silently ignore this */
	if( p != NULL )
	{
		/* points to packet payload, which starts with an Ethernet header */
		pxHeader = p->payload;

		switch( htons( pxHeader->type ) )
		{
			/* IP or ARP packet? */
			case ETHTYPE_IP:
			case ETHTYPE_ARP:
								/* full packet send to tcpip_thread to process */
								if( pxNetIf->input( p, pxNetIf ) != ERR_OK )
								{
									LWIP_DEBUGF(NETIF_DEBUG, ( "ethernetif_input: IP input error\n" ) );
									pbuf_free(p);
									p = NULL;
								}
								break;

			default:
								pbuf_free( p );
								p = NULL;
			break;
		}
	}

	xInsideISR--;
}
/*-----------------------------------------------------------*/

static void prvTxHandler( void *pvUnused )
{
	( void ) pvUnused;
	XIntc_AckIntr( XPAR_ETHERNET_LITE_BASEADDR, XPAR_ETHERNET_LITE_IP2INTC_IRPT_MASK );
}




