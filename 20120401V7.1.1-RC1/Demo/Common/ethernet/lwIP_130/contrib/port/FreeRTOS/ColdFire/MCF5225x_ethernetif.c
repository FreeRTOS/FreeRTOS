/*
 * Copyright (c) 2001-2004 Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT
 * SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 * This file is part of the lwIP TCP/IP stack.
 *
 * Author: Adam Dunkels <adam@sics.se>
 *
 */

/* Standard library includes. */
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

xTaskHandle xEthIntTask;

/* lwIP includes. */
#include "lwip/def.h"
#include "lwip/mem.h"
#include "lwip/pbuf.h"
#include "lwip/sys.h"
#include "lwip/stats.h"
#include "lwip/snmp.h"
#include "netif/etharp.h"

/* Hardware includes. */
#include "fec.h"

/* Delay to wait for a DMA buffer to become available if one is not already
available. */
#define netifBUFFER_WAIT_ATTEMPTS					10
#define netifBUFFER_WAIT_DELAY						(10 / portTICK_RATE_MS)

/* Delay between polling the PHY to see if a link has been established. */
#define netifLINK_DELAY								( 500 / portTICK_RATE_MS )

/* Delay between looking for incoming packets.  In ideal world this would be
infinite. */
#define netifBLOCK_TIME_WAITING_FOR_INPUT			netifLINK_DELAY

/* Name for the netif. */
#define IFNAME0 'e'
#define IFNAME1 'n'

/* Hardware specific. */
#define netifFIRST_FEC_VECTOR						23

/*-----------------------------------------------------------*/

/* The DMA descriptors.  This is a char array to allow us to align it correctly. */
static unsigned char xFECTxDescriptors_unaligned[ ( configNUM_FEC_TX_BUFFERS * sizeof( FECBD ) ) + 16 ];
static unsigned char xFECRxDescriptors_unaligned[ ( configNUM_FEC_RX_BUFFERS * sizeof( FECBD ) ) + 16 ];
static FECBD *xFECTxDescriptors;
static FECBD *xFECRxDescriptors;

/* The DMA buffers.  These are char arrays to allow them to be alligned correctly. */
static unsigned char ucFECTxBuffers[ ( configNUM_FEC_TX_BUFFERS * configFEC_BUFFER_SIZE ) + 16 ];
static unsigned char ucFECRxBuffers[ ( configNUM_FEC_RX_BUFFERS * configFEC_BUFFER_SIZE ) + 16 ];
static unsigned portBASE_TYPE uxNextRxBuffer = 0, uxNextTxBuffer = 0;

/* Semaphore used by the FEC interrupt handler to wake the handler task. */
static xSemaphoreHandle xFecSemaphore;

#pragma options align= packed
struct ethernetif
{
  struct eth_addr *ethaddr;
  /* Add whatever per-interface state that is needed here. */
};

/*-----------------------------------------------------------*/

/* Standard lwIP netif handlers. */
static void prvInitialiseFECBuffers( void );
static void low_level_init( struct netif *netif );
static err_t low_level_output(struct netif *netif, struct pbuf *p);
static struct pbuf *low_level_input(struct netif *netif);
static void ethernetif_input( void *pParams );

/* Functions adapted from Freescale provided code. */
static int fec_mii_write( int phy_addr, int reg_addr, int data );
static int fec_mii_read( int phy_addr, int reg_addr, uint16* data );
static uint8 fec_hash_address( const uint8* addr );
static void fec_set_address( const uint8 *pa );
static void fec_irq_enable( void );

/*-----------------------------------------------------------*/

/********************************************************************/
/*
 * Write a value to a PHY's MII register.
 *
 * Parameters:
 *  ch          FEC channel
 *  phy_addr    Address of the PHY.
 *  reg_addr    Address of the register in the PHY.
 *  data        Data to be written to the PHY register.
 *
 * Return Values:
 *  0 on failure
 *  1 on success.
 *
 * Please refer to your PHY manual for registers and their meanings.
 * mii_write() polls for the FEC's MII interrupt event and clears it. 
 * If after a suitable amount of time the event isn't triggered, a 
 * value of 0 is returned.
 */
static int fec_mii_write( int phy_addr, int reg_addr, int data )
{
int timeout;
uint32 eimr;

	/* Clear the MII interrupt bit */
	MCF_FEC_EIR = MCF_FEC_EIR_MII;

	/* Mask the MII interrupt */
	eimr = MCF_FEC_EIMR;
	MCF_FEC_EIMR &= ~MCF_FEC_EIMR_MII;

	/* Write to the MII Management Frame Register to kick-off the MII write */
	MCF_FEC_MMFR = MCF_FEC_MMFR_ST_01 | MCF_FEC_MMFR_OP_WRITE | MCF_FEC_MMFR_PA(phy_addr) | MCF_FEC_MMFR_RA(reg_addr) | MCF_FEC_MMFR_TA_10 | MCF_FEC_MMFR_DATA( data );

	/* Poll for the MII interrupt (interrupt should be masked) */
	for (timeout = 0; timeout < MII_TIMEOUT; timeout++)
	{
		if (MCF_FEC_EIR & MCF_FEC_EIR_MII)
		{
			break;
		}
	}

	if( timeout == MII_TIMEOUT )
	{
		return 0;
	}

	/* Clear the MII interrupt bit */
	MCF_FEC_EIR = MCF_FEC_EIR_MII;

	/* Restore the EIMR */
	MCF_FEC_EIMR = eimr;

	return 1;
}

/********************************************************************/
/*
 * Read a value from a PHY's MII register.
 *
 * Parameters:
 *  ch          FEC channel
 *  phy_addr    Address of the PHY.
 *  reg_addr    Address of the register in the PHY.
 *  data        Pointer to storage for the Data to be read
 *              from the PHY register (passed by reference)
 *
 * Return Values:
 *  0 on failure
 *  1 on success.
 *
 * Please refer to your PHY manual for registers and their meanings.
 * mii_read() polls for the FEC's MII interrupt event and clears it. 
 * If after a suitable amount of time the event isn't triggered, a 
 * value of 0 is returned.
 */
static int fec_mii_read( int phy_addr, int reg_addr, uint16* data )
{
int timeout;
uint32 eimr;

	/* Clear the MII interrupt bit */
	MCF_FEC_EIR = MCF_FEC_EIR_MII;

	/* Mask the MII interrupt */
	eimr = MCF_FEC_EIMR;
	MCF_FEC_EIMR &= ~MCF_FEC_EIMR_MII;

	/* Write to the MII Management Frame Register to kick-off the MII read */
	MCF_FEC_MMFR = MCF_FEC_MMFR_ST_01 | MCF_FEC_MMFR_OP_READ | MCF_FEC_MMFR_PA(phy_addr) | MCF_FEC_MMFR_RA(reg_addr) | MCF_FEC_MMFR_TA_10;

	/* Poll for the MII interrupt (interrupt should be masked) */
	for (timeout = 0; timeout < MII_TIMEOUT; timeout++)
	{
		if (MCF_FEC_EIR & MCF_FEC_EIR_MII)
		{
			break;
		}
	}

	if(timeout == MII_TIMEOUT)
	{
		return 0;
	}

	/* Clear the MII interrupt bit */
	MCF_FEC_EIR = MCF_FEC_EIR_MII;

	/* Restore the EIMR */
	MCF_FEC_EIMR = eimr;

	*data = (uint16)(MCF_FEC_MMFR & 0x0000FFFF);

	return 1;
}


/********************************************************************/
/*
 * Generate the hash table settings for the given address
 *
 * Parameters:
 *  addr    48-bit (6 byte) Address to generate the hash for
 *
 * Return Value:
 *  The 6 most significant bits of the 32-bit CRC result
 */
static uint8 fec_hash_address( const uint8* addr )
{
uint32 crc;
uint8 byte;
int i, j;

	crc = 0xFFFFFFFF;
	for(i=0; i<6; ++i)
	{
		byte = addr[i];
		for(j=0; j<8; ++j)
		{
			if((byte & 0x01)^(crc & 0x01))
			{
				crc >>= 1;
				crc = crc ^ 0xEDB88320;
			}
			else
			{
				crc >>= 1;
			}

			byte >>= 1;
		}
	}

	return (uint8)(crc >> 26);
}

/********************************************************************/
/*
 * Set the Physical (Hardware) Address and the Individual Address
 * Hash in the selected FEC
 *
 * Parameters:
 *  ch  FEC channel
 *  pa  Physical (Hardware) Address for the selected FEC
 */
static void fec_set_address( const uint8 *pa )
{
	uint8 crc;

	/*
	* Set the Physical Address
	*/
	MCF_FEC_PALR = (uint32)((pa[0]<<24) | (pa[1]<<16) | (pa[2]<<8) | pa[3]);
	MCF_FEC_PAUR = (uint32)((pa[4]<<24) | (pa[5]<<16));

	/*
	* Calculate and set the hash for given Physical Address
	* in the  Individual Address Hash registers
	*/
	crc = fec_hash_address(pa);
	if(crc >= 32)
	{
		MCF_FEC_IAUR |= (uint32)(1 << (crc - 32));
	}
	else
	{
		MCF_FEC_IALR |= (uint32)(1 << crc);
	}
}


/********************************************************************/
/*
 * Enable interrupts on the selected FEC
 *
 */
static void fec_irq_enable( void )
{
int fec_vbase;

#if INTC_LVL_FEC > configMAX_SYSCALL_INTERRUPT_PRIORITY
	#error INTC_LVL_FEC must be less than or equal to configMAX_SYSCALL_INTERRUPT_PRIORITY
#endif

	fec_vbase = 64 + netifFIRST_FEC_VECTOR;
    
	/* Enable FEC interrupts to the ColdFire core 
	 * Setup each ICR with a unique interrupt level combination */
	fec_vbase -= 64;

	/* FEC Rx Frame */
	MCF_INTC0_ICR(fec_vbase+4)  = MCF_INTC_ICR_IL(INTC_LVL_FEC);

	/* FEC Rx Buffer */                              
	MCF_INTC0_ICR(fec_vbase+5)  = MCF_INTC_ICR_IL(INTC_LVL_FEC);

	/* FEC FIFO Underrun */                              
	MCF_INTC0_ICR(fec_vbase+2)  = MCF_INTC_ICR_IL(INTC_LVL_FEC+1);

	/* FEC Collision Retry Limit */                              
	MCF_INTC0_ICR(fec_vbase+3)  = MCF_INTC_ICR_IL(INTC_LVL_FEC+1);

	/* FEC Late Collision */                                 
	MCF_INTC0_ICR(fec_vbase+7)  = MCF_INTC_ICR_IL(INTC_LVL_FEC+1);

	/* FEC Heartbeat Error */                                
	MCF_INTC0_ICR(fec_vbase+8)  = MCF_INTC_ICR_IL(INTC_LVL_FEC+1);

	/* FEC Bus Error */                              
	MCF_INTC0_ICR(fec_vbase+10) = MCF_INTC_ICR_IL(INTC_LVL_FEC+1);

	/* FEC Babbling Transmit */                              
	MCF_INTC0_ICR(fec_vbase+11) = MCF_INTC_ICR_IL(INTC_LVL_FEC+1);

	/* FEC Babbling Receive */                               
	MCF_INTC0_ICR(fec_vbase+12) = MCF_INTC_ICR_IL(INTC_LVL_FEC+1);
                                 
	/* Enable the FEC interrupts in the mask register */    
	MCF_INTC0_IMRH &= ~( MCF_INTC_IMRH_INT_MASK33 | MCF_INTC_IMRH_INT_MASK34 | MCF_INTC_IMRH_INT_MASK35 );
	MCF_INTC0_IMRL &= ~( MCF_INTC_IMRL_INT_MASK25 | MCF_INTC_IMRL_INT_MASK26 | MCF_INTC_IMRL_INT_MASK27 | MCF_INTC_IMRL_INT_MASK28 | MCF_INTC_IMRL_INT_MASK29 | MCF_INTC_IMRL_INT_MASK30 | MCF_INTC_IMRL_INT_MASK31 | MCF_INTC_IMRL_MASKALL );

    /* Clear any pending FEC interrupt events */
    MCF_FEC_EIR = MCF_FEC_EIR_CLEAR_ALL;

    /* Unmask all FEC interrupts */
    MCF_FEC_EIMR = MCF_FEC_EIMR_UNMASK_ALL;
}

/**
 * In this function, the hardware should be initialized.
 * Called from ethernetif_init().
 *
 * @param netif the already initialized lwip network interface structure
 *        for this ethernetif
 */
static void low_level_init( struct netif *netif )
{
unsigned short usData;
const unsigned char ucMACAddress[6] = 
{
	configMAC_0, configMAC_1,configMAC_2,configMAC_3,configMAC_4,configMAC_5
};

	prvInitialiseFECBuffers();
	vSemaphoreCreateBinary( xFecSemaphore );
	
	for( usData = 0; usData < 6; usData++ )
	{
		netif->hwaddr[ usData ] = ucMACAddress[ usData ];
	}

	/* Set the Reset bit and clear the Enable bit */
	MCF_FEC_ECR = MCF_FEC_ECR_RESET;

	/* Wait at least 8 clock cycles */
	for( usData = 0; usData < 10; usData++ )
	{
		asm( "NOP" );
	}

	/* Set MII speed to 2.5MHz. */
	MCF_FEC_MSCR = MCF_FEC_MSCR_MII_SPEED( ( ( configCPU_CLOCK_HZ / 1000000 ) / 5 ) + 1 );

	/*
	 * Make sure the external interface signals are enabled
	 */
	MCF_GPIO_PNQPAR = MCF_GPIO_PNQPAR_IRQ3_FEC_MDIO	| MCF_GPIO_PNQPAR_IRQ5_FEC_MDC;


    MCF_GPIO_PTIPAR = MCF_GPIO_PTIPAR_FEC_COL_FEC_COL			
					| MCF_GPIO_PTIPAR_FEC_CRS_FEC_CRS			
					| MCF_GPIO_PTIPAR_FEC_RXCLK_FEC_RXCLK		
					| MCF_GPIO_PTIPAR_FEC_RXD0_FEC_RXD0			
					| MCF_GPIO_PTIPAR_FEC_RXD1_FEC_RXD1			
					| MCF_GPIO_PTIPAR_FEC_RXD2_FEC_RXD2			
					| MCF_GPIO_PTIPAR_FEC_RXD3_FEC_RXD3			
					| MCF_GPIO_PTIPAR_FEC_RXDV_FEC_RXDV;		

	MCF_GPIO_PTJPAR = MCF_GPIO_PTJPAR_FEC_RXER_FEC_RXER			
					| MCF_GPIO_PTJPAR_FEC_TXCLK_FEC_TXCLK		
					| MCF_GPIO_PTJPAR_FEC_TXD0_FEC_TXD0			
					| MCF_GPIO_PTJPAR_FEC_TXD1_FEC_TXD1			
					| MCF_GPIO_PTJPAR_FEC_TXD2_FEC_TXD2			
					| MCF_GPIO_PTJPAR_FEC_TXD3_FEC_TXD3			
					| MCF_GPIO_PTJPAR_FEC_TXEN_FEC_TXEN			
					| MCF_GPIO_PTJPAR_FEC_TXER_FEC_TXER;		


	/* Can we talk to the PHY? */
	do
	{
		vTaskDelay( netifLINK_DELAY );
		usData = 0;
		fec_mii_read( configPHY_ADDRESS, PHY_PHYIDR1, &usData );

	} while( ( usData == 0xffff ) || ( usData == 0 ) );

	/* Start auto negotiate. */
	fec_mii_write( configPHY_ADDRESS, PHY_BMCR, ( PHY_BMCR_AN_RESTART | PHY_BMCR_AN_ENABLE ) );

	/* Wait for auto negotiate to complete. */
	do
	{
		vTaskDelay( netifLINK_DELAY );
		fec_mii_read( configPHY_ADDRESS, PHY_BMSR, &usData );

	} while( !( usData & PHY_BMSR_AN_COMPLETE ) );

	/* When we get here we have a link - find out what has been negotiated. */
	fec_mii_read( configPHY_ADDRESS, PHY_ANLPAR, &usData );
	
	if( ( usData & PHY_ANLPAR_100BTX_FDX ) || ( usData & PHY_ANLPAR_100BTX ) )
	{
		/* Speed is 100. */
	}
	else
	{
		/* Speed is 10. */
	}

	if( ( usData & PHY_ANLPAR_100BTX_FDX ) || ( usData & PHY_ANLPAR_10BTX_FDX ) )
	{
		/* Full duplex. */
		MCF_FEC_RCR &= (uint32)~MCF_FEC_RCR_DRT;
		MCF_FEC_TCR |= MCF_FEC_TCR_FDEN;
	}
	else
	{
		MCF_FEC_RCR |= MCF_FEC_RCR_DRT;
		MCF_FEC_TCR &= (uint32)~MCF_FEC_TCR_FDEN;
	}
	
	/* Clear the Individual and Group Address Hash registers */
	MCF_FEC_IALR = 0;
	MCF_FEC_IAUR = 0;
	MCF_FEC_GALR = 0;
	MCF_FEC_GAUR = 0;

	/* Set the Physical Address for the selected FEC */
	fec_set_address( ucMACAddress );

	/* Set Rx Buffer Size */
	MCF_FEC_EMRBR = (uint16)configFEC_BUFFER_SIZE;

	/* Point to the start of the circular Rx buffer descriptor queue */
	MCF_FEC_ERDSR = ( volatile unsigned long ) &( xFECRxDescriptors[ 0 ] );

	/* Point to the start of the circular Tx buffer descriptor queue */
	MCF_FEC_ETSDR = ( volatile unsigned long ) &( xFECTxDescriptors[ 0 ] );

	/* Mask all FEC interrupts */
	MCF_FEC_EIMR = MCF_FEC_EIMR_MASK_ALL;

	/* Clear all FEC interrupt events */
	MCF_FEC_EIR = MCF_FEC_EIR_CLEAR_ALL;

	/* Initialize the Receive Control Register */
	MCF_FEC_RCR = MCF_FEC_RCR_MAX_FL(ETH_MAX_FRM) | MCF_FEC_RCR_FCE;

	MCF_FEC_RCR |= MCF_FEC_RCR_MII_MODE;

	#if( configUSE_PROMISCUOUS_MODE == 1 )
	{
		MCF_FEC_RCR |= MCF_FEC_RCR_PROM;
	}
	#endif

	/* Create the task that handles the EMAC. */
	xTaskCreate( ethernetif_input, ( signed char * ) "ETH_INT", configETHERNET_INPUT_TASK_STACK_SIZE, (void *)netif, configETHERNET_INPUT_TASK_PRIORITY, &xEthIntTask );
	
	fec_irq_enable();
	MCF_FEC_ECR = MCF_FEC_ECR_ETHER_EN;
	MCF_FEC_RDAR = MCF_FEC_RDAR_R_DES_ACTIVE;	
}

/**
 * This function should do the actual transmission of the packet. The packet is
 * contained in the pbuf that is passed to the function. This pbuf
 * might be chained.
 *
 * @param netif the lwip network interface structure for this ethernetif
 * @param p the MAC packet to send (e.g. IP packet including MAC addresses and type)
 * @return ERR_OK if the packet could be sent
 *         an err_t value if the packet couldn't be sent
 *
 * @note Returning ERR_MEM here if a DMA queue of your MAC is full can lead to
 *       strange results. You might consider waiting for space in the DMA queue
 *       to become availale since the stack doesn't retry to send a packet
 *       dropped because of memory failure (except for the TCP timers).
 */
static err_t low_level_output(struct netif *netif, struct pbuf *p)
{
struct pbuf *q;
u32_t l = 0;
unsigned char *pcTxData = NULL;
portBASE_TYPE i;

	( void ) netif;

	#if ETH_PAD_SIZE
	  pbuf_header(p, -ETH_PAD_SIZE);			/* drop the padding word */
	#endif

	/* Get a DMA buffer into which we can write the data to send. */
	for( i = 0; i < netifBUFFER_WAIT_ATTEMPTS; i++ )
	{
		if( xFECTxDescriptors[ uxNextTxBuffer ].status & TX_BD_R )
		{
			/* Wait for the buffer to become available. */
			vTaskDelay( netifBUFFER_WAIT_DELAY );
		}
		else
		{
			pcTxData = xFECTxDescriptors[ uxNextTxBuffer ].data;
			break;
		}
	}

	if( pcTxData == NULL ) 
	{
		/* For break point only. */
		portNOP();

		return ERR_BUF;
	}
	else 
	{
		for( q = p; q != NULL; q = q->next ) 
		{
			/* Send the data from the pbuf to the interface, one pbuf at a
			time. The size of the data in each pbuf is kept in the ->len
			variable. */
			memcpy( &pcTxData[l], (u8_t*)q->payload, q->len );
			l += q->len;
		}
	}

	/* Setup the buffer descriptor for transmission */
	xFECTxDescriptors[ uxNextTxBuffer ].length = l;//nbuf->length + ETH_HDR_LEN;
	xFECTxDescriptors[ uxNextTxBuffer ].status |= (TX_BD_R | TX_BD_L);

	/* Continue the Tx DMA task (in case it was waiting for a new TxBD) */
	MCF_FEC_TDAR = MCF_FEC_TDAR_X_DES_ACTIVE;

	uxNextTxBuffer++;
	if( uxNextTxBuffer >= configNUM_FEC_TX_BUFFERS )
	{
		uxNextTxBuffer = 0;
	}

	#if ETH_PAD_SIZE
		pbuf_header(p, ETH_PAD_SIZE);			/* reclaim the padding word */
	#endif

	LINK_STATS_INC(link.xmit);

	return ERR_OK;
}

/**
 * Should allocate a pbuf and transfer the bytes of the incoming
 * packet from the interface into the pbuf.
 *
 * @param netif the lwip network interface structure for this ethernetif
 * @return a pbuf filled with the received packet (including MAC header)
 *         NULL on memory error
 */
static struct pbuf *low_level_input(struct netif *netif)
{
struct pbuf *p, *q;
u16_t len, l;

	( void ) netif;

	l = 0;
	p = NULL;

	/* Obtain the size of the packet and put it into the "len" variable. */
	len = xFECRxDescriptors[ uxNextRxBuffer ].length;

	if( ( len != 0 ) && ( ( xFECRxDescriptors[ uxNextRxBuffer ].status & RX_BD_E ) == 0 ) )
	{
		#if ETH_PAD_SIZE
			len += ETH_PAD_SIZE;						/* allow room for Ethernet padding */
		#endif

		/* We allocate a pbuf chain of pbufs from the pool. */
		p = pbuf_alloc(PBUF_RAW, len, PBUF_POOL);

		if (p != NULL) 
		{

			#if ETH_PAD_SIZE
					pbuf_header(p, -ETH_PAD_SIZE);			/* drop the padding word */
			#endif

			/* We iterate over the pbuf chain until we have read the entire
			 * packet into the pbuf. */
			for(q = p; q != NULL; q = q->next) 
			{
				/* Read enough bytes to fill this pbuf in the chain. The
				 * available data in the pbuf is given by the q->len
				 * variable. */
				memcpy((u8_t*)q->payload, &(xFECRxDescriptors[ uxNextRxBuffer ].data[l]), q->len);
				l = l + q->len;
			}


			#if ETH_PAD_SIZE
				pbuf_header(p, ETH_PAD_SIZE);			/* reclaim the padding word */
			#endif

			LINK_STATS_INC(link.recv);

		} 
		else 
		{

			LINK_STATS_INC(link.memerr);
			LINK_STATS_INC(link.drop);

		} /* End else */
		
		
		/* Free the descriptor. */
		xFECRxDescriptors[ uxNextRxBuffer ].status |= RX_BD_E;
		MCF_FEC_RDAR = MCF_FEC_RDAR_R_DES_ACTIVE;
		
		uxNextRxBuffer++;
		if( uxNextRxBuffer >= configNUM_FEC_RX_BUFFERS )
		{
			uxNextRxBuffer = 0;
		}		
		
	} /* End if */

	return p;
}

/**
 * This function should be called when a packet is ready to be read
 * from the interface. It uses the function low_level_input() that
 * should handle the actual reception of bytes from the network
 * interface.Then the type of the received packet is determined and
 * the appropriate input function is called.
 *
 * @param netif the lwip network interface structure for this ethernetif
 */

static void ethernetif_input( void *pParams )
{
struct netif *netif;
struct ethernetif *ethernetif;
struct eth_hdr *ethhdr;
struct pbuf *p;

	netif = (struct netif*) pParams;
	ethernetif = netif->state;

	for( ;; )
	{
		do
		{

			/* move received packet into a new pbuf */
			p = low_level_input( netif );

			if( p == NULL )
			{
				/* No packet could be read.  Wait a for an interrupt to tell us
				there is more data available. */
				xSemaphoreTake( xFecSemaphore, netifBLOCK_TIME_WAITING_FOR_INPUT );
			}

		} while( p == NULL );

		/* points to packet payload, which starts with an Ethernet header */
		ethhdr = p->payload;

		switch (htons(ethhdr->type)) {
			/* IP or ARP packet? */

		case ETHTYPE_IP:

			pbuf_header( p, (s16_t)-sizeof(struct eth_hdr) );

			/* full packet send to tcpip_thread to process */
			if (netif->input(p, netif) != ERR_OK)
			{
				LWIP_DEBUGF(NETIF_DEBUG, ("ethernetif_input: IP input error\n"));
				pbuf_free(p);
				p = NULL;
			}
			break;

		case ETHTYPE_ARP:

			#if ETHARP_TRUST_IP_MAC
				etharp_ip_input(netif, p);
			#endif

			etharp_arp_input(netif, ethernetif->ethaddr, p);
			break;

		default:
			pbuf_free(p);
			p = NULL;
			break;
		}
	}
}

/**
 * Should be called at the beginning of the program to set up the
 * network interface. It calls the function low_level_init() to do the
 * actual setup of the hardware.
 *
 * This function should be passed as a parameter to netif_add().
 *
 * @param netif the lwip network interface structure for this ethernetif
 * @return ERR_OK if the loopif is initialized
 *         ERR_MEM if private data couldn't be allocated
 *         any other err_t on error
 */
err_t ethernetif_init(struct netif *netif)
{
	struct ethernetif *ethernetif;

	LWIP_ASSERT("netif != NULL", (netif != NULL));

	ethernetif = mem_malloc(sizeof(struct ethernetif));

	if (ethernetif == NULL)
	{
		LWIP_DEBUGF(NETIF_DEBUG, ("ethernetif_init: out of memory\n"));
		return ERR_MEM;
	}

	#if LWIP_NETIF_HOSTNAME
	/* Initialize interface hostname */
	netif->hostname = "lwip";
	#endif /* LWIP_NETIF_HOSTNAME */

	/*
	* Initialize the snmp variables and counters inside the struct netif.
	* The last argument should be replaced with your link speed, in units
	* of bits per second.
	*/
	NETIF_INIT_SNMP(netif, snmp_ifType_ethernet_csmacd, 100);

	netif->state = ethernetif;
	netif->name[0] = IFNAME0;
	netif->name[1] = IFNAME1;

	/* We directly use etharp_output() here to save a function call.
	* You can instead declare your own function an call etharp_output()
	* from it if you have to do some checks before sending (e.g. if link
	* is available...)
	*/
	netif->output = etharp_output;
	netif->linkoutput = low_level_output;

	ethernetif->ethaddr = (struct eth_addr *)&(netif->hwaddr[0]);

	low_level_init(netif);

	return ERR_OK;
}
/*-----------------------------------------------------------*/

static void prvInitialiseFECBuffers( void )
{
unsigned portBASE_TYPE ux;
unsigned char *pcBufPointer;

	pcBufPointer = &( xFECTxDescriptors_unaligned[ 0 ] );
	while( ( ( unsigned long ) pcBufPointer & 0x0fUL ) != 0 )
	{
		pcBufPointer++;
	}
	
	xFECTxDescriptors = ( FECBD * ) pcBufPointer;
	
	pcBufPointer = &( xFECRxDescriptors_unaligned[ 0 ] );
	while( ( ( unsigned long ) pcBufPointer & 0x0fUL ) != 0 )
	{
		pcBufPointer++;
	}
	
	xFECRxDescriptors = ( FECBD * ) pcBufPointer;


	/* Setup the buffers and descriptors. */
	pcBufPointer = &( ucFECTxBuffers[ 0 ] );
	while( ( ( unsigned long ) pcBufPointer & 0x0fUL ) != 0 )
	{
		pcBufPointer++;
	}

	for( ux = 0; ux < configNUM_FEC_TX_BUFFERS; ux++ )
	{
		xFECTxDescriptors[ ux ].status = TX_BD_TC;
		xFECTxDescriptors[ ux ].data = pcBufPointer;
		pcBufPointer += configFEC_BUFFER_SIZE;
		xFECTxDescriptors[ ux ].length = 0;
	}

	pcBufPointer = &( ucFECRxBuffers[ 0 ] );
	while( ( ( unsigned long ) pcBufPointer & 0x0fUL ) != 0 )
	{
		pcBufPointer++;
	}
	
	for( ux = 0; ux < configNUM_FEC_RX_BUFFERS; ux++ )
	{
	    xFECRxDescriptors[ ux ].status = RX_BD_E;
	    xFECRxDescriptors[ ux ].length = configFEC_BUFFER_SIZE;
	    xFECRxDescriptors[ ux ].data = pcBufPointer;
	    pcBufPointer += configFEC_BUFFER_SIZE;
	}

	/* Set the wrap bit in the last descriptors to form a ring. */
	xFECTxDescriptors[ configNUM_FEC_TX_BUFFERS - 1 ].status |= TX_BD_W;
	xFECRxDescriptors[ configNUM_FEC_RX_BUFFERS - 1 ].status |= RX_BD_W;

	uxNextRxBuffer = 0;
	uxNextTxBuffer = 0;
}
/*-----------------------------------------------------------*/

__declspec(interrupt:0) void vFECISRHandler( void )
{
unsigned long ulEvent;
portBASE_TYPE xHighPriorityTaskWoken = pdFALSE;
   
	ulEvent = MCF_FEC_EIR & MCF_FEC_EIMR;
	MCF_FEC_EIR = ulEvent;

	if( ( ulEvent & MCF_FEC_EIR_RXB ) || ( ulEvent & MCF_FEC_EIR_RXF ) )
	{
		/* A packet has been received.  Wake the handler task. */
		xSemaphoreGiveFromISR( xFecSemaphore, &xHighPriorityTaskWoken );
	}

	if (ulEvent & ( MCF_FEC_EIR_UN | MCF_FEC_EIR_RL | MCF_FEC_EIR_LC | MCF_FEC_EIR_EBERR | MCF_FEC_EIR_BABT | MCF_FEC_EIR_BABR | MCF_FEC_EIR_HBERR ) )
	{
		/* Sledge hammer error handling. */
		prvInitialiseFECBuffers();
		MCF_FEC_RDAR = MCF_FEC_RDAR_R_DES_ACTIVE;
	}

	portEND_SWITCHING_ISR( xHighPriorityTaskWoken );
}
