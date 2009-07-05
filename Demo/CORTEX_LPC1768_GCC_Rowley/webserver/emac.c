/******************************************************************
 *****                                                        *****
 *****  Ver.: 1.0                                             *****
 *****  Date: 07/05/2001                                      *****
 *****  Auth: Andreas Dannenberg                              *****
 *****        HTWK Leipzig                                    *****
 *****        university of applied sciences                  *****
 *****        Germany                                         *****
 *****  Func: ethernet packet-driver for use with LAN-        *****
 *****        controller CS8900 from Crystal/Cirrus Logic     *****
 *****                                                        *****
 *****  Keil: Module modified for use with Philips            *****
 *****        LPC2378 EMAC Ethernet controller                *****
 *****                                                        *****
 ******************************************************************/

/* Adapted from file originally written by Andreas Dannenberg.  Supplied with permission. */
#include "FreeRTOS.h"
#include "semphr.h"
#include "task.h"
#include "LPC17xx_defs.h"
#include "EthDev_LPC17xx.h"

#define emacPINSEL2_VALUE 0x50150105

#define emacWAIT_FOR_LINK_TO_ESTABLISH ( 500 / portTICK_RATE_MS )
#define emacSHORT_DELAY				   ( 2 )

#define emacLINK_ESTABLISHED		( 0x0001 )
#define emacFULL_DUPLEX_ENABLED		( 0x0004 )
#define emac10BASE_T_MODE			( 0x0002 )

/* If no buffers are available, then wait this long before looking again.... */
#define emacBUFFER_WAIT_DELAY	( 3 / portTICK_RATE_MS )

/* ...and don't look more than this many times. */
#define emacBUFFER_WAIT_ATTEMPTS	( 30 )

#define emacTX_DESC_INDEX			( 0 )

/* The semaphore used to wake the uIP task when data arives. */
extern xSemaphoreHandle xEMACSemaphore;

static unsigned short	*rptr;
static unsigned short	*tptr;

static void prvInitDescriptors( void );
static void prvSetupEMACHardware( void );
static void prvConfigurePHY( void );
static long prvSetupLinkStatus( void );
static unsigned char *prvGetNextBuffer( void );
static void prvReturnBuffer( unsigned char *pucBuffer );

/* Each ucBufferInUse index corresponds to a position in the same index in the
ucMACBuffers array.  If the index contains a 1 then the buffer within
ucMACBuffers is in use, if it contains a 0 then the buffer is free. */
static unsigned char ucBufferInUse[ ETH_NUM_BUFFERS ] = { pdFALSE };

/* The uip_buffer is not a fixed array, but instead gets pointed to the buffers
allocated within this file. */
unsigned char * uip_buf;

/* Store the length of the data being sent so the data can be sent twice.  The
value will be set back to 0 once the data has been sent twice. */
static unsigned short usSendLen = 0;

/*-----------------------------------------------------------*/

int write_PHY( long lPhyReg, long lValue )
{
const long lMaxTime = 10;
long x;

	MAC_MADR = DP83848C_DEF_ADR | lPhyReg;
	MAC_MWTD = lValue;

	x = 0;
	for( x = 0; x < lMaxTime; x++ )
	{
		if( ( MAC_MIND & MIND_BUSY ) == 0 )
		{
			/* Operation has finished. */
			break;
		}

		vTaskDelay( emacSHORT_DELAY );
	}

	if( x < lMaxTime )
	{
		return pdPASS;
	}
	else
	{
		return pdFAIL;
	}
}
/*-----------------------------------------------------------*/

unsigned short read_PHY( unsigned char ucPhyReg, long *plStatus )
{
long x;
const long lMaxTime = 10;

	MAC_MADR = DP83848C_DEF_ADR | ucPhyReg;
	MAC_MCMD = MCMD_READ;

	for( x = 0; x < lMaxTime; x++ )
	{
		/* Operation has finished. */
		if( ( MAC_MIND & MIND_BUSY ) == 0 )
		{
			break;
		}

		vTaskDelay( emacSHORT_DELAY );
	}

	MAC_MCMD = 0;

	if( x >= lMaxTime )
	{
		*plStatus = pdFAIL;
	}

	return( MAC_MRDD );
}
/*-----------------------------------------------------------*/

static unsigned char *prvGetNextBuffer( void )
{
long x;
unsigned char *pucReturn = NULL;
unsigned long ulAttempts = 0;

	while( pucReturn == NULL )
	{
		/* Look through the buffers to find one that is not in use by
		anything else. */
		for( x = 0; x < ETH_NUM_BUFFERS; x++ )
		{
			if( ucBufferInUse[ x ] == pdFALSE )
			{
				ucBufferInUse[ x ] = pdTRUE;
				pucReturn = ( unsigned char * ) ETH_BUF( x );
				break;
			}
		}

		/* Was a buffer found? */
		if( pucReturn == NULL )
		{
			ulAttempts++;

			if( ulAttempts >= emacBUFFER_WAIT_ATTEMPTS )
			{
				break;
			}

			/* Wait then look again. */
			vTaskDelay( emacBUFFER_WAIT_DELAY );
		}
	}

	return pucReturn;
}
/*-----------------------------------------------------------*/

static void prvInitDescriptors( void )
{
long x, lNextBuffer = 0;

	for( x = 0; x < NUM_RX_FRAG; x++ )
	{
		/* Allocate the next Ethernet buffer to this descriptor. */
		RX_DESC_PACKET( x ) = ETH_BUF( lNextBuffer );
		RX_DESC_CTRL( x ) = RCTRL_INT | ( ETH_FRAG_SIZE - 1 );
		RX_STAT_INFO( x ) = 0;
		RX_STAT_HASHCRC( x ) = 0;

		/* The Ethernet buffer is now in use. */
		ucBufferInUse[ lNextBuffer ] = pdTRUE;
		lNextBuffer++;
	}

	/* Set EMAC Receive Descriptor Registers. */
	MAC_RXDESCRIPTOR = RX_DESC_BASE;
	MAC_RXSTATUS = RX_STAT_BASE;
	MAC_RXDESCRIPTORNUM = NUM_RX_FRAG - 1;

	/* Rx Descriptors Point to 0 */
	MAC_RXCONSUMEINDEX = 0;

	/* A buffer is not allocated to the Tx descriptors until they are actually
	used. */
	for( x = 0; x < NUM_TX_FRAG; x++ )
	{
		TX_DESC_PACKET( x ) = NULL;
		TX_DESC_CTRL( x ) = 0;
		TX_STAT_INFO( x ) = 0;
	}

	/* Set EMAC Transmit Descriptor Registers. */
	MAC_TXDESCRIPTOR = TX_DESC_BASE;
	MAC_TXSTATUS = TX_STAT_BASE;
	MAC_TXDESCRIPTORNUM = NUM_TX_FRAG - 1;

	/* Tx Descriptors Point to 0 */
	MAC_TXPRODUCEINDEX = 0;
}
/*-----------------------------------------------------------*/

static void prvSetupEMACHardware( void )
{
unsigned short us;
long x, lDummy;

	/* Enable P1 Ethernet Pins. */
	PINSEL2 = emacPINSEL2_VALUE;
	PINSEL3 = ( PINSEL3 & ~0x0000000F ) | 0x00000005;

	/* Power Up the EMAC controller. */
	PCONP |= PCONP_PCENET;
	vTaskDelay( emacSHORT_DELAY );

	/* Reset all EMAC internal modules. */
	MAC_MAC1 = MAC1_RES_TX | MAC1_RES_MCS_TX | MAC1_RES_RX | MAC1_RES_MCS_RX | MAC1_SIM_RES | MAC1_SOFT_RES;
	MAC_COMMAND = CR_REG_RES | CR_TX_RES | CR_RX_RES | CR_PASS_RUNT_FRM;

	/* A short delay after reset. */
	vTaskDelay( emacSHORT_DELAY );

	/* Initialize MAC control registers. */
	MAC_MAC1 = MAC1_PASS_ALL;
	MAC_MAC2 = MAC2_CRC_EN | MAC2_PAD_EN;
	MAC_MAXF = ETH_MAX_FLEN;
	MAC_CLRT = CLRT_DEF;
	MAC_IPGR = IPGR_DEF;

	/* Enable Reduced MII interface. */
	MAC_COMMAND = CR_RMII | CR_PASS_RUNT_FRM;

	/* Reset Reduced MII Logic. */
	MAC_SUPP = SUPP_RES_RMII;
	vTaskDelay( emacSHORT_DELAY );
	MAC_SUPP = 0;

	/* Put the PHY in reset mode */
	write_PHY( PHY_REG_BMCR, MCFG_RES_MII );
	write_PHY( PHY_REG_BMCR, MCFG_RES_MII );

	/* Wait for hardware reset to end. */
	for( x = 0; x < 100; x++ )
	{
		vTaskDelay( emacSHORT_DELAY * 5 );
		us = read_PHY( PHY_REG_BMCR, &lDummy );
		if( !( us & MCFG_RES_MII ) )
		{
			/* Reset complete */
			break;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvConfigurePHY( void )
{
unsigned short us;
long x, lDummy;

	/* Auto negotiate the configuration. */
	if( write_PHY( PHY_REG_BMCR, PHY_AUTO_NEG ) )
	{
		vTaskDelay( emacSHORT_DELAY * 5 );

		for( x = 0; x < 10; x++ )
		{
			us = read_PHY( PHY_REG_BMSR, &lDummy );

			if( us & PHY_AUTO_NEG_COMPLETE )
			{
				break;
			}

			vTaskDelay( emacWAIT_FOR_LINK_TO_ESTABLISH );
		}
	}
}
/*-----------------------------------------------------------*/

static long prvSetupLinkStatus( void )
{
long lReturn = pdFAIL, x;
unsigned short usLinkStatus;

	for( x = 0; x < 10; x++ )
	{
		usLinkStatus = read_PHY( PHY_REG_STS, &lReturn );
		if( usLinkStatus & emacLINK_ESTABLISHED )
		{
			/* Link is established. */
			lReturn = pdPASS;
			break;
		}

        vTaskDelay( emacWAIT_FOR_LINK_TO_ESTABLISH );
	}

	if( lReturn == pdPASS )
	{
		/* Configure Full/Half Duplex mode. */
		if( usLinkStatus & emacFULL_DUPLEX_ENABLED )
		{
			/* Full duplex is enabled. */
			MAC_MAC2 |= MAC2_FULL_DUP;
			MAC_COMMAND |= CR_FULL_DUP;
			MAC_IPGT = IPGT_FULL_DUP;
		}
		else
		{
			/* Half duplex mode. */
			MAC_IPGT = IPGT_HALF_DUP;
		}

		/* Configure 100MBit/10MBit mode. */
		if( usLinkStatus & emac10BASE_T_MODE )
		{
			/* 10MBit mode. */
			MAC_SUPP = 0;
		}
		else
		{
			/* 100MBit mode. */
			MAC_SUPP = SUPP_SPEED;
		}
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

long Init_EMAC( void )
{
long lReturn = pdPASS;
volatile unsigned long regv, tout;
unsigned long ulID1, ulID2;

	/* Reset peripherals, configure port pins and registers. */
	prvSetupEMACHardware();

	/* Check if connected to a DP83848C PHY. */
	ulID1 = read_PHY( PHY_REG_IDR1, &lReturn );
	ulID2 = read_PHY( PHY_REG_IDR2, &lReturn );
	if( ( (ulID1 << 16UL ) | ( ulID2 & 0xFFF0UL ) ) == DP83848C_ID )
	{
		/* Set the Ethernet MAC Address registers */
		MAC_SA0 = ( configMAC_ADDR0 << 8 ) | configMAC_ADDR1;
		MAC_SA1 = ( configMAC_ADDR2 << 8 ) | configMAC_ADDR3;
		MAC_SA2 = ( configMAC_ADDR4 << 8 ) | configMAC_ADDR5;

		/* Initialize Tx and Rx DMA Descriptors */
		prvInitDescriptors();

		/* Receive Broadcast and Perfect Match Packets */
		MAC_RXFILTERCTRL = RFC_UCAST_EN | RFC_BCAST_EN | RFC_PERFECT_EN;

		/* Setup the PHY. */
		prvConfigurePHY();
	}
	else
	{
		lReturn = pdFAIL;
	}

	/* Check the link status. */
	if( lReturn == pdPASS )
	{
		lReturn = prvSetupLinkStatus();
	}

	if( lReturn == pdPASS )
	{
		/* Initialise uip_buf to ensure it points somewhere valid. */
		uip_buf = prvGetNextBuffer();

		/* Reset all interrupts */
		MAC_INTCLEAR = ( INT_RX_OVERRUN | INT_RX_ERR | INT_RX_FIN | INT_RX_DONE | INT_TX_UNDERRUN | INT_TX_ERR | INT_TX_FIN | INT_TX_DONE | INT_SOFT_INT | INT_WAKEUP );

		/* Enable receive and transmit mode of MAC Ethernet core */
		MAC_COMMAND |= ( CR_RX_EN | CR_TX_EN );
		MAC_MAC1 |= MAC1_REC_EN;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

static void prvReturnBuffer( unsigned char *pucBuffer )
{
unsigned long ul;

	/* Mark a buffer as free for use. */
	for( ul = 0; ul < ETH_NUM_BUFFERS; ul++ )
	{
		if( ETH_BUF( ul ) == ( unsigned long ) pucBuffer )
		{
			ucBufferInUse[ ul ] = pdFALSE;
			break;
		}
	}
}
/*-----------------------------------------------------------*/

unsigned long ulGetEMACRxData( void )
{
unsigned long ulLen = 0;
long lIndex;

	if( MAC_RXPRODUCEINDEX != MAC_RXCONSUMEINDEX )
	{
		/* Mark the current buffer as free as uip_buf is going to be set to
		the buffer that contains the received data. */
		prvReturnBuffer( uip_buf );

		ulLen = ( RX_STAT_INFO( MAC_RXCONSUMEINDEX ) & RINFO_SIZE ) - 3;
		uip_buf = ( unsigned char * ) RX_DESC_PACKET( MAC_RXCONSUMEINDEX );

		/* Allocate a new buffer to the descriptor. */
        RX_DESC_PACKET( MAC_RXCONSUMEINDEX ) = ( unsigned long ) prvGetNextBuffer();

		/* Move the consume index onto the next position, ensuring it wraps to
		the beginning at the appropriate place. */
		lIndex = MAC_RXCONSUMEINDEX;

		lIndex++;
		if( lIndex >= NUM_RX_FRAG )
		{
			lIndex = 0;
		}

		MAC_RXCONSUMEINDEX = lIndex;
	}

	return ulLen;
}
/*-----------------------------------------------------------*/

void vSendEMACTxData( unsigned short usTxDataLen )
{
unsigned long ulAttempts = 0UL;

	/* Check to see if the Tx descriptor is free, indicated by its buffer being
	NULL. */
	while( TX_DESC_PACKET( emacTX_DESC_INDEX ) != NULL )
	{
		/* Wait for the Tx descriptor to become available. */
		vTaskDelay( emacBUFFER_WAIT_DELAY );

		ulAttempts++;
		if( ulAttempts > emacBUFFER_WAIT_ATTEMPTS )
		{
			/* Something has gone wrong as the Tx descriptor is still in use.
			Clear it down manually, the data it was sending will probably be
			lost. */
			prvReturnBuffer( ( unsigned char * ) TX_DESC_PACKET( emacTX_DESC_INDEX ) );
			break;
		}
	}

	/* Setup the Tx descriptor for transmission.  Remember the length of the
	data being sent so the second descriptor can be used to send it again from
	within the ISR. */
	usSendLen = usTxDataLen;
	TX_DESC_PACKET( emacTX_DESC_INDEX ) = ( unsigned long ) uip_buf;
	TX_DESC_CTRL( emacTX_DESC_INDEX ) = ( usTxDataLen | TCTRL_LAST | TCTRL_INT );
	MAC_TXPRODUCEINDEX = ( emacTX_DESC_INDEX + 1 );

	/* uip_buf is being sent by the Tx descriptor.  Allocate a new buffer. */
	uip_buf = prvGetNextBuffer();
}
/*-----------------------------------------------------------*/


static char c[ 256 ] = { 0 };
static int i = 0;


void vEMAC_ISR( void )
{
unsigned long ulStatus;
portBASE_TYPE	xHigherPriorityTaskWoken = pdFALSE;

	ulStatus = MAC_INTSTATUS;

	/* Clear the interrupt. */
	MAC_INTCLEAR = ulStatus;

	if( ulStatus & INT_RX_DONE )
	{
		/* Ensure the uIP task is not blocked as data has arrived. */
		xSemaphoreGiveFromISR( xEMACSemaphore, &xHigherPriorityTaskWoken );
	}

	if( ulStatus & INT_TX_DONE )
	{
		if( usSendLen > 0 )
		{
if( i < 255 )
	c[ i++ ] = 1;
			/* Send the data again, using the second descriptor.  As there are
			only two descriptors the index is set back to 0. */
			TX_DESC_PACKET( ( emacTX_DESC_INDEX + 1 ) ) = TX_DESC_PACKET( emacTX_DESC_INDEX );
			TX_DESC_CTRL( ( emacTX_DESC_INDEX + 1 ) ) = ( usSendLen | TCTRL_LAST | TCTRL_INT );
			MAC_TXPRODUCEINDEX = ( emacTX_DESC_INDEX );

			/* This is the second Tx so set usSendLen to 0 to indicate that the
			Tx descriptors will be free again. */
			usSendLen = 0UL;
		}
		else
		{
if( i < 255 )
	c[ i++ ] = 1;

			/* The Tx buffer is no longer required. */
			prvReturnBuffer( ( unsigned char * ) TX_DESC_PACKET( emacTX_DESC_INDEX ) );
            TX_DESC_PACKET( emacTX_DESC_INDEX ) = NULL;
		}
	}

	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
