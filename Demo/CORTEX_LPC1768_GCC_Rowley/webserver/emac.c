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

/* The semaphore used to wake the uIP task when data arives. */
xSemaphoreHandle		xEMACSemaphore = NULL;

static unsigned short	*rptr;
static unsigned short	*tptr;

static void prvInitDescriptors( void );
static void prvSetupEMACHardware( void );
static void prvConfigurePHY( void );
static long prvSetupLinkStatus( void );

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

unsigned short read_PHY( unsigned char ucPhyReg, portBASE_TYPE *pxStatus )
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
		*pxStatus = pdFAIL;
	}

	return( MAC_MRDD );
}
/*-----------------------------------------------------------*/

static void prvInitDescriptors( void )
{
long x;

	for( x = 0; x < NUM_RX_FRAG; x++ )
	{
		RX_DESC_PACKET( x ) = RX_BUF( x );
		RX_DESC_CTRL( x ) = RCTRL_INT | ( ETH_FRAG_SIZE - 1 );
		RX_STAT_INFO( x ) = 0;
		RX_STAT_HASHCRC( x ) = 0;
	}

	/* Set EMAC Receive Descriptor Registers. */
	MAC_RXDESCRIPTOR = RX_DESC_BASE;
	MAC_RXSTATUS = RX_STAT_BASE;
	MAC_RXDESCRIPTORNUM = NUM_RX_FRAG - 1;

	/* Rx Descriptors Point to 0 */
	MAC_RXCONSUMEINDEX = 0;

	for( x = 0; x < NUM_TX_FRAG; x++ )
	{
		TX_DESC_PACKET( x ) = TX_BUF( x );
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
long x;

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
		us = read_PHY( PHY_REG_BMCR, &us );
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
long x;

	/* Auto negotiate the configuration. */
	if( write_PHY( PHY_REG_BMCR, PHY_AUTO_NEG ) )
	{
		vTaskDelay( emacSHORT_DELAY * 5 );

		for( x = 0; x < 10; x++ )
		{
			us = read_PHY( PHY_REG_BMSR, &us );

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

portBASE_TYPE Init_EMAC( void )
{
portBASE_TYPE xReturn = pdPASS;
volatile unsigned long regv, tout;
unsigned long ulID1, ulID2;

	/* Reset peripherals, configure port pins and registers. */
	prvSetupEMACHardware();

	/* Check if connected to a DP83848C PHY. */
	ulID1 = read_PHY( PHY_REG_IDR1, &xReturn );
	ulID2 = read_PHY( PHY_REG_IDR2, &xReturn );
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

		/* Create the semaphore used to wake the uIP task. */
		vSemaphoreCreateBinary( xEMACSemaphore );

		/* Setup the PHY. */
		prvConfigurePHY();
	}
	else
	{
		xReturn = pdFAIL;
	}

	/* Check the link status. */
	if( xReturn == pdPASS )
	{
		xReturn = prvSetupLinkStatus();
	}

	if( xReturn == pdPASS )
	{
		/* Reset all interrupts */
		MAC_INTCLEAR = 0xFFFF;

		/* Enable receive and transmit mode of MAC Ethernet core */
		MAC_COMMAND |= ( CR_RX_EN | CR_TX_EN );
		MAC_MAC1 |= MAC1_REC_EN;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

// reads a word in little-endian byte order from RX_BUFFER
unsigned short ReadFrame_EMAC( void )
{
	return( *rptr++ );
}

// copies bytes from frame port to MCU-memory
// NOTES: * an odd number of byte may only be transfered
//          if the frame is read to the end!
//        * MCU-memory MUST start at word-boundary
void CopyFromFrame_EMAC( void *Dest, unsigned short Size )
{
	unsigned short	*piDest;	// Keil: Pointer added to correct expression
	piDest = Dest;				// Keil: Line added
	while( Size > 1 )
	{
		*piDest++ = ReadFrame_EMAC();
		Size -= 2;
	}

	if( Size )
	{	// check for leftover byte...
		*( unsigned char * ) piDest = ( char ) ReadFrame_EMAC();	// the LAN-Controller will return 0
	}	// for the highbyte
}


// Reads the length of the received ethernet frame and checks if the
// destination address is a broadcast message or not
// returns the frame length
unsigned short StartReadFrame( void )
{
	unsigned short	RxLen;
	unsigned int	idx;

	idx = MAC_RXCONSUMEINDEX;
	RxLen = ( RX_STAT_INFO(idx) & RINFO_SIZE ) - 3;
	rptr = ( unsigned short * ) RX_DESC_PACKET( idx );
	return( RxLen );
}

void EndReadFrame( void )
{
	unsigned int	idx;

	/* DMA free packet. */
	idx = MAC_RXCONSUMEINDEX;

	if( ++idx == NUM_RX_FRAG )
	{
		idx = 0;
	}

	MAC_RXCONSUMEINDEX = idx;
}

unsigned int uiGetEMACRxData( unsigned char *ucBuffer )
{
	unsigned int	uiLen = 0;

	if( MAC_RXPRODUCEINDEX != MAC_RXCONSUMEINDEX )
	{
		uiLen = StartReadFrame();
		CopyFromFrame_EMAC( ucBuffer, uiLen );
		EndReadFrame();
	}

	return uiLen;
}

// requests space in EMAC memory for storing an outgoing frame
void RequestSend( void )
{
	unsigned int	idx;

	idx = MAC_TXPRODUCEINDEX;
	tptr = ( unsigned short * ) TX_DESC_PACKET( idx );
}

// writes a word in little-endian byte order to TX_BUFFER
void WriteFrame_EMAC( unsigned short Data )
{
	*tptr++ = Data;
}

// copies bytes from MCU-memory to frame port
// NOTES: * an odd number of byte may only be transfered
//          if the frame is written to the end!
//        * MCU-memory MUST start at word-boundary
void CopyToFrame_EMAC( void *Source, unsigned int Size )
{
	unsigned short	*piSource;

	piSource = Source;
	Size = ( Size + 1 ) & 0xFFFE;	// round Size up to next even number
	while( Size > 0 )
	{
		WriteFrame_EMAC( *piSource++ );
		Size -= 2;
	}
}

void DoSend_EMAC( unsigned short FrameSize )
{
	unsigned int	idx;

	idx = MAC_TXPRODUCEINDEX;
	TX_DESC_CTRL( idx ) = FrameSize | TCTRL_LAST;
	if( ++idx == NUM_TX_FRAG )
	{
		idx = 0;
	}

	MAC_TXPRODUCEINDEX = idx;
}

void vEMAC_ISR( void )
{
	portBASE_TYPE	xHigherPriorityTaskWoken = pdFALSE;

	/* Clear the interrupt. */
	MAC_INTCLEAR = 0xffff;

	/* Ensure the uIP task is not blocked as data has arrived. */
	xSemaphoreGiveFromISR( xEMACSemaphore, &xHigherPriorityTaskWoken );

	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
