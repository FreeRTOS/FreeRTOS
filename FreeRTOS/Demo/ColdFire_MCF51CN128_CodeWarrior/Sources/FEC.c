/*
    This file is part of the FreeRTOS.org distribution.

    FreeRTOS.org is free software; you can redistribute it and/or modify it 
    under the terms of the GNU General Public License (version 2) as published
    by the Free Software Foundation and modified by the FreeRTOS exception.

    FreeRTOS.org is distributed in the hope that it will be useful,    but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for 
    more details.

    You should have received a copy of the GNU General Public License along 
    with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59 
    Temple Place, Suite 330, Boston, MA  02111-1307  USA.

    A special exception to the GPL is included to allow you to distribute a 
    combined work that includes FreeRTOS.org without being obliged to provide
    the source code for any proprietary components.  See the licensing section
    of http://www.FreeRTOS.org for full details.


    ***************************************************************************
    *                                                                         *
    * Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
    *                                                                         *
    * This is a concise, step by step, 'hands on' guide that describes both   *
    * general multitasking concepts and FreeRTOS specifics. It presents and   *
    * explains numerous examples that are written using the FreeRTOS API.     *
    * Full source code for all the examples is provided in an accompanying    *
    * .zip file.                                                              *
    *                                                                         *
    ***************************************************************************

    1 tab == 4 spaces!

    Please ensure to read the configuration and relevant port sections of the
    online documentation.
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/


/* Kernel includes. */
#include "FreeRTOS.h"
#include "semphr.h"
#include "task.h"

/* Demo includes. */
#include "FEC.h"
#include "fecbd.h"
#include "mii.h"
#include "eth_phy.h"
#include "eth.h"

/* uIP includes. */
#include "uip.h"
#include "uip_arp.h"

/*-----------------------------------------------------------*/

/* FEC hardware specifics. */
#define MCF_FEC_MSCR_MII_SPEED(x)			(((x)&0x3F)<<0x1)
#define MCF_FEC_RDAR_R_DES_ACTIVE           ( 0x1000000 )
#define MCF_FEC_TDAR_X_DES_ACTIVE           ( 0x1000000 )

/* PHY hardware specifics. */
#define PHY_STATUS							( 16 )
#define PHY_DUPLEX_STATUS					( 4 )

/* Delay between polling the PHY to see if a link has been established. */
#define fecLINK_DELAY						( 500 / portTICK_PERIOD_MS )

/* Very short delay to use when waiting for the Tx to finish with a buffer if
we run out of Rx buffers. */
#define fecMINIMAL_DELAY					( 3 / portTICK_PERIOD_MS )

/* Don't block to wait for a buffer more than this many times. */
#define uipBUFFER_WAIT_ATTEMPTS	( 30 )

/* The Tx re-uses the Rx buffers and only has one descriptor. */
#define fecNUM_TX_DESCRIPTORS				( 1 )

/* The total number of buffers available, which should be greater than the
number of Rx descriptors. */
#define fecNUM_BUFFERS 						( configNUM_FEC_RX_DESCRIPTORS + 2 )

/*-----------------------------------------------------------*/

/* 
 * Return an unused buffer to the pool of free buffers. 
 */
static void prvReturnBuffer( unsigned char *pucBuffer );

/*
 * Find and return the next buffer that is not in use by anything else.
 */
static unsigned char *prvGetFreeBuffer( void ); 
/*-----------------------------------------------------------*/

/* The semaphore used to wake the uIP task when data arrives. */
SemaphoreHandle_t xFECSemaphore = NULL;

/* The buffer used by the uIP stack.  In this case the pointer is used to
point to one of the Rx buffers to avoid having to copy the Rx buffer into
the uIP buffer. */
unsigned char *uip_buf;

/* The DMA descriptors.  These are char arrays to allow us to align them 
correctly. */
static unsigned char xFECTxDescriptors_unaligned[ ( fecNUM_TX_DESCRIPTORS * sizeof( FECBD ) ) + 16 ];
static unsigned char xFECRxDescriptors_unaligned[ ( configNUM_FEC_RX_DESCRIPTORS * sizeof( FECBD ) ) + 16 ];
static FECBD *pxFECTxDescriptor;
static FECBD *xFECRxDescriptors;

/* The DMA buffer.  This is a char arrays to allow it to be aligned correctly. */
static unsigned char ucFECRxBuffers[ ( fecNUM_BUFFERS * configFEC_BUFFER_SIZE ) + 16 ];

/* Index to the next descriptor to be inspected for received data. */
static unsigned long ulNextRxDescriptor = 0;

/* Contains the start address of each Rx buffer, after it has been correctly 
aligned. */
static unsigned char *pucAlignedBufferStartAddresses[ fecNUM_BUFFERS ] = { 0 };

/* Each ucBufferInUse index corresponds to a position in the same index in the
pucAlignedBufferStartAddresses array.  If the index contains a 1 then the 
buffer within pucAlignedBufferStartAddresses is in use, if it contains a 0 then
the buffer is free. */
static unsigned char ucBufferInUse[ fecNUM_BUFFERS ] = { 0 };

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
unsigned long eimr;

	/* Clear the MII interrupt bit */
	EIR = EIR_MII;

	/* Mask the MII interrupt */
	eimr = EIMR;
	EIMR &= ~EIMR_MII;

	/* Write to the MII Management Frame Register to kick-off the MII write */
	MMFR = ( unsigned long ) ( FEC_MMFR_ST_01 | FEC_MMFR_OP_WRITE | FEC_MMFR_PA(phy_addr) | FEC_MMFR_RA(reg_addr) | FEC_MMFR_TA_10 | FEC_MMFR_DATA( data ) );

	/* Poll for the MII interrupt (interrupt should be masked) */
	for (timeout = 0; timeout < FEC_MII_TIMEOUT; timeout++)
	{
		if( EIR & EIR_MII)
		{
			break;
		}
	}

	if( timeout == FEC_MII_TIMEOUT )
	{
		return 0;
	}

	/* Clear the MII interrupt bit */
	EIR = EIR_MII;

	/* Restore the EIMR */
	EIMR = eimr;

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
static int fec_mii_read( int phy_addr, int reg_addr, unsigned short* data )
{
int timeout;
unsigned long eimr;

	/* Clear the MII interrupt bit */
	EIR = 0xffffffff;

	/* Mask the MII interrupt */
	eimr = EIMR;
	EIMR &= ~EIMR_MII;

	/* Write to the MII Management Frame Register to kick-off the MII read */
	MMFR = ( unsigned long ) ( FEC_MMFR_ST_01 | FEC_MMFR_OP_READ | FEC_MMFR_PA(phy_addr) | FEC_MMFR_RA(reg_addr) | FEC_MMFR_TA_10 );

	/* Poll for the MII interrupt (interrupt should be masked) */
	for (timeout = 0; timeout < FEC_MII_TIMEOUT; timeout++)
	{
		if (EIR)
		{
			break;
		}
	}

	if(timeout == FEC_MII_TIMEOUT)
	{
		return 0;
	}

	/* Clear the MII interrupt bit */
	EIR = EIR_MII;

	/* Restore the EIMR */
	EIMR = eimr;

	*data = (unsigned short)(MMFR & 0x0000FFFF);

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
static unsigned char fec_hash_address( const unsigned char* addr )
{
unsigned long crc;
unsigned char byte;
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

	return (unsigned char)(crc >> 26);
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
static void fec_set_address( const unsigned char *pa )
{
	unsigned char crc;

	/*
	* Set the Physical Address
	*/
	PALR = (unsigned long)((pa[0]<<24) | (pa[1]<<16) | (pa[2]<<8) | pa[3]);
	PAUR = (unsigned long)((pa[4]<<24) | (pa[5]<<16));

	/*
	* Calculate and set the hash for given Physical Address
	* in the  Individual Address Hash registers
	*/
	crc = fec_hash_address(pa);
	if(crc >= 32)
	{
		IAUR |= (unsigned long)(1 << (crc - 32));
	}
	else
	{
		IALR |= (unsigned long)(1 << crc);
	}
}
/*-----------------------------------------------------------*/

static void prvInitialiseFECBuffers( void )
{
unsigned portBASE_TYPE ux;
unsigned char *pcBufPointer;

	/* Set the pointer to a correctly aligned address. */
	pcBufPointer = &( xFECTxDescriptors_unaligned[ 0 ] );
	while( ( ( unsigned long ) pcBufPointer & 0x0fUL ) != 0 )
	{
		pcBufPointer++;
	}
	
	pxFECTxDescriptor = ( FECBD * ) pcBufPointer;	

	/* Likewise the pointer to the Rx descriptor. */	
	pcBufPointer = &( xFECRxDescriptors_unaligned[ 0 ] );
	while( ( ( unsigned long ) pcBufPointer & 0x0fUL ) != 0 )
	{
		pcBufPointer++;
	}
	
	xFECRxDescriptors = ( FECBD * ) pcBufPointer;

	/* There is no Tx buffer as the Rx buffer is reused. */
	pxFECTxDescriptor->length = 0;
	pxFECTxDescriptor->status = 0;

	/* Align the Rx buffers. */
	pcBufPointer = &( ucFECRxBuffers[ 0 ] );
	while( ( ( unsigned long ) pcBufPointer & 0x0fUL ) != 0 )
	{
		pcBufPointer++;
	}
	
	/* Then fill in the Rx descriptors. */
	for( ux = 0; ux < configNUM_FEC_RX_DESCRIPTORS; ux++ )
	{
	    xFECRxDescriptors[ ux ].status = RX_BD_E;
	    xFECRxDescriptors[ ux ].length = configFEC_BUFFER_SIZE;
	    xFECRxDescriptors[ ux ].data = pcBufPointer;
		
		/* Note the start address of the buffer now that it is correctly
		aligned. */
		pucAlignedBufferStartAddresses[ ux ] = pcBufPointer;
		
		/* The buffer is in use by the descriptor. */
		ucBufferInUse[ ux ] = pdTRUE;
		
	    pcBufPointer += configFEC_BUFFER_SIZE;
	}
	
	/* Note the start address of the last buffer as one more buffer is
	allocated than there are Rx descriptors. */
	pucAlignedBufferStartAddresses[ ux ] = pcBufPointer;
	
	/* Set uip_buf to point to the last buffer. */
	uip_buf = pcBufPointer;
	ucBufferInUse[ ux ] = pdTRUE;

	/* Set the wrap bit in the last descriptors to form a ring. */
	xFECRxDescriptors[ configNUM_FEC_RX_DESCRIPTORS - 1 ].status |= RX_BD_W;

	/* We start with descriptor 0. */
	ulNextRxDescriptor = 0;
}
/*-----------------------------------------------------------*/

void vInitFEC( void )
{
unsigned short usData;
struct uip_eth_addr xAddr;
const unsigned char ucMACAddress[6] = 
{
	configMAC_0, configMAC_1,configMAC_2,configMAC_3,configMAC_4,configMAC_5
};

	prvInitialiseFECBuffers();

	/* Create the semaphore used to wake the uIP task when data arrives. */
	vSemaphoreCreateBinary( xFECSemaphore );
	
	/* Set the MAC address within the stack. */
	for( usData = 0; usData < 6; usData++ )
	{
		xAddr.addr[ usData ] = ucMACAddress[ usData ];
	}
	uip_setethaddr( xAddr );	

	/* Set the Reset bit and clear the Enable bit */
	ECR_RESET = 1;
	
	/* Enable the clock. */
	SCGC4 |= SCGC4_FEC_MASK;

	/* Wait at least 8 clock cycles */
	for( usData = 0; usData < 10; usData++ )
	{
		asm( "NOP" );
	}

	/* Set MII speed to 2.5MHz. */
	MSCR = MCF_FEC_MSCR_MII_SPEED( ( ( configCPU_CLOCK_HZ / 1000000 ) / 5 ) + 1 );

	/*
	 * Make sure the external interface signals are enabled
	 */
    PTCPF2_C0 = 1;
    PTCPF2_C1 = 1;
    PTCPF2_C2 = 1;
    PTAPF1 = 0x55;
    PTAPF2 = 0x55;
    PTBPF1 = 0x55;
    PTBPF2 = 0x55;
    
    /* Set all pins to full drive with no filter. */
    PTADS = 0x06;
    PTAIFE = 0x06;
    PTBDS = 0xf4;
    PTBIFE = 0xf4;
    PTCDS = 0;
    PTCIFE = 0;				

    
	/* Can we talk to the PHY? */
	do
	{
		vTaskDelay( fecLINK_DELAY );
		usData = 0xffff;
		fec_mii_read( configPHY_ADDRESS, PHY_PHYIDR1, &usData );

	} while( usData == 0xffff );

	/* Start auto negotiate. */
	fec_mii_write( configPHY_ADDRESS, PHY_BMCR, ( PHY_BMCR_AN_RESTART | PHY_BMCR_AN_ENABLE ) );

	/* Wait for auto negotiate to complete. */
	do
	{
		vTaskDelay( fecLINK_DELAY );
		fec_mii_read( configPHY_ADDRESS, PHY_BMSR, &usData );

	} while( !( usData & PHY_BMSR_AN_COMPLETE ) );

	/* When we get here we have a link - find out what has been negotiated. */
	usData = 0;
	fec_mii_read( configPHY_ADDRESS, PHY_STATUS, &usData );	

	/* Setup half or full duplex. */
	if( usData & PHY_DUPLEX_STATUS )
	{
		RCR &= (unsigned long)~RCR_DRT;
		TCR |= TCR_FDEN;
	}
	else
	{
		RCR |= RCR_DRT;
		TCR &= (unsigned long)~TCR_FDEN;
	}
	
	/* Clear the Individual and Group Address Hash registers */
	IALR = 0;
	IAUR = 0;
	GALR = 0;
	GAUR = 0;

	/* Set the Physical Address for the selected FEC */
	fec_set_address( ucMACAddress );

	/* Set Rx Buffer Size */
	EMRBR = (unsigned short) configFEC_BUFFER_SIZE;

	/* Point to the start of the circular Rx buffer descriptor queue */
	ERDSR = ( volatile unsigned long ) &( xFECRxDescriptors[ 0 ] );

	/* Point to the start of the circular Tx buffer descriptor queue */
	ETSDR = ( volatile unsigned long ) pxFECTxDescriptor;

	/* Clear all FEC interrupt events */
	EIR = ( unsigned long ) -1;

	/* Various mode/status setup. */
	RCR = 0;
	RCR_MAX_FL = configFEC_BUFFER_SIZE;
	RCR_MII_MODE = 1;

	#if( configUSE_PROMISCUOUS_MODE == 1 )
	{
		RCR |= RCR_PROM;
	}
	#endif

	/* Enable interrupts. */
	EIMR = EIR_TXF_MASK | EIMR_RXF_MASK | EIMR_RXB_MASK | EIMR_UN_MASK | EIMR_RL_MASK | EIMR_LC_MASK | EIMR_BABT_MASK | EIMR_BABR_MASK | EIMR_HBERR_MASK;

	/* Enable the MAC itself. */
    ECR = ECR_ETHER_EN_MASK;

    /* Indicate that there have been empty receive buffers produced */
    RDAR = MCF_FEC_RDAR_R_DES_ACTIVE;
}
/*-----------------------------------------------------------*/

unsigned long ulFECRx( void )
{
unsigned long ulLen = 0UL;

	/* Is a buffer ready? */
	if( ( xFECRxDescriptors[ ulNextRxDescriptor ].status & RX_BD_E ) == 0 )
	{
		/* uip_buf is about to be set to a new buffer, so return the buffer it
		is already pointing to. */
		prvReturnBuffer( uip_buf );
	
		/* Obtain the size of the packet and put it into the "len" variable. */
		ulLen = xFECRxDescriptors[ ulNextRxDescriptor ].length;
		uip_buf = xFECRxDescriptors[ ulNextRxDescriptor ].data;

		/* The buffer that this descriptor was using is now in use by the
		TCP/IP stack, so allocate it a new buffer. */
		xFECRxDescriptors[ ulNextRxDescriptor ].data = prvGetFreeBuffer();

		/* Doing this here could cause corruption! */		
		xFECRxDescriptors[ ulNextRxDescriptor ].status |= RX_BD_E;		
		
		portENTER_CRITICAL();
		{
			ulNextRxDescriptor++;
			if( ulNextRxDescriptor >= configNUM_FEC_RX_DESCRIPTORS )
			{
				ulNextRxDescriptor = 0;
			}
		}
		portEXIT_CRITICAL();	

		/* Tell the DMA a new buffer is available. */
		RDAR = MCF_FEC_RDAR_R_DES_ACTIVE;		
	}

    return ulLen;
}
/*-----------------------------------------------------------*/

void vFECTx( void )
{
	/* When we get here the Tx descriptor should show as having completed. */
	while( pxFECTxDescriptor->status & TX_BD_R )
	{
		vTaskDelay( fecMINIMAL_DELAY );
	}

	portENTER_CRITICAL();
	{
		/* To maintain the zero copy implementation, point the Tx descriptor
		to the data from the Rx buffer. */
		pxFECTxDescriptor->data = uip_buf;
		
		/* Setup the buffer descriptor for transmission */
		pxFECTxDescriptor->length = uip_len;
		
		/* NB this assumes only one Tx descriptor! */
		pxFECTxDescriptor->status = ( TX_BD_R | TX_BD_L | TX_BD_TC | TX_BD_W );
	}
	portEXIT_CRITICAL();
	
	/* Continue the Tx DMA task (in case it was waiting for a new TxBD) */
	TDAR = MCF_FEC_TDAR_X_DES_ACTIVE;
	
	/* uip_buf is being used by the Tx descriptor.  Allocate a new buffer to
	uip_buf. */
	uip_buf = prvGetFreeBuffer();
}
/*-----------------------------------------------------------*/

static void prvReturnBuffer( unsigned char *pucBuffer )
{
unsigned long ul;

	/* Mark a buffer as free for use. */
	for( ul = 0; ul < fecNUM_BUFFERS; ul++ )
	{
		if( pucAlignedBufferStartAddresses[ ul ] == pucBuffer )
		{
			ucBufferInUse[ ul ] = pdFALSE;
			break;
		}
	}
}
/*-----------------------------------------------------------*/

static unsigned char *prvGetFreeBuffer( void )
{
portBASE_TYPE x;
unsigned char *pucReturn = NULL;
unsigned long ulAttempts = 0;

	while( pucReturn == NULL )
	{
		/* Look through the buffers to find one that is not in use by
		anything else. */
		for( x = 0; x < fecNUM_BUFFERS; x++ )
		{
			if( ucBufferInUse[ x ] == pdFALSE )
			{
				ucBufferInUse[ x ] = pdTRUE;
				pucReturn = pucAlignedBufferStartAddresses[ x ];
				break;
			}
		}

		/* Was a buffer found? */
		if( pucReturn == NULL )
		{
			ulAttempts++;

			if( ulAttempts >= uipBUFFER_WAIT_ATTEMPTS )
			{
				break;
			}

			/* Wait then look again. */
			vTaskDelay( fecMINIMAL_DELAY );
		}
	}

	return pucReturn;
}
/*-----------------------------------------------------------*/

void interrupt 86 vFECISRHandler( void )
{
unsigned long ulEvent;
portBASE_TYPE xHighPriorityTaskWoken = pdFALSE;
   
	/* Determine the cause of the interrupt. */
	ulEvent = EIR & EIMR;
	EIR = ulEvent;

	if( ulEvent & EIR_RXF_MASK )
	{
		/* A packet has been received.  Wake the handler task in case it is 
		blocked. */
		xSemaphoreGiveFromISR( xFECSemaphore, &xHighPriorityTaskWoken );
	}
	
	if( ulEvent & EIR_TXF_MASK )
	{
		/* The Tx has completed.  Mark the buffer it was using as free again. */
		prvReturnBuffer( pxFECTxDescriptor->data );
		pxFECTxDescriptor->data = NULL;
	}

	if (ulEvent & ( EIR_UN_MASK | EIR_RL_MASK | EIR_LC_MASK | EIR_EBERR_MASK | EIR_BABT_MASK | EIR_BABR_MASK | EIR_HBERR_MASK ) )
	{
		/* Sledge hammer error handling. */
		prvInitialiseFECBuffers();
		RDAR = MCF_FEC_RDAR_R_DES_ACTIVE;
	}

	portEND_SWITCHING_ISR( xHighPriorityTaskWoken );
}
