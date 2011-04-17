/***************************************************************************//**
 * PHY access methods for DP83848C.
 * The implementation in this file is specific to the DP83848C,
 * If a different PHY support is required the PHY specific registers must
 * be updated.
 * (c) Copyright 2007 Actel Corporation
 *
 * SVN $Revision: 2324 $
 * SVN $Date: 2010-02-26 10:47:36 +0000 (Fri, 26 Feb 2010) $
 *
 ******************************************************************************/

#ifdef __cplusplus
extern "C" {
#endif 


#include "mss_ethernet_mac.h"
#include "mss_ethernet_mac_regs.h"

#include "phy.h"

#include "FreeRTOS.h"
#include "task.h"

extern MAC_instance_t g_mss_mac;

/***************************** MDIO FUNCTIONS *********************************/

/* Defines ********************************************************************/
#define MDIO_START				0x00004000UL
#define MDIO_READ				0x00002000UL
#define MDIO_WRITE				0x00001002UL
#define MDIO_ADDR_OFFSET		7UL
#define MDIO_ADDR_MASK			0x00000f80UL
#define MDIO_REG_ADDR_OFFSET	2UL
#define MDIO_REG_ADDR_MASK		0x0000007cUL
#define PREAMBLECOUNT           32UL
#define ONEMICROSECOND          20UL

typedef enum {
	MDIO_CMD_READ,
	MDIO_CMD_WRITE
}mdio_cmd_t;



/***************************************************************************//**
 * Set clock high or low.
 */
static void
MDIO_management_clock
(
    int32_t clock
)
{
	int32_t volatile a;
    
    MAC_BITBAND->CSR9_MDC = (uint32_t)clock;
    
	/* delay for 1us */
	for( a = 0; a < ONEMICROSECOND; a++ ){}
}


/***************************************************************************//**
 * Send read or write command to PHY.
 */
static void
MDIO_send_cmd
(
    uint8_t regad,
    mdio_cmd_t mdio_cmd
)
{
    int32_t i;
    uint16_t mask, data;

    /* enable MII output */
    MAC_BITBAND->CSR9_MDEN = 1;

    /* send 32 1's preamble */
    MAC_BITBAND->CSR9_MDO = 1;
    for (i = 0; i < PREAMBLECOUNT; i++) {
    	MDIO_management_clock( 0 );
    	MDIO_management_clock( 1 );
    }

    /* calculate data bits */
    data = MDIO_START |
    	(( mdio_cmd == MDIO_CMD_READ ) ? MDIO_READ : MDIO_WRITE ) |
    	((g_mss_mac.phy_address << MDIO_ADDR_OFFSET) & MDIO_ADDR_MASK) |
    	((regad << MDIO_REG_ADDR_OFFSET) & MDIO_REG_ADDR_MASK);

    /* sent out */
    for( mask = 0x00008000L; mask>0; mask >>= 1 )
    {
        if ((mask == 0x2) && (mdio_cmd == MDIO_CMD_READ)) {
    		/* enable MII input */
            MAC_BITBAND->CSR9_MDEN = 0;
        }

    	MDIO_management_clock( 0 );

        /* prepare MDO */
        MAC_BITBAND->CSR9_MDO = (uint32_t)((mask & data) != 0 ? 1UL : 0UL);
        
    	MDIO_management_clock( 1 );
    }
}


/***************************************************************************//**
 * Reads a PHY register.
 */
static uint16_t
MDIO_read
(
    uint8_t regad
)
{
    uint16_t mask;
    uint16_t data;

    MDIO_send_cmd( regad, MDIO_CMD_READ);

    /* read data */
    data = 0;
    for( mask = 0x00008000L; mask>0; mask >>= 1 )
    {
    	MDIO_management_clock( 0 );

        /* read MDI */
        if(MAC_BITBAND-> CSR9_MDI != 0){
            data |= mask;
        }

    	MDIO_management_clock( 1 );
    }

    MDIO_management_clock( 0 );

    return data;
}


/***************************************************************************//**
 * Writes to a PHY register.
 */
static void
MDIO_write
(
    uint8_t regad,
    uint16_t data
)
{
    uint16_t mask;

    MDIO_send_cmd(regad, MDIO_CMD_WRITE);

    /* write data */
    for( mask = 0x00008000L; mask>0; mask >>= 1 )
    {
    	MDIO_management_clock( 0 );

        /* prepare MDO */
    	MAC_BITBAND->CSR9_MDO = (uint32_t)((mask & data) != 0 ? 1UL : 0UL);

    	MDIO_management_clock( 1 );
    }

    MDIO_management_clock( 0 );
}


/****************************** PHY FUNCTIONS *********************************/

/* Defines ********************************************************************/

/* Base registers */
#define PHYREG_MIIMCR		0x00    /**< MII Management Control Register */
#define MIIMCR_RESET					(1<<15)
#define MIIMCR_LOOPBACK                 (1<<14)
#define MIIMCR_SPEED_SELECT				(1<<13)
#define MIIMCR_ENABLE_AUTONEGOTIATION	(1<<12)
#define MIIMCR_RESTART_AUTONEGOTIATION	(1<<9)
#define MIIMCR_DUPLEX_MODE				(1<<8)
#define MIIMCR_COLLISION_TEST			(1<<7)

#define PHYREG_MIIMSR		0x01    /**< MII Management Status Register */
#define MIIMSR_ANC			(1<<5)	/**< Auto-Negotiation Completed. */
#define MIIMSR_LINK			(1<<2)	/**< Link is established. */

#define PHYREG_PHYID1R		0x02    /**< PHY Identifier 1 Register */
#define PHYREG_PHYID2R		0x03    /**< PHY Identifier 2 Register */

#define PHYREG_ANAR			0x04    /**< Auto-Negotiation Advertisement Register */
#define ANAR_100FD			(1<<8)
#define ANAR_100HD			(1<<7)
#define ANAR_10FD			(1<<6)
#define ANAR_10HD			(1<<5)

#define PHYREG_ANLPAR		0x05    /**< Auto-Negotiation Link Partner Ability Register */
#define PHYREG_ANER			0x06    /**< Auto-Negotiation Expansion Register */
#define PHYREG_NPAR			0x07    /**< Next Page Advertisement Register */
/*			0x08-			0x0F  Reserved */
#define PHYREG_MFR			0x10    /**< Miscellaneous Features Register */
#define PHYREG_ICSR			0x11    /**< Interrupt Control/Status Register */

#define PHYREG_DR			0x12    /**< Diagnostic Register */
#define DR_DPLX				(1<<11)
#define DR_DATA_RATE		(1<<10)

#define PHYREG_PMLR			0x13    /**< Power Management & Loopback Register */
/*			0x14 Reserved */
#define PHYREG_MCR			0x15    /**< Mode Control Register */
#define MCR_LED_SEL			(1<<9)
/*			0x16 Reserved */
#define PHYREG_DCR			0x17    /**< Disconnect Counter */
#define PHYREG_RECR			0x18    /**< Receive Error Counter */
/*                         0x19-0x1F  Reserved */

/***************************************************************************//**
 * Probe used PHY.
 *
 * return	PHY address. If PHY don't fount, returns 255.
 */
uint8_t PHY_probe( void )
{
	uint8_t phy;
	uint8_t phy_found;
	uint16_t reg;

	phy_found = 0;
	for (phy = MSS_PHY_ADDRESS_MIN; phy <= MSS_PHY_ADDRESS_MAX; phy++) {
		g_mss_mac.phy_address = phy;

        reg = MDIO_read( PHYREG_PHYID1R );

        if ((reg != 0x0000ffffUL) && (reg != 0x00000000UL)) {
        	phy_found = 1;
        	phy = MSS_PHY_ADDRESS_MAX + 1;
        }
    }

    if( phy_found == 0 ) {
    	g_mss_mac.phy_address = MSS_PHY_ADDRESS_AUTO_DETECT;
    }
    return g_mss_mac.phy_address;
}


/***************************************************************************//**
 * Resets the PHY.
 */
void PHY_reset( void )
{
	MDIO_write( PHYREG_MIIMCR, MIIMCR_RESET );
	MDIO_write( PHYREG_MIIMCR,
		MIIMCR_ENABLE_AUTONEGOTIATION |
		MIIMCR_RESTART_AUTONEGOTIATION |
		MIIMCR_COLLISION_TEST );
}


/***************************************************************************//**
 * Restarts PHY auto-negotiation and wait until it's over.
 */
void PHY_auto_negotiate( void )
{
	int32_t a;
	uint16_t reg;

	reg = MDIO_read( PHYREG_MIIMCR );
	MDIO_write( PHYREG_MIIMCR,
		(uint16_t)( MIIMCR_ENABLE_AUTONEGOTIATION |
		MIIMCR_RESTART_AUTONEGOTIATION |
		reg) );

	for( ;; ) {
		reg = MDIO_read( PHYREG_MIIMSR );
		if( (reg & MIIMSR_ANC) != 0 ) {
			break;
		} else {
			vTaskDelay( 200 );
		}
	}
}


/***************************************************************************//**
 * Returns link status.
 *
 * @return          #MAC_LINK_STATUS_LINK if link is up.
 */
uint8_t PHY_link_status( void )
{
	uint8_t retval = 0;
	if(( MDIO_read( PHYREG_MIIMSR ) & MIIMSR_LINK ) != 0 ){
		retval = MSS_MAC_LINK_STATUS_LINK;
	}
	return retval;
}


/***************************************************************************//**
 * Returns link type.
 *
 * @return          the logical OR of the following values:
 *      #MAC_LINK_STATUS_100MB   - Connection is 100Mb
 *      #MAC_LINK_STATUS_FDX     - Connection is full duplex
 */
uint8_t PHY_link_type( void )
{
	uint16_t diagnostic;
	uint8_t type = 0;

	diagnostic = MDIO_read( PHYREG_DR );

    if( (diagnostic & DR_DPLX) != 0 ) {
    	type = MSS_MAC_LINK_STATUS_FDX;
    }

    if( (diagnostic & DR_DATA_RATE) != 0 ) {
    	type |= MSS_MAC_LINK_STATUS_100MB;
    }

    return type;
}


/***************************************************************************//**
 * Sets link type.
 */
void
PHY_set_link_type
(
    uint8_t type
)
{
	uint16_t reg;

	reg = MDIO_read( PHYREG_ANAR );
	reg |= ANAR_100FD | ANAR_100HD | ANAR_10FD | ANAR_10HD;

	if( (type & MSS_MAC_LINK_STATUS_100MB) == 0 ) {
		reg &= ~(ANAR_100FD | ANAR_100HD);
	}

	if( (type & MSS_MAC_LINK_STATUS_FDX) == 0 ) {
		reg &= ~(ANAR_100FD | ANAR_10FD);
	}

	MDIO_write( PHYREG_ANAR, reg );
}


/***************************************************************************//**
 * Puts the Phy in Loopback mode
 */
uint16_t
PHY_set_loopback
(
   uint8_t enable
)
{

	uint16_t reg = 0;   
	

	reg = MDIO_read( PHYREG_MIIMCR );
	// If set to one we need to set the LOCAL Phy loopback
	if(enable == 1)
		reg |= MIIMCR_LOOPBACK;
	else // else we want to clear the bit..
		reg ^= MIIMCR_LOOPBACK;
	
	
	MDIO_write( PHYREG_MIIMCR,reg );
	reg = MDIO_read( PHYREG_MIIMCR );
	
	return reg;
	
}

#ifdef __cplusplus
}
#endif

/******************************** END OF FILE *********************************/

