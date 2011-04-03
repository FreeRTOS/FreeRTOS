/***************************************************************************//**
 * PHY access methods.
 *
 * (c) Copyright 2007 Actel Corporation
 *
 * SVN $Revision: 2293 $
 * SVN $Date: 2010-02-24 13:52:02 +0000 (Wed, 24 Feb 2010) $
 *
 ******************************************************************************/

#ifndef __MSS_ETHERNET_MAC_PHY_H
#define __MSS_ETHERNET_MAC_PHY_H	1

#ifdef __cplusplus
extern "C" {
#endif 

/***************************************************************************//**
 * Resets the PHY.
 */
void PHY_reset( void );


/***************************************************************************//**
 * Restarts PHY auto-negotiation and wait until it's over.
 */
void PHY_auto_negotiate( void );


/***************************************************************************//**
 * Probe used PHY.
 *
 * return	PHY address. If PHY don't fount, returns 255.
 */
uint8_t PHY_probe( void );


/***************************************************************************//**
 * Returns link status.
 *
 * @return          #MAC_LINK_STATUS_LINK if link is up.
 */
uint8_t PHY_link_status( void );


/***************************************************************************//**
 * Returns link type.
 *
 * @return          the logical OR of the following values:
 *      #MAC_LINK_STATUS_100MB   - Connection is 100Mb
 *      #MAC_LINK_STATUS_FDX     - Connection is full duplex
 */
uint8_t PHY_link_type( void );


/***************************************************************************//**
 * Sets link type.
 */
void
PHY_set_link_type
(
    uint8_t type
);

/***************************************************************************//**
 * Sets/Clears the phy loop back mode, based on the enable value
 */
uint16_t
PHY_set_loopback
(
    uint8_t enable
);

#ifdef __cplusplus
}
#endif

#endif /*__MSS_ETHERNET_MAC_PHY_H*/
