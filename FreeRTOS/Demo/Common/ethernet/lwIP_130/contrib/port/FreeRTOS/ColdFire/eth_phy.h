/*!
 * \file    eth.h
 * \brief   Definitions for Ethernet Physical Layer Interface
 * \version $Revision: 1.3 $
 * \author  Michael Norman
 */

#ifndef _ETH_PHY_H
#define _ETH_PHY_H

/*******************************************************************/

int
eth_phy_autoneg(int phy_addr, MII_SPEED speed, MII_DUPLEX duplex);

int 
eth_phy_manual(int phy_addr, MII_SPEED speed, MII_DUPLEX duplex, int loop);

int 
eth_phy_get_speed(int, int*);

int 
eth_phy_get_duplex(int, int*);

int 
eth_phy_reg_dump(int);

/*******************************************************************/

/* MII Register Addresses */
#define PHY_BMCR				    (0x00)
#define PHY_BMSR                    (0x01)
#define PHY_PHYIDR1				    (0x02)
#define PHY_PHYIDR2				    (0x03)
#define PHY_ANAR				    (0x04)
#define PHY_ANLPAR		            (0x05)

/* Bit definitions and macros for PHY_CTRL */
#define PHY_BMCR_RESET		        (0x8000)
#define PHY_BMCR_LOOP   		    (0x4000)
#define PHY_BMCR_SPEED		        (0x2000)
#define PHY_BMCR_AN_ENABLE		    (0x1000)
#define PHY_BMCR_POWERDOWN  	    (0x0800)
#define PHY_BMCR_ISOLATE	        (0x0400)
#define PHY_BMCR_AN_RESTART	        (0x0200)
#define PHY_BMCR_FDX			    (0x0100)
#define PHY_BMCR_COL_TEST	        (0x0080)

/* Bit definitions and macros for PHY_STAT */
#define PHY_BMSR_100BT4             (0x8000)
#define PHY_BMSR_100BTX_FDX         (0x4000)
#define PHY_BMSR_100BTX             (0x2000)
#define PHY_BMSR_10BT_FDX           (0x1000)
#define PHY_BMSR_10BT               (0x0800)
#define PHY_BMSR_NO_PREAMBLE        (0x0040)
#define PHY_BMSR_AN_COMPLETE        (0x0020)
#define PHY_BMSR_REMOTE_FAULT       (0x0010)
#define PHY_BMSR_AN_ABILITY         (0x0008)
#define PHY_BMSR_LINK               (0x0004)
#define PHY_BMSR_JABBER             (0x0002)
#define PHY_BMSR_EXTENDED           (0x0001)

/* Bit definitions and macros for PHY_AN_ADV */
#define PHY_ANAR_NEXT_PAGE          (0x8001)
#define PHY_ANAR_REM_FAULT	        (0x2001)
#define PHY_ANAR_PAUSE		        (0x0401)
#define PHY_ANAR_100BT4		        (0x0201)
#define PHY_ANAR_100BTX_FDX	        (0x0101)
#define PHY_ANAR_100BTX		        (0x0081)
#define PHY_ANAR_10BT_FDX		    (0x0041)
#define PHY_ANAR_10BT		        (0x0021)
#define PHY_ANAR_802_3		        (0x0001)

/* Bit definitions and macros for PHY_AN_LINK_PAR */
#define PHY_ANLPAR_NEXT_PAGE        (0x8000)
#define PHY_ANLPAR_ACK              (0x4000)
#define PHY_ANLPAR_REM_FAULT	    (0x2000)
#define PHY_ANLPAR_PAUSE		    (0x0400)
#define PHY_ANLPAR_100BT4		    (0x0200)
#define PHY_ANLPAR_100BTX_FDX	    (0x0100)
#define PHY_ANLPAR_100BTX		    (0x0080)
#define PHY_ANLPAR_10BTX_FDX        (0x0040)
#define PHY_ANLPAR_10BT		        (0x0020)

/*******************************************************************/

#endif  /* _ETH_PHY_H */
