/*!
 * \file    mii.h
 * \brief   Media Independent Interface (MII) driver
 * \version $Revision: 1.3 $
 * \author  Michael Norman
 * 
 * \warning This driver assumes that FEC0 is used for all MII management
 *          communications.  For dual PHYs, etc., insure that FEC0_MDC and
 *          FEC0_MDIO are connected to the PHY's MDC and MDIO.
 */

#ifndef _MII_H_
#define _MII_H_

/*******************************************************************/

int
mii_write(int, int, uint16);

int
mii_read(int, int, uint16*);

void
mii_init(int);

/* MII Speed Settings */
typedef enum {
	MII_10BASE_T,	/*!< 10Base-T  operation */
	MII_100BASE_TX	/*!< 100Base-TX operation */
} MII_SPEED;

/* MII Duplex Settings */
typedef enum {
	MII_HDX,		/*!< half-duplex */
	MII_FDX			/*!< full-duplex */
} MII_DUPLEX;

#define MII_TIMEOUT		    0x10000
#define MII_LINK_TIMEOUT	0x10000

/*******************************************************************/

#endif /* _MII_H_ */
