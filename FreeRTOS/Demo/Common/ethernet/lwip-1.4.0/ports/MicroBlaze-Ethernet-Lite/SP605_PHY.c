/*
 * Code provided by Xilinx.
 */

/* BSP includes. */
#include "xemaclite.h"

/* lwIP includes. */
#include "lwip/opt.h"


/* Advertisement control register. */
#define ADVERTISE_10HALF		0x0020  /* Try for 10mbps half-duplex  */
#define ADVERTISE_10FULL		0x0040  /* Try for 10mbps full-duplex  */
#define ADVERTISE_100HALF		0x0080  /* Try for 100mbps half-duplex */
#define ADVERTISE_100FULL		0x0100  /* Try for 100mbps full-duplex */
#define ADVERTISE_100_AND_10	(ADVERTISE_10FULL | ADVERTISE_100FULL | ADVERTISE_10HALF | ADVERTISE_100HALF)

/* PHY registers/offsets. */
#define IEEE_CONTROL_REG_OFFSET					0
#define IEEE_STATUS_REG_OFFSET					1
#define IEEE_AUTONEGO_ADVERTISE_REG				4
#define IEEE_PARTNER_ABILITIES_1_REG_OFFSET		5
#define IEEE_PARTNER_ABILITIES_3_REG_OFFSET		10
#define IEEE_1000_ADVERTISE_REG_OFFSET			9
#define IEEE_CTRL_1GBPS_LINKSPEED_MASK			0x2040
#define IEEE_CTRL_LINKSPEED_MASK				0x0040
#define IEEE_CTRL_LINKSPEED_1000M				0x0040
#define IEEE_CTRL_LINKSPEED_100M				0x2000
#define IEEE_CTRL_LINKSPEED_10M					0x0000
#define IEEE_CTRL_AUTONEGOTIATE_ENABLE			0x1000
#define IEEE_STAT_AUTONEGOTIATE_CAPABLE			0x0008
#define IEEE_STAT_AUTONEGOTIATE_COMPLETE		0x0020
#define IEEE_STAT_AUTONEGOTIATE_RESTART			0x0200
#define IEEE_STAT_1GBPS_EXTENSIONS				0x0100
#define IEEE_AN3_ABILITY_MASK_1GBPS				0x0C00
#define IEEE_AN1_ABILITY_MASK_100MBPS			0x0380
#define IEEE_AN1_ABILITY_MASK_10MBPS			0x0060

#define PHY_DETECT_REG							1
#define PHY_DETECT_MASK							0x1808

static int detect_phy_emaclite(XEmacLite *pxEMACLiteInstance);

unsigned short vInitialisePHY( XEmacLite *pxEMACLiteInstance )
{
u16 control;
u16 status;
u16 partner_capabilities;
u16 partner_capabilities_1000;
u16 phylinkspeed;
u32 phy_addr = detect_phy_emaclite(pxEMACLiteInstance);

	/* Dont advertise PHY speed of 1000 Mbps */
	XEmacLite_PhyWrite(pxEMACLiteInstance, phy_addr,
				IEEE_1000_ADVERTISE_REG_OFFSET,
				0);
	/* Advertise PHY speed of 100 and 10 Mbps */
	XEmacLite_PhyWrite(pxEMACLiteInstance, phy_addr,
				IEEE_AUTONEGO_ADVERTISE_REG,
				ADVERTISE_100_AND_10);

	XEmacLite_PhyRead(pxEMACLiteInstance, phy_addr,
				     IEEE_CONTROL_REG_OFFSET,
				     &control);
	control |= (IEEE_CTRL_AUTONEGOTIATE_ENABLE |
					IEEE_STAT_AUTONEGOTIATE_RESTART);

	XEmacLite_PhyWrite(pxEMACLiteInstance, phy_addr,
				IEEE_CONTROL_REG_OFFSET,
				control);

	/* Read PHY control and status registers is successful. */
	XEmacLite_PhyRead(pxEMACLiteInstance, phy_addr,
				     IEEE_CONTROL_REG_OFFSET,
				     &control);
	XEmacLite_PhyRead(pxEMACLiteInstance, phy_addr,
				     IEEE_STATUS_REG_OFFSET,
				     &status);

	if ((control & IEEE_CTRL_AUTONEGOTIATE_ENABLE) &&
			(status & IEEE_STAT_AUTONEGOTIATE_CAPABLE)) {

		while ( !(status & IEEE_STAT_AUTONEGOTIATE_COMPLETE) ) {
			XEmacLite_PhyRead(pxEMACLiteInstance, phy_addr,
						     IEEE_STATUS_REG_OFFSET,
						     &status);
		}

		XEmacLite_PhyRead(pxEMACLiteInstance, phy_addr,
					     IEEE_PARTNER_ABILITIES_1_REG_OFFSET,
					     &partner_capabilities);

		if (status & IEEE_STAT_1GBPS_EXTENSIONS) {
			XEmacLite_PhyRead(pxEMACLiteInstance, phy_addr,
						     IEEE_PARTNER_ABILITIES_3_REG_OFFSET,
						     &partner_capabilities_1000);
			if (partner_capabilities_1000 & IEEE_AN3_ABILITY_MASK_1GBPS) return 1000;
		}

		if (partner_capabilities & IEEE_AN1_ABILITY_MASK_100MBPS) return 100;
		if (partner_capabilities & IEEE_AN1_ABILITY_MASK_10MBPS) return 10;

		xil_printf("%s: unknown PHY link speed, setting TEMAC speed to be 10 Mbps\r\n",
				__FUNCTION__);
		return 10;


	} else {

		/* Update TEMAC speed accordingly */
		if (status & IEEE_STAT_1GBPS_EXTENSIONS) {

			/* Get commanded link speed */
			phylinkspeed = control & IEEE_CTRL_1GBPS_LINKSPEED_MASK;

			switch (phylinkspeed) {
				case (IEEE_CTRL_LINKSPEED_1000M):
					return 1000;
				case (IEEE_CTRL_LINKSPEED_100M):
					return 100;
				case (IEEE_CTRL_LINKSPEED_10M):
					return 10;
				default:
					xil_printf("%s: unknown PHY link speed (%d), setting TEMAC speed to be 10 Mbps\r\n",
							__FUNCTION__, phylinkspeed);
					return 10;
			}

		} else {

			return (control & IEEE_CTRL_LINKSPEED_MASK) ? 100 : 10;

		}

	}
}


static int detect_phy_emaclite(XEmacLite *pxEMACLiteInstance)
{
	u16 phy_reg;
	u32 phy_addr;

	for (phy_addr = 31; phy_addr > 0; phy_addr--) {
		XEmacLite_PhyRead(pxEMACLiteInstance, phy_addr, PHY_DETECT_REG, &phy_reg);

		if ((phy_reg != 0xFFFF) &&
			((phy_reg & PHY_DETECT_MASK) == PHY_DETECT_MASK)) {
			/* Found a valid PHY address */
			LWIP_DEBUGF(NETIF_DEBUG, ("XEMacLite detect_phy: PHY detected at address %d.\r\n", phy_addr));
			LWIP_DEBUGF(NETIF_DEBUG, ("XEMacLite detect_phy: PHY detected.\r\n"));
			return phy_addr;
		}
	}

	LWIP_DEBUGF(NETIF_DEBUG, ("XEMacLite detect_phy: No PHY detected.  Assuming a PHY at address 0\r\n"));

	/* default to zero */
	return 0;
}


