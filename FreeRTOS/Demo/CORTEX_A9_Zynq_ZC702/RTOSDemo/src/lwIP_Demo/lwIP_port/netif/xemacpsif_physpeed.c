/*
 * Copyright (c) 2007-2008, Advanced Micro Devices, Inc.
 *               All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *    * Redistributions of source code must retain the above copyright
 *      notice, this list of conditions and the following disclaimer.
 *    * Redistributions in binary form must reproduce the above copyright
 *      notice, this list of conditions and the following disclaimer in
 *      the documentation and/or other materials provided with the
 *      distribution.
 *    * Neither the name of Advanced Micro Devices, Inc. nor the names
 *      of its contributors may be used to endorse or promote products
 *      derived from this software without specific prior written
 *      permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * Some portions copyright (c) 2010-2013 Xilinx, Inc.  All rights reserved.
 *
 * Xilinx, Inc.
 * XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS" AS A
 * COURTESY TO YOU.  BY PROVIDING THIS DESIGN, CODE, OR INFORMATION AS
 * ONE POSSIBLE   IMPLEMENTATION OF THIS FEATURE, APPLICATION OR
 * STANDARD, XILINX IS MAKING NO REPRESENTATION THAT THIS IMPLEMENTATION
 * IS FREE FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE RESPONSIBLE
 * FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE FOR YOUR IMPLEMENTATION.
 * XILINX EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH RESPECT TO
 * THE ADEQUACY OF THE IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO
 * ANY WARRANTIES OR REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE
 * FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS FOR A PARTICULAR PURPOSE.
 *
 */

#include "netif/xemacpsif.h"
#include "lwipopts.h"
#include "xparameters_ps.h"
#include "xparameters.h"

/*** IMPORTANT: Define PEEP in xemacpsif.h and sys_arch_raw.c
 *** to run it on a PEEP board
 ***/

/* Advertisement control register. */
#define ADVERTISE_10HALF		0x0020  /* Try for 10mbps half-duplex  */
#define ADVERTISE_10FULL		0x0040  /* Try for 10mbps full-duplex  */
#define ADVERTISE_100HALF		0x0080  /* Try for 100mbps half-duplex */
#define ADVERTISE_100FULL		0x0100  /* Try for 100mbps full-duplex */

#define ADVERTISE_100_AND_10	(ADVERTISE_10FULL | ADVERTISE_100FULL | \
								ADVERTISE_10HALF | ADVERTISE_100HALF)
#define ADVERTISE_100			(ADVERTISE_100FULL | ADVERTISE_100HALF)
#define ADVERTISE_10			(ADVERTISE_10FULL | ADVERTISE_10HALF)

#define ADVERTISE_1000			0x0300


#define IEEE_CONTROL_REG_OFFSET				0
#define IEEE_STATUS_REG_OFFSET				1
#define IEEE_AUTONEGO_ADVERTISE_REG			4
#define IEEE_PARTNER_ABILITIES_1_REG_OFFSET	5
#define IEEE_1000_ADVERTISE_REG_OFFSET		9
#define IEEE_PARTNER_ABILITIES_3_REG_OFFSET	10
#define IEEE_COPPER_SPECIFIC_CONTROL_REG	16
#define IEEE_SPECIFIC_STATUS_REG			17
#define IEEE_COPPER_SPECIFIC_STATUS_REG_2	19
#define IEEE_CONTROL_REG_MAC				21
#define IEEE_PAGE_ADDRESS_REGISTER			22


#define IEEE_CTRL_1GBPS_LINKSPEED_MASK		0x2040
#define IEEE_CTRL_LINKSPEED_MASK			0x0040
#define IEEE_CTRL_LINKSPEED_1000M			0x0040
#define IEEE_CTRL_LINKSPEED_100M			0x2000
#define IEEE_CTRL_LINKSPEED_10M				0x0000
#define IEEE_CTRL_RESET_MASK				0x8000
#define IEEE_CTRL_AUTONEGOTIATE_ENABLE		0x1000
#if XPAR_GIGE_PCS_PMA_CORE_PRESENT == 1
#define IEEE_CTRL_RESET                         0x9140
#define IEEE_CTRL_ISOLATE_DISABLE               0xFBFF
#endif
#define IEEE_STAT_AUTONEGOTIATE_CAPABLE		0x0008
#define IEEE_STAT_AUTONEGOTIATE_COMPLETE	0x0020
#define IEEE_STAT_AUTONEGOTIATE_RESTART		0x0200
#define IEEE_STAT_1GBPS_EXTENSIONS			0x0100
#define IEEE_AN1_ABILITY_MASK				0x1FE0
#define IEEE_AN3_ABILITY_MASK_1GBPS			0x0C00
#define IEEE_AN1_ABILITY_MASK_100MBPS		0x0380
#define IEEE_AN1_ABILITY_MASK_10MBPS		0x0060
#define IEEE_RGMII_TXRX_CLOCK_DELAYED_MASK	0x0030

#define IEEE_ASYMMETRIC_PAUSE_MASK			0x0800
#define IEEE_PAUSE_MASK						0x0400
#define IEEE_AUTONEG_ERROR_MASK				0x8000

#define PHY_DETECT_REG  1
#define PHY_DETECT_MASK 0x1808

#define XEMACPS_GMII2RGMII_SPEED1000_FD		0x140
#define XEMACPS_GMII2RGMII_SPEED100_FD		0x2100
#define XEMACPS_GMII2RGMII_SPEED10_FD		0x100
#define XEMACPS_GMII2RGMII_REG_NUM			0x10

/* Frequency setting */
#define SLCR_LOCK_ADDR			(XPS_SYS_CTRL_BASEADDR + 0x4)
#define SLCR_UNLOCK_ADDR		(XPS_SYS_CTRL_BASEADDR + 0x8)
#define SLCR_GEM0_CLK_CTRL_ADDR	(XPS_SYS_CTRL_BASEADDR + 0x140)
#define SLCR_GEM1_CLK_CTRL_ADDR	(XPS_SYS_CTRL_BASEADDR + 0x144)
#ifdef PEEP
#define SLCR_GEM_10M_CLK_CTRL_VALUE		0x00103031
#define SLCR_GEM_100M_CLK_CTRL_VALUE	0x00103001
#define SLCR_GEM_1G_CLK_CTRL_VALUE		0x00103011
#endif
#define SLCR_LOCK_KEY_VALUE 			0x767B
#define SLCR_UNLOCK_KEY_VALUE			0xDF0D
#define SLCR_ADDR_GEM_RST_CTRL			(XPS_SYS_CTRL_BASEADDR + 0x214)
#define EMACPS_SLCR_DIV_MASK			0xFC0FC0FF

#define EMAC0_BASE_ADDRESS				0xE000B000
#define EMAC1_BASE_ADDRESS				0xE000C000

static int detect_phy(XEmacPs *xemacpsp)
{
	u16 phy_reg;
	u32 phy_addr;

	for (phy_addr = 31; phy_addr > 0; phy_addr--) {
		XEmacPs_PhyRead(xemacpsp, phy_addr, PHY_DETECT_REG,
							&phy_reg);

		if ((phy_reg != 0xFFFF) &&
			((phy_reg & PHY_DETECT_MASK) == PHY_DETECT_MASK)) {
			/* Found a valid PHY address */
			LWIP_DEBUGF(NETIF_DEBUG, ("XEmacPs detect_phy: PHY detected at address %d.\r\n",
																	phy_addr));
			LWIP_DEBUGF(NETIF_DEBUG, ("XEmacPs detect_phy: PHY detected.\r\n"));
			return phy_addr;
		}
	}

	LWIP_DEBUGF(NETIF_DEBUG, ("XEmacPs detect_phy: No PHY detected.  Assuming a PHY at address 0\r\n"));

        /* default to zero */
	return 0;
}

#ifdef PEEP
unsigned get_IEEE_phy_speed(XEmacPs *xemacpsp)
{

	u16 control;
	u16 status;
	u16 partner_capabilities;
	u16 partner_capabilities_1000;
	u16 phylinkspeed;
	u32 phy_addr = detect_phy(xemacpsp);

	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET,
															ADVERTISE_1000);
	/* Advertise PHY speed of 100 and 10 Mbps */
	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG,
													ADVERTISE_100_AND_10);

	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET,
																&control);
	control |= (IEEE_CTRL_AUTONEGOTIATE_ENABLE |
					IEEE_STAT_AUTONEGOTIATE_RESTART);

	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, control);

	/* Read PHY control and status registers is successful. */
	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control);
	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_STATUS_REG_OFFSET, &status);

	if ((control & IEEE_CTRL_AUTONEGOTIATE_ENABLE) && (status &
					IEEE_STAT_AUTONEGOTIATE_CAPABLE)) {

		while ( !(status & IEEE_STAT_AUTONEGOTIATE_COMPLETE) ) {
			XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_STATUS_REG_OFFSET,
																&status);
		}

		XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_PARTNER_ABILITIES_1_REG_OFFSET,
															&partner_capabilities);

		if (status & IEEE_STAT_1GBPS_EXTENSIONS) {
			XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_PARTNER_ABILITIES_3_REG_OFFSET,
														&partner_capabilities_1000);
			if (partner_capabilities_1000 & IEEE_AN3_ABILITY_MASK_1GBPS)
				return 1000;
		}

		if (partner_capabilities & IEEE_AN1_ABILITY_MASK_100MBPS)
			return 100;
		if (partner_capabilities & IEEE_AN1_ABILITY_MASK_10MBPS)
			return 10;

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

#else /* Zynq */
unsigned get_IEEE_phy_speed(XEmacPs *xemacpsp)
{
	u16 temp;
	u16 control;
	u16 status;
	u16 partner_capabilities;
#if XPAR_GIGE_PCS_PMA_CORE_PRESENT == 1
	u32 phy_addr = XPAR_PCSPMA_SGMII_PHYADDR;
#else
	u32 phy_addr = detect_phy(xemacpsp);
#endif
	xil_printf("Start PHY autonegotiation \r\n");

#if XPAR_GIGE_PCS_PMA_CORE_PRESENT == 1
#else
	XEmacPs_PhyWrite(xemacpsp,phy_addr, IEEE_PAGE_ADDRESS_REGISTER, 2);
	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_CONTROL_REG_MAC, &control);
	control |= IEEE_RGMII_TXRX_CLOCK_DELAYED_MASK;
	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_CONTROL_REG_MAC, control);

	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_PAGE_ADDRESS_REGISTER, 0);

	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, &control);
	control |= IEEE_ASYMMETRIC_PAUSE_MASK;
	control |= IEEE_PAUSE_MASK;
	control |= ADVERTISE_100;
	control |= ADVERTISE_10;
	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, control);

	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET,
																	&control);
	control |= ADVERTISE_1000;
	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET,
																	control);

	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_PAGE_ADDRESS_REGISTER, 0);
	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_COPPER_SPECIFIC_CONTROL_REG,
																&control);
	control |= (7 << 12);	/* max number of gigabit attempts */
	control |= (1 << 11);	/* enable downshift */
	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_COPPER_SPECIFIC_CONTROL_REG,
																control);
#endif
	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control);
	control |= IEEE_CTRL_AUTONEGOTIATE_ENABLE;
	control |= IEEE_STAT_AUTONEGOTIATE_RESTART;
#if XPAR_GIGE_PCS_PMA_CORE_PRESENT == 1
    control &= IEEE_CTRL_ISOLATE_DISABLE;
#endif

	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, control);


#if XPAR_GIGE_PCS_PMA_CORE_PRESENT == 1
#else
	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control);
	control |= IEEE_CTRL_RESET_MASK;
	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, control);

	while (1) {
		XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control);
		if (control & IEEE_CTRL_RESET_MASK)
			continue;
		else
			break;
	}
#endif
	xil_printf("Waiting for PHY to complete autonegotiation.\r\n");

	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_STATUS_REG_OFFSET, &status);
	while ( !(status & IEEE_STAT_AUTONEGOTIATE_COMPLETE) ) {
		sleep(1);
#if XPAR_GIGE_PCS_PMA_CORE_PRESENT == 1
#else
		XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_COPPER_SPECIFIC_STATUS_REG_2,
																	&temp);
		if (temp & IEEE_AUTONEG_ERROR_MASK) {
			xil_printf("Auto negotiation error \r\n");
		}
#endif
		XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_STATUS_REG_OFFSET,
																&status);
		}

	xil_printf("autonegotiation complete \r\n");

#if XPAR_GIGE_PCS_PMA_CORE_PRESENT == 1
#else
	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_SPECIFIC_STATUS_REG, &partner_capabilities);
#endif

#if XPAR_GIGE_PCS_PMA_CORE_PRESENT == 1
	xil_printf("Waiting for Link to be up; Polling for SGMII core Reg \r\n");
	XEmacPs_PhyRead(xemacpsp, phy_addr, 5, &temp);
	while(!(temp & 0x8000)) {
		XEmacPs_PhyRead(xemacpsp, phy_addr, 5, &temp);
	}
	if((temp & 0x0C00) == 0x0800) {
		XEmacPs_PhyRead(xemacpsp, phy_addr, 0, &temp);
		return 1000;
	}
	else if((temp & 0x0C00) == 0x0400) {
		XEmacPs_PhyRead(xemacpsp, phy_addr, 0, &temp);
		return 100;
	}
	else if((temp & 0x0C00) == 0x0000) {
		XEmacPs_PhyRead(xemacpsp, phy_addr, 0, &temp);
		return 10;
	} else {
		xil_printf("get_IEEE_phy_speed(): Invalid speed bit value, Deafulting to Speed = 10 Mbps\r\n");
		XEmacPs_PhyRead(xemacpsp, phy_addr, 0, &temp);
		XEmacPs_PhyWrite(xemacpsp, phy_addr, 0, 0x0100);
		return 10;
	}
#else
	if ( ((partner_capabilities >> 14) & 3) == 2)/* 1000Mbps */
		return 1000;
	else if ( ((partner_capabilities >> 14) & 3) == 1)/* 100Mbps */
		return 100;
	else					/* 10Mbps */
		return 10;
#endif
}
#endif

unsigned configure_IEEE_phy_speed(XEmacPs *xemacpsp, unsigned speed)
{
	u16 control;
	u32 phy_addr = detect_phy(xemacpsp);

	XEmacPs_PhyWrite(xemacpsp,phy_addr, IEEE_PAGE_ADDRESS_REGISTER, 2);
	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_CONTROL_REG_MAC, &control);
	control |= IEEE_RGMII_TXRX_CLOCK_DELAYED_MASK;
	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_CONTROL_REG_MAC, control);

	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_PAGE_ADDRESS_REGISTER, 0);

	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, &control);
	control |= IEEE_ASYMMETRIC_PAUSE_MASK;
	control |= IEEE_PAUSE_MASK;
	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, control);

	XEmacPs_PhyRead(xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control);
	control &= ~IEEE_CTRL_LINKSPEED_1000M;
	control &= ~IEEE_CTRL_LINKSPEED_100M;
	control &= ~IEEE_CTRL_LINKSPEED_10M;

	if (speed == 1000) {
		control |= IEEE_CTRL_LINKSPEED_1000M;
	}

	else if (speed == 100) {
		control |= IEEE_CTRL_LINKSPEED_100M;
		/* Dont advertise PHY speed of 1000 Mbps */
		XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET, 0);
		/* Dont advertise PHY speed of 10 Mbps */
		XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG,
																ADVERTISE_100);
	}

	else if (speed == 10) {
		control |= IEEE_CTRL_LINKSPEED_10M;
		/* Dont advertise PHY speed of 1000 Mbps */
		XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET,
																			0);
		/* Dont advertise PHY speed of 100 Mbps */
		XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG,
																ADVERTISE_10);
	}

	XEmacPs_PhyWrite(xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET,
											control | IEEE_CTRL_RESET_MASK);
	{
		volatile int wait;
		for (wait=0; wait < 100000; wait++);
	}
	return 0;
}

static void SetUpSLCRDivisors(int mac_baseaddr, int speed)
{
	volatile u32 slcrBaseAddress;
#ifndef PEEP
	u32 SlcrDiv0;
	u32 SlcrDiv1;
	u32 SlcrTxClkCntrl;
#endif

	*(volatile unsigned int *)(SLCR_UNLOCK_ADDR) = SLCR_UNLOCK_KEY_VALUE;

	if ((unsigned long)mac_baseaddr == EMAC0_BASE_ADDRESS) {
		slcrBaseAddress = SLCR_GEM0_CLK_CTRL_ADDR;
	} else {
		slcrBaseAddress = SLCR_GEM1_CLK_CTRL_ADDR;
	}
#ifdef PEEP
	if (speed == 1000) {
		*(volatile unsigned int *)(slcrBaseAddress) =
											SLCR_GEM_1G_CLK_CTRL_VALUE;
	} else if (speed == 100) {
		*(volatile unsigned int *)(slcrBaseAddress) =
											SLCR_GEM_100M_CLK_CTRL_VALUE;
	} else {
		*(volatile unsigned int *)(slcrBaseAddress) =
											SLCR_GEM_10M_CLK_CTRL_VALUE;
	}
#else
	if (speed == 1000) {
		if ((unsigned long)mac_baseaddr == EMAC0_BASE_ADDRESS) {
#ifdef XPAR_PS7_ETHERNET_0_ENET_SLCR_1000MBPS_DIV0
			SlcrDiv0 = XPAR_PS7_ETHERNET_0_ENET_SLCR_1000MBPS_DIV0;
			SlcrDiv1 = XPAR_PS7_ETHERNET_0_ENET_SLCR_1000MBPS_DIV1;
#endif
		} else {
#ifdef XPAR_PS7_ETHERNET_1_ENET_SLCR_1000MBPS_DIV0
			SlcrDiv0 = XPAR_PS7_ETHERNET_1_ENET_SLCR_1000MBPS_DIV0;
			SlcrDiv1 = XPAR_PS7_ETHERNET_1_ENET_SLCR_1000MBPS_DIV1;
#endif
		}
	} else if (speed == 100) {
		if ((unsigned long)mac_baseaddr == EMAC0_BASE_ADDRESS) {
#ifdef XPAR_PS7_ETHERNET_0_ENET_SLCR_100MBPS_DIV0
			SlcrDiv0 = XPAR_PS7_ETHERNET_0_ENET_SLCR_100MBPS_DIV0;
			SlcrDiv1 = XPAR_PS7_ETHERNET_0_ENET_SLCR_100MBPS_DIV1;
#endif
		} else {
#ifdef XPAR_PS7_ETHERNET_1_ENET_SLCR_100MBPS_DIV0
			SlcrDiv0 = XPAR_PS7_ETHERNET_1_ENET_SLCR_100MBPS_DIV0;
			SlcrDiv1 = XPAR_PS7_ETHERNET_1_ENET_SLCR_100MBPS_DIV1;
#endif
		}
	} else {
		if ((unsigned long)mac_baseaddr == EMAC0_BASE_ADDRESS) {
#ifdef XPAR_PS7_ETHERNET_0_ENET_SLCR_10MBPS_DIV0
			SlcrDiv0 = XPAR_PS7_ETHERNET_0_ENET_SLCR_10MBPS_DIV0;
			SlcrDiv1 = XPAR_PS7_ETHERNET_0_ENET_SLCR_10MBPS_DIV1;
#endif
		} else {
#ifdef XPAR_PS7_ETHERNET_1_ENET_SLCR_10MBPS_DIV0
			SlcrDiv0 = XPAR_PS7_ETHERNET_1_ENET_SLCR_10MBPS_DIV0;
			SlcrDiv1 = XPAR_PS7_ETHERNET_1_ENET_SLCR_10MBPS_DIV1;
#endif
		}
	}
	SlcrTxClkCntrl = *(volatile unsigned int *)(slcrBaseAddress);
	SlcrTxClkCntrl &= EMACPS_SLCR_DIV_MASK;
	SlcrTxClkCntrl |= (SlcrDiv1 << 20);
	SlcrTxClkCntrl |= (SlcrDiv0 << 8);
	*(volatile unsigned int *)(slcrBaseAddress) = SlcrTxClkCntrl;
#endif
	*(volatile unsigned int *)(SLCR_LOCK_ADDR) = SLCR_LOCK_KEY_VALUE;
	return;
}


unsigned Phy_Setup (XEmacPs *xemacpsp)
{
	unsigned link_speed;
	unsigned long conv_present = 0;
	unsigned long convspeeddupsetting = 0;
	unsigned long convphyaddr = 0;

#ifdef XPAR_GMII2RGMIICON_0N_ETH0_ADDR
	convphyaddr = XPAR_GMII2RGMIICON_0N_ETH0_ADDR;
	conv_present = 1;
#else
#ifdef XPAR_GMII2RGMIICON_0N_ETH1_ADDR
	convphyaddr = XPAR_GMII2RGMIICON_0N_ETH1_ADDR;
	conv_present = 1;
#endif
#endif

#ifdef  CONFIG_LINKSPEED_AUTODETECT
	link_speed = get_IEEE_phy_speed(xemacpsp);
	if (link_speed == 1000) {
		SetUpSLCRDivisors(xemacpsp->Config.BaseAddress,1000);
		convspeeddupsetting = XEMACPS_GMII2RGMII_SPEED1000_FD;
	} else if (link_speed == 100) {
		SetUpSLCRDivisors(xemacpsp->Config.BaseAddress,100);
		convspeeddupsetting = XEMACPS_GMII2RGMII_SPEED100_FD;
	} else {
		SetUpSLCRDivisors(xemacpsp->Config.BaseAddress,10);
		convspeeddupsetting = XEMACPS_GMII2RGMII_SPEED10_FD;
	}
#elif	defined(CONFIG_LINKSPEED1000)
	SetUpSLCRDivisors(xemacpsp->Config.BaseAddress,1000);
	link_speed = 1000;
	configure_IEEE_phy_speed(xemacpsp, link_speed);
	convspeeddupsetting = XEMACPS_GMII2RGMII_SPEED1000_FD;
	sleep(1);
#elif	defined(CONFIG_LINKSPEED100)
	SetUpSLCRDivisors(xemacpsp->Config.BaseAddress,100);
	link_speed = 100;
	configure_IEEE_phy_speed(xemacpsp, link_speed);
	convspeeddupsetting = XEMACPS_GMII2RGMII_SPEED100_FD;
	sleep(1);
#elif	defined(CONFIG_LINKSPEED10)
	SetUpSLCRDivisors(xemacpsp->Config.BaseAddress,10);
	link_speed = 10;
	configure_IEEE_phy_speed(xemacpsp, link_speed);
	convspeeddupsetting = XEMACPS_GMII2RGMII_SPEED10_FD;
	sleep(1);
#endif
	if (conv_present) {
		XEmacPs_PhyWrite(xemacpsp, convphyaddr,
		XEMACPS_GMII2RGMII_REG_NUM, convspeeddupsetting);
	}

	xil_printf("link speed: %d\r\n", link_speed);
	return link_speed;
}

