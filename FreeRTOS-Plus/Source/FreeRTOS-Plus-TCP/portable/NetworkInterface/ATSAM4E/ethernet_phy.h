/**
 * \file
 *
 * \brief KSZ8051MNL (Ethernet PHY) driver for SAM.
 *
 * Copyright (c) 2013 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */

#ifndef ETHERNET_PHY_H_INCLUDED
#define ETHERNET_PHY_H_INCLUDED

#include "compiler.h"

#ifdef __cplusplus
extern "C" {
#endif

// IEEE defined Registers
#define GMII_BMCR        0x00   // Basic Control
#define GMII_BMSR        0x01   // Basic Status
#define GMII_PHYID1      0x02   // PHY Idendifier 1
#define GMII_PHYID2      0x03   // PHY Idendifier 2
#define GMII_ANAR        0x04   // Auto_Negotiation Advertisement
#define GMII_ANLPAR      0x05   // Auto_negotiation Link Partner Ability
#define GMII_ANER        0x06   // Auto-negotiation Expansion
#define GMII_ANNPR       0x07   // Auto-negotiation Next Page
#define GMII_ANLPNPAR    0x08   // Link Partner Next Page Ability
//#define GMII_1000BTCR    9   // 1000Base-T Control  // Reserved
//#define GMII_1000BTSR   10   // 1000Base-T Status   // Reserved
#define GMII_AFECR1        0x11   // AFE Control 1
//#define GMII_ERDWR      12   // Extend Register - Data Write Register
//#define GMII_ERDRR      13   // Extend Register - Data Read Register
//14    reserved
#define GMII_RXERCR        0x15   // RXER Counter

	#define PHY_REG_01_BMSR            0x01 // Basic mode status register
	#define PHY_REG_02_PHYSID1         0x02 // PHYS ID 1
	#define PHY_REG_03_PHYSID2         0x03 // PHYS ID 2
	#define PHY_REG_04_ADVERTISE       0x04 // Advertisement control reg
	#define PHY_REG_05_LPA             0x05 // Link partner ability reg
	#define	PHY_REG_06_ANER            0x06 //	6	RW		Auto-Negotiation Expansion Register
	#define	PHY_REG_07_ANNPTR          0x07 //	7	RW		Auto-Negotiation Next Page TX
	#define	PHY_REG_08_RESERVED0       0x08 // 0x08..0x0Fh	8-15	RW		RESERVED

	#define	PHY_REG_10_PHYSTS     0x10	// 16	RO		PHY Status Register
	#define	PHY_REG_11_MICR       0x11	// 17	RW		MII Interrupt Control Register
	#define	PHY_REG_12_MISR       0x12	// 18	RO		MII Interrupt Status Register
	#define	PHY_REG_13_RESERVED1  0x13	// 19	RW		RESERVED
	#define	PHY_REG_14_FCSCR      0x14	// 20	RO		False Carrier Sense Counter Register
	#define	PHY_REG_15_RECR       0x15	// 21	RO		Receive Error Counter Register
	#define	PHY_REG_16_PCSR       0x16	// 22	RW		PCS Sub-Layer Configuration and Status Register
	#define	PHY_REG_17_RBR        0x17	// 23	RW		RMII and Bypass Register
	#define	PHY_REG_18_LEDCR      0x18	// 24	RW		LED Direct Control Register
	#define	PHY_REG_19_PHYCR      0x19	// 25	RW		PHY Control Register
	#define	PHY_REG_1A_10BTSCR    0x1A	// 26	RW		10Base-T Status/Control Register
	#define	PHY_REG_1B_CDCTRL1    0x1B	// 27	RW		CD Test Control Register and BIST Extensions Register
	#define	PHY_REG_1B_INT_CTRL   0x1B	// 27	RW		KSZ8041NL interrupt control
	#define	PHY_REG_1C_RESERVED2  0x1C	// 28	RW		RESERVED
	#define	PHY_REG_1D_EDCR       0x1D	// 29	RW		Energy Detect Control Register
	#define	PHY_REG_1E_RESERVED3  0x1E	//
	#define	PHY_REG_1F_RESERVED4  0x1F	// 30-31	RW		RESERVED

	#define	PHY_REG_1E_PHYCR_1    0x1E	//
	#define	PHY_REG_1F_PHYCR_2    0x1F	//

	#define	PHY_SPEED_10       1
	#define	PHY_SPEED_100      2
	#define	PHY_SPEED_AUTO     (PHY_SPEED_10|PHY_SPEED_100)

	#define	PHY_MDIX_DIRECT    1
	#define	PHY_MDIX_CROSSED   2
	#define	PHY_MDIX_AUTO      (PHY_MDIX_CROSSED|PHY_MDIX_DIRECT)

	#define	PHY_DUPLEX_HALF    1
	#define	PHY_DUPLEX_FULL    2
	#define	PHY_DUPLEX_AUTO    (PHY_DUPLEX_FULL|PHY_DUPLEX_HALF)

	typedef struct _SPhyProps {
		unsigned char speed;
		unsigned char mdix;
		unsigned char duplex;
		unsigned char spare;
	} SPhyProps;

	const char *phyPrintable (const SPhyProps *apProps);

	extern SPhyProps phyProps;

#define GMII_OMSOR        0x16   // Operation Mode Strap Override
#define GMII_OMSSR       0x17   // Operation Mode Strap Status
#define GMII_ECR      0x18   // Expanded Control
//#define GMII_DPPSR      19   // Digital PMA/PCS Status
//20    reserved
//#define GMII_RXERCR     21   // RXER Counter Register
//22-26 reserved
#define GMII_ICSR        0x1B   // Interrupt Control/Status
//#define GMII_DDC1R       28   // Digital Debug Control 1 Register
#define GMII_LCSR        0x1D   // LinkMD Control/Status

//29-30 reserved
#define GMII_PCR1       0x1E   // PHY Control 1
#define GMII_PCR2       0x1F   // PHY Control 2

/*
//Extend Registers
#define GMII_CCR        256  // Common Control Register
#define GMII_SSR        257  // Strap Status Register
#define GMII_OMSOR      258  // Operation Mode Strap Override Register
#define GMII_OMSSR      259  // Operation Mode Strap Status Register
#define GMII_RCCPSR     260  // RGMII Clock and Control Pad Skew Register
#define GMII_RRDPSR     261  // RGMII RX Data Pad Skew Register
#define GMII_ATR        263  // Analog Test Register
*/


// Bit definitions: GMII_BMCR 0x00 Basic Control
#define GMII_RESET             (1 << 15) // 1= Software Reset; 0=Normal Operation
#define GMII_LOOPBACK          (1 << 14) // 1=loopback Enabled; 0=Normal Operation
#define GMII_SPEED_SELECT      (1 << 13) // 1=100Mbps; 0=10Mbps
#define GMII_AUTONEG           (1 << 12) // Auto-negotiation Enable
#define GMII_POWER_DOWN        (1 << 11) // 1=Power down 0=Normal operation
#define GMII_ISOLATE           (1 << 10) // 1 = Isolates 0 = Normal operation
#define GMII_RESTART_AUTONEG   (1 << 9)  // 1 = Restart auto-negotiation 0 = Normal operation
#define GMII_DUPLEX_MODE       (1 << 8)  // 1 = Full duplex operation 0 = Normal operation
#define GMII_COLLISION_TEST    (1 << 7)  // 1 = Enable COL test; 0 = Disable COL test
//#define GMII_SPEED_SELECT_MSB  (1 << 6)  // Reserved
//      Reserved                6 to 0   // Read as 0, ignore on write

// Bit definitions: GMII_BMSR 0x01 Basic Status
#define GMII_100BASE_T4        (1 << 15) // 100BASE-T4 Capable
#define GMII_100BASE_TX_FD     (1 << 14) // 100BASE-TX Full Duplex Capable
#define GMII_100BASE_T4_HD     (1 << 13) // 100BASE-TX Half Duplex Capable
#define GMII_10BASE_T_FD       (1 << 12) // 10BASE-T Full Duplex Capable
#define GMII_10BASE_T_HD       (1 << 11) // 10BASE-T Half Duplex Capable
//      Reserved                10 to79  // Read as 0, ignore on write
//#define GMII_EXTEND_STATUS     (1 << 8)  // 1 = Extend Status Information In Reg 15
//      Reserved                7
#define GMII_MF_PREAMB_SUPPR   (1 << 6)  // MII Frame Preamble Suppression
#define GMII_AUTONEG_COMP      (1 << 5)  // Auto-negotiation Complete
#define GMII_REMOTE_FAULT      (1 << 4)  // Remote Fault
#define GMII_AUTONEG_ABILITY   (1 << 3)  // Auto Configuration Ability
#define GMII_LINK_STATUS       (1 << 2)  // Link Status
#define GMII_JABBER_DETECT     (1 << 1)  // Jabber Detect
#define GMII_EXTEND_CAPAB      (1 << 0)  // Extended Capability


// Bit definitions: GMII_PHYID1 0x02 PHY Idendifier 1
// Bit definitions: GMII_PHYID2 0x03 PHY Idendifier 2
#define GMII_LSB_MASK           0x3F
#define GMII_OUI_MSB            0x0022
#define GMII_OUI_LSB            0x05


// Bit definitions: GMII_ANAR   0x04 Auto_Negotiation Advertisement
// Bit definitions: GMII_ANLPAR 0x05 Auto_negotiation Link Partner Ability
#define GMII_NP               (1 << 15) // Next page Indication
//      Reserved               7
#define GMII_RF               (1 << 13) // Remote Fault
//      Reserved               12       // Write as 0, ignore on read
#define GMII_PAUSE_MASK       (3 << 11) // 0,0 = No Pause 1,0 = Asymmetric Pause(link partner)
                                        // 0,1 = Symmetric Pause 1,1 = Symmetric&Asymmetric Pause(local device)
#define GMII_100T4               (1 << 9)  // 100BASE-T4 Support
#define GMII_100TX_FDX           (1 << 8)  // 100BASE-TX Full Duplex Support
#define GMII_100TX_HDX           (1 << 7)  // 100BASE-TX Support
#define GMII_10_FDX           (1 << 6)  // 10BASE-T Full Duplex Support
#define GMII_10_HDX           (1 << 5)  // 10BASE-T Support
//      Selector                 4 to 0   // Protocol Selection Bits
#define GMII_AN_IEEE_802_3      0x0001    // [00001] = IEEE 802.3


// Bit definitions: GMII_ANER 0x06 Auto-negotiation Expansion
//      Reserved                15 to 5  // Read as 0, ignore on write
#define GMII_PDF              (1 << 4) // Local Device Parallel Detection Fault
#define GMII_LP_NP_ABLE       (1 << 3) // Link Partner Next Page Able
#define GMII_NP_ABLE          (1 << 2) // Local Device Next Page Able
#define GMII_PAGE_RX          (1 << 1) // New Page Received
#define GMII_LP_AN_ABLE       (1 << 0) // Link Partner Auto-negotiation Able

/**
 * \brief Perform a HW initialization to the PHY and set up clocks.
 *
 * This should be called only once to initialize the PHY pre-settings.
 * The PHY address is the reset status of CRS, RXD[3:0] (the GmacPins' pullups).
 * The COL pin is used to select MII mode on reset (pulled up for Reduced MII).
 * The RXDV pin is used to select test mode on reset (pulled up for test mode).
 * The above pins should be predefined for corresponding settings in resetPins.
 * The GMAC peripheral pins are configured after the reset is done.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_phy_addr PHY address.
 * \param ul_mck GMAC MCK.
 *
 * Return GMAC_OK if successfully, GMAC_TIMEOUT if timeout.
 */
uint8_t ethernet_phy_init(Gmac *p_gmac, uint8_t uc_phy_addr, uint32_t ul_mck);


/**
 * \brief Get the Link & speed settings, and automatically set up the GMAC with the
 * settings.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_phy_addr PHY address.
 * \param uc_apply_setting_flag Set to 0 to not apply the PHY configurations, else to apply.
 *
 * Return GMAC_OK if successfully, GMAC_TIMEOUT if timeout.
 */
uint8_t ethernet_phy_set_link(Gmac *p_gmac, uint8_t uc_phy_addr,
		uint8_t uc_apply_setting_flag);


/**
 * \brief Issue an auto negotiation of the PHY.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_phy_addr PHY address.
 *
 * Return GMAC_OK if successfully, GMAC_TIMEOUT if timeout.
 */
uint8_t ethernet_phy_auto_negotiate(Gmac *p_gmac, uint8_t uc_phy_addr);

/**
 * \brief Issue a SW reset to reset all registers of the PHY.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_phy_addr PHY address.
 *
 * \Return GMAC_OK if successfully, GMAC_TIMEOUT if timeout.
 */
uint8_t ethernet_phy_reset(Gmac *p_gmac, uint8_t uc_phy_addr);

typedef struct xPHY_PROPS {
	signed char phy_result;
	uint32_t phy_params;
	uint32_t phy_stat1;
	uint32_t phy_stat2;
	unsigned char phy_chn;
} PhyProps_t;
extern PhyProps_t phy_props;

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* #ifndef ETHERNET_PHY_H_INCLUDED */

