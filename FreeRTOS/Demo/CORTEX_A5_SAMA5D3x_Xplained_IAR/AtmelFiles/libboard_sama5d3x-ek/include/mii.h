/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _MII_DEFINE_H
#define _MII_DEFINE_H
/** \addtogroup eth_phy_mii
  @{*/

/*---------------------------------------------------------------------------
 *         Definitions
 *---------------------------------------------------------------------------*/

/** \addtogroup mii_registers PHY registers Addresses
    @{*/
#define MII_BMCR        0   /**< Basic Mode Control Register */
#define MII_BMSR        1   /**< Basic Mode Status Register */
#define MII_PHYID1      2   /**< PHY Idendifier Register 1 */
#define MII_PHYID2      3   /**< PHY Idendifier Register 2 */
#define MII_ANAR        4   /**< Auto_Negotiation Advertisement Register */
#define MII_ANLPAR      5   /**< Auto_negotiation Link Partner Ability Register */
#define MII_ANER        6   /**< Auto-negotiation Expansion Register */
#define MII_DSCR       16   /**< Specified Configuration Register */
#define MII_DSCSR      17   /**< Specified Configuration and Status Register */
#define MII_10BTCSR    18   /**< 10BASE-T Configuration and Satus Register */
#define MII_PWDOR      19   /**< Power Down Control Register */
#define MII_CONFIGR    20   /**< Specified config Register */
#define MII_MDINTR     21   /**< Specified Interrupt Register */
#define MII_RECR       22   /**< Specified Receive Error Counter Register */
#define MII_DISCR      23   /**< Specified Disconnect Counter Register */
#define MII_RLSR       24   /**< Hardware Reset Latch State Register */
/** @}*/

/** \addtogroup phy_bmcr Basic Mode Control Register (BMCR, 0)
    List Bit definitions: \ref MII_BMCR
    @{*/
#define MII_RESET             (1ul << 15) /**< 1= Software Reset; 0=Normal Operation */
#define MII_LOOPBACK          (1ul << 14) /**< 1=loopback Enabled; 0=Normal Operation */
#define MII_SPEED_SELECT      (1ul << 13) /**< 1=100Mbps; 0=10Mbps */
#define MII_AUTONEG           (1ul << 12) /**< Auto-negotiation Enable */
#define MII_POWER_DOWN        (1ul << 11) /**< 1=Power down 0=Normal operation */
#define MII_ISOLATE           (1ul << 10) /**< 1 = Isolates 0 = Normal operation */
#define MII_RESTART_AUTONEG   (1ul << 9)  /**< 1 = Restart auto-negotiation 0 = Normal operation */
#define MII_DUPLEX_MODE       (1ul << 8)  /**< 1 = Full duplex operation 0 = Normal operation */
#define MII_COLLISION_TEST    (1ul << 7)  /**< 1 = Collision test enabled 0 = Normal operation */
/** Reserved bits: 6 to 0, Read as 0, ignore on write */
/** @}*/

/** \addtogroup phy_bmsr Basic Mode Status Register (BMSR, 1)
    List Bit definitions: \ref MII_BMSR
    @{*/
#define MII_100BASE_T4        (1ul << 15) /**< 100BASE-T4 Capable */
#define MII_100BASE_TX_FD     (1ul << 14) /**< 100BASE-TX Full Duplex Capable */
#define MII_100BASE_T4_HD     (1ul << 13) /**< 100BASE-TX Half Duplex Capable */
#define MII_10BASE_T_FD       (1ul << 12) /**< 10BASE-T Full Duplex Capable */
#define MII_10BASE_T_HD       (1ul << 11) /**< 10BASE-T Half Duplex Capable */
/** Reserved bits: 10 to 7, Read as 0, ignore on write */
#define MII_MF_PREAMB_SUPPR   (1ul << 6)  /**< MII Frame Preamble Suppression */
#define MII_AUTONEG_COMP      (1ul << 5)  /**< Auto-negotiation Complete */
#define MII_REMOTE_FAULT      (1ul << 4)  /**< Remote Fault */
#define MII_AUTONEG_ABILITY   (1ul << 3)  /**< Auto Configuration Ability */
#define MII_LINK_STATUS       (1ul << 2)  /**< Link Status */
#define MII_JABBER_DETECT     (1ul << 1)  /**< Jabber Detect */
#define MII_EXTEND_CAPAB      (1ul << 0)  /**< Extended Capability */
/** @}*/

/** \addtogroup phy_id PHY ID Identifier Register (PHYID, 2,3)
    List definitions: \ref MII_PHYID1, \ref MII_PHYID2
    @{*/
#define MII_LSB_MASK             0x3F   /**< Mask for PHY ID LSB */

#if defined(BOARD_EMAC_PHY_COMP_DM9161)
#define MII_OUI_MSB            0x0181
#define MII_OUI_LSB              0x2E
//#define MII_PHYID1_OUI         0x606E   // OUI: Organizationally Unique Identifier
//#define MII_ID             0x0181b8a0
#elif defined(BOARD_EMAC_PHY_COMP_LAN8700)
#define MII_OUI_MSB            0x0007
#define MII_OUI_LSB              0x30
#elif defined(BOARD_EMAC_PHY_COMP_KSZ8051RNL)
#define MII_OUI_MSB            0x0022
#define MII_OUI_LSB              0x05
#else
#error no PHY Ethernet component defined !
#endif
/** @}*/

/** \addtogroup phy_neg Auto-negotiation (ANAR, 4; ANLPAR, 5)
    - Auto-negotiation Advertisement Register (ANAR)
    - Auto-negotiation Link Partner Ability Register (ANLPAR)
    Lists Bit definitions: \ref MII_ANAR, \ref MII_ANLPAR
    @{*/
#define MII_NP               (1ul << 15) /**< Next page Indication */
#define MII_ACK              (1ul << 14) /**< Acknowledge */
#define MII_RF               (1ul << 13) /**< Remote Fault */
/** Reserved: 12 to 11, Write as 0, ignore on read */
#define MII_FCS              (1ul << 10) /**< Flow Control Support */
#define MII_T4               (1ul << 9)  /**< 100BASE-T4 Support */
#define MII_TX_FDX           (1ul << 8)  /**< 100BASE-TX Full Duplex Support */
#define MII_TX_HDX           (1ul << 7)  /**< 100BASE-TX Support */
#define MII_10_FDX           (1ul << 6)  /**< 10BASE-T Full Duplex Support */
#define MII_10_HDX           (1ul << 5)  /**< 10BASE-T Support */
/** Selector: 4 to 0, Protocol Selection Bits */
#define MII_AN_IEEE_802_3      0x0001
/** @}*/

/** \addtogroup phy_neg_exp Auto-negotiation Expansion Register (ANER, 6)
    List Bit definitions: \ref MII_ANER
    @{*/
/** Reserved: 15 to 5, Read as 0, ignore on write */
#define MII_PDF              (1ul << 4) /**< Local Device Parallel Detection Fault */
#define MII_LP_NP_ABLE       (1ul << 3) /**< Link Partner Next Page Able */
#define MII_NP_ABLE          (1ul << 2) /**< Local Device Next Page Able */
#define MII_PAGE_RX          (1ul << 1) /**< New Page Received */
#define MII_LP_AN_ABLE       (1ul << 0) /**< Link Partner Auto-negotiation Able */
/** @}*/

/** \addtogroup phy_dscr Specified Configuration Register (DSCR, 16)
    List Bit definitions: \ref MII_DSCR
    @{*/
#define MII_BP4B5B           (1ul << 15) /**< Bypass 4B5B Encoding and 5B4B Decoding */
#define MII_BP_SCR           (1ul << 14) /**< Bypass Scrambler/Descrambler Function */
#define MII_BP_ALIGN         (1ul << 13) /**< Bypass Symbol Alignment Function */
#define MII_BP_ADPOK         (1ul << 12) /**< BYPASS ADPOK */
#define MII_REPEATER         (1ul << 11) /**< Repeater/Node Mode */
#define MII_TX               (1ul << 10) /**< 100BASE-TX Mode Control */
#define MII_FEF              (1ul << 9)  /**< Far end Fault enable */
#define MII_RMII_ENABLE      (1ul << 8)  /**< Reduced MII Enable */
#define MII_F_LINK_100       (1ul << 7)  /**< Force Good Link in 100Mbps */
#define MII_SPLED_CTL        (1ul << 6)  /**< Speed LED Disable */
#define MII_COLLED_CTL       (1ul << 5)  /**< Collision LED Enable */
#define MII_RPDCTR_EN        (1ul << 4)  /**< Reduced Power Down Control Enable */
#define MII_SM_RST           (1ul << 3)  /**< Reset State Machine */
#define MII_MFP_SC           (1ul << 2)  /**< MF Preamble Suppression Control */
#define MII_SLEEP            (1ul << 1)  /**< Sleep Mode */
#define MII_RLOUT            (1ul << 0)  /**< Remote Loopout Control */
/** @}*/

/** \addtogroup phy_dscsr Specified Configuration and Status Register (DSCSR, 17)
    List Bit definitions: \ref MII_DSCSR
    @{*/
#define MII_100FDX           (1ul << 15) /**< 100M Full Duplex Operation Mode */
#define MII_100HDX           (1ul << 14) /**< 100M Half Duplex Operation Mode */
#define MII_10FDX            (1ul << 13) /**< 10M Full Duplex Operation Mode */
#define MII_10HDX            (1ul << 12) /**< 10M Half Duplex Operation Mode */
/** @}*/

/** \addtogroup phy_10btcsr 10BASE-T Configuration/Status (10BTCSR, 18)
    List Bit definitions: \ref MII_10BTCSR
    @{*/
/** Reserved: 18 to 15, Read as 0, ignore on write */
#define MII_LP_EN            (1ul << 14) /**< Link Pulse Enable */
#define MII_HBE              (1ul << 13) /**< Heartbeat Enable */
#define MII_SQUELCH          (1ul << 12) /**< Squelch Enable */
#define MII_JABEN            (1ul << 11) /**< Jabber Enable */
#define MII_10BT_SER         (1ul << 10) /**< 10BASE-T GPSI Mode */
/** Reserved: 9 to  1, Read as 0, ignore on write */
#define MII_POLR             (1ul << 0)  /**< Polarity Reversed */
/** @}*/

/** \addtogroup phy_mdintr Specified Interrupt Register (MDINTR, 21)
    List Bit definitions: \ref MII_MDINTR
    @{*/
#define MII_INTR_PEND        (1ul << 15) /**< Interrupt Pending */
/** Reserved: 14 to 12, Reserved */
#define MII_FDX_MASK         (1ul << 11) /**< Full-duplex Interrupt Mask */
#define MII_SPD_MASK         (1ul << 10) /**< Speed Interrupt Mask */
#define MII_LINK_MASK        (1ul << 9)  /**< Link Interrupt Mask */
#define MII_INTR_MASK        (1ul << 8)  /**< Master Interrupt Mask */
/** Reserved: 7 to 5, Reserved */
#define MII_FDX_CHANGE       (1ul << 4)  /**< Duplex Status Change Interrupt */
#define MII_SPD_CHANGE       (1ul << 3)  /**< Speed Status Change Interrupt */
#define MII_LINK_CHANGE      (1ul << 2)  /**< Link Status Change Interrupt */
/** Reserved: 1, Reserved */
#define MII_INTR_STATUS      (1ul << 0)  /**< Interrupt Status */
/** @}*/

/**@}*/
#endif // #ifndef _MII_DEFINE_H

