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

#ifndef _GMII_DEFINE_H
#define _GMII_DEFINE_H


/*---------------------------------------------------------------------------
 *         Definitions
 *---------------------------------------------------------------------------*/

//IEEE defined Registers
#define GMII_BMCR        0x0   // Basic Mode Control Register
#define GMII_BMSR        0x1   // Basic Mode Status Register
#define GMII_PHYID1R     0x2   // PHY Identifier Register 1
#define GMII_PHYID2R     0x3   // PHY Identifier Register 2
#define GMII_ANAR        0x4   // Auto_Negotiation Advertisement Register
#define GMII_ANLPAR      0x5   // Auto_negotiation Link Partner Ability Register
#define GMII_ANER        0x6   // Auto-negotiation Expansion Register
#define GMII_ANNPR       0x7   // Auto-negotiation Next Page Register
#define GMII_ANLPNPAR    0x8   // Auto_negotiation Link Partner Next Page Ability Register
#define GMII_AFEC0R      0x11  // AFE Control 0 Register
#define GMII_AFEC3R      0x14  // AFE Control 3 Register
#define GMII_RXERCR      0x15  // RXER Counter Register
#define GMII_OMSSR       0x17  // Operation Mode Strap Status Register
#define GMII_ECR         0x18  // Expanded Control Register
#define GMII_ICSR        0x1B  // Interrupt Control/Status Register
#define GMII_FC          0x1C  // Function Control
#define GMII_LCSR        0x1D  // LinkMD® Control/Status Register
#define GMII_PC1R        0x1E  // PHY Control 1 Register
#define GMII_PC2R        0x1F  // PHY Control 2 Register

// PHY ID Identifier Register
#define GMII_LSB_MASK           0x0U
// definitions: MII_PHYID1
#define GMII_OUI_MSB            0x0022
// definitions: MII_PHYID2
#define GMII_OUI_LSB            0x1572          // KSZ8061 PHY Id2

// Basic Mode Control Register (BMCR)
// Bit definitions: MII_BMCR
#define GMII_RESET             (1 << 15) // 1= Software Reset; 0=Normal Operation
#define GMII_LOOPBACK          (1 << 14) // 1=loopback Enabled; 0=Normal Operation
#define GMII_SPEED_SELECT_LSB  (1 << 13) // 1,0=1000Mbps 0,1=100Mbps; 0,0=10Mbps
#define GMII_AUTONEG           (1 << 12) // Auto-negotiation Enable
#define GMII_POWER_DOWN        (1 << 11) // 1=Power down 0=Normal operation
#define GMII_ISOLATE           (1 << 10) // 1 = Isolates 0 = Normal operation
#define GMII_RESTART_AUTONEG   (1 << 9)  // 1 = Restart auto-negotiation 0 = Normal operation
#define GMII_DUPLEX_MODE       (1 << 8)  // 1 = Full duplex operation 0 = Normal operation
//      Reserved                7        // Read as 0, ignore on write
#define GMII_SPEED_SELECT_MSB  (1 << 6)  // 
//      Reserved                5 to 0   // Read as 0, ignore on write


// Basic Mode Status Register (BMSR)
// Bit definitions: MII_BMSR
#define GMII_100BASE_T4        (1 << 15) // 100BASE-T4 Capable
#define GMII_100BASE_TX_FD     (1 << 14) // 100BASE-TX Full Duplex Capable
#define GMII_100BASE_T4_HD     (1 << 13) // 100BASE-TX Half Duplex Capable
#define GMII_10BASE_T_FD       (1 << 12) // 10BASE-T Full Duplex Capable
#define GMII_10BASE_T_HD       (1 << 11) // 10BASE-T Half Duplex Capable
//      Reserved                10 to 9  // Read as 0, ignore on write
#define GMII_EXTEND_STATUS     (1 << 8)  // 1 = Extend Status Information In Reg 15
//      Reserved                7
#define GMII_MF_PREAMB_SUPPR   (1 << 6)  // MII Frame Preamble Suppression
#define GMII_AUTONEG_COMP      (1 << 5)  // Auto-negotiation Complete
#define GMII_REMOTE_FAULT      (1 << 4)  // Remote Fault
#define GMII_AUTONEG_ABILITY   (1 << 3)  // Auto Configuration Ability
#define GMII_LINK_STATUS       (1 << 2)  // Link Status
#define GMII_JABBER_DETECT     (1 << 1)  // Jabber Detect
#define GMII_EXTEND_CAPAB      (1 << 0)  // Extended Capability

// Auto-negotiation Advertisement Register (ANAR)
// Auto-negotiation Link Partner Ability Register (ANLPAR)
// Bit definitions: MII_ANAR, MII_ANLPAR
#define GMII_NP               (1 << 15) // Next page Indication
//      Reserved               7
#define GMII_RF               (1 << 13) // Remote Fault
//      Reserved               12       // Write as 0, ignore on read
#define GMII_PAUSE_MASK       (3 << 11) // 0,0 = No Pause 1,0 = Asymmetric Pause(link partner)
                                        // 0,1 = Symmetric Pause 1,1 = Symmetric&Asymmetric Pause(local device)
#define GMII_T4               (1 << 9)  // 100BASE-T4 Support
#define GMII_TX_FDX           (1 << 8)  // 100BASE-TX Full Duplex Support
#define GMII_TX_HDX           (1 << 7)  // 100BASE-TX Support
#define GMII_10_FDX           (1 << 6)  // 10BASE-T Full Duplex Support
#define GMII_10_HDX           (1 << 5)  // 10BASE-T Support
//      Selector                 4 to 0   // Protocol Selection Bits
#define GMII_AN_IEEE_802_3      0x00001

#endif // #ifndef _MII_DEFINE_H
