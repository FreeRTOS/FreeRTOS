/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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


//-----------------------------------------------------------------------------
///         Definitions
//-----------------------------------------------------------------------------
//IEEE defined Registers
#define GMII_BMCR        0   // Basic Mode Control Register
#define GMII_BMSR        1   // Basic Mode Status Register
#define GMII_PHYID1      2   // PHY Idendifier Register 1
#define GMII_PHYID2      3   // PHY Idendifier Register 2
#define GMII_ANAR        4   // Auto_Negotiation Advertisement Register
#define GMII_ANLPAR      5   // Auto_negotiation Link Partner Ability Register
#define GMII_ANER        6   // Auto-negotiation Expansion Register
#define GMII_ANNPR       7   // Auto-negotiation Next Page Register
#define GMII_ANLPNPAR    8   // Auto_negotiation Link Partner Next Page Ability Register
#define GMII_1000BTCR    9   // 1000Base-T Control
#define GMII_1000BTSR   10   // 1000Base-T Status
#define GMII_ERCR       11   // Extend Register - Control Register
#define GMII_ERDWR      12   // Extend Register - Data Write Register
#define GMII_ERDRR      13   // Extend Register - Data Read Register
//14    reserved
#define GMII_EMSR       15   // Extend MII Status Register

//Vender Specific Register
//16    reserved
#define GMII_RLLMR      17   // Remote Loopback, LED Mode Register
#define GMII_LMDCDR     18   // LinkND - Cable Diagnostic Register
#define GMII_DPPSR      19   // Digital PMA/PCS Status
//20    reserved
#define GMII_RXERCR     21   // RXER Counter Register
//22-26 reserved
#define GMII_ICSR       27   // Interrupt Control/Status Register
#define GMII_DDC1R      28   // Digital Debug Control 1 Register
//29-30 reserved
#define GMII_PHYCR      31   // PHY Control Register

//Extend Registers
#define GMII_CCR        256  // Common Control Register
#define GMII_SSR        257  // Strap Status Register
#define GMII_OMSOR      258  // Operation Mode Strap Override Register
#define GMII_OMSSR      259  // Operation Mode Strap Status Register
#define GMII_RCCPSR     260  // RGMII Clock and Control Pad Skew Register
#define GMII_RRDPSR     261  // RGMII RX Data Pad Skew Register
#define GMII_ATR        263  // Analog Test Register



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

// PHY ID Identifier Register
// definitions: MII_PHYID1
#define GMII_LSB_MASK           0x3F
#define GMII_OUI_MSB            0x0022
#define GMII_OUI_LSB            0x05

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
#define GMII_AN_IEEE_802_3      0x0001

// Auto-negotiation Expansion Register (ANER)
// Bit definitions: MII_ANER
//      Reserved                15 to 5  // Read as 0, ignore on write
#define GMII_PDF              (1 << 4) // Local Device Parallel Detection Fault
#define GMII_LP_NP_ABLE       (1 << 3) // Link Partner Next Page Able
#define GMII_NP_ABLE          (1 << 2) // Local Device Next Page Able
#define GMII_PAGE_RX          (1 << 1) // New Page Received
#define GMII_LP_AN_ABLE       (1 << 0) // Link Partner Auto-negotiation Able

// GMII_1000BTCR
#define GMII_1000BaseT_HALF_DUPLEX       (1 << 8)  
#define GMII_1000BaseT_FULL_DUPLEX       (1 << 9)  
#define GMII_MARSTER_SLAVE_ENABLE        (1 << 12)  
#define GMII_MARSTER_SLAVE_CONFIG        (1 << 11)  
#define GMII_PORT_TYPE                   (1 << 10)  

// GMII_1000BTSR  
#define GMII_LINKP_1000BaseT_HALF_DUPLEX (1 << 10)  
#define GMII_LINKP_1000BaseT_FULL_DUPLEX (1 << 11)  

// 1 master 0 slave
#endif // #ifndef _MII_DEFINE_H

