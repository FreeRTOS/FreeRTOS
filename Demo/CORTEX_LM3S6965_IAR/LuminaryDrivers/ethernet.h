//*****************************************************************************
//
// ethernet.h - Defines and Macros for the ethernet module.
//
// Copyright (c) 2006-2007 Luminary Micro, Inc.  All rights reserved.
// 
// Software License Agreement
// 
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
// 
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  Any use in violation
// of the foregoing restrictions may subject the user to criminal sanctions
// under applicable laws, as well as to civil liability for the breach of the
// terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
// 
// This is part of revision 1408 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __ETHERNET_H__
#define __ETHERNET_H__

#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// Values that can be passed to EthernetConfigSet as the ulConfig value, and
// returned from EthernetConfigGet.
//
//*****************************************************************************
#define ETH_CFG_RX_BADCRCDIS    0x000800    // Disable RX BAD CRC Packets
#define ETH_CFG_RX_PRMSEN       0x000400    // Enable RX Promiscuous
#define ETH_CFG_RX_AMULEN       0x000200    // Enable RX Multicast
#define ETH_CFG_TX_DPLXEN       0x000010    // Enable TX Duplex Mode
#define ETH_CFG_TX_CRCEN        0x000004    // Enable TX CRC Generation
#define ETH_CFG_TX_PADEN        0x000002    // Enable TX Padding

//*****************************************************************************
//
// Values that can be passed to EthernetIntEnable, EthernetIntDisable, and
// EthernetIntClear as the ulIntFlags parameter, and returned from
// EthernetIntStatus.
//
//*****************************************************************************
#define ETH_INT_PHY             0x040       // PHY Event/Interrupt
#define ETH_INT_MDIO            0x020       // Management Transaction
#define ETH_INT_RXER            0x010       // RX Error
#define ETH_INT_RXOF            0x008       // RX FIFO Overrun
#define ETH_INT_TX              0x004       // TX Complete
#define ETH_INT_TXER            0x002       // TX Error
#define ETH_INT_RX              0x001       // RX Complete

//*****************************************************************************
//
// The following define values that can be passed as register addresses to
// EthernetPHYRead and EthernetPHYWrite.
//
//*****************************************************************************
#define PHY_MR0                  0          // Control
#define PHY_MR1                  1          // Status
#define PHY_MR2                  2          // PHY Identifier 1
#define PHY_MR3                  3          // PHY Identifier 2
#define PHY_MR4                  4          // Auto-Neg. Advertisement
#define PHY_MR5                  5          // Auto-Neg. Link Partner Ability
#define PHY_MR6                  6          // Auto-Neg. Expansion
                                            // 7-15 Reserved/Not Implemented
#define PHY_MR16                16          // Vendor Specific
#define PHY_MR17                17          // Interrupt Control/Status
#define PHY_MR18                18          // Diagnostic Register
#define PHY_MR19                19          // Transceiver Control
                                            // 20-22 Reserved
#define PHY_MR23                23          // LED Configuration Register
#define PHY_MR24                24          // MDI/MDIX Control Register
                                            // 25-31 Reserved/Not Implemented

//*****************************************************************************
//
// The following define bit fields in the ETH_MR0 register
//
//*****************************************************************************
#define PHY_MR0_RESET           0x8000      // Reset the PHY
#define PHY_MR0_LOOPBK          0x4000      // TXD to RXD Loopback
#define PHY_MR0_SPEEDSL         0x2000      // Speed Selection
#define PHY_MR0_SPEEDSL_10      0x0000      // Speed Selection 10BASE-T
#define PHY_MR0_SPEEDSL_100     0x2000      // Speed Selection 100BASE-T
#define PHY_MR0_ANEGEN          0x1000      // Auto-Negotiation Enable
#define PHY_MR0_PWRDN           0x0800      // Power Down
#define PHY_MR0_RANEG           0x0200      // Restart Auto-Negotiation
#define PHY_MR0_DUPLEX          0x0100      // Enable full duplex
#define PHY_MR0_DUPLEX_HALF     0x0000      // Enable half duplex mode
#define PHY_MR0_DUPLEX_FULL     0x0100      // Enable full duplex mode

//*****************************************************************************
//
// The following define bit fields in the ETH_MR1 register
//
//*****************************************************************************
#define PHY_MR1_ANEGC           0x0020      // Auto-Negotiate Complete
#define PHY_MR1_RFAULT          0x0010      // Remove Fault Detected
#define PHY_MR1_LINK            0x0004      // Link Established
#define PHY_MR1_JAB             0x0002      // Jabber Condition Detected

//*****************************************************************************
//
// The following define bit fields in the ETH_MR17 register
//
//*****************************************************************************
#define PHY_MR17_RXER_IE        0x4000      // Enable Receive Error Interrupt
#define PHY_MR17_LSCHG_IE       0x0400      // Enable Link Status Change Int.
#define PHY_MR17_ANEGCOMP_IE    0x0100      // Enable Auto-Negotiate Cmpl. Int.
#define PHY_MR17_RXER_INT       0x0040      // Receive Error Interrupt
#define PHY_MR17_LSCHG_INT      0x0004      // Link Status Change Interrupt
#define PHY_MR17_ANEGCOMP_INT   0x0001      // Auto-Negotiate Complete Int.

//*****************************************************************************
//
// The following define bit fields in the ETH_MR18 register
//
//*****************************************************************************
#define PHY_MR18_ANEGF          0x1000      // Auto-Negotiate Failed
#define PHY_MR18_DPLX           0x0800      // Duplex Mode Negotiated
#define PHY_MR18_DPLX_HALF      0x0000      // Half Duplex Mode Negotiated
#define PHY_MR18_DPLX_FULL      0x0800      // Full Duplex Mode Negotiated
#define PHY_MR18_RATE           0x0400      // Rate Negotiated
#define PHY_MR18_RATE_10        0x0000      // Rate Negotiated is 10BASE-T
#define PHY_MR18_RATE_100       0x0400      // Rate Negotiated is 100BASE-TX

//*****************************************************************************
//
// The following define bit fields in the ETH_MR23 register
//
//*****************************************************************************
#define PHY_MR23_LED1           0x00f0      // LED1 Configuration
#define PHY_MR23_LED1_LINK      0x0000      // LED1 is Link Status
#define PHY_MR23_LED1_RXTX      0x0010      // LED1 is RX or TX Activity
#define PHY_MR23_LED1_TX        0x0020      // LED1 is TX Activity
#define PHY_MR23_LED1_RX        0x0030      // LED1 is RX Activity
#define PHY_MR23_LED1_COL       0x0040      // LED1 is RX Activity
#define PHY_MR23_LED1_100       0x0050      // LED1 is RX Activity
#define PHY_MR23_LED1_10        0x0060      // LED1 is RX Activity
#define PHY_MR23_LED1_DUPLEX    0x0070      // LED1 is RX Activity
#define PHY_MR23_LED1_LINKACT   0x0080      // LED1 is Link Status + Activity
#define PHY_MR23_LED0           0x000f      // LED0 Configuration
#define PHY_MR23_LED0_LINK      0x0000      // LED0 is Link Status
#define PHY_MR23_LED0_RXTX      0x0001      // LED0 is RX or TX Activity
#define PHY_MR23_LED0_TX        0x0002      // LED0 is TX Activity
#define PHY_MR23_LED0_RX        0x0003      // LED0 is RX Activity
#define PHY_MR23_LED0_COL       0x0004      // LED0 is RX Activity
#define PHY_MR23_LED0_100       0x0005      // LED0 is RX Activity
#define PHY_MR23_LED0_10        0x0006      // LED0 is RX Activity
#define PHY_MR23_LED0_DUPLEX    0x0007      // LED0 is RX Activity
#define PHY_MR23_LED0_LINKACT   0x0008      // LED0 is Link Status + Activity

//*****************************************************************************
//
// The following define bit fields in the ETH_MR24 register
//
//*****************************************************************************
#define PHY_MR24_MDIX           0x0020      // Auto-Switching Configuration
#define PHY_MR24_MDIX_NORMAL    0x0000      // Auto-Switching in passthrough
#define PHY_MR23_MDIX_CROSSOVER 0x0020      // Auto-Switching in crossover

//*****************************************************************************
//
// Helper Macros for Ethernet Processing
//
//*****************************************************************************
//
// htonl/ntohl - big endian/little endian byte swapping macros for
// 32-bit (long) values
//
//*****************************************************************************
#ifndef htonl
    #define htonl(a)                    \
        ((((a) >> 24) & 0x000000ff) |   \
         (((a) >>  8) & 0x0000ff00) |   \
         (((a) <<  8) & 0x00ff0000) |   \
         (((a) << 24) & 0xff000000))
#endif

#ifndef ntohl
    #define ntohl(a)    htonl((a))
#endif

//*****************************************************************************
//
// htons/ntohs - big endian/little endian byte swapping macros for
// 16-bit (short) values
//
//*****************************************************************************
#ifndef htons
    #define htons(a)                \
        ((((a) >> 8) & 0x00ff) |    \
         (((a) << 8) & 0xff00))
#endif

#ifndef ntohs
    #define ntohs(a)    htons((a))
#endif

//*****************************************************************************
//
// API Function prototypes
//
//*****************************************************************************
extern void EthernetInit(unsigned long ulBase);
extern void EthernetConfigSet(unsigned long ulBase, unsigned long ulConfig);
extern unsigned long EthernetConfigGet(unsigned long ulBase);
extern void EthernetMACAddrSet(unsigned long ulBase,
                               unsigned char *pucMACAddr);
extern void EthernetMACAddrGet(unsigned long ulBase,
                               unsigned char *pucMACAddr);
extern void EthernetEnable(unsigned long ulBase);
extern void EthernetDisable(unsigned long ulBase);
extern tBoolean EthernetPacketAvail(unsigned long ulBase);
extern tBoolean EthernetSpaceAvail(unsigned long ulBase);
extern long EthernetPacketNonBlockingGet(unsigned long ulBase,
                                         unsigned char *pucBuf,
                                         long lBufLen);
extern long EthernetPacketGet(unsigned long ulBase, unsigned char *pucBuf,
                              long lBufLen);
extern long EthernetPacketNonBlockingPut(unsigned long ulBase,
                                         unsigned char *pucBuf,
                                         long lBufLen);
extern long EthernetPacketPut(unsigned long ulBase, unsigned char *pucBuf,
                              long lBufLen);
extern void EthernetIntRegister(unsigned long ulBase,
                                void (*pfnHandler)(void));
extern void EthernetIntUnregister(unsigned long ulBase);
extern void EthernetIntEnable(unsigned long ulBase, unsigned long ulIntFlags);
extern void EthernetIntDisable(unsigned long ulBase, unsigned long ulIntFlags);
extern unsigned long EthernetIntStatus(unsigned long ulBase, tBoolean bMasked);
extern void EthernetIntClear(unsigned long ulBase, unsigned long ulIntFlags);
extern void EthernetPHYWrite(unsigned long ulBase, unsigned char ucRegAddr,
                             unsigned long ulData);
extern unsigned long EthernetPHYRead(unsigned long ulBase,
                                     unsigned char ucRegAddr);

#ifdef __cplusplus
}
#endif

#endif //  __ETHERNET_H__
