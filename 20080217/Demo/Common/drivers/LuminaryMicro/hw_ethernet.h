//*****************************************************************************
//
// hw_ethernet.h - Macros used when accessing the ethernet hardware.
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
// This is part of revision 1582 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __HW_ETHERNET_H__
#define __HW_ETHERNET_H__

//*****************************************************************************
//
// The following define the offsets of the MAC registers in the Ethernet
// Controller.
//
//*****************************************************************************
#define MAC_O_IS                0x00000000  // Interrupt Status Register
#define MAC_O_IACK              0x00000000  // Interrupt Acknowledge Register
#define MAC_O_IM                0x00000004  // Interrupt Mask Register
#define MAC_O_RCTL              0x00000008  // Receive Control Register
#define MAC_O_TCTL              0x0000000C  // Transmit Control Register
#define MAC_O_DATA              0x00000010  // Data Register
#define MAC_O_IA0               0x00000014  // Individual Address Register 0
#define MAC_O_IA1               0x00000018  // Individual Address Register 1
#define MAC_O_THR               0x0000001C  // Threshold Register
#define MAC_O_MCTL              0x00000020  // Management Control Register
#define MAC_O_MDV               0x00000024  // Management Divider Register
#define MAC_O_MADD              0x00000028  // Management Address Register
#define MAC_O_MTXD              0x0000002C  // Management Transmit Data Reg
#define MAC_O_MRXD              0x00000030  // Management Receive Data Reg
#define MAC_O_NP                0x00000034  // Number of Packets Register
#define MAC_O_TR                0x00000038  // Transmission Request Register
#define MAC_O_TS                0x0000003C  // Timer Support Register

//*****************************************************************************
//
// The following define the reset values of the MAC registers.
//
//*****************************************************************************
#define MAC_RV_IS               0x00000000
#define MAC_RV_IACK             0x00000000
#define MAC_RV_IM               0x0000007F
#define MAC_RV_RCTL             0x00000008
#define MAC_RV_TCTL             0x00000000
#define MAC_RV_DATA             0x00000000
#define MAC_RV_IA0              0x00000000
#define MAC_RV_IA1              0x00000000
#define MAC_RV_THR              0x0000003F
#define MAC_RV_MCTL             0x00000000
#define MAC_RV_MDV              0x00000080
#define MAC_RV_MADD             0x00000000
#define MAC_RV_MTXD             0x00000000
#define MAC_RV_MRXD             0x00000000
#define MAC_RV_NP               0x00000000
#define MAC_RV_TR               0x00000000

//*****************************************************************************
//
// The following define the bit fields in the MAC_IS register.
//
//*****************************************************************************
#define MAC_IS_PHYINT           0x00000040  // PHY Interrupt
#define MAC_IS_MDINT            0x00000020  // MDI Transaction Complete
#define MAC_IS_RXER             0x00000010  // RX Error
#define MAC_IS_FOV              0x00000008  // RX FIFO Overrun
#define MAC_IS_TXEMP            0x00000004  // TX FIFO Empy
#define MAC_IS_TXER             0x00000002  // TX Error
#define MAC_IS_RXINT            0x00000001  // RX Packet Available

//*****************************************************************************
//
// The following define the bit fields in the MAC_IACK register.
//
//*****************************************************************************
#define MAC_IACK_PHYINT         0x00000040  // Clear PHY Interrupt
#define MAC_IACK_MDINT          0x00000020  // Clear MDI Transaction Complete
#define MAC_IACK_RXER           0x00000010  // Clear RX Error
#define MAC_IACK_FOV            0x00000008  // Clear RX FIFO Overrun
#define MAC_IACK_TXEMP          0x00000004  // Clear TX FIFO Empy
#define MAC_IACK_TXER           0x00000002  // Clear TX Error
#define MAC_IACK_RXINT          0x00000001  // Clear RX Packet Available

//*****************************************************************************
//
// The following define the bit fields in the MAC_IM register.
//
//*****************************************************************************
#define MAC_IM_PHYINTM          0x00000040  // Mask PHY Interrupt
#define MAC_IM_MDINTM           0x00000020  // Mask MDI Transaction Complete
#define MAC_IM_RXERM            0x00000010  // Mask RX Error
#define MAC_IM_FOVM             0x00000008  // Mask RX FIFO Overrun
#define MAC_IM_TXEMPM           0x00000004  // Mask TX FIFO Empy
#define MAC_IM_TXERM            0x00000002  // Mask TX Error
#define MAC_IM_RXINTM           0x00000001  // Mask RX Packet Available

//*****************************************************************************
//
// The following define the bit fields in the MAC_RCTL register.
//
//*****************************************************************************
#define MAC_RCTL_RSTFIFO        0x00000010  // Clear the Receive FIFO
#define MAC_RCTL_BADCRC         0x00000008  // Reject Packets With Bad CRC
#define MAC_RCTL_PRMS           0x00000004  // Enable Promiscuous Mode
#define MAC_RCTL_AMUL           0x00000002  // Enable Multicast Packets
#define MAC_RCTL_RXEN           0x00000001  // Enable Ethernet Receiver

//*****************************************************************************
//
// The following define the bit fields in the MAC_TCTL register.
//
//*****************************************************************************
#define MAC_TCTL_DUPLEX         0x00000010  // Enable Duplex mode
#define MAC_TCTL_CRC            0x00000004  // Enable CRC Generation
#define MAC_TCTL_PADEN          0x00000002  // Enable Automatic Padding
#define MAC_TCTL_TXEN           0x00000001  // Enable Ethernet Transmitter

//*****************************************************************************
//
// The following define the bit fields in the MAC_IA0 register.
//
//*****************************************************************************
#define MAC_IA0_MACOCT4         0xFF000000  // 4th Octet of MAC address
#define MAC_IA0_MACOCT3         0x00FF0000  // 3rd Octet of MAC address
#define MAC_IA0_MACOCT2         0x0000FF00  // 2nd Octet of MAC address
#define MAC_IA0_MACOCT1         0x000000FF  // 1st Octet of MAC address

//*****************************************************************************
//
// The following define the bit fields in the MAC_IA1 register.
//
//*****************************************************************************
#define MAC_IA1_MACOCT6         0x0000FF00  // 6th Octet of MAC address
#define MAC_IA1_MACOCT5         0x000000FF  // 5th Octet of MAC address

//*****************************************************************************
//
// The following define the bit fields in the MAC_TXTH register.
//
//*****************************************************************************
#define MAC_THR_THRESH          0x0000003F  // Transmit Threshold Value

//*****************************************************************************
//
// The following define the bit fields in the MAC_MCTL register.
//
//*****************************************************************************
#define MAC_MCTL_REGADR         0x000000F8  // Address for Next MII Transaction
#define MAC_MCTL_WRITE          0x00000002  // Next MII Transaction is Write
#define MAC_MCTL_START          0x00000001  // Start MII Transaction

//*****************************************************************************
//
// The following define the bit fields in the MAC_MDV register.
//
//*****************************************************************************
#define MAC_MDV_DIV             0x000000FF  // Clock Divider for MDC for TX

//*****************************************************************************
//
// The following define the bit fields in the MAC_MTXD register.
//
//*****************************************************************************
#define MAC_MTXD_MDTX           0x0000FFFF  // Data for Next MII Transaction

//*****************************************************************************
//
// The following define the bit fields in the MAC_MRXD register.
//
//*****************************************************************************
#define MAC_MRXD_MDRX           0x0000FFFF  // Data Read from Last MII Trans.

//*****************************************************************************
//
// The following define the bit fields in the MAC_NP register.
//
//*****************************************************************************
#define MAC_NP_NPR              0x0000003F   // Number of RX Frames in FIFO

//*****************************************************************************
//
// The following define the bit fields in the MAC_TXRQ register.
//
//*****************************************************************************
#define MAC_TR_NEWTX            0x00000001  // Start an Ethernet Transmission

//*****************************************************************************
//
// The following define the bit fields in the MAC_TS register.
//
//*****************************************************************************
#define MAC_TS_TSEN             0x00000001  // Enable Timestamp Logic

#endif // __HW_ETHERNET_H__
