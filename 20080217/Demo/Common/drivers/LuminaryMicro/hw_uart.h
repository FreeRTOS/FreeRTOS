//*****************************************************************************
//
// hw_uart.h - Macros and defines used when accessing the UART hardware
//
// Copyright (c) 2005-2007 Luminary Micro, Inc.  All rights reserved.
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

#ifndef __HW_UART_H__
#define __HW_UART_H__

//*****************************************************************************
//
// UART Register Offsets.
//
//*****************************************************************************
#define UART_O_DR               0x00000000  // Data Register
#define UART_O_RSR              0x00000004  // Receive Status Register (read)
#define UART_O_ECR              0x00000004  // Error Clear Register (write)
#define UART_O_FR               0x00000018  // Flag Register (read only)
#define UART_O_IBRD             0x00000024  // Integer Baud Rate Divisor Reg
#define UART_O_FBRD             0x00000028  // Fractional Baud Rate Divisor Reg
#define UART_O_LCR_H            0x0000002C  // Line Control Register, HIGH byte
#define UART_O_CTL              0x00000030  // Control Register
#define UART_O_IFLS             0x00000034  // Interrupt FIFO Level Select Reg
#define UART_O_IM               0x00000038  // Interrupt Mask Set/Clear Reg
#define UART_O_RIS              0x0000003C  // Raw Interrupt Status Register
#define UART_O_MIS              0x00000040  // Masked Interrupt Status Register
#define UART_O_ICR              0x00000044  // Interrupt Clear Register
#define UART_O_PeriphID4        0x00000FD0  //
#define UART_O_PeriphID5        0x00000FD4  //
#define UART_O_PeriphID6        0x00000FD8  //
#define UART_O_PeriphID7        0x00000FDC  //
#define UART_O_PeriphID0        0x00000FE0  //
#define UART_O_PeriphID1        0x00000FE4  //
#define UART_O_PeriphID2        0x00000FE8  //
#define UART_O_PeriphID3        0x00000FEC  //
#define UART_O_PCellID0         0x00000FF0  //
#define UART_O_PCellID1         0x00000FF4  //
#define UART_O_PCellID2         0x00000FF8  //
#define UART_O_PCellID3         0x00000FFC  //

//*****************************************************************************
//
// Data Register bits
//
//*****************************************************************************
#define UART_DR_OE              0x00000800  // Overrun Error
#define UART_DR_BE              0x00000400  // Break Error
#define UART_DR_PE              0x00000200  // Parity Error
#define UART_DR_FE              0x00000100  // Framing Error
#define UART_DR_DATA_MASK       0x000000FF  // UART data

//*****************************************************************************
//
// Receive Status Register bits
//
//*****************************************************************************
#define UART_RSR_OE             0x00000008  // Overrun Error
#define UART_RSR_BE             0x00000004  // Break Error
#define UART_RSR_PE             0x00000002  // Parity Error
#define UART_RSR_FE             0x00000001  // Framing Error

//*****************************************************************************
//
// Flag Register bits
//
//*****************************************************************************
#define UART_FR_TXFE            0x00000080  // TX FIFO Empty
#define UART_FR_RXFF            0x00000040  // RX FIFO Full
#define UART_FR_TXFF            0x00000020  // TX FIFO Full
#define UART_FR_RXFE            0x00000010  // RX FIFO Empty
#define UART_FR_BUSY            0x00000008  // UART Busy

//*****************************************************************************
//
// Integer baud-rate divisor
//
//*****************************************************************************
#define UART_IBRD_DIVINT_MASK   0x0000FFFF  // Integer baud-rate divisor

//*****************************************************************************
//
// Fractional baud-rate divisor
//
//*****************************************************************************
#define UART_FBRD_DIVFRAC_MASK  0x0000003F  // Fractional baud-rate divisor

//*****************************************************************************
//
// Line Control Register High bits
//
//*****************************************************************************
#define UART_LCR_H_SPS          0x00000080  // Stick Parity Select
#define UART_LCR_H_WLEN         0x00000060  // Word length
#define UART_LCR_H_WLEN_8       0x00000060  // 8 bit data
#define UART_LCR_H_WLEN_7       0x00000040  // 7 bit data
#define UART_LCR_H_WLEN_6       0x00000020  // 6 bit data
#define UART_LCR_H_WLEN_5       0x00000000  // 5 bit data
#define UART_LCR_H_FEN          0x00000010  // Enable FIFO
#define UART_LCR_H_STP2         0x00000008  // Two Stop Bits Select
#define UART_LCR_H_EPS          0x00000004  // Even Parity Select
#define UART_LCR_H_PEN          0x00000002  // Parity Enable
#define UART_LCR_H_BRK          0x00000001  // Send Break

//*****************************************************************************
//
// Control Register bits
//
//*****************************************************************************
#define UART_CTL_RXE            0x00000200  // Receive Enable
#define UART_CTL_TXE            0x00000100  // Transmit Enable
#define UART_CTL_LBE            0x00000080  // Loopback Enable
#define UART_CTL_SIRLP          0x00000004  // SIR (IrDA) Low Power Enable
#define UART_CTL_SIREN          0x00000002  // SIR (IrDA) Enable
#define UART_CTL_UARTEN         0x00000001  // UART Enable

//*****************************************************************************
//
// Interrupt FIFO Level Select Register bits
//
//*****************************************************************************
#define UART_IFLS_RX_MASK       0x00000038  // RX FIFO level mask
#define UART_IFLS_RX1_8         0x00000000  // 1/8 Full
#define UART_IFLS_RX2_8         0x00000008  // 1/4 Full
#define UART_IFLS_RX4_8         0x00000010  // 1/2 Full
#define UART_IFLS_RX6_8         0x00000018  // 3/4 Full
#define UART_IFLS_RX7_8         0x00000020  // 7/8 Full
#define UART_IFLS_TX_MASK       0x00000007  // TX FIFO level mask
#define UART_IFLS_TX1_8         0x00000000  // 1/8 Full
#define UART_IFLS_TX2_8         0x00000001  // 1/4 Full
#define UART_IFLS_TX4_8         0x00000002  // 1/2 Full
#define UART_IFLS_TX6_8         0x00000003  // 3/4 Full
#define UART_IFLS_TX7_8         0x00000004  // 7/8 Full

//*****************************************************************************
//
// Interrupt Mask Set/Clear Register bits
//
//*****************************************************************************
#define UART_IM_OEIM            0x00000400  // Overrun Error Interrupt Mask
#define UART_IM_BEIM            0x00000200  // Break Error Interrupt Mask
#define UART_IM_PEIM            0x00000100  // Parity Error Interrupt Mask
#define UART_IM_FEIM            0x00000080  // Framing Error Interrupt Mask
#define UART_IM_RTIM            0x00000040  // Receive Timeout Interrupt Mask
#define UART_IM_TXIM            0x00000020  // Transmit Interrupt Mask
#define UART_IM_RXIM            0x00000010  // Receive Interrupt Mask

//*****************************************************************************
//
// Raw Interrupt Status Register
//
//*****************************************************************************
#define UART_RIS_OERIS          0x00000400  // Overrun Error Interrupt Status
#define UART_RIS_BERIS          0x00000200  // Break Error Interrupt Status
#define UART_RIS_PERIS          0x00000100  // Parity Error Interrupt Status
#define UART_RIS_FERIS          0x00000080  // Framing Error Interrupt Status
#define UART_RIS_RTRIS          0x00000040  // Receive Timeout Interrupt Status
#define UART_RIS_TXRIS          0x00000020  // Transmit Interrupt Status
#define UART_RIS_RXRIS          0x00000010  // Receive Interrupt Status

//*****************************************************************************
//
// Masked Interrupt Status Register
//
//*****************************************************************************
#define UART_MIS_OEMIS          0x00000400  // Overrun Error Interrupt Status
#define UART_MIS_BEMIS          0x00000200  // Break Error Interrupt Status
#define UART_MIS_PEMIS          0x00000100  // Parity Error Interrupt Status
#define UART_MIS_FEMIS          0x00000080  // Framing Error Interrupt Status
#define UART_MIS_RTMIS          0x00000040  // Receive Timeout Interrupt Status
#define UART_MIS_TXMIS          0x00000020  // Transmit Interrupt Status
#define UART_MIS_RXMIS          0x00000010  // Receive Interrupt Status

//*****************************************************************************
//
// Interrupt Clear Register bits
//
//*****************************************************************************
#define UART_ICR_OEIC           0x00000400  // Overrun Error Interrupt Clear
#define UART_ICR_BEIC           0x00000200  // Break Error Interrupt Clear
#define UART_ICR_PEIC           0x00000100  // Parity Error Interrupt Clear
#define UART_ICR_FEIC           0x00000080  // Framing Error Interrupt Clear
#define UART_ICR_RTIC           0x00000040  // Receive Timeout Interrupt Clear
#define UART_ICR_TXIC           0x00000020  // Transmit Interrupt Clear
#define UART_ICR_RXIC           0x00000010  // Receive Interrupt Clear

#define UART_RSR_ANY            (UART_RSR_OE |                                \
                                 UART_RSR_BE |                                \
                                 UART_RSR_PE |                                \
                                 UART_RSR_FE)

//*****************************************************************************
//
// Reset Values for UART Registers.
//
//*****************************************************************************
#define UART_RV_DR              0x00000000
#define UART_RV_RSR             0x00000000
#define UART_RV_ECR             0x00000000
#define UART_RV_FR              0x00000090
#define UART_RV_IBRD            0x00000000
#define UART_RV_FBRD            0x00000000
#define UART_RV_LCR_H           0x00000000
#define UART_RV_CTL             0x00000300
#define UART_RV_IFLS            0x00000012
#define UART_RV_IM              0x00000000
#define UART_RV_RIS             0x00000000
#define UART_RV_MIS             0x00000000
#define UART_RV_ICR             0x00000000
#define UART_RV_PeriphID4       0x00000000
#define UART_RV_PeriphID5       0x00000000
#define UART_RV_PeriphID6       0x00000000
#define UART_RV_PeriphID7       0x00000000
#define UART_RV_PeriphID0       0x00000011
#define UART_RV_PeriphID1       0x00000000
#define UART_RV_PeriphID2       0x00000018
#define UART_RV_PeriphID3       0x00000001
#define UART_RV_PCellID0        0x0000000D
#define UART_RV_PCellID1        0x000000F0
#define UART_RV_PCellID2        0x00000005
#define UART_RV_PCellID3        0x000000B1

#endif // __HW_UART_H__
