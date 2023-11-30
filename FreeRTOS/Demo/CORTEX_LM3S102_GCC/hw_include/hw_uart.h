//*****************************************************************************
//
// hw_uart.h - Macros and defines used when accessing the UART hardware
//
// Copyright (c) 2005,2006 Luminary Micro, Inc.  All rights reserved.
//
// Software License Agreement
//
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's Stellaris Family of microcontroller products.
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
// This is part of revision 523 of the Stellaris Driver Library.
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

//*****************************************************************************
//
// Data Register bits
//
//*****************************************************************************
#define UART_DR_OE              0x00000800  // Overrun Error
#define UART_DR_BE              0x00000400  // Break Error
#define UART_DR_PE              0x00000200  // Parity Error
#define UART_DR_FE              0x00000100  // Framing Error

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
#define UART_FR_RI              0x100       // Ring Indicator
#define UART_FR_TXFE            0x080       // TX FIFO Empty
#define UART_FR_RXFF            0x040       // RX FIFO Full
#define UART_FR_TXFF            0x020       // TX FIFO Full
#define UART_FR_RXFE            0x010       // RX FIFO Empty
#define UART_FR_BUSY            0x008       // UART Busy

//*****************************************************************************
//
// Line Control Register High bits
//
//*****************************************************************************
#define UART_LCR_H_SPS          0x80        // Stick Parity Select
#define UART_LCR_H_WLEN         0x60        // Word length
#define UART_LCR_H_WLEN_8       0x60        // 8 bit data
#define UART_LCR_H_WLEN_7       0x40        // 7 bit data
#define UART_LCR_H_WLEN_6       0x20        // 6 bit data
#define UART_LCR_H_WLEN_5       0x00        // 5 bit data
#define UART_LCR_H_FEN          0x10        // Enable FIFO
#define UART_LCR_H_STP2         0x08        // Two Stop Bits Select
#define UART_LCR_H_EPS          0x04        // Even Parity Select
#define UART_LCR_H_PEN          0x02        // Parity Enable
#define UART_LCR_H_BRK          0x01        // Send Break

//*****************************************************************************
//
// Control Register bits
//
//*****************************************************************************
#define UART_CTL_CTSEN          0x8000      // CTS Hardware Flow Control
#define UART_CTL_RTSEN          0x4000      // RTS Hardware Flow Control
#define UART_CTL_OUT2           0x2000      // OUT2
#define UART_CTL_OUT1           0x1000      // OUT1
#define UART_CTL_RTS            0x0800      // Request To Send
#define UART_CTL_DTR            0x0400      // Data Terminal Ready
#define UART_CTL_RXE            0x0200      // Receive Enable
#define UART_CTL_TXE            0x0100      // Transmit Enable
#define UART_CTL_LBE            0x0080      // Loopback Enable
#define UART_CTL_IIRLP          0x0004      // IrDA SIR low power mode
#define UART_CTL_SIREN          0x0002      // SIR Enable
#define UART_CTL_UARTEN         0x0001      // UART Enable

//*****************************************************************************
//
// Interrupt FIFO Level Select Register bits
//
//*****************************************************************************
#define UART_IFLS_RX1_8         0x00        // 1/8 Full
#define UART_IFLS_RX2_8         0x10        // 1/4 Full
#define UART_IFLS_RX4_8         0x20        // 1/2 Full
#define UART_IFLS_RX6_8         0x30        // 3/4 Full
#define UART_IFLS_RX7_8         0x40        // 7/8 Full
#define UART_IFLS_TX1_8         0x00        // 1/8 Full
#define UART_IFLS_TX2_8         0x01        // 1/4 Full
#define UART_IFLS_TX4_8         0x02        // 1/2 Full
#define UART_IFLS_TX6_8         0x03        // 3/4 Full
#define UART_IFLS_TX7_8         0x04        // 7/8 Full

//*****************************************************************************
//
// Interrupt Mask Set/Clear Register bits
//
//*****************************************************************************
#define UART_IM_OEIM            0x400       // Overrun Error Interrupt Mask
#define UART_IM_BEIM            0x200       // Break Error Interrupt Mask
#define UART_IM_PEIM            0x100       // Parity Error Interrupt Mask
#define UART_IM_FEIM            0x080       // Framing Error Interrupt Mask
#define UART_IM_RTIM            0x040       // Receive Timeout Interrupt Mask
#define UART_IM_TXIM            0x020       // Transmit Interrupt Mask
#define UART_IM_RXIM            0x010       // Receive Interrupt Mask
#define UART_IM_DSRMIM          0x008       // DSR Interrupt Mask
#define UART_IM_DCDMIM          0x004       // DCD Interrupt Mask
#define UART_IM_CTSMIM          0x002       // CTS Interrupt Mask
#define UART_IM_RIMIM           0x001       // RI Interrupt Mask

//*****************************************************************************
//
// Raw Interrupt Status Register
//
//*****************************************************************************
#define UART_RIS_OERIS          0x400       // Overrun Error Interrupt Status
#define UART_RIS_BERIS          0x200       // Break Error Interrupt Status
#define UART_RIS_PERIS          0x100       // Parity Error Interrupt Status
#define UART_RIS_FERIS          0x080       // Framing Error Interrupt Status
#define UART_RIS_RTRIS          0x040       // Receive Timeout Interrupt Status
#define UART_RIS_TXRIS          0x020       // Transmit Interrupt Status
#define UART_RIS_RXRIS          0x010       // Receive Interrupt Status
#define UART_RIS_DSRRMIS        0x008       // DSR Interrupt Status
#define UART_RIS_DCDRMIS        0x004       // DCD Interrupt Status
#define UART_RIS_CTSRMIS        0x002       // CTS Interrupt Status
#define UART_RIS_RIRMIS         0x001       // RI Interrupt Status

//*****************************************************************************
//
// Masked Interrupt Status Register
//
//*****************************************************************************
#define UART_MIS_OEMIS          0x400       // Overrun Error Interrupt Status
#define UART_MIS_BEMIS          0x200       // Break Error Interrupt Status
#define UART_MIS_PEMIS          0x100       // Parity Error Interrupt Status
#define UART_MIS_FEMIS          0x080       // Framing Error Interrupt Status
#define UART_MIS_RTMIS          0x040       // Receive Timeout Interrupt Status
#define UART_MIS_TXMIS          0x020       // Transmit Interrupt Status
#define UART_MIS_RXMIS          0x010       // Receive Interrupt Status
#define UART_MIS_DSRMMIS        0x008       // DSR Interrupt Status
#define UART_MIS_DCDMMIS        0x004       // DCD Interrupt Status
#define UART_MIS_CTSMMIS        0x002       // CTS Interrupt Status
#define UART_MIS_RIMMIS         0x001       // RI Interrupt Status

//*****************************************************************************
//
// Interrupt Clear Register bits
//
//*****************************************************************************
#define UART_ICR_OEIC           0x200       // Overrun Error Interrupt Clear
#define UART_ICR_BEIC           0x200       // Break Error Interrupt Clear
#define UART_ICR_PEIC           0x200       // Parity Error Interrupt Clear
#define UART_ICR_FEIC           0x200       // Framing Error Interrupt Clear
#define UART_ICR_RTIC           0x200       // Receive Timeout Interrupt Clear
#define UART_ICR_TXIC           0x200       // Transmit Interrupt Clear
#define UART_ICR_RXIC           0x200       // Receive Interrupt Clear
#define UART_ICR_DSRMIC         0x200       // DSR Interrupt Clear
#define UART_ICR_DCDMIC         0x200       // DCD Interrupt Clear
#define UART_ICR_CTSMIC         0x200       // CTS Interrupt Clear
#define UART_ICR_RIMIC          0x200       // RI Interrupt Clear

//*****************************************************************************
//
// DMA Control Register bits
//
//*****************************************************************************
#define UART_DMACRDMAONERR      0x04        // Disable DMA On Error
#define UART_DMACRTXDMAE        0x02        // Enable Transmit DMA
#define UART_DMACRRXDMAE        0x01        // Enable Receive DMA

#define UART_RSR_ANY            (UART_RSR_OE |                                \
                                 UART_RSR_BE |                                \
                                 UART_RSR_PE |                                \
                                 UART_RSR_FE)

//*****************************************************************************
//
// Reset Values for UART Registers.
//
//*****************************************************************************
#define UART_RV_DR              0
#define UART_RV_RSR             0x0
#define UART_RV_ECR             0
#define UART_RV_FR              0x90
#define UART_RV_IBRD            0x0000
#define UART_RV_FBRD            0x00
#define UART_RV_LCR_H           0x00
#define UART_RV_CTL             0x0300
#define UART_RV_IFLS            0x12
#define UART_RV_IM              0x000
#define UART_RV_RIS             0x000
#define UART_RV_MIS             0x000
#define UART_RV_ICR             0x000

#endif // __HW_UART_H__
