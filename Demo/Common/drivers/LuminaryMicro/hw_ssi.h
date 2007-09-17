//*****************************************************************************
//
// hw_ssi.h - Macros used when accessing the SSI hardware.
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

#ifndef __HW_SSI_H__
#define __HW_SSI_H__

//*****************************************************************************
//
// The following define the offsets of the SSI registers.
//
//*****************************************************************************
#define SSI_O_CR0               0x00000000  // Control register 0
#define SSI_O_CR1               0x00000004  // Control register 1
#define SSI_O_DR                0x00000008  // Data register
#define SSI_O_SR                0x0000000C  // Status register
#define SSI_O_CPSR              0x00000010  // Clock prescale register
#define SSI_O_IM                0x00000014  // Int mask set and clear register
#define SSI_O_RIS               0x00000018  // Raw interrupt register
#define SSI_O_MIS               0x0000001C  // Masked interrupt register
#define SSI_O_ICR               0x00000020  // Interrupt clear register

//*****************************************************************************
//
// The following define the bit fields in the SSI Control register 0.
//
//*****************************************************************************
#define SSI_CR0_SCR             0x0000FF00  // Serial clock rate
#define SSI_CR0_SPH             0x00000080  // SSPCLKOUT phase
#define SSI_CR0_SPO             0x00000040  // SSPCLKOUT polarity
#define SSI_CR0_FRF_MASK        0x00000030  // Frame format mask
#define SSI_CR0_FRF_MOTO        0x00000000  // Motorola SPI frame format
#define SSI_CR0_FRF_TI          0x00000010  // TI sync serial frame format
#define SSI_CR0_FRF_NMW         0x00000020  // National Microwire frame format
#define SSI_CR0_DSS             0x0000000F  // Data size select
#define SSI_CR0_DSS_4           0x00000003  // 4 bit data
#define SSI_CR0_DSS_5           0x00000004  // 5 bit data
#define SSI_CR0_DSS_6           0x00000005  // 6 bit data
#define SSI_CR0_DSS_7           0x00000006  // 7 bit data
#define SSI_CR0_DSS_8           0x00000007  // 8 bit data
#define SSI_CR0_DSS_9           0x00000008  // 9 bit data
#define SSI_CR0_DSS_10          0x00000009  // 10 bit data
#define SSI_CR0_DSS_11          0x0000000A  // 11 bit data
#define SSI_CR0_DSS_12          0x0000000B  // 12 bit data
#define SSI_CR0_DSS_13          0x0000000C  // 13 bit data
#define SSI_CR0_DSS_14          0x0000000D  // 14 bit data
#define SSI_CR0_DSS_15          0x0000000E  // 15 bit data
#define SSI_CR0_DSS_16          0x0000000F  // 16 bit data

//*****************************************************************************
//
// The following define the bit fields in the SSI Control register 1.
//
//*****************************************************************************
#define SSI_CR1_SOD             0x00000008  // Slave mode output disable
#define SSI_CR1_MS              0x00000004  // Master or slave mode select
#define SSI_CR1_SSE             0x00000002  // Sync serial port enable
#define SSI_CR1_LBM             0x00000001  // Loopback mode

//*****************************************************************************
//
// The following define the bit fields in the SSI Status register.
//
//*****************************************************************************
#define SSI_SR_BSY              0x00000010  // SSI busy
#define SSI_SR_RFF              0x00000008  // RX FIFO full
#define SSI_SR_RNE              0x00000004  // RX FIFO not empty
#define SSI_SR_TNF              0x00000002  // TX FIFO not full
#define SSI_SR_TFE              0x00000001  // TX FIFO empty

//*****************************************************************************
//
// The following define the bit fields in the SSI clock prescale register.
//
//*****************************************************************************
#define SSI_CPSR_CPSDVSR_MASK   0x000000FF  // Clock prescale

//*****************************************************************************
//
// The following define information concerning the SSI Data register.
//
//*****************************************************************************
#define TX_FIFO_SIZE            (8)         // Number of entries in the TX FIFO
#define RX_FIFO_SIZE            (8)         // Number of entries in the RX FIFO

//*****************************************************************************
//
// The following define the bit fields in the interrupt mask set and clear,
// raw interrupt, masked interrupt, and interrupt clear registers.
//
//*****************************************************************************
#define SSI_INT_TXFF            0x00000008  // TX FIFO interrupt
#define SSI_INT_RXFF            0x00000004  // RX FIFO interrupt
#define SSI_INT_RXTO            0x00000002  // RX timeout interrupt
#define SSI_INT_RXOR            0x00000001  // RX overrun interrupt

#endif // __HW_SSI_H__
