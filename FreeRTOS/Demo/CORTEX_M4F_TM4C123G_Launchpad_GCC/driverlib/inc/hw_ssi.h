//*****************************************************************************
//
// hw_ssi.h - Macros used when accessing the SSI hardware.
//
// Copyright (c) 2005-2020 Texas Instruments Incorporated.  All rights reserved.
// Software License Agreement
// 
//   Redistribution and use in source and binary forms, with or without
//   modification, are permitted provided that the following conditions
//   are met:
// 
//   Redistributions of source code must retain the above copyright
//   notice, this list of conditions and the following disclaimer.
// 
//   Redistributions in binary form must reproduce the above copyright
//   notice, this list of conditions and the following disclaimer in the
//   documentation and/or other materials provided with the  
//   distribution.
// 
//   Neither the name of Texas Instruments Incorporated nor the names of
//   its contributors may be used to endorse or promote products derived
//   from this software without specific prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// 
// This is part of revision 2.2.0.295 of the Tiva Firmware Development Package.
//
//*****************************************************************************

#ifndef __HW_SSI_H__
#define __HW_SSI_H__

//*****************************************************************************
//
// The following are defines for the SSI register offsets.
//
//*****************************************************************************
#define SSI_O_CR0               0x00000000  // SSI Control 0
#define SSI_O_CR1               0x00000004  // SSI Control 1
#define SSI_O_DR                0x00000008  // SSI Data
#define SSI_O_SR                0x0000000C  // SSI Status
#define SSI_O_CPSR              0x00000010  // SSI Clock Prescale
#define SSI_O_IM                0x00000014  // SSI Interrupt Mask
#define SSI_O_RIS               0x00000018  // SSI Raw Interrupt Status
#define SSI_O_MIS               0x0000001C  // SSI Masked Interrupt Status
#define SSI_O_ICR               0x00000020  // SSI Interrupt Clear
#define SSI_O_DMACTL            0x00000024  // SSI DMA Control
#define SSI_O_PP                0x00000FC0  // SSI Peripheral Properties
#define SSI_O_CC                0x00000FC8  // SSI Clock Configuration

//*****************************************************************************
//
// The following are defines for the bit fields in the SSI_O_CR0 register.
//
//*****************************************************************************
#define SSI_CR0_SCR_M           0x0000FF00  // SSI Serial Clock Rate
#define SSI_CR0_SPH             0x00000080  // SSI Serial Clock Phase
#define SSI_CR0_SPO             0x00000040  // SSI Serial Clock Polarity
#define SSI_CR0_FRF_M           0x00000030  // SSI Frame Format Select
#define SSI_CR0_FRF_MOTO        0x00000000  // Freescale SPI Frame Format
#define SSI_CR0_FRF_TI          0x00000010  // Synchronous Serial Frame Format
#define SSI_CR0_FRF_NMW         0x00000020  // MICROWIRE Frame Format
#define SSI_CR0_DSS_M           0x0000000F  // SSI Data Size Select
#define SSI_CR0_DSS_4           0x00000003  // 4-bit data
#define SSI_CR0_DSS_5           0x00000004  // 5-bit data
#define SSI_CR0_DSS_6           0x00000005  // 6-bit data
#define SSI_CR0_DSS_7           0x00000006  // 7-bit data
#define SSI_CR0_DSS_8           0x00000007  // 8-bit data
#define SSI_CR0_DSS_9           0x00000008  // 9-bit data
#define SSI_CR0_DSS_10          0x00000009  // 10-bit data
#define SSI_CR0_DSS_11          0x0000000A  // 11-bit data
#define SSI_CR0_DSS_12          0x0000000B  // 12-bit data
#define SSI_CR0_DSS_13          0x0000000C  // 13-bit data
#define SSI_CR0_DSS_14          0x0000000D  // 14-bit data
#define SSI_CR0_DSS_15          0x0000000E  // 15-bit data
#define SSI_CR0_DSS_16          0x0000000F  // 16-bit data
#define SSI_CR0_SCR_S           8

//*****************************************************************************
//
// The following are defines for the bit fields in the SSI_O_CR1 register.
//
//*****************************************************************************
#define SSI_CR1_EOM             0x00000800  // Stop Frame (End of Message)
#define SSI_CR1_FSSHLDFRM       0x00000400  // FSS Hold Frame
#define SSI_CR1_HSCLKEN         0x00000200  // High Speed Clock Enable
#define SSI_CR1_DIR             0x00000100  // SSI Direction of Operation
#define SSI_CR1_MODE_M          0x000000C0  // SSI Mode
#define SSI_CR1_MODE_LEGACY     0x00000000  // Legacy SSI mode
#define SSI_CR1_MODE_BI         0x00000040  // Bi-SSI mode
#define SSI_CR1_MODE_QUAD       0x00000080  // Quad-SSI Mode
#define SSI_CR1_MODE_ADVANCED   0x000000C0  // Advanced SSI Mode with 8-bit
                                            // packet size
#define SSI_CR1_EOT             0x00000010  // End of Transmission
#define SSI_CR1_MS              0x00000004  // SSI Master/Slave Select
#define SSI_CR1_SSE             0x00000002  // SSI Synchronous Serial Port
                                            // Enable
#define SSI_CR1_LBM             0x00000001  // SSI Loopback Mode

//*****************************************************************************
//
// The following are defines for the bit fields in the SSI_O_DR register.
//
//*****************************************************************************
#define SSI_DR_DATA_M           0x0000FFFF  // SSI Receive/Transmit Data
#define SSI_DR_DATA_S           0

//*****************************************************************************
//
// The following are defines for the bit fields in the SSI_O_SR register.
//
//*****************************************************************************
#define SSI_SR_BSY              0x00000010  // SSI Busy Bit
#define SSI_SR_RFF              0x00000008  // SSI Receive FIFO Full
#define SSI_SR_RNE              0x00000004  // SSI Receive FIFO Not Empty
#define SSI_SR_TNF              0x00000002  // SSI Transmit FIFO Not Full
#define SSI_SR_TFE              0x00000001  // SSI Transmit FIFO Empty

//*****************************************************************************
//
// The following are defines for the bit fields in the SSI_O_CPSR register.
//
//*****************************************************************************
#define SSI_CPSR_CPSDVSR_M      0x000000FF  // SSI Clock Prescale Divisor
#define SSI_CPSR_CPSDVSR_S      0

//*****************************************************************************
//
// The following are defines for the bit fields in the SSI_O_IM register.
//
//*****************************************************************************
#define SSI_IM_EOTIM            0x00000040  // End of Transmit Interrupt Mask
#define SSI_IM_DMATXIM          0x00000020  // SSI Transmit DMA Interrupt Mask
#define SSI_IM_DMARXIM          0x00000010  // SSI Receive DMA Interrupt Mask
#define SSI_IM_TXIM             0x00000008  // SSI Transmit FIFO Interrupt Mask
#define SSI_IM_RXIM             0x00000004  // SSI Receive FIFO Interrupt Mask
#define SSI_IM_RTIM             0x00000002  // SSI Receive Time-Out Interrupt
                                            // Mask
#define SSI_IM_RORIM            0x00000001  // SSI Receive Overrun Interrupt
                                            // Mask

//*****************************************************************************
//
// The following are defines for the bit fields in the SSI_O_RIS register.
//
//*****************************************************************************
#define SSI_RIS_EOTRIS          0x00000040  // End of Transmit Raw Interrupt
                                            // Status
#define SSI_RIS_DMATXRIS        0x00000020  // SSI Transmit DMA Raw Interrupt
                                            // Status
#define SSI_RIS_DMARXRIS        0x00000010  // SSI Receive DMA Raw Interrupt
                                            // Status
#define SSI_RIS_TXRIS           0x00000008  // SSI Transmit FIFO Raw Interrupt
                                            // Status
#define SSI_RIS_RXRIS           0x00000004  // SSI Receive FIFO Raw Interrupt
                                            // Status
#define SSI_RIS_RTRIS           0x00000002  // SSI Receive Time-Out Raw
                                            // Interrupt Status
#define SSI_RIS_RORRIS          0x00000001  // SSI Receive Overrun Raw
                                            // Interrupt Status

//*****************************************************************************
//
// The following are defines for the bit fields in the SSI_O_MIS register.
//
//*****************************************************************************
#define SSI_MIS_EOTMIS          0x00000040  // End of Transmit Masked Interrupt
                                            // Status
#define SSI_MIS_DMATXMIS        0x00000020  // SSI Transmit DMA Masked
                                            // Interrupt Status
#define SSI_MIS_DMARXMIS        0x00000010  // SSI Receive DMA Masked Interrupt
                                            // Status
#define SSI_MIS_TXMIS           0x00000008  // SSI Transmit FIFO Masked
                                            // Interrupt Status
#define SSI_MIS_RXMIS           0x00000004  // SSI Receive FIFO Masked
                                            // Interrupt Status
#define SSI_MIS_RTMIS           0x00000002  // SSI Receive Time-Out Masked
                                            // Interrupt Status
#define SSI_MIS_RORMIS          0x00000001  // SSI Receive Overrun Masked
                                            // Interrupt Status

//*****************************************************************************
//
// The following are defines for the bit fields in the SSI_O_ICR register.
//
//*****************************************************************************
#define SSI_ICR_EOTIC           0x00000040  // End of Transmit Interrupt Clear
#define SSI_ICR_DMATXIC         0x00000020  // SSI Transmit DMA Interrupt Clear
#define SSI_ICR_DMARXIC         0x00000010  // SSI Receive DMA Interrupt Clear
#define SSI_ICR_RTIC            0x00000002  // SSI Receive Time-Out Interrupt
                                            // Clear
#define SSI_ICR_RORIC           0x00000001  // SSI Receive Overrun Interrupt
                                            // Clear

//*****************************************************************************
//
// The following are defines for the bit fields in the SSI_O_DMACTL register.
//
//*****************************************************************************
#define SSI_DMACTL_TXDMAE       0x00000002  // Transmit DMA Enable
#define SSI_DMACTL_RXDMAE       0x00000001  // Receive DMA Enable

//*****************************************************************************
//
// The following are defines for the bit fields in the SSI_O_PP register.
//
//*****************************************************************************
#define SSI_PP_FSSHLDFRM        0x00000008  // FSS Hold Frame Capability
#define SSI_PP_MODE_M           0x00000006  // Mode of Operation
#define SSI_PP_MODE_LEGACY      0x00000000  // Legacy SSI mode
#define SSI_PP_MODE_ADVBI       0x00000002  // Legacy mode, Advanced SSI mode
                                            // and Bi-SSI mode enabled
#define SSI_PP_MODE_ADVBIQUAD   0x00000004  // Legacy mode, Advanced mode,
                                            // Bi-SSI and Quad-SSI mode enabled
#define SSI_PP_HSCLK            0x00000001  // High Speed Capability

//*****************************************************************************
//
// The following are defines for the bit fields in the SSI_O_CC register.
//
//*****************************************************************************
#define SSI_CC_CS_M             0x0000000F  // SSI Baud Clock Source
#define SSI_CC_CS_SYSPLL        0x00000000  // System clock (based on clock
                                            // source and divisor factor)
#define SSI_CC_CS_PIOSC         0x00000005  // PIOSC

#endif // __HW_SSI_H__
