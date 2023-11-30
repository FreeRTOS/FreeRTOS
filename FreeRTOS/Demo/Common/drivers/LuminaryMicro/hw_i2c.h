//*****************************************************************************
//
// hw_i2c.h - Macros used when accessing the I2C master and slave hardware.
//
// Copyright (c) 2005-2008 Luminary Micro, Inc.  All rights reserved.
// 
// Software License Agreement
// 
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
// 
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  You may not combine
// this software with "viral" open-source software in order to form a larger
// program.  Any use in violation of the foregoing restrictions may subject
// the user to criminal sanctions under applicable laws, as well as to civil
// liability for the breach of the terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
// 
// This is part of revision 2523 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __HW_I2C_H__
#define __HW_I2C_H__

//*****************************************************************************
//
// The following are defines for the offsets between the I2C master and slave
// registers.
//
//*****************************************************************************
#define I2C_O_MSA               0x00000000  // I2C Master Slave Address
#define I2C_O_SOAR              0x00000000  // I2C Slave Own Address
#define I2C_O_SCSR              0x00000004  // I2C Slave Control/Status
#define I2C_O_MCS               0x00000004  // I2C Master Control/Status
#define I2C_O_SDR               0x00000008  // I2C Slave Data
#define I2C_O_MDR               0x00000008  // I2C Master Data
#define I2C_O_MTPR              0x0000000C  // I2C Master Timer Period
#define I2C_O_SIMR              0x0000000C  // I2C Slave Interrupt Mask
#define I2C_O_SRIS              0x00000010  // I2C Slave Raw Interrupt Status
#define I2C_O_MIMR              0x00000010  // I2C Master Interrupt Mask
#define I2C_O_MRIS              0x00000014  // I2C Master Raw Interrupt Status
#define I2C_O_SMIS              0x00000014  // I2C Slave Masked Interrupt
                                            // Status
#define I2C_O_SICR              0x00000018  // I2C Slave Interrupt Clear
#define I2C_O_MMIS              0x00000018  // I2C Master Masked Interrupt
                                            // Status
#define I2C_O_MICR              0x0000001C  // I2C Master Interrupt Clear
#define I2C_O_MCR               0x00000020  // I2C Master Configuration

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_MSA register.
//
//*****************************************************************************
#define I2C_MSA_SA_M            0x000000FE  // I2C Slave Address.
#define I2C_MSA_RS              0x00000001  // Receive not Send
#define I2C_MSA_SA_S            1

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_SOAR register.
//
//*****************************************************************************
#define I2C_SOAR_OAR_M          0x0000007F  // I2C Slave Own Address.
#define I2C_SOAR_OAR_S          0

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_SCSR register.
//
//*****************************************************************************
#define I2C_SCSR_FBR            0x00000004  // First Byte Received.
#define I2C_SCSR_TREQ           0x00000002  // Transmit Request.
#define I2C_SCSR_DA             0x00000001  // Device Active.
#define I2C_SCSR_RREQ           0x00000001  // Receive Request.

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_MCS register.
//
//*****************************************************************************
#define I2C_MCS_BUSBSY          0x00000040  // Bus Busy.
#define I2C_MCS_IDLE            0x00000020  // I2C Idle.
#define I2C_MCS_ARBLST          0x00000010  // Arbitration Lost.
#define I2C_MCS_ACK             0x00000008  // Data Acknowledge Enable.
#define I2C_MCS_DATACK          0x00000008  // Acknowledge Data.
#define I2C_MCS_ADRACK          0x00000004  // Acknowledge Address.
#define I2C_MCS_STOP            0x00000004  // Generate STOP.
#define I2C_MCS_START           0x00000002  // Generate START.
#define I2C_MCS_ERROR           0x00000002  // Error.
#define I2C_MCS_RUN             0x00000001  // I2C Master Enable.
#define I2C_MCS_BUSY            0x00000001  // I2C Busy.

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_SDR register.
//
//*****************************************************************************
#define I2C_SDR_DATA_M          0x000000FF  // Data for Transfer.
#define I2C_SDR_DATA_S          0

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_MDR register.
//
//*****************************************************************************
#define I2C_MDR_DATA_M          0x000000FF  // Data Transferred.
#define I2C_MDR_DATA_S          0

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_MTPR register.
//
//*****************************************************************************
#define I2C_MTPR_TPR_M          0x000000FF  // SCL Clock Period.
#define I2C_MTPR_TPR_S          0

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_SIMR register.
//
//*****************************************************************************
#define I2C_SIMR_STOPIM         0x00000004  // Stop Condition Interrupt Mask.
#define I2C_SIMR_STARTIM        0x00000002  // Start Condition Interrupt Mask.
#define I2C_SIMR_DATAIM         0x00000001  // Data Interrupt Mask.

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_SRIS register.
//
//*****************************************************************************
#define I2C_SRIS_STOPRIS        0x00000004  // Stop Condition Raw Interrupt
                                            // Status.
#define I2C_SRIS_STARTRIS       0x00000002  // Start Condition Raw Interrupt
                                            // Status.
#define I2C_SRIS_DATARIS        0x00000001  // Data Raw Interrupt Status.

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_MIMR register.
//
//*****************************************************************************
#define I2C_MIMR_IM             0x00000001  // Interrupt Mask.

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_MRIS register.
//
//*****************************************************************************
#define I2C_MRIS_RIS            0x00000001  // Raw Interrupt Status.

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_SMIS register.
//
//*****************************************************************************
#define I2C_SMIS_STOPMIS        0x00000004  // Stop Condition Masked Interrupt
                                            // Status.
#define I2C_SMIS_STARTMIS       0x00000002  // Start Condition Masked Interrupt
                                            // Status.
#define I2C_SMIS_DATAMIS        0x00000001  // Data Masked Interrupt Status.

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_SICR register.
//
//*****************************************************************************
#define I2C_SICR_STOPIC         0x00000004  // Stop Condition Interrupt Clear.
#define I2C_SICR_STARTIC        0x00000002  // Start Condition Interrupt Clear.
#define I2C_SICR_DATAIC         0x00000001  // Data Clear Interrupt.

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_MMIS register.
//
//*****************************************************************************
#define I2C_MMIS_MIS            0x00000001  // Masked Interrupt Status.

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_MICR register.
//
//*****************************************************************************
#define I2C_MICR_IC             0x00000001  // Interrupt Clear.

//*****************************************************************************
//
// The following are defines for the bit fields in the I2C_O_MCR register.
//
//*****************************************************************************
#define I2C_MCR_SFE             0x00000020  // I2C Slave Function Enable.
#define I2C_MCR_MFE             0x00000010  // I2C Master Function Enable.
#define I2C_MCR_LPBK            0x00000001  // I2C Loopback.

//*****************************************************************************
//
// The following definitions are deprecated.
//
//*****************************************************************************
#ifndef DEPRECATED

//*****************************************************************************
//
// The following are deprecated defines for the offsets between the I2C master
// and slave registers.
//
//*****************************************************************************
#define I2C_O_SLAVE             0x00000800  // Offset from master to slave

//*****************************************************************************
//
// The following are deprecated defines for the I2C master register offsets.
//
//*****************************************************************************
#define I2C_MASTER_O_SA         0x00000000  // Slave address register
#define I2C_MASTER_O_CS         0x00000004  // Control and Status register
#define I2C_MASTER_O_DR         0x00000008  // Data register
#define I2C_MASTER_O_TPR        0x0000000C  // Timer period register
#define I2C_MASTER_O_IMR        0x00000010  // Interrupt mask register
#define I2C_MASTER_O_RIS        0x00000014  // Raw interrupt status register
#define I2C_MASTER_O_MIS        0x00000018  // Masked interrupt status reg
#define I2C_MASTER_O_MICR       0x0000001C  // Interrupt clear register
#define I2C_MASTER_O_CR         0x00000020  // Configuration register

//*****************************************************************************
//
// The following are deprecated defines for the I2C slave register offsets.
//
//*****************************************************************************
#define I2C_SLAVE_O_SICR        0x00000018  // Interrupt clear register
#define I2C_SLAVE_O_MIS         0x00000014  // Masked interrupt status reg
#define I2C_SLAVE_O_RIS         0x00000010  // Raw interrupt status register
#define I2C_SLAVE_O_IM          0x0000000C  // Interrupt mask register
#define I2C_SLAVE_O_DR          0x00000008  // Data register
#define I2C_SLAVE_O_CSR         0x00000004  // Control/Status register
#define I2C_SLAVE_O_OAR         0x00000000  // Own address register

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C master
// slave address register.
//
//*****************************************************************************
#define I2C_MASTER_SA_SA_MASK   0x000000FE  // Slave address
#define I2C_MASTER_SA_RS        0x00000001  // Receive/send
#define I2C_MASTER_SA_SA_SHIFT  1

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C Master
// Control and Status register.
//
//*****************************************************************************
#define I2C_MASTER_CS_BUS_BUSY  0x00000040  // Bus busy
#define I2C_MASTER_CS_IDLE      0x00000020  // Idle
#define I2C_MASTER_CS_ERR_MASK  0x0000001C
#define I2C_MASTER_CS_BUSY      0x00000001  // Controller is TX/RX data
#define I2C_MASTER_CS_ERROR     0x00000002  // Error occurred
#define I2C_MASTER_CS_ADDR_ACK  0x00000004  // Address byte not acknowledged
#define I2C_MASTER_CS_DATA_ACK  0x00000008  // Data byte not acknowledged
#define I2C_MASTER_CS_ARB_LOST  0x00000010  // Lost arbitration
#define I2C_MASTER_CS_ACK       0x00000008  // Acknowlegde
#define I2C_MASTER_CS_STOP      0x00000004  // Stop
#define I2C_MASTER_CS_START     0x00000002  // Start
#define I2C_MASTER_CS_RUN       0x00000001  // Run

//*****************************************************************************
//
// The following are deprecated defines for the values used in determining the
// contents of the I2C Master Timer Period register.
//
//*****************************************************************************
#define I2C_SCL_FAST            400000      // SCL fast frequency
#define I2C_SCL_STANDARD        100000      // SCL standard frequency
#define I2C_MASTER_TPR_SCL_LP   0x00000006  // SCL low period
#define I2C_MASTER_TPR_SCL_HP   0x00000004  // SCL high period
#define I2C_MASTER_TPR_SCL      (I2C_MASTER_TPR_SCL_HP + I2C_MASTER_TPR_SCL_LP)

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C Master
// Interrupt Mask register.
//
//*****************************************************************************
#define I2C_MASTER_IMR_IM       0x00000001  // Master interrupt mask

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C Master
// Raw Interrupt Status register.
//
//*****************************************************************************
#define I2C_MASTER_RIS_RIS      0x00000001  // Master raw interrupt status

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C Master
// Masked Interrupt Status register.
//
//*****************************************************************************
#define I2C_MASTER_MIS_MIS      0x00000001  // Master masked interrupt status

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C Master
// Interrupt Clear register.
//
//*****************************************************************************
#define I2C_MASTER_MICR_IC      0x00000001  // Master interrupt clear

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C Master
// Configuration register.
//
//*****************************************************************************
#define I2C_MASTER_CR_SFE       0x00000020  // Slave function enable
#define I2C_MASTER_CR_MFE       0x00000010  // Master function enable
#define I2C_MASTER_CR_LPBK      0x00000001  // Loopback enable

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C Slave Own
// Address register.
//
//*****************************************************************************
#define I2C_SLAVE_SOAR_OAR_MASK 0x0000007F  // Slave address

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C Slave
// Control/Status register.
//
//*****************************************************************************
#define I2C_SLAVE_CSR_FBR       0x00000004  // First byte received from master
#define I2C_SLAVE_CSR_TREQ      0x00000002  // Transmit request received
#define I2C_SLAVE_CSR_DA        0x00000001  // Enable the device
#define I2C_SLAVE_CSR_RREQ      0x00000001  // Receive data from I2C master

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C Slave
// Interrupt Mask register.
//
//*****************************************************************************
#define I2C_SLAVE_IMR_IM        0x00000001  // Slave interrupt mask

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C Slave Raw
// Interrupt Status register.
//
//*****************************************************************************
#define I2C_SLAVE_RIS_RIS       0x00000001  // Slave raw interrupt status

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C Slave
// Masked Interrupt Status register.
//
//*****************************************************************************
#define I2C_SLAVE_MIS_MIS       0x00000001  // Slave masked interrupt status

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C Slave
// Interrupt Clear register.
//
//*****************************************************************************
#define I2C_SLAVE_SICR_IC       0x00000001  // Slave interrupt clear

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C_O_SIMR
// register.
//
//*****************************************************************************
#define I2C_SIMR_IM             0x00000001  // Interrupt Mask.

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C_O_SRIS
// register.
//
//*****************************************************************************
#define I2C_SRIS_RIS            0x00000001  // Raw Interrupt Status.

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C_O_SMIS
// register.
//
//*****************************************************************************
#define I2C_SMIS_MIS            0x00000001  // Masked Interrupt Status.

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the I2C_O_SICR
// register.
//
//*****************************************************************************
#define I2C_SICR_IC             0x00000001  // Clear Interrupt.

#endif

#endif // __HW_I2C_H__
