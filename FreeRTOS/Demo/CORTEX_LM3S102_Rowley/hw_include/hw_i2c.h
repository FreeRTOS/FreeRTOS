//*****************************************************************************
//
// hw_i2c.h - Macros used when accessing the I2C master and slave hardware.
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

#ifndef __HW_I2C_H__
#define __HW_I2C_H__

//*****************************************************************************
//
// The following define the offsets of the I2C master registers.
//
//*****************************************************************************
#define I2C_MASTER_O_SA         0x00000000  // Slave address register
#define I2C_MASTER_O_CS         0x00000004  // Control and Status register
#define I2C_MASTER_O_DR         0x00000008  // Data register
#define I2C_MASTER_O_TPR        0x0000000C  // Timer period register
#define I2C_MASTER_O_IMR        0x00000010  // Interrupt mask register
#define I2C_MASTER_O_RIS        0x00000014  // Raw interrupt status register
#define I2C_MASTER_O_MIS        0x00000018  // Masked interrupt status reg
#define I2C_MASTER_O_ICR        0x0000001c  // Interrupt clear register
#define I2C_MASTER_O_CR         0x00000020  // Configuration register

//*****************************************************************************
//
// The following define the offsets of the I2C slave registers.
//
//*****************************************************************************
#define I2C_SLAVE_O_OAR         0x00000000  // Own address register
#define I2C_SLAVE_O_CSR         0x00000004  // Control/Status register
#define I2C_SLAVE_O_DR          0x00000008  // Data register
#define I2C_SLAVE_O_IM          0x0000000C  // Interrupt mask register
#define I2C_SLAVE_O_RIS         0x00000010  // Raw interrupt status register
#define I2C_SLAVE_O_MIS         0x00000014  // Masked interrupt status reg
#define I2C_SLAVE_O_ICR         0x00000018  // Interrupt clear register

//*****************************************************************************
//
// The following define the bit fields in the I2C Master Control and Status
// register.
//
//*****************************************************************************
#define I2C_MASTER_CS_ACK       0x00000008  // Acknowlegde
#define I2C_MASTER_CS_STOP      0x00000004  // Stop
#define I2C_MASTER_CS_START     0x00000002  // Start
#define I2C_MASTER_CS_RUN       0x00000001  // Run
#define I2C_MASTER_CS_BUS_BUSY  0x00000040  // Bus busy
#define I2C_MASTER_CS_IDLE      0x00000020  // Idle
#define I2C_MASTER_CS_ARB_LOST  0x00000010  // Lost arbitration
#define I2C_MASTER_CS_DATA_ACK  0x00000008  // Data byte not acknowledged
#define I2C_MASTER_CS_ADDR_ACK  0x00000004  // Address byte not acknowledged
#define I2C_MASTER_CS_ERROR     0x00000002  // Error occurred
#define I2C_MASTER_CS_BUSY      0x00000001  // Controller is TX/RX data
#define I2C_MASTER_CS_ERR_MASK  0x0000001C

//*****************************************************************************
//
// The following define values used in determining the contents of the I2C
// Master Timer Period register.
//
//*****************************************************************************
#define I2C_MASTER_TPR_SCL_HP   0x00000004  // SCL high period
#define I2C_MASTER_TPR_SCL_LP   0x00000006  // SCL low period
#define I2C_SCL_STANDARD        100000      // SCL standard frequency
#define I2C_SCL_FAST            400000      // SCL fast frequency

//*****************************************************************************
//
// The following define the bit fields in the I2C Master Interrupt Mask
// register.
//
//*****************************************************************************
#define I2C_MASTER_IMR_IM       0x00000001  // Master interrupt mask

//*****************************************************************************
//
// The following define the bit fields in the I2C Master Raw Interrupt Status
// register.
//
//*****************************************************************************
#define I2C_MASTER_RIS_RIS      0x00000001  // Master raw interrupt status

//*****************************************************************************
//
// The following define the bit fields in the I2C Master Masked Interrupt
// Status register.
//
//*****************************************************************************
#define I2C_MASTER_MIS_MIS      0x00000001  // Master masked interrupt status

//*****************************************************************************
//
// The following define the bit fields in the I2C Master Configuration
// register.
//
//*****************************************************************************
#define I2C_MASTER_CR_SFE       0x00000020  // Slave function enable
#define I2C_MASTER_CR_MFE       0x00000010  // Master function enable
#define I2C_MASTER_CR_LPBK      0x00000001  // Loopback enable

//*****************************************************************************
//
// The following define the bit fields in the I2C Slave Control/Status
// register.
//
//*****************************************************************************
#define I2C_SLAVE_CSR_DA        0x00000001  // Enable the device
#define I2C_SLAVE_CSR_TREQ      0x00000002  // Transmit request received
#define I2C_SLAVE_CSR_RREQ      0x00000001  // Receive data from I2C master

//*****************************************************************************
//
// The following define the bit fields in the I2C Slave Interrupt Mask
// register.
//
//*****************************************************************************
#define I2C_SLAVE_IMR_IM       0x00000001  // Slave interrupt mask

//*****************************************************************************
//
// The following define the bit fields in the I2C Slave Raw Interrupt Status
// register.
//
//*****************************************************************************
#define I2C_SLAVE_RIS_RIS      0x00000001  // Slave raw interrupt status

//*****************************************************************************
//
// The following define the bit fields in the I2C Slave Masked Interrupt
// Status register.
//
//*****************************************************************************
#define I2C_SLAVE_MIS_MIS      0x00000001  // Master masked interrupt status

#endif // __HW_I2C_H__
