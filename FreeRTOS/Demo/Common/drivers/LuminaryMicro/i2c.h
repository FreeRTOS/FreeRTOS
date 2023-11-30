//*****************************************************************************
//
// i2c.h - Prototypes for the I2C Driver.
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

#ifndef __I2C_H__
#define __I2C_H__

//*****************************************************************************
//
// If building with a C++ compiler, make all of the definitions in this header
// have a C binding.
//
//*****************************************************************************
#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// Defines for the API.
//
//*****************************************************************************

//*****************************************************************************
//
// Interrupt defines.
//
//*****************************************************************************
#define I2C_INT_MASTER          0x00000001
#define I2C_INT_SLAVE           0x00000002

//*****************************************************************************
//
// I2C Master commands.
//
//*****************************************************************************
#define I2C_MASTER_CMD_SINGLE_SEND              0x00000007
#define I2C_MASTER_CMD_SINGLE_RECEIVE           0x00000007
#define I2C_MASTER_CMD_BURST_SEND_START         0x00000003
#define I2C_MASTER_CMD_BURST_SEND_CONT          0x00000001
#define I2C_MASTER_CMD_BURST_SEND_FINISH        0x00000005
#define I2C_MASTER_CMD_BURST_SEND_ERROR_STOP    0x00000004
#define I2C_MASTER_CMD_BURST_RECEIVE_START      0x0000000b
#define I2C_MASTER_CMD_BURST_RECEIVE_CONT       0x00000009
#define I2C_MASTER_CMD_BURST_RECEIVE_FINISH     0x00000005
#define I2C_MASTER_CMD_BURST_RECEIVE_ERROR_STOP 0x00000005

//*****************************************************************************
//
// I2C Master error status.
//
//*****************************************************************************
#define I2C_MASTER_ERR_NONE     0
#define I2C_MASTER_ERR_ADDR_ACK 0x00000004
#define I2C_MASTER_ERR_DATA_ACK 0x00000008
#define I2C_MASTER_ERR_ARB_LOST 0x00000010

//*****************************************************************************
//
// I2C Slave action requests
//
//*****************************************************************************
#define I2C_SLAVE_ACT_NONE      0
#define I2C_SLAVE_ACT_RREQ      0x00000001  // Master has sent data
#define I2C_SLAVE_ACT_TREQ      0x00000002  // Master has requested data
#define I2C_SLAVE_ACT_RREQ_FBR  0x00000005  // Master has sent first byte

//*****************************************************************************
//
// Miscellaneous I2C driver definitions.
//
//*****************************************************************************
#define I2C_MASTER_MAX_RETRIES  1000        // Number of retries

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************
extern void I2CIntRegister(unsigned long ulBase, void(fnHandler)(void));
extern void I2CIntUnregister(unsigned long ulBase);
extern tBoolean I2CMasterBusBusy(unsigned long ulBase);
extern tBoolean I2CMasterBusy(unsigned long ulBase);
extern void I2CMasterControl(unsigned long ulBase, unsigned long ulCmd);
extern unsigned long I2CMasterDataGet(unsigned long ulBase);
extern void I2CMasterDataPut(unsigned long ulBase, unsigned char ucData);
extern void I2CMasterDisable(unsigned long ulBase);
extern void I2CMasterEnable(unsigned long ulBase);
extern unsigned long I2CMasterErr(unsigned long ulBase);
extern void I2CMasterInitExpClk(unsigned long ulBase, unsigned long ulI2CClk,
                                tBoolean bFast);
extern void I2CMasterIntClear(unsigned long ulBase);
extern void I2CMasterIntDisable(unsigned long ulBase);
extern void I2CMasterIntEnable(unsigned long ulBase);
extern tBoolean I2CMasterIntStatus(unsigned long ulBase, tBoolean bMasked);
extern void I2CMasterSlaveAddrSet(unsigned long ulBase,
                                  unsigned char ucSlaveAddr,
                                  tBoolean bReceive);
extern unsigned long I2CSlaveDataGet(unsigned long ulBase);
extern void I2CSlaveDataPut(unsigned long ulBase, unsigned char ucData);
extern void I2CSlaveDisable(unsigned long ulBase);
extern void I2CSlaveEnable(unsigned long ulBase);
extern void I2CSlaveInit(unsigned long ulBase, unsigned char ucSlaveAddr);
extern void I2CSlaveIntClear(unsigned long ulBase);
extern void I2CSlaveIntDisable(unsigned long ulBase);
extern void I2CSlaveIntEnable(unsigned long ulBase);
extern tBoolean I2CSlaveIntStatus(unsigned long ulBase, tBoolean bMasked);
extern unsigned long I2CSlaveStatus(unsigned long ulBase);

//*****************************************************************************
//
// Several I2C APIs have been renamed, with the original function name being
// deprecated.  These defines provide backward compatibility.
//
//*****************************************************************************
#ifndef DEPRECATED
#include "sysctl.h"
#define I2CMasterInit(a, b)                         \
        I2CMasterInitExpClk(a, SysCtlClockGet(), b)
#endif

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif // __I2C_H__
