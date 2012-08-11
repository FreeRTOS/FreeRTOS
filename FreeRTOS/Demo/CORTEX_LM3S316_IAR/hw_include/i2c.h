//*****************************************************************************
//
// i2c.h - Prototypes for the I2C Driver.
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
// This is part of revision 635 of the Stellaris Driver Library.
//
//*****************************************************************************

#ifndef __I2C_H__
#define __I2C_H__

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
#define I2C_MASTER_CMD_SINGLE_SEND                                            \
            (I2C_MASTER_CS_STOP | I2C_MASTER_CS_START | I2C_MASTER_CS_RUN)
#define I2C_MASTER_CMD_SINGLE_RECEIVE                                         \
            (I2C_MASTER_CS_STOP | I2C_MASTER_CS_START | I2C_MASTER_CS_RUN)
#define I2C_MASTER_CMD_BURST_SEND_START                                       \
            (I2C_MASTER_CS_START | I2C_MASTER_CS_RUN)
#define I2C_MASTER_CMD_BURST_SEND_CONT                                        \
            (I2C_MASTER_CS_RUN)
#define I2C_MASTER_CMD_BURST_SEND_FINISH                                      \
            (I2C_MASTER_CS_STOP | I2C_MASTER_CS_RUN)
#define I2C_MASTER_CMD_BURST_SEND_ERROR_STOP                                  \
            (I2C_MASTER_CS_STOP)
#define I2C_MASTER_CMD_BURST_RECEIVE_START                                    \
            (I2C_MASTER_CS_ACK | I2C_MASTER_CS_START | I2C_MASTER_CS_RUN)
#define I2C_MASTER_CMD_BURST_RECEIVE_CONT                                     \
            (I2C_MASTER_CS_ACK | I2C_MASTER_CS_RUN)
#define I2C_MASTER_CMD_BURST_RECEIVE_FINISH                                   \
            (I2C_MASTER_CS_STOP | I2C_MASTER_CS_RUN)
#define I2C_MASTER_CMD_BURST_RECEIVE_ERROR_STOP                               \
            (I2C_MASTER_CS_STOP | I2C_MASTER_CS_RUN)

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

//*****************************************************************************
// Miscellaneous I2C driver definitions.
//*****************************************************************************
#define I2C_MASTER_MAX_RETRIES 1000        // Number of retries

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
extern void I2CMasterInit(unsigned long ulBase, tBoolean bFast);
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

#ifdef __cplusplus
}
#endif

#endif // __I2C_H__
