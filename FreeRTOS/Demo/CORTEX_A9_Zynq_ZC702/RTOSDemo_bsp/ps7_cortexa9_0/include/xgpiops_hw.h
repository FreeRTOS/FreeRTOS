/******************************************************************************
*
* Copyright (C) 2010 - 2014 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xgpiops_hw.h
*
* This header file contains the identifiers and basic driver functions (or
* macros) that can be used to access the device. Other driver functions
* are defined in xgpiops.h.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------
* 1.00a sv   01/15/10 First Release
* 1.02a hk   08/22/13 Added low level reset API function prototype and
*                     related constant definitions
* </pre>
*
******************************************************************************/
#ifndef XGPIOPS_HW_H		/* prevent circular inclusions */
#define XGPIOPS_HW_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/

/** @name Register offsets for the GPIO. Each register is 32 bits.
 *  @{
 */
#define XGPIOPS_DATA_LSW_OFFSET  0x000  /* Mask and Data Register LSW, WO */
#define XGPIOPS_DATA_MSW_OFFSET  0x004  /* Mask and Data Register MSW, WO */
#define XGPIOPS_DATA_OFFSET	 0x040  /* Data Register, RW */
#define XGPIOPS_DATA_RO_OFFSET	 0x060  /* Data Register - Input, RO */
#define XGPIOPS_DIRM_OFFSET	 0x204  /* Direction Mode Register, RW */
#define XGPIOPS_OUTEN_OFFSET	 0x208  /* Output Enable Register, RW */
#define XGPIOPS_INTMASK_OFFSET	 0x20C  /* Interrupt Mask Register, RO */
#define XGPIOPS_INTEN_OFFSET	 0x210  /* Interrupt Enable Register, WO */
#define XGPIOPS_INTDIS_OFFSET	 0x214  /* Interrupt Disable Register, WO*/
#define XGPIOPS_INTSTS_OFFSET	 0x218  /* Interrupt Status Register, RO */
#define XGPIOPS_INTTYPE_OFFSET	 0x21C  /* Interrupt Type Register, RW */
#define XGPIOPS_INTPOL_OFFSET	 0x220  /* Interrupt Polarity Register, RW */
#define XGPIOPS_INTANY_OFFSET	 0x224  /* Interrupt On Any Register, RW */
/* @} */

/** @name Register offsets for each Bank.
 *  @{
 */
#define XGPIOPS_DATA_MASK_OFFSET 0x8  /* Data/Mask Registers offset */
#define XGPIOPS_DATA_BANK_OFFSET 0x4  /* Data Registers offset */
#define XGPIOPS_REG_MASK_OFFSET 0x40  /* Registers offset */
/* @} */

/* For backwards compatibility */
#define XGPIOPS_BYPM_MASK_OFFSET	XGPIOPS_REG_MASK_OFFSET

/** @name Interrupt type reset values for each bank
 *  @{
 */
#define XGPIOPS_INTTYPE_BANK0_RESET  0xFFFFFFFF
#define XGPIOPS_INTTYPE_BANK1_RESET  0x3FFFFFFF
#define XGPIOPS_INTTYPE_BANK2_RESET  0xFFFFFFFF
#define XGPIOPS_INTTYPE_BANK3_RESET  0xFFFFFFFF
/* @} */

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* This macro reads the given register.
*
* @param	BaseAddr is the base address of the device.
* @param	RegOffset is the register offset to be read.
*
* @return	The 32-bit value of the register
*
* @note		None.
*
*****************************************************************************/
#define XGpioPs_ReadReg(BaseAddr, RegOffset)		\
		Xil_In32((BaseAddr) + (RegOffset))

/****************************************************************************/
/**
*
* This macro writes to the given register.
*
* @param	BaseAddr is the base address of the device.
* @param	RegOffset is the offset of the register to be written.
* @param	Data is the 32-bit value to write to the register.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
#define XGpioPs_WriteReg(BaseAddr, RegOffset, Data)	\
		Xil_Out32((BaseAddr) + (RegOffset), (Data))

/************************** Function Prototypes ******************************/

void XGpioPs_ResetHw(u32 BaseAddress);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* XGPIOPS_HW_H */
