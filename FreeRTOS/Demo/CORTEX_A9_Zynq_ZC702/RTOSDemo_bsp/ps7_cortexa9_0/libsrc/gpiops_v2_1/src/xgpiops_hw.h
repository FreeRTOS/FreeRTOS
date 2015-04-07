/******************************************************************************
*
* (c) Copyright 2010-14 Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
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
