/******************************************************************************
*
* Copyright (C) 2011 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xbram_hw.h
*
* This header file contains identifiers and driver functions (or
* macros) that can be used to access the device.  The user should refer to the
* hardware device specification for more details of the device operation.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a sa   24/11/10 First release
* </pre>
*
******************************************************************************/
#ifndef XBRAM_HW_H		/* prevent circular inclusions */
#define XBRAM_HW_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/

/** @name Registers
 *
 * Register offsets for this device.
 * @{
 */

#define XBRAM_ECC_STATUS_OFFSET	0x0  /**< ECC status Register */
#define XBRAM_ECC_EN_IRQ_OFFSET	0x4  /**< ECC interrupt enable Register */
#define XBRAM_ECC_ON_OFF_OFFSET	0x8  /**< ECC on/off register */
#define XBRAM_CE_CNT_OFFSET	0xC  /**< Correctable error counter Register */

#define XBRAM_CE_FFD_0_OFFSET	0x100 /**< Correctable error first failing
				        *  data Register, 31-0 */
#define XBRAM_CE_FFD_1_OFFSET	0x104 /**< Correctable error first failing
				        *  data Register, 63-32 */
#define XBRAM_CE_FFD_2_OFFSET	0x108 /**< Correctable error first failing
				        *  data Register, 95-64 */
#define XBRAM_CE_FFD_3_OFFSET	0x10C /**< Correctable error first failing
				        *  data Register, 127-96 */
#define XBRAM_CE_FFD_4_OFFSET	0x110 /**< Correctable error first failing
				        *  data Register, 159-128 */
#define XBRAM_CE_FFD_5_OFFSET	0x114 /**< Correctable error first failing
				        *  data Register, 191-160 */
#define XBRAM_CE_FFD_6_OFFSET	0x118 /**< Correctable error first failing
				        *  data Register, 223-192 */
#define XBRAM_CE_FFD_7_OFFSET	0x11C /**< Correctable error first failing
				        *  data Register, 255-224 */
#define XBRAM_CE_FFD_8_OFFSET	0x120 /**< Correctable error first failing
				        *  data Register, 287-256 */
#define XBRAM_CE_FFD_9_OFFSET	0x124 /**< Correctable error first failing
				        *  data Register, 319-288 */
#define XBRAM_CE_FFD_10_OFFSET	0x128 /**< Correctable error first failing
				        *  data Register, 351-320 */
#define XBRAM_CE_FFD_11_OFFSET	0x12C /**< Correctable error first failing
				        *  data Register, 383-352 */
#define XBRAM_CE_FFD_12_OFFSET	0x130 /**< Correctable error first failing
				        *  data Register, 415-384 */
#define XBRAM_CE_FFD_13_OFFSET	0x134 /**< Correctable error first failing
				        *  data Register, 447-416 */
#define XBRAM_CE_FFD_14_OFFSET	0x138 /**< Correctable error first failing
				        *  data Register, 479-448 */
#define XBRAM_CE_FFD_15_OFFSET	0x13C /**< Correctable error first failing
				        *  data Register, 511-480 */
#define XBRAM_CE_FFD_16_OFFSET	0x140 /**< Correctable error first failing
				        *  data Register, 543-512 */
#define XBRAM_CE_FFD_17_OFFSET	0x144 /**< Correctable error first failing
				        *  data Register, 575-544 */
#define XBRAM_CE_FFD_18_OFFSET	0x148 /**< Correctable error first failing
				        *  data Register, 607-576 */
#define XBRAM_CE_FFD_19_OFFSET	0x14C /**< Correctable error first failing
				        *  data Register, 639-608 */
#define XBRAM_CE_FFD_20_OFFSET	0x150 /**< Correctable error first failing
				        *  data Register, 671-640 */
#define XBRAM_CE_FFD_21_OFFSET	0x154 /**< Correctable error first failing
				        *  data Register, 703-672 */
#define XBRAM_CE_FFD_22_OFFSET	0x158 /**< Correctable error first failing
				        *  data Register, 735-704 */
#define XBRAM_CE_FFD_23_OFFSET	0x15C /**< Correctable error first failing
				        *  data Register, 767-736 */
#define XBRAM_CE_FFD_24_OFFSET	0x160 /**< Correctable error first failing
				        *  data Register, 799-768 */
#define XBRAM_CE_FFD_25_OFFSET	0x164 /**< Correctable error first failing
				        *  data Register, 831-800 */
#define XBRAM_CE_FFD_26_OFFSET	0x168 /**< Correctable error first failing
				        *  data Register, 863-832 */
#define XBRAM_CE_FFD_27_OFFSET	0x16C /**< Correctable error first failing
				        *  data Register, 895-864 */
#define XBRAM_CE_FFD_28_OFFSET	0x170 /**< Correctable error first failing
				        *  data Register, 927-896 */
#define XBRAM_CE_FFD_29_OFFSET	0x174 /**< Correctable error first failing
				        *  data Register, 959-928 */
#define XBRAM_CE_FFD_30_OFFSET	0x178 /**< Correctable error first failing
				        *  data Register, 991-960 */
#define XBRAM_CE_FFD_31_OFFSET	0x17C /**< Correctable error first failing
				        *  data Register, 1023-992 */

#define XBRAM_CE_FFE_0_OFFSET	0x180 /**< Correctable error first failing
				        *  ECC Register, 31-0 */
#define XBRAM_CE_FFE_1_OFFSET	0x184 /**< Correctable error first failing
				        *  ECC Register, 63-32 */
#define XBRAM_CE_FFE_2_OFFSET	0x188 /**< Correctable error first failing
				        *  ECC Register, 95-64 */
#define XBRAM_CE_FFE_3_OFFSET	0x18C /**< Correctable error first failing
				        *  ECC Register, 127-96 */
#define XBRAM_CE_FFE_4_OFFSET	0x190 /**< Correctable error first failing
				        *  ECC Register, 159-128 */
#define XBRAM_CE_FFE_5_OFFSET	0x194 /**< Correctable error first failing
				        *  ECC Register, 191-160 */
#define XBRAM_CE_FFE_6_OFFSET	0x198 /**< Correctable error first failing
				        *  ECC Register, 223-192 */
#define XBRAM_CE_FFE_7_OFFSET	0x19C /**< Correctable error first failing
				        *  ECC Register, 255-224 */

#define XBRAM_CE_FFA_0_OFFSET	0x1C0 /**< Correctable error first failing
				        *  address Register 31-0 */
#define XBRAM_CE_FFA_1_OFFSET	0x1C4 /**< Correctable error first failing
				        *  address Register 63-32 */

#define XBRAM_UE_FFD_0_OFFSET	0x200 /**< Uncorrectable error first failing
				        *  data Register, 31-0 */
#define XBRAM_UE_FFD_1_OFFSET	0x204 /**< Uncorrectable error first failing
				        *  data Register, 63-32 */
#define XBRAM_UE_FFD_2_OFFSET	0x208 /**< Uncorrectable error first failing
				        *  data Register, 95-64 */
#define XBRAM_UE_FFD_3_OFFSET	0x20C /**< Uncorrectable error first failing
				        *  data Register, 127-96 */
#define XBRAM_UE_FFD_4_OFFSET	0x210 /**< Uncorrectable error first failing
				        *  data Register, 159-128 */
#define XBRAM_UE_FFD_5_OFFSET	0x214 /**< Uncorrectable error first failing
				        *  data Register, 191-160 */
#define XBRAM_UE_FFD_6_OFFSET	0x218 /**< Uncorrectable error first failing
				        *  data Register, 223-192 */
#define XBRAM_UE_FFD_7_OFFSET	0x21C /**< Uncorrectable error first failing
				        *  data Register, 255-224 */
#define XBRAM_UE_FFD_8_OFFSET	0x220 /**< Uncorrectable error first failing
				        *  data Register, 287-256 */
#define XBRAM_UE_FFD_9_OFFSET	0x224 /**< Uncorrectable error first failing
				        *  data Register, 319-288 */
#define XBRAM_UE_FFD_10_OFFSET	0x228 /**< Uncorrectable error first failing
				        *  data Register, 351-320 */
#define XBRAM_UE_FFD_11_OFFSET	0x22C /**< Uncorrectable error first failing
				        *  data Register, 383-352 */
#define XBRAM_UE_FFD_12_OFFSET	0x230 /**< Uncorrectable error first failing
				        *  data Register, 415-384 */
#define XBRAM_UE_FFD_13_OFFSET	0x234 /**< Uncorrectable error first failing
				        *  data Register, 447-416 */
#define XBRAM_UE_FFD_14_OFFSET	0x238 /**< Uncorrectable error first failing
				        *  data Register, 479-448 */
#define XBRAM_UE_FFD_15_OFFSET	0x23C /**< Uncorrectable error first failing
				        *  data Register, 511-480 */
#define XBRAM_UE_FFD_16_OFFSET	0x240 /**< Uncorrectable error first failing
				        *  data Register, 543-512 */
#define XBRAM_UE_FFD_17_OFFSET	0x244 /**< Uncorrectable error first failing
				        *  data Register, 575-544 */
#define XBRAM_UE_FFD_18_OFFSET	0x248 /**< Uncorrectable error first failing
				        *  data Register, 607-576 */
#define XBRAM_UE_FFD_19_OFFSET	0x24C /**< Uncorrectable error first failing
				        *  data Register, 639-608 */
#define XBRAM_UE_FFD_20_OFFSET	0x250 /**< Uncorrectable error first failing
				        *  data Register, 671-640 */
#define XBRAM_UE_FFD_21_OFFSET	0x254 /**< Uncorrectable error first failing
				        *  data Register, 703-672 */
#define XBRAM_UE_FFD_22_OFFSET	0x258 /**< Uncorrectable error first failing
				        *  data Register, 735-704 */
#define XBRAM_UE_FFD_23_OFFSET	0x25C /**< Uncorrectable error first failing
				        *  data Register, 767-736 */
#define XBRAM_UE_FFD_24_OFFSET	0x260 /**< Uncorrectable error first failing
				        *  data Register, 799-768 */
#define XBRAM_UE_FFD_25_OFFSET	0x264 /**< Uncorrectable error first failing
				        *  data Register, 831-800 */
#define XBRAM_UE_FFD_26_OFFSET	0x268 /**< Uncorrectable error first failing
				        *  data Register, 863-832 */
#define XBRAM_UE_FFD_27_OFFSET	0x26C /**< Uncorrectable error first failing
				        *  data Register, 895-864 */
#define XBRAM_UE_FFD_28_OFFSET	0x270 /**< Uncorrectable error first failing
				        *  data Register, 927-896 */
#define XBRAM_UE_FFD_29_OFFSET	0x274 /**< Uncorrectable error first failing
				        *  data Register, 959-928 */
#define XBRAM_UE_FFD_30_OFFSET	0x278 /**< Uncorrectable error first failing
				        *  data Register, 991-960 */
#define XBRAM_UE_FFD_31_OFFSET	0x27C /**< Uncorrectable error first failing
				        *  data Register, 1023-992 */

#define XBRAM_UE_FFE_0_OFFSET	0x280 /**< Uncorrectable error first failing
				        *  ECC Register, 31-0 */
#define XBRAM_UE_FFE_1_OFFSET	0x284 /**< Uncorrectable error first failing
				        *  ECC Register, 63-32 */
#define XBRAM_UE_FFE_2_OFFSET	0x288 /**< Uncorrectable error first failing
				        *  ECC Register, 95-64 */
#define XBRAM_UE_FFE_3_OFFSET	0x28C /**< Uncorrectable error first failing
				        *  ECC Register, 127-96 */
#define XBRAM_UE_FFE_4_OFFSET	0x290 /**< Uncorrectable error first failing
				        *  ECC Register, 159-128 */
#define XBRAM_UE_FFE_5_OFFSET	0x294 /**< Uncorrectable error first failing
				        *  ECC Register, 191-160 */
#define XBRAM_UE_FFE_6_OFFSET	0x298 /**< Uncorrectable error first failing
				        *  ECC Register, 223-192 */
#define XBRAM_UE_FFE_7_OFFSET	0x29C /**< Uncorrectable error first failing
				        *  ECC Register, 255-224 */

#define XBRAM_UE_FFA_0_OFFSET	0x2C0 /**< Uncorrectable error first failing
				        *  address Register 31-0 */
#define XBRAM_UE_FFA_1_OFFSET	0x2C4 /**< Uncorrectable error first failing
				        *  address Register 63-32 */

#define XBRAM_FI_D_0_OFFSET	0x300 /**< Fault injection Data Register,
				        *  31-0 */
#define XBRAM_FI_D_1_OFFSET	0x304 /**< Fault injection Data Register,
				        *  63-32 */
#define XBRAM_FI_D_2_OFFSET	0x308 /**< Fault injection Data Register,
				        *  95-64 */
#define XBRAM_FI_D_3_OFFSET	0x30C /**< Fault injection Data Register,
				        *  127-96 */
#define XBRAM_FI_D_4_OFFSET	0x310 /**< Fault injection Data Register,
				        *  159-128 */
#define XBRAM_FI_D_5_OFFSET	0x314 /**< Fault injection Data Register,
				        *  191-160 */
#define XBRAM_FI_D_6_OFFSET	0x318 /**< Fault injection Data Register,
				        *  223-192 */
#define XBRAM_FI_D_7_OFFSET	0x31C /**< Fault injection Data Register,
				        *  255-224 */
#define XBRAM_FI_D_8_OFFSET	0x320 /**< Fault injection Data Register,
				        *  287-256 */
#define XBRAM_FI_D_9_OFFSET	0x324 /**< Fault injection Data Register,
				        *  319-288 */
#define XBRAM_FI_D_10_OFFSET	0x328 /**< Fault injection Data Register,
				        *  351-320 */
#define XBRAM_FI_D_11_OFFSET	0x32C /**< Fault injection Data Register,
				        *  383-352 */
#define XBRAM_FI_D_12_OFFSET	0x330 /**< Fault injection Data Register,
				        *  415-384 */
#define XBRAM_FI_D_13_OFFSET	0x334 /**< Fault injection Data Register,
				        *  447-416 */
#define XBRAM_FI_D_14_OFFSET	0x338 /**< Fault injection Data Register,
				        *  479-448 */
#define XBRAM_FI_D_15_OFFSET	0x33C /**< Fault injection Data Register,
				        *  511-480 */
#define XBRAM_FI_D_16_OFFSET	0x340 /**< Fault injection Data Register,
				        *  543-512 */
#define XBRAM_FI_D_17_OFFSET	0x344 /**< Fault injection Data Register,
				        *  575-544 */
#define XBRAM_FI_D_18_OFFSET	0x348 /**< Fault injection Data Register,
				        *  607-576 */
#define XBRAM_FI_D_19_OFFSET	0x34C /**< Fault injection Data Register,
				        *  639-608 */
#define XBRAM_FI_D_20_OFFSET	0x350 /**< Fault injection Data Register,
				        *  671-640 */
#define XBRAM_FI_D_21_OFFSET	0x354 /**< Fault injection Data Register,
				        *  703-672 */
#define XBRAM_FI_D_22_OFFSET	0x358 /**< Fault injection Data Register,
				        *  735-704 */
#define XBRAM_FI_D_23_OFFSET	0x35C /**< Fault injection Data Register,
				        *  767-736 */
#define XBRAM_FI_D_24_OFFSET	0x360 /**< Fault injection Data Register,
				        *  799-768 */
#define XBRAM_FI_D_25_OFFSET	0x364 /**< Fault injection Data Register,
				        *  831-800 */
#define XBRAM_FI_D_26_OFFSET	0x368 /**< Fault injection Data Register,
				        *  863-832 */
#define XBRAM_FI_D_27_OFFSET	0x36C /**< Fault injection Data Register,
				        *  895-864 */
#define XBRAM_FI_D_28_OFFSET	0x370 /**< Fault injection Data Register,
				        *  927-896 */
#define XBRAM_FI_D_29_OFFSET	0x374 /**< Fault injection Data Register,
				        *  959-928 */
#define XBRAM_FI_D_30_OFFSET	0x378 /**< Fault injection Data Register,
				        *  991-960 */
#define XBRAM_FI_D_31_OFFSET	0x37C /**< Fault injection Data Register,
				        *  1023-992 */

#define XBRAM_FI_ECC_0_OFFSET	0x380 /**< Fault injection ECC Register,
				        *  31-0 */
#define XBRAM_FI_ECC_1_OFFSET	0x384 /**< Fault injection ECC Register,
				        *  63-32 */
#define XBRAM_FI_ECC_2_OFFSET	0x388 /**< Fault injection ECC Register,
				        *  95-64 */
#define XBRAM_FI_ECC_3_OFFSET	0x38C /**< Fault injection ECC Register,
				        *  127-96 */
#define XBRAM_FI_ECC_4_OFFSET	0x390 /**< Fault injection ECC Register,
				        *  159-128 */
#define XBRAM_FI_ECC_5_OFFSET	0x394 /**< Fault injection ECC Register,
				        *  191-160 */
#define XBRAM_FI_ECC_6_OFFSET	0x398 /**< Fault injection ECC Register,
				        *  223-192 */
#define XBRAM_FI_ECC_7_OFFSET	0x39C /**< Fault injection ECC Register,
				        *  255-224 */


/* @} */

/** @name Interrupt Status and Enable Register bitmaps and masks
 *
 * Bit definitions for the ECC status register and ECC interrupt enable register.
 * @{
 */
#define XBRAM_IR_CE_MASK	0x2 /**< Mask for the correctable error */
#define XBRAM_IR_UE_MASK	0x1 /**< Mask for the uncorrectable error */
#define XBRAM_IR_ALL_MASK	0x3 /**< Mask of all bits */
/*@}*/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/

#define XBram_In32  Xil_In32
#define XBram_Out32 Xil_Out32

#define XBram_In16  Xil_In16
#define XBram_Out16 Xil_Out16

#define XBram_In8  Xil_In8
#define XBram_Out8 Xil_Out8


/****************************************************************************/
/**
*
* Write a value to a BRAM register. A 32 bit write is performed.
*
* @param	BaseAddress is the base address of the BRAM device register.
* @param	RegOffset is the register offset from the base to write to.
* @param	Data is the data written to the register.
*
* @return	None.
*
* @note		C-style signature:
*		void XBram_WriteReg(u32 BaseAddress, u32 RegOffset, u32 Data)
*
****************************************************************************/
#define XBram_WriteReg(BaseAddress, RegOffset, Data) \
	XBram_Out32((BaseAddress) + (RegOffset), (u32)(Data))

/****************************************************************************/
/**
*
* Read a value from a BRAM register. A 32 bit read is performed.
*
* @param	BaseAddress is the base address of the BRAM device registers.
* @param	RegOffset is the register offset from the base to read from.
*
* @return	Data read from the register.
*
* @note		C-style signature:
*		u32 XBram_ReadReg(u32 BaseAddress, u32 RegOffset)
*
****************************************************************************/
#define XBram_ReadReg(BaseAddress, RegOffset) \
	XBram_In32((BaseAddress) + (RegOffset))

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/



#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
