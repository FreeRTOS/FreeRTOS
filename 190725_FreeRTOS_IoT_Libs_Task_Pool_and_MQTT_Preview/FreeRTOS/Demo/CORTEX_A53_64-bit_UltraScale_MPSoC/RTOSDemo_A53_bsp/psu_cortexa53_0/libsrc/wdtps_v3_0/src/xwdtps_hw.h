/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
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
/****************************************************************************/
/**
*
* @file xwdtps_hw.h
* @addtogroup wdtps_v3_0
* @{
*
* This file contains the hardware interface to the System Watch Dog Timer (WDT).
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- ---------------------------------------------
* 1.00a ecm/jz 01/15/10 First release
* 1.02a  sg    07/15/12 Removed defines related to  External Signal
*			Length functionality for CR 658287
* 3.00  kvn    02/13/15 Modified code for MISRA-C:2012 compliance.
* </pre>
*
******************************************************************************/
#ifndef XWDTPS_HW_H		/* prevent circular inclusions */
#define XWDTPS_HW_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/

/** @name Register Map
 * Offsets of registers from the start of the device
 * @{
 */

#define XWDTPS_ZMR_OFFSET	0x00000000U /**< Zero Mode Register */
#define XWDTPS_CCR_OFFSET	0x00000004U /**< Counter Control Register */
#define XWDTPS_RESTART_OFFSET	0x00000008U /**< Restart Register */
#define XWDTPS_SR_OFFSET	0x0000000CU /**< Status Register */
/* @} */


/** @name Zero Mode Register
 * This register controls how the time out is indicated and also contains
 * the access code (0xABC) to allow writes to the register
 * @{
 */
#define XWDTPS_ZMR_WDEN_MASK	0x00000001U /**< enable the WDT */
#define XWDTPS_ZMR_RSTEN_MASK	0x00000002U /**< enable the reset output */
#define XWDTPS_ZMR_IRQEN_MASK	0x00000004U /**< enable the IRQ output */

#define XWDTPS_ZMR_RSTLN_MASK	0x00000070U /**< set length of reset pulse */
#define XWDTPS_ZMR_RSTLN_SHIFT	4U	   /**< shift for reset pulse */

#define XWDTPS_ZMR_IRQLN_MASK	0x00000180U /**< set length of interrupt pulse */
#define XWDTPS_ZMR_IRQLN_SHIFT	7U	   /**< shift for interrupt pulse */

#define XWDTPS_ZMR_ZKEY_MASK	0x00FFF000U /**< mask for writing access key */
#define XWDTPS_ZMR_ZKEY_VAL		0x00ABC000U /**< access key, 0xABC << 12 */

/* @} */

/** @name  Counter Control register
 * This register controls how fast the timer runs and the reset value
 * and also contains the access code (0x248) to allow writes to the
 * register
 * @{
 */

#define XWDTPS_CCR_CLKSEL_MASK	0x00000003U /**< counter clock prescale */

#define XWDTPS_CCR_CRV_MASK	0x00003FFCU /**< counter reset value */
#define XWDTPS_CCR_CRV_SHIFT	2U	   /**< shift for writing value */

#define XWDTPS_CCR_CKEY_MASK	0x03FFC000U /**< mask for writing access key */
#define XWDTPS_CCR_CKEY_VAL	0x00920000U /**< access key, 0x248 << 14 */

/* Bit patterns for Clock prescale divider values */

#define XWDTPS_CCR_PSCALE_0008  0x00000000U /**< divide clock by 8 */
#define XWDTPS_CCR_PSCALE_0064  0x00000001U /**< divide clock by 64 */
#define XWDTPS_CCR_PSCALE_0512  0x00000002U /**< divide clock by 512 */
#define XWDTPS_CCR_PSCALE_4096  0x00000003U /**< divide clock by 4096 */

/* @} */

/** @name  Restart register
 * This register resets the timer preventing a timeout. Value is specific
 * 0x1999
 * @{
 */

#define XWDTPS_RESTART_KEY_VAL	0x00001999U /**< valid key */

/*@}*/

/** @name Status register
 * This register indicates timer reached zero count.
 * @{
 */
#define XWDTPS_SR_WDZ_MASK	0x00000001U /**< time out occurred */

/*@}*/

/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* Read the given register.
*
* @param	BaseAddress is the base address of the device
* @param	RegOffset is the register offset to be read
*
* @return	The 32-bit value of the register
*
* @note		C-style signature:
*		u32 XWdtPs_ReadReg(u32 BaseAddress, u32 RegOffset)
*
*****************************************************************************/
#define XWdtPs_ReadReg(BaseAddress, RegOffset) \
	Xil_In32((BaseAddress) + (u32)(RegOffset))

/****************************************************************************/
/**
*
* Write the given register.
*
* @param	BaseAddress is the base address of the device
* @param	RegOffset is the register offset to be written
* @param	Data is the 32-bit value to write to the register
*
* @return	None.
*
* @note		C-style signature:
*		void XWdtPs_WriteReg(u32 BaseAddress, u32 RegOffset, u32 Data)
*
*****************************************************************************/
#define XWdtPs_WriteReg(BaseAddress, RegOffset, Data) \
	Xil_Out32((BaseAddress) + (u32)(RegOffset), (u32)(Data))


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/

#ifdef __cplusplus
}
#endif

#endif
/** @} */
