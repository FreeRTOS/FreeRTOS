/******************************************************************************
*
* (c) Copyright 2011-2013 Xilinx, Inc. All rights reserved.
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
* @file xadcps_intr.c
*
* This file contains interrupt handling API functions of the XADC
* device.
*
* The device must be configured at hardware build time to support interrupt
* for all the functions in this file to work.
*
* Refer to xadcps.h header file and device specification for more information.
*
* @note
*
* Calling the interrupt functions without including the interrupt component will
* result in asserts if asserts are enabled, and will result in a unpredictable
* behavior if the asserts are not enabled.
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- -----  -------- -----------------------------------------------------
* 1.00a ssb    12/22/11 First release based on the XPS/AXI xadc driver
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xadcps.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/


/****************************************************************************/
/**
*
* This function enables the specified interrupts in the device.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Mask is the bit-mask of the interrupts to be enabled.
*		Bit positions of 1 will be enabled. Bit positions of 0 will
*		keep the previous setting. This mask is formed by OR'ing
*		XADCPS_INTX_* bits defined in xadcps_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAdcPs_IntrEnable(XAdcPs *InstancePtr, u32 Mask)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Disable the specified interrupts in the IPIER.
	 */
	RegValue = XAdcPs_ReadReg(InstancePtr->Config.BaseAddress,
				    XADCPS_INT_MASK_OFFSET);
	RegValue &= ~(Mask & XADCPS_INTX_ALL_MASK);
	XAdcPs_WriteReg(InstancePtr->Config.BaseAddress,
				XADCPS_INT_MASK_OFFSET,
			  	RegValue);
}


/****************************************************************************/
/**
*
* This function disables the specified interrupts in the device.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Mask is the bit-mask of the interrupts to be disabled.
*		Bit positions of 1 will be disabled. Bit positions of 0 will
*		keep the previous setting. This mask is formed by OR'ing
*		XADCPS_INTX_* bits defined in xadcps_hw.h.
*
* @return	None.
*
* @note		None
*
*****************************************************************************/
void XAdcPs_IntrDisable(XAdcPs *InstancePtr, u32 Mask)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Enable the specified interrupts in the IPIER.
	 */
	RegValue = XAdcPs_ReadReg(InstancePtr->Config.BaseAddress,
				    XADCPS_INT_MASK_OFFSET);
	RegValue |= (Mask & XADCPS_INTX_ALL_MASK);
	XAdcPs_WriteReg(InstancePtr->Config.BaseAddress,
				XADCPS_INT_MASK_OFFSET,
			  	RegValue);
}
/****************************************************************************/
/**
*
* This function returns the enabled interrupts read from the Interrupt Mask
* Register (IPIER). Use the XADCPS_IPIXR_* constants defined in xadcps_hw.h to
* interpret the returned value.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	A 32-bit value representing the contents of the I.
*
* @note		None.
*
*****************************************************************************/
u32 XAdcPs_IntrGetEnabled(XAdcPs *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Return the value read from the Interrupt Enable Register.
	 */
	return (~ XAdcPs_ReadReg(InstancePtr->Config.BaseAddress,
				XADCPS_INT_MASK_OFFSET) & XADCPS_INTX_ALL_MASK);
}

/****************************************************************************/
/**
*
* This function returns the interrupt status read from Interrupt Status
* Register(IPISR). Use the XADCPS_IPIXR_* constants defined in xadcps_hw.h
* to interpret the returned value.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	A 32-bit value representing the contents of the IPISR.
*
* @note		The device must be configured at hardware build time to include
*		interrupt component for this function to work.
*
*****************************************************************************/
u32 XAdcPs_IntrGetStatus(XAdcPs *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Return the value read from the Interrupt Status register.
	 */
	return XAdcPs_ReadReg(InstancePtr->Config.BaseAddress,
				XADCPS_INT_STS_OFFSET) & XADCPS_INTX_ALL_MASK;
}

/****************************************************************************/
/**
*
* This function clears the specified interrupts in the Interrupt Status
* Register (IPISR).
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Mask is the bit-mask of the interrupts to be cleared.
*		Bit positions of 1 will be cleared. Bit positions of 0 will not
* 		change the previous interrupt status. This mask is formed by
* 		OR'ing XADCPS_IPIXR_* bits which are defined in xadcps_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAdcPs_IntrClear(XAdcPs *InstancePtr, u32 Mask)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Clear the specified interrupts in the Interrupt Status register.
	 */
	RegValue = XAdcPs_ReadReg(InstancePtr->Config.BaseAddress,
				    XADCPS_INT_STS_OFFSET);
	RegValue &= (Mask & XADCPS_INTX_ALL_MASK);
	XAdcPs_WriteReg(InstancePtr->Config.BaseAddress, XADCPS_INT_STS_OFFSET,
			  RegValue);

}
