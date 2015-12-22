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
/*****************************************************************************/
/**
*
* @file xgpiops_intr.c
*
* This file contains functions related to GPIO interrupt handling.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a sv   01/18/10 First Release
* 2.2	sk	 10/13/14 Used Pin number in Bank instead of pin number
* 					  passed to API's. CR# 822636
* 3.00  kvn  02/13/15 Modified code for MISRA-C:2012 compliance.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xgpiops.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

void StubHandler(void *CallBackRef, u32 Bank, u32 Status);

/****************************************************************************/
/**
*
* This function enables the interrupts for the specified pins in the specified
* bank.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
* @param	Mask is the bit mask of the pins for which interrupts are to
*		be enabled. Bit positions of 1 will be enabled. Bit positions
*		of 0 will keep the previous setting.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XGpioPs_IntrEnable(XGpioPs *InstancePtr, u8 Bank, u32 Mask)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Bank < XGPIOPS_MAX_BANKS);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTEN_OFFSET, Mask);
}

/****************************************************************************/
/**
*
* This function enables the interrupt for the specified pin.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Pin is the pin number for which the interrupt is to be enabled.
*		Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XGpioPs_IntrEnablePin(XGpioPs *InstancePtr, u32 Pin)
{
	u8 Bank;
	u8 PinNumber;
	u32 IntrReg = 0U;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin((u8)Pin, &Bank, &PinNumber);

	IntrReg = ((u32)1 << (u32)PinNumber);
	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTEN_OFFSET, IntrReg);
}

/****************************************************************************/
/**
*
* This function disables the interrupts for the specified pins in the specified
* bank.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
* @param	Mask is the bit mask of the pins for which interrupts are
*		to be disabled. Bit positions of 1 will be disabled. Bit
*		positions of 0 will keep the previous setting.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XGpioPs_IntrDisable(XGpioPs *InstancePtr, u8 Bank, u32 Mask)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Bank < XGPIOPS_MAX_BANKS);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTDIS_OFFSET, Mask);
}

/****************************************************************************/
/**
*
* This function disables the interrupts for the specified pin.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Pin is the pin number for which the interrupt is to be disabled.
*		Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XGpioPs_IntrDisablePin(XGpioPs *InstancePtr, u32 Pin)
{
	u8 Bank;
	u8 PinNumber;
	u32 IntrReg = 0U;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin((u8)Pin, &Bank, &PinNumber);

	IntrReg =  ((u32)1 << (u32)PinNumber);
	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTDIS_OFFSET, IntrReg);
}

/****************************************************************************/
/**
*
* This function returns the interrupt enable status for a bank.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
*
* @return	Enabled interrupt(s) in a 32-bit format. Bit positions with 1
*		indicate that the interrupt for that pin is enabled, bit
*		positions with 0 indicate that the interrupt for that pin is
*		disabled.
*
* @note		None.
*
*****************************************************************************/
u32 XGpioPs_IntrGetEnabled(XGpioPs *InstancePtr, u8 Bank)
{
	u32 IntrMask;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Bank < XGPIOPS_MAX_BANKS);

	IntrMask = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				    ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				    XGPIOPS_INTMASK_OFFSET);
	return (~IntrMask);
}

/****************************************************************************/
/**
*
* This function returns whether interrupts are enabled for the specified pin.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Pin is the pin number for which the interrupt enable status
*		is to be known.
*		Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
*
* @return
*		- TRUE if the interrupt is enabled.
*		- FALSE if the interrupt is disabled.
*
* @note		None.
*
*****************************************************************************/
u32 XGpioPs_IntrGetEnabledPin(XGpioPs *InstancePtr, u32 Pin)
{
	u8 Bank;
	u8 PinNumber;
	u32 IntrReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin((u8)Pin, &Bank, &PinNumber);

	IntrReg  = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				    ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				    XGPIOPS_INTMASK_OFFSET);

	return (((IntrReg & ((u32)1 << PinNumber)) != (u32)0)? FALSE : TRUE);
}

/****************************************************************************/
/**
*
* This function returns interrupt status read from Interrupt Status Register.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
*
* @return	The value read from Interrupt Status Register.
*
* @note		None.
*
*****************************************************************************/
u32 XGpioPs_IntrGetStatus(XGpioPs *InstancePtr, u8 Bank)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Bank < XGPIOPS_MAX_BANKS);

	return XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				XGPIOPS_INTSTS_OFFSET);
}

/****************************************************************************/
/**
*
* This function returns interrupt enable status of the specified pin.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Pin is the pin number for which the interrupt enable status
*		is to be known.
*		Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
*
* @return
*		- TRUE if the interrupt has occurred.
*		- FALSE if the interrupt has not occurred.
*
* @note		None.
*
*****************************************************************************/
u32 XGpioPs_IntrGetStatusPin(XGpioPs *InstancePtr, u32 Pin)
{
	u8 Bank;
	u8 PinNumber;
	u32 IntrReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin((u8)Pin, &Bank, &PinNumber);

	IntrReg = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				   ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				   XGPIOPS_INTSTS_OFFSET);

	return (((IntrReg & ((u32)1 << PinNumber)) != (u32)0)? TRUE : FALSE);
}

/****************************************************************************/
/**
*
* This function clears pending interrupt(s) with the provided mask. This
* function should be called after the software has serviced the interrupts
* that are pending.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
* @param	Mask is the mask of the interrupts to be cleared. Bit positions
*		of 1 will be cleared. Bit positions of 0 will not change the
*		previous interrupt status.
*
* @note		None.
*
*****************************************************************************/
void XGpioPs_IntrClear(XGpioPs *InstancePtr, u8 Bank, u32 Mask)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Bank < XGPIOPS_MAX_BANKS);

	/*
	 * Clear the currently pending interrupts.
	 */
	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTSTS_OFFSET, Mask);
}

/****************************************************************************/
/**
*
* This function clears the specified pending interrupt. This function should be
* called after the software has serviced the interrupts that are pending.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Pin is the pin number for which the interrupt status is to be
*		cleared. Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
*
* @note		None.
*
*****************************************************************************/
void XGpioPs_IntrClearPin(XGpioPs *InstancePtr, u32 Pin)
{
	u8 Bank;
	u8 PinNumber;
	u32 IntrReg;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin((u8)Pin, &Bank, &PinNumber);

	/*
	 * Clear the specified pending interrupts.
	 */
	IntrReg = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				   ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				   XGPIOPS_INTSTS_OFFSET);

	IntrReg &= ((u32)1 << PinNumber);
	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTSTS_OFFSET, IntrReg);
}

/****************************************************************************/
/**
*
* This function is used for setting the Interrupt Type, Interrupt Polarity and
* Interrupt On Any for the specified GPIO Bank pins.
*
* @param	InstancePtr is a pointer to an XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
* @param	IntrType is the 32 bit mask of the interrupt type.
*		0 means Level Sensitive and 1 means Edge Sensitive.
* @param	IntrPolarity is the 32 bit mask of the interrupt polarity.
*		0 means Active Low or Falling Edge and 1 means Active High or
*		Rising Edge.
* @param	IntrOnAny is the 32 bit mask of the interrupt trigger for
*		edge triggered interrupts. 0 means trigger on single edge using
*		the configured interrupt polarity and 1 means  trigger on both
*		edges.
*
* @return	None.
*
* @note		This function is used for setting the interrupt related
*		properties of all the pins in the specified bank. The previous
*		state of the pins is not maintained.
*		To change the Interrupt properties of a single GPIO pin, use the
*		function XGpioPs_SetPinIntrType().
*
*****************************************************************************/
void XGpioPs_SetIntrType(XGpioPs *InstancePtr, u8 Bank, u32 IntrType,
			  u32 IntrPolarity, u32 IntrOnAny)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Bank < XGPIOPS_MAX_BANKS);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTTYPE_OFFSET, IntrType);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTPOL_OFFSET, IntrPolarity);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTANY_OFFSET, IntrOnAny);
}

/****************************************************************************/
/**
*
* This function is used for getting the Interrupt Type, Interrupt Polarity and
* Interrupt On Any for the specified GPIO Bank pins.
*
* @param	InstancePtr is a pointer to an XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
* @param	IntrType returns the 32 bit mask of the interrupt type.
*		0 means Level Sensitive and 1 means Edge Sensitive.
* @param	IntrPolarity returns the 32 bit mask of the interrupt
*		polarity. 0 means Active Low or Falling Edge and 1 means
*		Active High or Rising Edge.
* @param	IntrOnAny returns the 32 bit mask of the interrupt trigger for
*		edge triggered interrupts. 0 means trigger on single edge using
*		the configured interrupt polarity and 1 means trigger on both
*		edges.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XGpioPs_GetIntrType(XGpioPs *InstancePtr, u8 Bank, u32 *IntrType,
			  u32 *IntrPolarity, u32 *IntrOnAny)

{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Bank < XGPIOPS_MAX_BANKS);

	*IntrType = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				     ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				     XGPIOPS_INTTYPE_OFFSET);

	*IntrPolarity = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
					 ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
					 XGPIOPS_INTPOL_OFFSET);

	*IntrOnAny = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				      ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				      XGPIOPS_INTANY_OFFSET);
}

/****************************************************************************/
/**
*
* This function is used for setting the IRQ Type of a single GPIO pin.
*
* @param	InstancePtr is a pointer to an XGpioPs instance.
* @param	Pin is the pin number whose IRQ type is to be set.
*		Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
* @param	IrqType is the IRQ type for GPIO Pin. Use XGPIOPS_IRQ_TYPE_*
*		defined in xgpiops.h to specify the IRQ type.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XGpioPs_SetIntrTypePin(XGpioPs *InstancePtr, u32 Pin, u8 IrqType)
{
	u32 IntrTypeReg;
	u32 IntrPolReg;
	u32 IntrOnAnyReg;
	u8 Bank;
	u8 PinNumber;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);
	Xil_AssertVoid(IrqType <= XGPIOPS_IRQ_TYPE_LEVEL_LOW);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin((u8)Pin, &Bank, &PinNumber);

	IntrTypeReg = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				       ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				       XGPIOPS_INTTYPE_OFFSET);

	IntrPolReg = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				      ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				      XGPIOPS_INTPOL_OFFSET);

	IntrOnAnyReg = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
					((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
					XGPIOPS_INTANY_OFFSET);

	switch (IrqType) {
		case XGPIOPS_IRQ_TYPE_EDGE_RISING:
			IntrTypeReg |= ((u32)1 << (u32)PinNumber);
			IntrPolReg |= ((u32)1 << (u32)PinNumber);
			IntrOnAnyReg &= ~((u32)1 << (u32)PinNumber);
			break;
		case XGPIOPS_IRQ_TYPE_EDGE_FALLING:
			IntrTypeReg |= ((u32)1 << (u32)PinNumber);
			IntrPolReg &= ~((u32)1 << (u32)PinNumber);
			IntrOnAnyReg &= ~((u32)1 << (u32)PinNumber);
			break;
		case XGPIOPS_IRQ_TYPE_EDGE_BOTH:
			IntrTypeReg |= ((u32)1 << (u32)PinNumber);
			IntrOnAnyReg |= ((u32)1 << (u32)PinNumber);
			break;
		case XGPIOPS_IRQ_TYPE_LEVEL_HIGH:
			IntrTypeReg &= ~((u32)1 << (u32)PinNumber);
			IntrPolReg |= ((u32)1 << (u32)PinNumber);
			break;
		case XGPIOPS_IRQ_TYPE_LEVEL_LOW:
			IntrTypeReg &= ~((u32)1 << (u32)PinNumber);
			IntrPolReg &= ~((u32)1 << (u32)PinNumber);
			break;
		default:
			/**< Default statement is added for MISRA C compliance. */
			break;
	}

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTTYPE_OFFSET, IntrTypeReg);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTPOL_OFFSET, IntrPolReg);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTANY_OFFSET, IntrOnAnyReg);
}

/****************************************************************************/
/**
*
* This function returns the IRQ Type of a given GPIO pin.
*
* @param	InstancePtr is a pointer to an XGpioPs instance.
* @param	Pin is the pin number whose IRQ type is to be obtained.
*		Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
*
* @return	None.
*
* @note		Use XGPIOPS_IRQ_TYPE_* defined in xgpiops.h for the IRQ type
*		returned by this function.
*
*****************************************************************************/
u8 XGpioPs_GetIntrTypePin(XGpioPs *InstancePtr, u32 Pin)
{
	u32 IntrType;
	u32 IntrPol;
	u32 IntrOnAny;
	u8 Bank;
	u8 PinNumber;
	u8 IrqType;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin((u8)Pin, &Bank, &PinNumber);

	IntrType = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				    ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				    XGPIOPS_INTTYPE_OFFSET) & ((u32)1 << PinNumber);

	if (IntrType == ((u32)1 << PinNumber)) {

		IntrOnAny = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				     ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				     XGPIOPS_INTANY_OFFSET) & ((u32)1 << PinNumber);

		IntrPol = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				   ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				   XGPIOPS_INTPOL_OFFSET) & ((u32)1 << PinNumber);


		if (IntrOnAny == ((u32)1 << PinNumber)) {
			IrqType = XGPIOPS_IRQ_TYPE_EDGE_BOTH;
		} else if (IntrPol == ((u32)1 << PinNumber)) {
			IrqType = XGPIOPS_IRQ_TYPE_EDGE_RISING;
		} else {
			IrqType = XGPIOPS_IRQ_TYPE_EDGE_FALLING;
		}
	} else {

		IntrPol = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				   ((u32)(Bank) * XGPIOPS_REG_MASK_OFFSET) +
				   XGPIOPS_INTPOL_OFFSET) & ((u32)1 << PinNumber);

		if (IntrPol == ((u32)1 << PinNumber)) {
			IrqType = XGPIOPS_IRQ_TYPE_LEVEL_HIGH;
		} else {
			IrqType = XGPIOPS_IRQ_TYPE_LEVEL_LOW;
		}
	}

	return IrqType;
}

/*****************************************************************************/
/**
*
* This function sets the status callback function. The callback function is
* called by the  XGpioPs_IntrHandler when an interrupt occurs.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	CallBackRef is the upper layer callback reference passed back
*		when the callback function is invoked.
* @param	FuncPtr is the pointer to the callback function.
*
*
* @return	None.
*
* @note		The handler is called within interrupt context, so it should do
*		its work quickly and queue potentially time-consuming work to a
*		task-level thread.
*
******************************************************************************/
void XGpioPs_SetCallbackHandler(XGpioPs *InstancePtr, void *CallBackRef,
				 XGpioPs_Handler FuncPointer)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(FuncPointer != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->Handler = FuncPointer;
	InstancePtr->CallBackRef = CallBackRef;
}

/*****************************************************************************/
/**
*
* This function is the interrupt handler for GPIO interrupts.It checks the
* interrupt status registers of all the banks to determine the actual bank in
* which an interrupt has been triggered. It then calls the upper layer callback
* handler set by the function XGpioPs_SetBankHandler(). The callback is called
* when an interrupt
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
*
* @return	None.
*
* @note		This function does not save and restore the processor context
*		such that the user must provide this processing.
*
******************************************************************************/
void XGpioPs_IntrHandler(XGpioPs *InstancePtr)
{
	u8 Bank;
	u32 IntrStatus;
	u32 IntrEnabled;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	for (Bank = 0U; Bank < XGPIOPS_MAX_BANKS; Bank++) {
		IntrStatus = XGpioPs_IntrGetStatus(InstancePtr, Bank);
		if (IntrStatus != (u32)0) {
			IntrEnabled = XGpioPs_IntrGetEnabled(InstancePtr,
							      Bank);
			XGpioPs_IntrClear((XGpioPs *)InstancePtr, Bank,
							(IntrStatus & IntrEnabled));
			InstancePtr->Handler(InstancePtr->
					     CallBackRef, Bank,
					     (IntrStatus & IntrEnabled));
		}
	}
}

/*****************************************************************************/
/**
*
* This is a stub for the status callback. The stub is here in case the upper
* layers do not set the handler.
*
* @param	CallBackRef is a pointer to the upper layer callback reference
* @param	Bank is the GPIO Bank in which an interrupt occurred.
* @param	Status is the Interrupt status of the GPIO bank.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void StubHandler(void *CallBackRef, u32 Bank, u32 Status)
{
	(void*) CallBackRef;
	(void) Bank;
	(void) Status;

	Xil_AssertVoidAlways();
}
