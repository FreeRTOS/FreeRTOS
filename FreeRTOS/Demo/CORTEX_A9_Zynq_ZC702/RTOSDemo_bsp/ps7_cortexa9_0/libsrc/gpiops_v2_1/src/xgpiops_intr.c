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

void StubHandler(void *CallBackRef, int Bank, u32 Status);

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
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
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
void XGpioPs_IntrEnablePin(XGpioPs *InstancePtr, int Pin)
{
	u8 Bank;
	u8 PinNumber;
	u32 IntrReg = 0;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	IntrReg = 1 << PinNumber;
	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
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
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
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
void XGpioPs_IntrDisablePin(XGpioPs *InstancePtr, int Pin)
{
	u8 Bank;
	u8 PinNumber;
	u32 IntrReg = 0;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	IntrReg =  1 << PinNumber;
	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
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
				    ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				    XGPIOPS_INTMASK_OFFSET);
	return ~IntrMask;
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
int XGpioPs_IntrGetEnabledPin(XGpioPs *InstancePtr, int Pin)
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
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	IntrReg  = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				    ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				    XGPIOPS_INTMASK_OFFSET);

	return (IntrReg & (1 << Pin)) ? TRUE : FALSE;
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
				((Bank) * XGPIOPS_REG_MASK_OFFSET) +
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
int XGpioPs_IntrGetStatusPin(XGpioPs *InstancePtr, int Pin)
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
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	IntrReg = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				   ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				   XGPIOPS_INTSTS_OFFSET);

	return (IntrReg & (1 << Pin)) ? TRUE : FALSE;
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
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
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
void XGpioPs_IntrClearPin(XGpioPs *InstancePtr, int Pin)
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
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	/*
	 * Clear the specified pending interrupts.
	 */
	IntrReg = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				   ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				   XGPIOPS_INTSTS_OFFSET);

	IntrReg &= (1 << Pin);
	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
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
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTTYPE_OFFSET, IntrType);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTPOL_OFFSET, IntrPolarity);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
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
				     ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				     XGPIOPS_INTTYPE_OFFSET);

	*IntrPolarity = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
					 ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
					 XGPIOPS_INTPOL_OFFSET);

	*IntrOnAny = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				      ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
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
void XGpioPs_SetIntrTypePin(XGpioPs *InstancePtr, int Pin, u8 IrqType)
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
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	IntrTypeReg = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				       ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				       XGPIOPS_INTTYPE_OFFSET);

	IntrPolReg = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				      ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				      XGPIOPS_INTPOL_OFFSET);

	IntrOnAnyReg = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
					((Bank) * XGPIOPS_REG_MASK_OFFSET) +
					XGPIOPS_INTANY_OFFSET);

	switch (IrqType) {
		case XGPIOPS_IRQ_TYPE_EDGE_RISING:
			IntrTypeReg |= (1 << PinNumber);
			IntrPolReg |= (1 << PinNumber);
			IntrOnAnyReg &= ~(1 << PinNumber);
			break;
		case XGPIOPS_IRQ_TYPE_EDGE_FALLING:
			IntrTypeReg |= (1 << PinNumber);
			IntrPolReg &= ~(1 << PinNumber);
			IntrOnAnyReg &= ~(1 << PinNumber);
			break;
		case XGPIOPS_IRQ_TYPE_EDGE_BOTH:
			IntrTypeReg |= (1 << PinNumber);
			IntrOnAnyReg |= (1 << PinNumber);
			break;
		case XGPIOPS_IRQ_TYPE_LEVEL_HIGH:
			IntrTypeReg &= ~(1 << PinNumber);
			IntrPolReg |= (1 << PinNumber);
			break;
		case XGPIOPS_IRQ_TYPE_LEVEL_LOW:
			IntrTypeReg &= ~(1 << PinNumber);
			IntrPolReg &= ~(1 << PinNumber);
			break;
	}

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTTYPE_OFFSET, IntrTypeReg);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTPOL_OFFSET, IntrPolReg);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
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
u8 XGpioPs_GetIntrTypePin(XGpioPs *InstancePtr, int Pin)
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
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	IntrType = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				    ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				    XGPIOPS_INTTYPE_OFFSET) & PinNumber;

	IntrPol = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				   ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				   XGPIOPS_INTPOL_OFFSET) & PinNumber;

	IntrOnAny = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				     ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				     XGPIOPS_INTANY_OFFSET) & PinNumber;

	if (IntrType == 1) {
		if (IntrOnAny == 1) {
			IrqType = XGPIOPS_IRQ_TYPE_EDGE_BOTH;
		} else if (IntrPol == 1) {
			IrqType = XGPIOPS_IRQ_TYPE_EDGE_RISING;
		} else {
			IrqType = XGPIOPS_IRQ_TYPE_EDGE_FALLING;
		}
	} else {
		if (IntrPol == 1) {
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
				 XGpioPs_Handler FuncPtr)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(FuncPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->Handler = FuncPtr;
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

	for (Bank = 0; Bank < XGPIOPS_MAX_BANKS; Bank++) {
		IntrStatus = XGpioPs_IntrGetStatus(InstancePtr, Bank);
		if (IntrStatus != 0) {
			IntrEnabled = XGpioPs_IntrGetEnabled(InstancePtr,
							      Bank);
			XGpioPs_IntrClear(InstancePtr, Bank,
					   IntrStatus & IntrEnabled);
			InstancePtr->Handler((void *)InstancePtr->
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
void StubHandler(void *CallBackRef, int Bank, u32 Status)
{
	(void) CallBackRef;
	(void) Bank;
	(void) Status;

	Xil_AssertVoidAlways();
}
