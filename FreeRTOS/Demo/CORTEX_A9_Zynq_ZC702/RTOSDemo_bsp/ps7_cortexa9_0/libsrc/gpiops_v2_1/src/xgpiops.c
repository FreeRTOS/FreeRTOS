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
* @file xgpiops.c
* @addtogroup gpiops_v2_1
* @{
*
* The XGpioPs driver. Functions in this file are the minimum required functions
* for this driver. See xgpiops.h for a detailed description of the driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a sv   01/15/10 First Release
* 1.01a sv   04/15/12 Removed the APIs XGpioPs_SetMode, XGpioPs_SetModePin
*                     XGpioPs_GetMode, XGpioPs_GetModePin as they are not
*		      relevant to Zynq device. The interrupts are disabled
*		      for output pins on all banks during initialization.
* 2.1   hk   04/29/14 Use Input data register DATA_RO for read. CR# 771667.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xgpiops.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Variable Definitions *****************************/

/*
 * This structure defines the mapping of the pin numbers to the banks when
 * the driver APIs are used for working on the individual pins.
 */
unsigned int XGpioPsPinTable[] = {
	31, /* 0 - 31, Bank 0 */
	53, /* 32 - 53, Bank 1 */
	85, /* 54 - 85, Bank 2 */
	117 /* 86 - 117 Bank 3 */
};

/************************** Function Prototypes ******************************/

extern void StubHandler(void *CallBackRef, int Bank, u32 Status);

/*****************************************************************************/
/*
*
* This function initializes a XGpioPs instance/driver.
* All members of the XGpioPs instance structure are initialized and
* StubHandlers are assigned to the Bank Status Handlers.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	ConfigPtr points to the XGpioPs device configuration structure.
* @param	EffectiveAddr is the device base address in the virtual memory
*		address space. If the address translation is not used then the
*		physical address should be passed.
*		Unexpected errors may occur if the address mapping is changed
*		after this function is invoked.
*
* @return	XST_SUCCESS always.
*
* @note		None.
*
******************************************************************************/
int XGpioPs_CfgInitialize(XGpioPs *InstancePtr, XGpioPs_Config *ConfigPtr,
				u32 EffectiveAddr)
{

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/*
	 * Set some default values for instance data, don't indicate the device
	 * is ready to use until everything has been initialized successfully.
	 */
	InstancePtr->IsReady = 0;
	InstancePtr->GpioConfig.BaseAddr = EffectiveAddr;
	InstancePtr->GpioConfig.DeviceId = ConfigPtr->DeviceId;
	InstancePtr->Handler = StubHandler;

	/*
	 * By default, interrupts are not masked in GPIO. Disable
	 * interrupts for all pins in all the 4 banks.
	 */
	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  XGPIOPS_INTDIS_OFFSET, 0xFFFFFFFF);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((1) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTDIS_OFFSET, 0xFFFFFFFF);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((2) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTDIS_OFFSET, 0xFFFFFFFF);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((3) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_INTDIS_OFFSET, 0xFFFFFFFF);

	/*
	 * Indicate the component is now ready to use.
	 */
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* Read the Data register of the specified GPIO bank.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
*
* @return	Current value of the Data register.
*
* @note		This function is used for reading the state of all the GPIO pins
*		of specified bank.
*
*****************************************************************************/
u32 XGpioPs_Read(XGpioPs *InstancePtr, u8 Bank)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Bank < XGPIOPS_MAX_BANKS);

	return XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				 ((Bank) * XGPIOPS_DATA_BANK_OFFSET) +
				 XGPIOPS_DATA_RO_OFFSET);
}

/****************************************************************************/
/**
*
* Read Data from the specified pin.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Pin is the pin number for which the data has to be read.
*		Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
*		See xgpiops.h for the mapping of the pin numbers in the banks.
*
* @return	Current value of the Pin (0 or 1).
*
* @note		This function is used for reading the state of the specified
*		GPIO pin.
*
*****************************************************************************/
int XGpioPs_ReadPin(XGpioPs *InstancePtr, int Pin)
{
	u8 Bank;
	u8 PinNumber;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	return (XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				 ((Bank) * XGPIOPS_DATA_BANK_OFFSET) +
				 XGPIOPS_DATA_RO_OFFSET) >> PinNumber) & 1;

}

/****************************************************************************/
/**
*
* Write to the Data register of the specified GPIO bank.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
* @param	Data is the value to be written to the Data register.
*
* @return	None.
*
* @note		This function is used for writing to all the GPIO pins of
*		the bank. The previous state of the pins is not maintained.
*
*****************************************************************************/
void XGpioPs_Write(XGpioPs *InstancePtr, u8 Bank, u32 Data)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Bank < XGPIOPS_MAX_BANKS);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_DATA_BANK_OFFSET) +
			  XGPIOPS_DATA_OFFSET, Data);
}

/****************************************************************************/
/**
*
* Write data to the specified pin.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Pin is the pin number to which the Data is to be written.
*		Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
* @param	Data is the data to be written to the specified pin (0 or 1).
*
* @return	None.
*
* @note		This function does a masked write to the specified pin of
*		the specified GPIO bank. The previous state of other pins
*		is maintained.
*
*****************************************************************************/
void XGpioPs_WritePin(XGpioPs *InstancePtr, int Pin, int Data)
{
	u32 RegOffset;
	u32 Value;
	u8 Bank;
	u8 PinNumber;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	if (PinNumber > 15) {
		/*
		 * There are only 16 data bits in bit maskable register.
		 */
		PinNumber -= 16;
		RegOffset = XGPIOPS_DATA_MSW_OFFSET;
	} else {
		RegOffset = XGPIOPS_DATA_LSW_OFFSET;
	}

	/*
	 * Get the 32 bit value to be written to the Mask/Data register where
	 * the upper 16 bits is the mask and lower 16 bits is the data.
	 */
	Data &= 0x01;
	Value = ~(1 << (PinNumber + 16)) & ((Data << PinNumber) | 0xFFFF0000);
	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_DATA_MASK_OFFSET) +
			  RegOffset, Value);
}



/****************************************************************************/
/**
*
* Set the Direction of the pins of the specified GPIO Bank.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
* @param	Direction is the 32 bit mask of the Pin direction to be set for
*		all the pins in the Bank. Bits with 0 are set to Input mode,
*		bits with 1 are	set to Output Mode.
*
* @return	None.
*
* @note		This function is used for setting the direction of all the pins
*		in the specified bank. The previous state of the pins is
*		not maintained.
*
*****************************************************************************/
void XGpioPs_SetDirection(XGpioPs *InstancePtr, u8 Bank, u32 Direction)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Bank < XGPIOPS_MAX_BANKS);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_DIRM_OFFSET, Direction);
}

/****************************************************************************/
/**
*
* Set the Direction of the specified pin.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Pin is the pin number to which the Data is to be written.
*		Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
* @param	Direction is the direction to be set for the specified pin.
*		Valid values are 0 for Input Direction, 1 for Output Direction.
*
* @return	None.
*
*****************************************************************************/
void XGpioPs_SetDirectionPin(XGpioPs *InstancePtr, int Pin, int Direction)
{
	u8 Bank;
	u8 PinNumber;
	u32 DirModeReg;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);
	Xil_AssertVoid((Direction == 0) || (Direction == 1));

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	DirModeReg = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				      ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				      XGPIOPS_DIRM_OFFSET);

	if (Direction) { /*  Output Direction */
		DirModeReg |= (1 << PinNumber);
	} else { /* Input Direction */
		DirModeReg &= ~ (1 << PinNumber);
	}

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			 ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
			 XGPIOPS_DIRM_OFFSET, DirModeReg);
}

/****************************************************************************/
/**
*
* Get the Direction of the pins of the specified GPIO Bank.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
*
* return	Returns a 32 bit mask of the Direction register. Bits with 0 are
*		in Input mode, bits with 1 are in Output Mode.
*
* @note		None.
*
*****************************************************************************/
u32 XGpioPs_GetDirection(XGpioPs *InstancePtr, u8 Bank)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Bank < XGPIOPS_MAX_BANKS);

	return XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				XGPIOPS_DIRM_OFFSET);
}

/****************************************************************************/
/**
*
* Get the Direction of the specified pin.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Pin is the pin number for which the Direction is to be
*		retrieved.
*		Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
*
* @return	Direction of the specified pin.
*		- 0 for Input Direction
*		- 1 for Output Direction
*
* @note		None.
*
*****************************************************************************/
int XGpioPs_GetDirectionPin(XGpioPs *InstancePtr, int Pin)
{
	u8 Bank;
	u8 PinNumber;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	return (XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				 ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				 XGPIOPS_DIRM_OFFSET) >> PinNumber) & 1;
}

/****************************************************************************/
/**
*
* Set the Output Enable of the pins of the specified GPIO Bank.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
* @param	OpEnable is the 32 bit mask of the Output Enables to be set for
*		all the pins in the Bank. The Output Enable of bits with 0 are
*		disabled, the Output Enable of bits with 1 are enabled.
*
* @return	None.
*
* @note		This function is used for setting the Output Enables of all the
*		pins in the specified bank. The previous state of the Output
*		Enables is not maintained.
*
*****************************************************************************/
void XGpioPs_SetOutputEnable(XGpioPs *InstancePtr, u8 Bank, u32 OpEnable)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Bank < XGPIOPS_MAX_BANKS);

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_OUTEN_OFFSET, OpEnable);
}

/****************************************************************************/
/**
*
* Set the Output Enable of the specified pin.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Pin is the pin number to which the Data is to be written.
*		Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
* @param	OpEnable specifies whether the Output Enable for the specified
*		pin should be enabled.
*		Valid values are 0 for Disabling Output Enable,
*		1 for Enabling Output Enable.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XGpioPs_SetOutputEnablePin(XGpioPs *InstancePtr, int Pin, int OpEnable)
{
	u8 Bank;
	u8 PinNumber;
	u32 OpEnableReg;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);
	Xil_AssertVoid((OpEnable == 0) || (OpEnable == 1));

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	OpEnableReg = XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				       ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				       XGPIOPS_OUTEN_OFFSET);

	if (OpEnable) { /*  Enable Output Enable */
		OpEnableReg |= (1 << PinNumber);
	} else { /* Disable Output Enable */
		OpEnableReg &= ~ (1 << PinNumber);
	}

	XGpioPs_WriteReg(InstancePtr->GpioConfig.BaseAddr,
			  ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
			  XGPIOPS_OUTEN_OFFSET, OpEnableReg);
}
/****************************************************************************/
/**
*
* Get the Output Enable status of the pins of the specified GPIO Bank.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Bank is the bank number of the GPIO to operate on.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
*
* return	Returns a a 32 bit mask of the Output Enable register.
*		Bits with 0 are in Disabled state, bits with 1 are in
*		Enabled State.
*
* @note		None.
*
*****************************************************************************/
u32 XGpioPs_GetOutputEnable(XGpioPs *InstancePtr, u8 Bank)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Bank < XGPIOPS_MAX_BANKS);

	return XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				XGPIOPS_OUTEN_OFFSET);
}

/****************************************************************************/
/**
*
* Get the Output Enable status of the specified pin.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
* @param	Pin is the pin number for which the Output Enable status is to
*		be retrieved.
*		Valid values are 0 to XGPIOPS_DEVICE_MAX_PIN_NUM - 1.
*
* @return	Output Enable of the specified pin.
*		- 0 if Output Enable is disabled for this pin
*		- 1 if Output Enable is enabled for this pin
*
* @note		None.
*
*****************************************************************************/
int XGpioPs_GetOutputEnablePin(XGpioPs *InstancePtr, int Pin)
{
	u8 Bank;
	u8 PinNumber;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Pin < XGPIOPS_DEVICE_MAX_PIN_NUM);

	/*
	 * Get the Bank number and Pin number within the bank.
	 */
	XGpioPs_GetBankPin(Pin, &Bank, &PinNumber);

	return (XGpioPs_ReadReg(InstancePtr->GpioConfig.BaseAddr,
				 ((Bank) * XGPIOPS_REG_MASK_OFFSET) +
				 XGPIOPS_OUTEN_OFFSET) >> PinNumber) & 1;
}

/****************************************************************************/
/*
*
* Get the Bank number and the Pin number in the Bank, for the given PinNumber
* in the GPIO device.
*
* @param	PinNumber is the Pin number in the GPIO device.
* @param	BankNumber returns the Bank in which this GPIO pin is present.
*		Valid values are 0 to XGPIOPS_MAX_BANKS - 1.
* @param	PinNumberInBank returns the Pin Number within the Bank.
*
* return	None;
*
* @note		None.
*
*****************************************************************************/
void XGpioPs_GetBankPin(u8 PinNumber,	u8 *BankNumber, u8 *PinNumberInBank)
{
	for (*BankNumber = 0; *BankNumber < 4; (*BankNumber)++)
		if (PinNumber <= XGpioPsPinTable[*BankNumber])
			break;

	if (*BankNumber == 0) {
		*PinNumberInBank = PinNumber;
	} else {
		*PinNumberInBank = PinNumber %
					(XGpioPsPinTable[*BankNumber - 1] + 1);
	}
}
/** @} */
