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
* @file xspips_options.c
*
* Contains functions for the configuration of the XSpiPs driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- -----------------------------------------------
* 1.00  drg/jz 01/25/10 First release
* 1.00	sdm    10/25/11 Removed the Divide by 2 in the SPI Clock Prescaler
*			options as this is not supported in the device
* 1.04a	sg     01/30/13 Added XSPIPS_MANUAL_START_OPTION. SetDelays and
*			GetDelays API's include DelayNss parameter.
* 1.05a hk 	   26/04/13 Added disable and enable in XSpiPs_SetOptions when
*				CPOL/CPHA bits are set/reset. Fix for CR#707669.
* 3.00  kvn    02/13/15 Modified code for MISRA-C:2012 compliance.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xspips.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/

/*
 * Create the table of options which are processed to get/set the device
 * options. These options are table driven to allow easy maintenance and
 * expansion of the options.
 */
typedef struct {
	u32 Option;
	u32 Mask;
} OptionsMap;

static OptionsMap OptionsTable[] = {
	{XSPIPS_MASTER_OPTION, XSPIPS_CR_MSTREN_MASK},
	{XSPIPS_CLK_ACTIVE_LOW_OPTION, XSPIPS_CR_CPOL_MASK},
	{XSPIPS_CLK_PHASE_1_OPTION, XSPIPS_CR_CPHA_MASK},
	{XSPIPS_DECODE_SSELECT_OPTION, XSPIPS_CR_SSDECEN_MASK},
	{XSPIPS_FORCE_SSELECT_OPTION, XSPIPS_CR_SSFORCE_MASK},
	{XSPIPS_MANUAL_START_OPTION, XSPIPS_CR_MANSTRTEN_MASK}
};

#define XSPIPS_NUM_OPTIONS	(sizeof(OptionsTable) / sizeof(OptionsMap))

/*****************************************************************************/
/**
*
* This function sets the options for the SPI device driver. The options control
* how the device behaves relative to the SPI bus. The device must be idle
* rather than busy transferring data before setting these device options.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
* @param	Options contains the specified options to be set. This is a bit
*		mask where a 1 means to turn the option on, and a 0 means to
*		turn the option off. One or more bit values may be contained in
*		the mask. See the bit definitions named XSPIPS_*_OPTIONS in the
*		file xspips.h.
*
* @return
*		- XST_SUCCESS if options are successfully set.
*		- XST_DEVICE_BUSY if the device is currently transferring data.
*		The transfer must complete or be aborted before setting options.
*
* @note
* This function is not thread-safe.
*
******************************************************************************/
s32 XSpiPs_SetOptions(XSpiPs *InstancePtr, u32 Options)
{
	u32 ConfigReg;
	u32 Index;
	u32 CurrentConfigReg;
	s32 Status;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Do not allow the slave select to change while a transfer is in
	 * progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy == TRUE) {
		Status = (s32)XST_DEVICE_BUSY;
	} else {

		ConfigReg = XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
					 XSPIPS_CR_OFFSET);

		CurrentConfigReg = ConfigReg;

		/*
		 * Loop through the options table, turning the option on or off
		 * depending on whether the bit is set in the incoming options flag.
		 */
		for (Index = 0U; Index < XSPIPS_NUM_OPTIONS; Index++) {
			if ((Options & OptionsTable[Index].Option) != (u32)0U) {
				/* Turn it on */
				ConfigReg |= OptionsTable[Index].Mask;
			}
			else {
				/* Turn it off */
				ConfigReg &= ~(OptionsTable[Index].Mask);
			}
		}


		/*
		 * If CPOL-CPHA bits are toggled from previous state,
		 * disable before writing the configuration register and then enable.
		 */
		if( ((CurrentConfigReg & XSPIPS_CR_CPOL_MASK) !=
			(ConfigReg & XSPIPS_CR_CPOL_MASK)) ||
			((CurrentConfigReg & XSPIPS_CR_CPHA_MASK) !=
			(ConfigReg & XSPIPS_CR_CPHA_MASK)) ) {
				XSpiPs_Disable(InstancePtr);
			}

		/*
		 * Now write the Config register. Leave it to the upper layers
		 * to restart the device.
		 */
		XSpiPs_WriteReg(InstancePtr->Config.BaseAddress,
					XSPIPS_CR_OFFSET, ConfigReg);

		/*
		 * Enable
		 */
		if( ((CurrentConfigReg & XSPIPS_CR_CPOL_MASK) !=
			(ConfigReg & XSPIPS_CR_CPOL_MASK)) ||
			((CurrentConfigReg & XSPIPS_CR_CPHA_MASK) !=
			(ConfigReg & XSPIPS_CR_CPHA_MASK)) ) {
				XSpiPs_Enable(InstancePtr);
			}

		Status = (s32)XST_SUCCESS;
	}
	return Status;
}

/*****************************************************************************/
/**
*
* This function gets the options for the SPI device. The options control how
* the device behaves relative to the SPI bus.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return
*
* Options contains the specified options currently set. This is a bit value
* where a 1 means the option is on, and a 0 means the option is off.
* See the bit definitions named XSPIPS_*_OPTIONS in file xspips.h.
*
* @note		None.
*
******************************************************************************/
u32 XSpiPs_GetOptions(XSpiPs *InstancePtr)
{
	u32 OptionsFlag = 0U;
	u32 ConfigReg;
	u32 Index;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Get the current options
	 */
	ConfigReg =
		XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
				 XSPIPS_CR_OFFSET);

	/*
	 * Loop through the options table to grab options
	 */
	for (Index = 0; Index < XSPIPS_NUM_OPTIONS; Index++) {
		if (ConfigReg & OptionsTable[Index].Mask) {
			OptionsFlag |= OptionsTable[Index].Option;
		}
	}

	return OptionsFlag;
}

/*****************************************************************************/
/**
*
* This function sets the clock prescaler for an SPI device. The device
* must be idle rather than busy transferring data before setting these device
* options.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
* @param	Prescaler is the value that determine how much the clock should
*		be divided by. Use the XSPIPS_CLK_PRESCALE_* constants defined
*		in xspips.h for this setting.
*
* @return
*		- XST_SUCCESS if options are successfully set.
*		- XST_DEVICE_BUSY if the device is currently transferring data.
*		The transfer must complete or be aborted before setting options.
*
* @note
* This function is not thread-safe.
*
******************************************************************************/
s32 XSpiPs_SetClkPrescaler(XSpiPs *InstancePtr, u8 Prescaler)
{
	u32 ConfigReg;
	s32 Status;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((Prescaler > 0U) && (Prescaler <= XSPIPS_CR_PRESC_MAXIMUM));

	/*
	 * Do not allow the prescaler to be changed while a transfer is in
	 * progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy == TRUE) {
		Status = (s32)XST_DEVICE_BUSY;
	} else {

		/*
		 * Read the Config register, mask out the interesting bits, and set
		 * them with the shifted value passed into the function. Write the
		 * results back to the Config register.
		 */
		ConfigReg = XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
					 XSPIPS_CR_OFFSET);

		ConfigReg &= (u32)(~XSPIPS_CR_PRESC_MASK);
		ConfigReg |= (u32) ((u32)Prescaler & (u32)XSPIPS_CR_PRESC_MAXIMUM) <<
			XSPIPS_CR_PRESC_SHIFT;

		XSpiPs_WriteReg(InstancePtr->Config.BaseAddress,
				XSPIPS_CR_OFFSET,
				ConfigReg);

		Status = (s32)XST_SUCCESS;
	}
	return Status;
}

/*****************************************************************************/
/**
*
* This function gets the clock prescaler of an SPI device.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return	The prescaler value.
*
* @note		None.
*
*
******************************************************************************/
u8 XSpiPs_GetClkPrescaler(XSpiPs *InstancePtr)
{
	u32 ConfigReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	ConfigReg = XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
			XSPIPS_CR_OFFSET);

	ConfigReg &= XSPIPS_CR_PRESC_MASK;

	return (u8)(ConfigReg >> XSPIPS_CR_PRESC_SHIFT);

}

/*****************************************************************************/
/**
*
* This function sets the delay register for the SPI device driver.
* The delay register controls the Delay Between Transfers, Delay After
* Transfers, and the Delay Initially. The default value is 0x0. The range of
* each delay value is 0-255.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
* @param	DelayNss is the delay for which the chip select outputs will
*		be de-asserted between words when CPHA=0.
* @param	DelayBtwn is the delay between one Slave Select being
*		de-activated and the activation of another slave. The delay is
*		the number of master clock periods given by DelayBtwn + 2.
* @param	DelayAfter define the delay between the last bit of the current
*		byte transfer and the first bit of the next byte transfer.
*		The delay in number of master clock periods is given as:
*		CPHA=0:DelayInit+DelayAfter+3
*		CPHA=1:DelayAfter+1
* @param	DelayInit is the delay between asserting the slave select signal
*		and the first bit transfer. The delay int number of master clock
*		periods is DelayInit+1.
*
* @return
*		- XST_SUCCESS if delays are successfully set.
*		- XST_DEVICE_BUSY if the device is currently transferring data.
*		The transfer must complete or be aborted before setting options.
*
* @note		None.
*
******************************************************************************/
s32 XSpiPs_SetDelays(XSpiPs *InstancePtr, u8 DelayNss, u8 DelayBtwn,
			 u8 DelayAfter, u8 DelayInit)
{
	u32 DelayRegister;
	s32 Status;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Do not allow the delays to change while a transfer is in
	 * progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy == TRUE) {
		Status = (s32)XST_DEVICE_BUSY;
	} else {

		/* Shift, Mask and OR the values to build the register settings */
		DelayRegister = (u32) DelayNss << XSPIPS_DR_NSS_SHIFT;
		DelayRegister |= (u32) DelayBtwn << XSPIPS_DR_BTWN_SHIFT;
		DelayRegister |= (u32) DelayAfter << XSPIPS_DR_AFTER_SHIFT;
		DelayRegister |= (u32) DelayInit;

		XSpiPs_WriteReg(InstancePtr->Config.BaseAddress,
				XSPIPS_DR_OFFSET, DelayRegister);

		Status = (s32)XST_SUCCESS;
	}
	return Status;
}

/*****************************************************************************/
/**
*
* This function gets the delay settings for an SPI device.
* The delay register controls the Delay Between Transfers, Delay After
* Transfers, and the Delay Initially. The default value is 0x0.
*
* @param	InstancePtr is a pointer to the XSpiPs instance.
* @param	DelayNss is a pointer to the delay for which the chip select
*		outputs will be de-asserted between words when CPHA=0.
* @param	DelayBtwn is a pointer to the Delay Between transfers value.
*		This is a return parameter.
* @param	DelayAfter is a pointer to the Delay After transfer value.
*		This is a return parameter.
* @param	DelayInit is a pointer to the Delay Initially value. This is
*		a return parameter.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XSpiPs_GetDelays(XSpiPs *InstancePtr,u8 *DelayNss, u8 *DelayBtwn,
			u8 *DelayAfter, u8 *DelayInit)
{
	u32 DelayRegister;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	DelayRegister = XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
					XSPIPS_DR_OFFSET);

	*DelayInit = (u8)(DelayRegister & XSPIPS_DR_INIT_MASK);

	*DelayAfter = (u8)((DelayRegister & XSPIPS_DR_AFTER_MASK) >>
				 XSPIPS_DR_AFTER_SHIFT);

	*DelayBtwn = (u8)((DelayRegister & XSPIPS_DR_BTWN_MASK) >>
				XSPIPS_DR_BTWN_SHIFT);

	*DelayNss = (u8)((DelayRegister & XSPIPS_DR_NSS_MASK) >>
				XSPIPS_DR_NSS_SHIFT);

}
