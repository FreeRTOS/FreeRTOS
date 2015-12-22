/******************************************************************************
*
* Copyright (C) 2014 Xilinx, Inc.  All rights reserved.
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
* @file xqspipsu_options.c
*
* This file implements funcitons to configure the QSPIPSU component,
* specifically some optional settings, clock and flash related information.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- -----------------------------------------------
* 1.0   hk  08/21/14 First release
*       sk  03/13/15 Added IO mode support.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xqspipsu.h"

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
	{XQSPIPSU_CLK_ACTIVE_LOW_OPTION, XQSPIPSU_CFG_CLK_POL_MASK},
	{XQSPIPSU_CLK_PHASE_1_OPTION, XQSPIPSU_CFG_CLK_PHA_MASK},
	{XQSPIPSU_MANUAL_START_OPTION, XQSPIPSU_CFG_GEN_FIFO_START_MODE_MASK},
};

#define XQSPIPSU_NUM_OPTIONS	(sizeof(OptionsTable) / sizeof(OptionsMap))

/*****************************************************************************/
/**
*
* This function sets the options for the QSPIPSU device driver.The options
* control how the device behaves relative to the QSPIPSU bus. The device must be
* idle rather than busy transferring data before setting these device options.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	Options contains the specified options to be set. This is a bit
*		mask where a 1 indicates the option should be turned ON and
*		a 0 indicates no action. One or more bit values may be
*		contained in the mask. See the bit definitions named
*		XQSPIPSU_*_OPTIONS in the file xqspipsu.h.
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
int XQspiPsu_SetOptions(XQspiPsu *InstancePtr, u32 Options)
{
	u32 ConfigReg;
	unsigned int Index;
	u32 QspiPsuOptions;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Do not allow to modify the Control Register while a transfer is in
	 * progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy) {
		return XST_DEVICE_BUSY;
	}

	ConfigReg = XQspiPsu_ReadReg(InstancePtr->Config.BaseAddress,
				      XQSPIPSU_CFG_OFFSET);

	/*
	 * Loop through the options table, turning the option on
	 * depending on whether the bit is set in the incoming options flag.
	 */
	for (Index = 0; Index < XQSPIPSU_NUM_OPTIONS; Index++) {
		if (Options & OptionsTable[Index].Option) {
			/* Turn it on */
			ConfigReg |= OptionsTable[Index].Mask;
		}
	}

	/*
	 * Now write the control register. Leave it to the upper layers
	 * to restart the device.
	 */
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress, XQSPIPSU_CFG_OFFSET,
			 ConfigReg);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function resets the options for the QSPIPSU device driver.The options
* control how the device behaves relative to the QSPIPSU bus. The device must be
* idle rather than busy transferring data before setting these device options.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	Options contains the specified options to be set. This is a bit
*		mask where a 1 indicates the option should be turned OFF and
*		a 0 indicates no action. One or more bit values may be
*		contained in the mask. See the bit definitions named
*		XQSPIPSU_*_OPTIONS in the file xqspipsu.h.
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
int XQspiPsu_ClearOptions(XQspiPsu *InstancePtr, u32 Options)
{
	u32 ConfigReg;
	unsigned int Index;
	u32 QspiPsuOptions;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Do not allow to modify the Control Register while a transfer is in
	 * progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy) {
		return XST_DEVICE_BUSY;
	}

	ConfigReg = XQspiPsu_ReadReg(InstancePtr->Config.BaseAddress,
				      XQSPIPSU_CFG_OFFSET);

	/*
	 * Loop through the options table, turning the option on
	 * depending on whether the bit is set in the incoming options flag.
	 */
	for (Index = 0; Index < XQSPIPSU_NUM_OPTIONS; Index++) {
		if (Options & OptionsTable[Index].Option) {
			/* Turn it off */
			ConfigReg &= ~OptionsTable[Index].Mask;
		}
	}

	/*
	 * Now write the control register. Leave it to the upper layers
	 * to restart the device.
	 */
	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress, XQSPIPSU_CFG_OFFSET,
			 ConfigReg);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function gets the options for the QSPIPSU device. The options control how
* the device behaves relative to the QSPIPSU bus.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
*
* @return
*
* Options contains the specified options currently set. This is a bit value
* where a 1 means the option is on, and a 0 means the option is off.
* See the bit definitions named XQSPIPSU_*_OPTIONS in file xqspipsu.h.
*
* @note		None.
*
******************************************************************************/
u32 XQspiPsu_GetOptions(XQspiPsu *InstancePtr)
{
	u32 OptionsFlag = 0;
	u32 ConfigReg;
	unsigned int Index;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Get the current options from QSPIPSU configuration register.
	 */
	ConfigReg = XQspiPsu_ReadReg(InstancePtr->Config.BaseAddress,
				      XQSPIPSU_CFG_OFFSET);

	/* Loop through the options table to grab options */
	for (Index = 0; Index < XQSPIPSU_NUM_OPTIONS; Index++) {
		if (ConfigReg & OptionsTable[Index].Mask) {
			OptionsFlag |= OptionsTable[Index].Option;
		}
	}

	return OptionsFlag;
}

/*****************************************************************************/
/**
*
* Configures the clock according to the prescaler passed.
*
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	Prescaler - clock prescaler to be set.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_DEVICE_IS_STARTED if the device is already started.
*		It must be stopped to re-initialize.
*
* @note		None.
*
******************************************************************************/
int XQspiPsu_SetClkPrescaler(XQspiPsu *InstancePtr, u8 Prescaler)
{
	u32 ConfigReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Prescaler <= XQSPIPSU_CR_PRESC_MAXIMUM);

	/*
	 * Do not allow the slave select to change while a transfer is in
	 * progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy) {
		return XST_DEVICE_BUSY;
	}

	/*
	 * Read the configuration register, mask out the relevant bits, and set
	 * them with the shifted value passed into the function. Write the
	 * results back to the configuration register.
	 */
	ConfigReg = XQspiPsu_ReadReg(InstancePtr->Config.BaseAddress,
				      XQSPIPSU_CFG_OFFSET);

	ConfigReg &= ~XQSPIPSU_CFG_BAUD_RATE_DIV_MASK;
	ConfigReg |= (u32) (Prescaler & XQSPIPSU_CR_PRESC_MAXIMUM) <<
			    XQSPIPSU_CFG_BAUD_RATE_DIV_SHIFT;

	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress,
			  XQSPIPSU_CFG_OFFSET, ConfigReg);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This funciton should be used to tell the QSPIPSU driver the HW flash
* configuration being used. This API should be called atleast once in the
* application. If desired, it can be called multiple times when switching
* between communicating to different flahs devices/using different configs.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	FlashCS - Flash Chip Select.
* @param	FlashBus - Flash Bus (Upper, Lower or Both).
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_DEVICE_IS_STARTED if the device is already started.
*		It must be stopped to re-initialize.
*
* @note		If this funciton is not called atleast once in the application,
*		the driver assumes there is a single flash connected to the
*		lower bus and CS line.
*
******************************************************************************/
void XQspiPsu_SelectFlash(XQspiPsu *InstancePtr, u8 FlashCS, u8 FlashBus)
{
	Xil_AssertVoid(InstancePtr != NULL);

	/*
	 * Bus and CS lines selected here will be updated in the instance and
	 * used for subsequent GENFIFO entries during transfer.
	 */

	/* Choose slave select line */
	switch (FlashCS) {
		case XQSPIPSU_SELECT_FLASH_CS_BOTH:
			InstancePtr->GenFifoCS = XQSPIPSU_GENFIFO_CS_LOWER |
						XQSPIPSU_GENFIFO_CS_UPPER;
			break;
		case XQSPIPSU_SELECT_FLASH_CS_UPPER:
			InstancePtr->GenFifoCS = XQSPIPSU_GENFIFO_CS_UPPER;
			break;
		case XQSPIPSU_SELECT_FLASH_CS_LOWER:
		default:
			InstancePtr->GenFifoCS = XQSPIPSU_GENFIFO_CS_LOWER;
	}

	/* Choose bus */
	switch (FlashBus) {
		case XQSPIPSU_SELECT_FLASH_BUS_BOTH:
			InstancePtr->GenFifoBus = XQSPIPSU_GENFIFO_BUS_LOWER |
						XQSPIPSU_GENFIFO_BUS_UPPER;
			break;
		case XQSPIPSU_SELECT_FLASH_BUS_UPPER:
			InstancePtr->GenFifoBus = XQSPIPSU_GENFIFO_BUS_UPPER;
			break;
		case XQSPIPSU_SELECT_FLASH_BUS_LOWER:
		default:
			InstancePtr->GenFifoBus = XQSPIPSU_GENFIFO_BUS_LOWER;
	}
}

/*****************************************************************************/
/**
*
* This function sets the Read mode for the QSPIPSU device driver.The device
* must be idle rather than busy transferring data before setting Read mode
* options.
*
* @param	InstancePtr is a pointer to the XQspiPsu instance.
* @param	Mode contains the specified Mode to be set. See the
* 		bit definitions named XQSPIPSU_READMODE_* in the file xqspipsu.h.
*
* @return
*		- XST_SUCCESS if options are successfully set.
*		- XST_DEVICE_BUSY if the device is currently transferring data.
*		The transfer must complete or be aborted before setting Mode.
*
* @note
* This function is not thread-safe.
*
******************************************************************************/
int XQspiPsu_SetReadMode(XQspiPsu *InstancePtr, u32 Mode)
{
	u32 ConfigReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Do not allow to modify the Control Register while a transfer is in
	 * progress. Not thread-safe.
	 */
	if (InstancePtr->IsBusy) {
		return XST_DEVICE_BUSY;
	}

	InstancePtr->ReadMode = Mode;

	ConfigReg = XQspiPsu_ReadReg(InstancePtr->Config.BaseAddress,
				      XQSPIPSU_CFG_OFFSET);

	if (Mode == XQSPIPSU_READMODE_DMA) {
		ConfigReg &= ~XQSPIPSU_CFG_MODE_EN_MASK;
		ConfigReg |= XQSPIPSU_CFG_MODE_EN_DMA_MASK;
	} else {
		ConfigReg &= ~XQSPIPSU_CFG_MODE_EN_MASK;
	}

	XQspiPsu_WriteReg(InstancePtr->Config.BaseAddress, XQSPIPSU_CFG_OFFSET,
			 ConfigReg);

	return XST_SUCCESS;
}
