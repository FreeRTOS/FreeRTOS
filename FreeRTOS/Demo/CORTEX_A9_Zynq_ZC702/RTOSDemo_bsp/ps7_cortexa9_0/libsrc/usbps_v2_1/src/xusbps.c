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
/******************************************************************************/
/**
 * @file xusbps.c
 *
 * The XUsbPs driver. Functions in this file are the minimum required
 * functions for this driver. See xusbps.h for a detailed description of the
 * driver.
 *
 * @note	None.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- --------------------------------------------------------
 * 1.00a jz  10/10/10 First release
 * 2.1   kpc 04/28/14 Removed ununsed functions
 * </pre>
 ******************************************************************************/

/***************************** Include Files **********************************/
#include <stdio.h>
#include "xusbps.h"

/************************** Constant Definitions ******************************/

/**************************** Type Definitions ********************************/

/***************** Macros (Inline Functions) Definitions **********************/

/************************** Variable Definitions ******************************/

/************************** Function Prototypes *******************************/

/*****************************************************************************/
/**
*
* This function initializes a XUsbPs instance/driver.
*
* The initialization entails:
* - Initialize all members of the XUsbPs structure.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	ConfigPtr is a pointer to a XUsbPs_Config configuration
*		structure. This structure will contain the requested
*		configuration for the device. Typically, this is a local
*		structure and the content of which will be copied into the
*		configuration structure within XUsbPs.
* @param	VirtBaseAddress is the base address of the device. For systems
*		with virtual memory, this address must be the virtual address
*		of the device.
* 		For systems that do not support virtual memory this address
* 		should be the physical address of the device. For backwards
* 		compatibilty NULL may be passed in systems that do not support
* 		virtual memory (deprecated).
*
* @return
*		- XST_SUCCESS no errors occured.
*		- XST_FAILURE an error occured during initialization.
*
* @note
*		After calling XUsbPs_CfgInitialize() the controller
*		IS NOT READY for use. Before the controller can be used its
*		DEVICE parameters must be configured. See xusbps.h
*		for details.
*
******************************************************************************/
int XUsbPs_CfgInitialize(XUsbPs *InstancePtr,
			  const XUsbPs_Config *ConfigPtr, u32 VirtBaseAddress)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr   != NULL);

	/* Copy the config structure. */
	InstancePtr->Config = *ConfigPtr;

	/* Check if the user provided a non-NULL base address. If so, we have
	 * to overwrite the base address in the configuration structure.
	 */
	if (0 != VirtBaseAddress) {
		InstancePtr->Config.BaseAddress = VirtBaseAddress;
	}

	/* Initialize the XUsbPs structure to default values. */
	InstancePtr->CurrentAltSetting	= XUSBPS_DEFAULT_ALT_SETTING;

	InstancePtr->HandlerFunc	= NULL;

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function performs device reset, device is stopped at the end.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
*
* @return	None.
*
* @note 	None.
*
******************************************************************************/
void XUsbPs_DeviceReset(XUsbPs *InstancePtr)
{
	int Timeout;

	/* Clear all setup token semaphores by reading the
	 * XUSBPS_EPSTAT_OFFSET register and writing its value back to
	 * itself.
	 */
	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress, XUSBPS_EPSTAT_OFFSET,
		XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
			XUSBPS_EPSTAT_OFFSET));

	/* Clear all the endpoint complete status bits by reading the
	 * XUSBPS_EPCOMPL_OFFSET register and writings its value back
	 * to itself.
	 */
	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress, XUSBPS_EPCOMPL_OFFSET,
		XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
			XUSBPS_EPCOMPL_OFFSET));

	/* Cancel all endpoint prime status by waiting until all bits
	 * in XUSBPS_EPPRIME_OFFSET are 0 and then writing 0xFFFFFFFF
	 * to XUSBPS_EPFLUSH_OFFSET.
	 *
	 * Avoid hanging here by using a Timeout counter...
	 */
	Timeout = XUSBPS_TIMEOUT_COUNTER;
	while ((XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
				XUSBPS_EPPRIME_OFFSET) &
				XUSBPS_EP_ALL_MASK) && --Timeout) {
		/* NOP */
	}
	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress,
				XUSBPS_EPFLUSH_OFFSET, 0xFFFFFFFF);

	XUsbPs_Stop(InstancePtr);

	/* Write to CR register for controller reset */
 	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress, XUSBPS_CMD_OFFSET,
		XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
				XUSBPS_CMD_OFFSET) | XUSBPS_CMD_RST_MASK);

	/* Wait for reset to finish, hardware clears the reset bit once done  */
	Timeout = 1000000;
	while((XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
				XUSBPS_CMD_OFFSET) &
				XUSBPS_CMD_RST_MASK) && --Timeout) {
		/* NOP */
	}
}
/*****************************************************************************/
/**
*
* This function resets the USB device. All the configuration registers are
* reset to their default values. The function waits until the reset operation
* is complete or for a certain duration within which the reset operation is
* expected to be completed.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
*
* @return
*		- XST_SUCCESS Reset operation completed successfully.
*		- XST_FAILURE Reset operation timed out.
*
* @note 	None.
*
******************************************************************************/
int XUsbPs_Reset(XUsbPs *InstancePtr)
{
	int Timeout;

	Xil_AssertNonvoid(InstancePtr != NULL);

	/* Write a 1 to the RESET bit. The RESET bit is cleared by HW once the
	 * RESET is complete.
	 *
	 * We are going to wait for the RESET bit to clear before we return
	 * from this function. Unfortunately we do not have timers available at
	 * this point to determine when we should report a Timeout.
	 *
	 * However, by using a large number for the poll loop we can assume
	 * that the polling operation will take longer than the expected time
	 * the HW needs to RESET. If the poll loop expires we can assume a
	 * Timeout. The drawback is that on a slow system (and even on a fast
	 * system) this can lead to _very_ long Timeout periods.
	 */
	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress,
				XUSBPS_CMD_OFFSET, XUSBPS_CMD_RST_MASK);


	/* Wait for the RESET bit to be cleared by HW. */
	Timeout = XUSBPS_TIMEOUT_COUNTER;
	while ((XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
				XUSBPS_CMD_OFFSET) &
				XUSBPS_CMD_RST_MASK) && --Timeout) {
		/* NOP */
	}

	if (0 == Timeout) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
 * USB Suspend
 *
 * In order to conserve power, USB devices automatically enter the suspended
 * state when the device has observed no bus traffic for a specified period.
 * When suspended, the USB device maintains any internal status, including its
 * address and configuration. Attached devices must be prepared to suspend at
 * any time they are powered, regardless of if they have been assigned a
 * non-default address, are configured, or neither. Bus activity may cease due
 * to the host entering a suspend mode of its own. In addition, a USB device
 * shall also enter the suspended state when the hub port it is attached to is
 * disabled.
 *
 * A USB device exits suspend mode when there is bus activity. A USB device may
 * also request the host to exit suspend mode or selective suspend by using
 * electrical signaling to indicate remote wakeup. The ability of a device to
 * signal remote wakeup is optional. If the USB device is capable of remote
 * wakeup signaling, the device must support the ability of the host to enable
 * and disable this capability. When the device is reset, remote wakeup
 * signaling must be disabled.
 *
 * @param	InstancePtr is a pointer to XUsbPs instance of the controller.
 *
 * @return
 *		- XST_SUCCESS if the USB device has entered Suspend mode
 *		successfully
 *		- XST_FAILURE on any error
 *
 * @note 	None.
 *
 ******************************************************************************/
int XUsbPs_Suspend(const XUsbPs *InstancePtr)
{
	(void) InstancePtr;

	return XST_SUCCESS;
}


/*****************************************************************************/
/**
* USB Resume
*
 If the USB controller is suspended, its operation is resumed when any
* non-idle signaling is received on its upstream facing port.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
*
* @return
*		- XST_SUCCESS if the USB device has Resumed successfully
*		- XST_FAILURE on any error
*
* @note 	None.
*
******************************************************************************/
int XUsbPs_Resume(const XUsbPs *InstancePtr)
{
	(void) InstancePtr;
	return XST_SUCCESS;
}


/*****************************************************************************/
/**
* USB Assert Resume
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
*
* @return
*		- XST_SUCCESS if the USB device has Resumed successfully
*		- XST_FAILURE on any error
*
* @note 	None.
*
******************************************************************************/

int XUsbPs_RequestHostResume(const XUsbPs *InstancePtr)
{
	(void) InstancePtr;
	return XST_SUCCESS;
}

/****************************************************************************/
/**
* This functions sets the controller's DEVICE address. It also sets the
* advance bit so the controller will wait for the next IN-ACK before the new
* address takes effect.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	Address is the Address of the device.
*
* @return
*		- XST_SUCCESS: Address set successfully.
*		- XST_FAILURE: An error occured.
*		- XST_INVALID_PARAM: Invalid parameter passed, e.g. address
*		value too big.
*
* @note 	None.
*
*****************************************************************************/
int XUsbPs_SetDeviceAddress(XUsbPs *InstancePtr, u8 Address)
{
	Xil_AssertNonvoid(InstancePtr != NULL);

	/* Check address range validity. */
	if (Address > XUSBPS_DEVICEADDR_MAX) {
		return XST_INVALID_PARAM;
	}

	/* Set the address register with the Address value provided. Also set
	 * the Address Advance Bit. This will cause the address to be set only
	 * after an IN occured and has been ACKed on the endpoint.
	 */
	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress,
				XUSBPS_DEVICEADDR_OFFSET,
			 	(Address << XUSBPS_DEVICEADDR_ADDR_SHIFT) |
			 	XUSBPS_DEVICEADDR_DEVICEAADV_MASK);

	return XST_SUCCESS;
}

