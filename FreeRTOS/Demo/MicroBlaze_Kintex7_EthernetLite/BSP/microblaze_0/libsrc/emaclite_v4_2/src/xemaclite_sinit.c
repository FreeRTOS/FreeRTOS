/******************************************************************************
*
* Copyright (C) 2007 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xemaclite_sinit.c
* @addtogroup emaclite_v4_1
* @{
*
* This file contains the implementation of the XEmacLite driver's static
* initialization functionality.
*
* @note		None.
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.12a sv   11/28/07 First release
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xparameters.h"
#include "xemaclite.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/
extern XEmacLite_Config XEmacLite_ConfigTable[];

/*****************************************************************************/
/**
*
* Lookup the device configuration based on the unique device ID.  The table
* XEmacLite_ConfigTable contains the configuration info for each device in the
* system.
*
* @param 	DeviceId is the unique device ID of the device being looked up.
*
* @return	A pointer to the configuration table entry corresponding to the
*		given device ID, or NULL if no match is found.
*
* @note		None.
*
******************************************************************************/
XEmacLite_Config *XEmacLite_LookupConfig(u16 DeviceId)
{
	XEmacLite_Config *CfgPtr = NULL;
	u32 Index;

	for (Index = 0; Index < XPAR_XEMACLITE_NUM_INSTANCES; Index++) {
		if (XEmacLite_ConfigTable[Index].DeviceId == DeviceId) {
			CfgPtr = &XEmacLite_ConfigTable[Index];
			break;
		}
	}

	return CfgPtr;
}


/*****************************************************************************/
/**
*
* Initialize a specific XEmacLite instance/driver.  The initialization entails:
* - Initialize fields of the XEmacLite instance structure.
*
* The driver defaults to polled mode operation.
*
* @param	InstancePtr is a pointer to the XEmacLite instance.
* @param 	DeviceId is the unique id of the device controlled by this
*		XEmacLite instance.  Passing in a device id associates the
*		generic XEmacLite instance to a specific device, as chosen by
*		the caller or application developer.
*
* @return
* 		- XST_SUCCESS if initialization was successful.
* 		- XST_DEVICE_NOT_FOUND/XST_FAILURE if device configuration
*		information was not found for a device with the supplied
*		device ID.
*
* @note		None
*
******************************************************************************/
int XEmacLite_Initialize(XEmacLite *InstancePtr, u16 DeviceId)
{
	int Status;
	XEmacLite_Config *EmacLiteConfigPtr;/* Pointer to Configuration data. */

	/*
	 * Verify that each of the inputs are valid.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);

	/*
	 * Lookup the device configuration in the configuration table. Use this
	 * configuration info down below when initializing this driver.
	 */
	EmacLiteConfigPtr = XEmacLite_LookupConfig(DeviceId);
	if (EmacLiteConfigPtr == NULL) {
		return XST_DEVICE_NOT_FOUND;
	}

	Status = XEmacLite_CfgInitialize(InstancePtr,
					 EmacLiteConfigPtr,
					 EmacLiteConfigPtr->BaseAddress);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}


/** @} */
