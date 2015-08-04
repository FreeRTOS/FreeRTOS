/******************************************************************************
*
* Copyright (C) 2002 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xintc_options.c
*
* Contains option functions for the XIntc driver. These functions allow the
* user to configure an instance of the XIntc driver.  This file requires other
* files of the component to be linked in also.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------------
* 1.00b jhl  02/21/02 First release
* 1.00c rpm  10/17/03 New release. Support the relocation of the options flag
*                     from the instance structure to the xintc_g.c
*                     configuration table.
* 1.10c mta  03/21/07 Updated to new coding style
* 2.00a ktn  10/20/09 Updated to use HAL Processor APIs
* 2.06a bss  01/28/13 To support Cascade mode:
*		      Modified XIntc_SetOptions API.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xintc.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
* Set the options for the interrupt controller driver. In Cascade mode same
* Option is set to Slave controllers.
*
* @param	InstancePtr is a pointer to the XIntc instance to be worked on.
* @param	Options to be set. The available options are described in
*		xintc.h.
*
* @return
* 		- XST_SUCCESS if the options were set successfully
* 		- XST_INVALID_PARAM if the specified option was not valid
*
* @note		None.
*
****************************************************************************/
int XIntc_SetOptions(XIntc * InstancePtr, u32 Options)
{
	XIntc_Config *CfgPtr;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Make sure option request is valid
	 */
	if ((Options == XIN_SVC_SGL_ISR_OPTION) ||
	    (Options == XIN_SVC_ALL_ISRS_OPTION)) {
		InstancePtr->CfgPtr->Options = Options;
		/* If Cascade mode set the option for all Slaves */
		if (InstancePtr->CfgPtr->IntcType != XIN_INTC_NOCASCADE) {
			int Index;
			for (Index = 1; Index <= XPAR_XINTC_NUM_INSTANCES - 1;
								Index++) {
				CfgPtr = XIntc_LookupConfig(Index);
				CfgPtr->Options = Options;
			}
		}
		return XST_SUCCESS;
	}
	else {
		return XST_INVALID_PARAM;
	}
}

/*****************************************************************************/
/**
*
* Return the currently set options.
*
* @param	InstancePtr is a pointer to the XIntc instance to be worked on.
*
* @return	The currently set options. The options are described in xintc.h.
*
* @note		None.
*
****************************************************************************/
u32 XIntc_GetOptions(XIntc * InstancePtr)
{
	/*
	 * Assert the arguments
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	return InstancePtr->CfgPtr->Options;
}
