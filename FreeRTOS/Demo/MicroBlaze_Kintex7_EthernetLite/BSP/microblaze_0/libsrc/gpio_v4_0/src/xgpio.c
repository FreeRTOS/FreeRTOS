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
* @file xgpio.c
*
* The implementation of the XGpio driver's basic functionality. See xgpio.h
* for more information about the driver.
*
* @note
*
* None
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a rmm  02/04/02 First release
* 2.00a jhl  12/16/02 Update for dual channel and interrupt support
* 2.01a jvb  12/13/05 Changed Initialize() into CfgInitialize(), and made
*                     CfgInitialize() take a pointer to a config structure
*                     instead of a device id. Moved Initialize() into
*                     xgpio_sinit.c, and had Initialize() call CfgInitialize()
*                     after it retrieved the config structure using the device
*                     id. Removed include of xparameters.h along with any
*                     dependencies on xparameters.h and the _g.c config table.
* 2.11a mta  03/21/07 Updated to new coding style, added GetDataDirection
* 2.12a sv   11/21/07 Updated driver to support access through DCR bus
* 3.00a sv   11/21/09 Updated to use HAL Processor APIs. Renamed the
*		      macros to remove _m from the name.
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xgpio.h"
#include "xstatus.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/


/************************** Function Prototypes *****************************/


/****************************************************************************/
/**
* Initialize the XGpio instance provided by the caller based on the
* given configuration data.
*
* Nothing is done except to initialize the InstancePtr.
*
* @param	InstancePtr is a pointer to an XGpio instance. The memory the
*		pointer references must be pre-allocated by the caller. Further
*		calls to manipulate the driver through the XGpio API must be
*		made with this pointer.
* @param	Config is a reference to a structure containing information
*		about a specific GPIO device. This function initializes an
*		InstancePtr object for a specific device specified by the
*		contents of Config. This function can initialize multiple
*		instance objects with the use of multiple calls giving different
*		Config information on each call.
* @param 	EffectiveAddr is the device base address in the virtual memory
*		address space. The caller is responsible for keeping the address
*		mapping from EffectiveAddr to the device physical base address
*		unchanged once this function is invoked. Unexpected errors may
*		occur if the address mapping changes after this function is
*		called. If address translation is not used, use
*		Config->BaseAddress for this parameters, passing the physical
*		address instead.
*
* @return
* 		- XST_SUCCESS	Initialization was successfull.
*
* @note		None.
*
*****************************************************************************/
int XGpio_CfgInitialize(XGpio * InstancePtr, XGpio_Config * Config,
			u32 EffectiveAddr)
{
	/*
	 * Assert arguments
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);

	/*
	 * Set some default values.
	 */
#if (XPAR_XGPIO_USE_DCR_BRIDGE != 0)
	InstancePtr->BaseAddress = ((EffectiveAddr >> 2)) & 0xFFF;
#else
	InstancePtr->BaseAddress = EffectiveAddr;
#endif

	InstancePtr->InterruptPresent = Config->InterruptPresent;
	InstancePtr->IsDual = Config->IsDual;

	/*
	 * Indicate the instance is now ready to use, initialized without error
	 */
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;
	return (XST_SUCCESS);
}


/****************************************************************************/
/**
* Set the input/output direction of all discrete signals for the specified
* GPIO channel.
*
* @param	InstancePtr is a pointer to an XGpio instance to be worked on.
* @param	Channel contains the channel of the GPIO (1 or 2) to operate on.
* @param	DirectionMask is a bitmask specifying which discretes are input
*		and which are output. Bits set to 0 are output and bits set to 1
*		are input.
*
* @return	None.
*
* @note		The hardware must be built for dual channels if this function
*		is used with any channel other than 1.  If it is not, this
*		function will assert.
*
*****************************************************************************/
void XGpio_SetDataDirection(XGpio * InstancePtr, unsigned Channel,
			    u32 DirectionMask)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((Channel == 1) ||
		     ((Channel == 2) && (InstancePtr->IsDual == TRUE)));

	XGpio_WriteReg(InstancePtr->BaseAddress,
			((Channel - 1) * XGPIO_CHAN_OFFSET) + XGPIO_TRI_OFFSET,
			DirectionMask);
}

/****************************************************************************/
/**
* Get the input/output direction of all discrete signals for the specified
* GPIO channel.
*
* @param	InstancePtr is a pointer to an XGpio instance to be worked on.
* @param	Channel contains the channel of the GPIO (1 or 2) to operate on.
*
* @return	Bitmask specifying which discretes are input and
*		which are output. Bits set to 0 are output and bits set to 1 are
*		input.
*
* @note
*
* The hardware must be built for dual channels if this function is used
* with any channel other than 1.  If it is not, this function will assert.
*
*****************************************************************************/
u32 XGpio_GetDataDirection(XGpio *InstancePtr, unsigned Channel)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((Channel == 1)  ||
		((Channel == 2) &&
		(InstancePtr->IsDual == TRUE)));

	return XGpio_ReadReg(InstancePtr->BaseAddress,
		((Channel - 1) * XGPIO_CHAN_OFFSET) + XGPIO_TRI_OFFSET);
}

/****************************************************************************/
/**
* Read state of discretes for the specified GPIO channnel.
*
* @param	InstancePtr is a pointer to an XGpio instance to be worked on.
* @param	Channel contains the channel of the GPIO (1 or 2) to operate on.
*
* @return	Current copy of the discretes register.
*
* @note		The hardware must be built for dual channels if this function
*		is used with any channel other than 1.  If it is not, this
*		function will assert.
*
*****************************************************************************/
u32 XGpio_DiscreteRead(XGpio * InstancePtr, unsigned Channel)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((Channel == 1) ||
			((Channel == 2) && (InstancePtr->IsDual == TRUE)));

	return XGpio_ReadReg(InstancePtr->BaseAddress,
			      ((Channel - 1) * XGPIO_CHAN_OFFSET) +
			      XGPIO_DATA_OFFSET);
}

/****************************************************************************/
/**
* Write to discretes register for the specified GPIO channel.
*
* @param	InstancePtr is a pointer to an XGpio instance to be worked on.
* @param	Channel contains the channel of the GPIO (1 or 2) to operate on.
* @param	Data is the value to be written to the discretes register.
*
* @return	None.
*
* @note		The hardware must be built for dual channels if this function
*		is  used with any channel other than 1.  If it is not, this
*		function will assert. See also XGpio_DiscreteSet() and
*		XGpio_DiscreteClear().
*
*****************************************************************************/
void XGpio_DiscreteWrite(XGpio * InstancePtr, unsigned Channel, u32 Data)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((Channel == 1) ||
		     ((Channel == 2) && (InstancePtr->IsDual == TRUE)));

	XGpio_WriteReg(InstancePtr->BaseAddress,
			((Channel - 1) * XGPIO_CHAN_OFFSET) + XGPIO_DATA_OFFSET,
			Data);
}
