/*******************************************************************************
 *
 * Copyright (C) 2017 Xilinx, Inc.  All rights reserved.
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
*******************************************************************************/
/******************************************************************************/
/**
 *
 * @file xdpdma_sinit.c
 * @addtogroup dpdma_v1_0
 * @{
 *
 * This file contains static initialization methods for the XDpDma driver.
 *
 * @note	None.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- -----------------------------------------------
 * 1.0   aad  01/20/15 Initial release.
 * </pre>
 *
*******************************************************************************/

/******************************* Include Files ********************************/

#include "xdpdma.h"
#include "xparameters.h"

/*************************** Variable Declarations ****************************/

/**
 * A table of configuration structures containing the configuration information
 * for each DisplayPort TX core in the system.
 */
extern XDpDma_Config XDpDma_ConfigTable[XPAR_XDPDMA_NUM_INSTANCES];

/**************************** Function Definitions ****************************/

/******************************************************************************/
/**
 * This function looks for the device configuration based on the unique device
 * ID. The table XDpDma_ConfigTable[] contains the configuration information for
 * each device in the system.
 *
 * @param	DeviceId is the unique device ID of the device being looked up.
 *
 * @return	A pointer to the configuration table entry corresponding to the
 *		given device ID, or NULL if no match is found.
 *
 * @note	None.
 *
*******************************************************************************/
XDpDma_Config *XDpDma_LookupConfig(u16 DeviceId)
{
	XDpDma_Config *CfgPtr;
	u32 Index;

	for (Index = 0; Index < XPAR_XDPDMA_NUM_INSTANCES; Index++) {
		if (XDpDma_ConfigTable[Index].DeviceId == DeviceId) {
			CfgPtr = &XDpDma_ConfigTable[Index];
			break;
		}
	}

	return CfgPtr;
}
/** @} */
