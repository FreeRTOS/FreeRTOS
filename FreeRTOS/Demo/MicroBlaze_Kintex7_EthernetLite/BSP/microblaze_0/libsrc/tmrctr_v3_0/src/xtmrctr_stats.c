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
* @file xtmrctr_stats.c
*
* Contains function to get and clear statistics for the XTmrCtr component.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00b jhl  02/06/02 First release.
* 1.10b mta  03/21/07 Updated for new coding style.
* 2.00a ktn  10/30/09 Updated to use HAL API's.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xtmrctr.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
* Get a copy of the XTmrCtrStats structure, which contains the current
* statistics for this driver.
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
* @param	StatsPtr is a pointer to a XTmrCtrStats structure which will get
*		a copy of current statistics.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XTmrCtr_GetStats(XTmrCtr * InstancePtr, XTmrCtrStats * StatsPtr)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(StatsPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	StatsPtr->Interrupts = InstancePtr->Stats.Interrupts;
}

/*****************************************************************************/
/**
*
* Clear the XTmrCtrStats structure for this driver.
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XTmrCtr_ClearStats(XTmrCtr * InstancePtr)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->Stats.Interrupts = 0;
}
