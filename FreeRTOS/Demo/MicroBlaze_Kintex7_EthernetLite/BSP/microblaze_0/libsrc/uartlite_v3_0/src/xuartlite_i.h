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
/****************************************************************************/
/**
*
* @file xuartlite_i.h
*
* Contains data which is shared between the files of the XUartLite component.
* It is intended for internal use only.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a ecm  08/31/01 First release
* 1.00b jhl  02/21/02 Reparitioned the driver for smaller files
* 1.00b rpm  04/24/02 Moved register definitions to xuartlite_l.h and
*                     updated macro naming convention
* 2.00a ktn  10/20/09 The macros have been renamed to remove _m from
*		      the name. XUartLite_mClearStats macro is removed and
*		      XUartLite_ClearStats function should be used in its place.

* </pre>
*
*****************************************************************************/

#ifndef XUARTLITE_I_H /* prevent circular inclusions */
#define XUARTLITE_I_H /* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/

#include "xuartlite.h"
#include "xuartlite_l.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/****************************************************************************
*
* Update the statistics of the instance.
*
* @param	InstancePtr is a pointer to the XUartLite instance.
* @param	StatusRegister contains the contents of the UART status
*		register to update the statistics with.
*
* @return	None.
*
* @note
*
* Signature: void XUartLite_UpdateStats(XUartLite *InstancePtr,
*						u32 StatusRegister)
*
*****************************************************************************/
#define XUartLite_UpdateStats(InstancePtr, StatusRegister)	\
{								\
	if ((StatusRegister) & XUL_SR_OVERRUN_ERROR)		\
	{							\
		(InstancePtr)->Stats.ReceiveOverrunErrors++;	\
	}							\
	if ((StatusRegister) & XUL_SR_PARITY_ERROR)		\
	{							\
		(InstancePtr)->Stats.ReceiveParityErrors++;	\
	}							\
	if ((StatusRegister) & XUL_SR_FRAMING_ERROR)		\
	{							\
		(InstancePtr)->Stats.ReceiveFramingErrors++;	\
	}							\
}

/************************** Variable Definitions ****************************/

/* the configuration table */
extern XUartLite_Config XUartLite_ConfigTable[];

/************************** Function Prototypes *****************************/

unsigned int XUartLite_SendBuffer(XUartLite *InstancePtr);
unsigned int XUartLite_ReceiveBuffer(XUartLite *InstancePtr);

#ifdef __cplusplus
}
#endif

#endif		/* end of protection macro */

