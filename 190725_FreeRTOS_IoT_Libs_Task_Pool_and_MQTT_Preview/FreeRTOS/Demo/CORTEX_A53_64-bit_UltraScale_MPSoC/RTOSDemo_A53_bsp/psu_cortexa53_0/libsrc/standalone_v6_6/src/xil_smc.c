/******************************************************************************
*
* Copyright (C) 2017 Xilinx, Inc. All rights reserved.
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
* @file xil_smc.c
*
* This file contains function for initiating SMC call
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who      Date     Changes
* ----- -------- -------- -----------------------------------------------
* 6.2 	pkp  	 02/16/17 First release
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/
#include "xil_types.h"
#include "xil_smc.h"

#if EL1_NONSECURE
/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Function Prototypes *****************************/

/************************** Variable Definitions *****************************/
XSmc_OutVar SmcResult;

/*****************************************************************************/
/**
* @brief	Initiate SMC call to EL3 secure monitor to request for secure
*			service. This function is only applicable for EL1 Non-secure bsp.
*
* @param	FunctionID is the SMC identifier for a particular secure service
*			request
* @param	Arg1 to Arg6 is the arguements passed to EL3 secure monitor
* @param	Arg7 is Hypervisor Client ID register
*
* @return	Result from secure payload service
* @note		FunctionID and Arg1-Arg7 should be as per SMC calling convention
*
******************************************************************************/
XSmc_OutVar Xil_Smc(u64 FunctionID, u64 Arg1, u64 Arg2, u64 Arg3, u64 Arg4,
					u64 Arg5, u64 Arg6, u64 Arg7){

	/*
	 * Since registers x8 to x17 are not saved by secure monitor during SMC
	 * it must be preserved.
	 */
	XSave_X8toX17();

	/* Moving to EL3 secure monitor with smc call. */

	__asm__ __volatile__ ("smc #0x0");

	/*
	 * The result of the secure services are stored in x0 - x3. They are
	 * moved to SmcResult to return the result.
	 */
	__asm__ __volatile__("mov	x8, x0");
	__asm__ __volatile__("mov	x9, x1");
	__asm__ __volatile__("mov	x10, x2");
	__asm__ __volatile__("mov	x11, x3");

	__asm__ __volatile__("mov	%0, x8" : "=r" (SmcResult.Arg0));
	__asm__ __volatile__("mov	%0, x9" : "=r" (SmcResult.Arg1));
	__asm__ __volatile__("mov	%0, x10" : "=r" (SmcResult.Arg2));
	__asm__ __volatile__("mov	%0, x11" : "=r" (SmcResult.Arg3));

	XRestore_X8toX17();

	return SmcResult;
}
#endif