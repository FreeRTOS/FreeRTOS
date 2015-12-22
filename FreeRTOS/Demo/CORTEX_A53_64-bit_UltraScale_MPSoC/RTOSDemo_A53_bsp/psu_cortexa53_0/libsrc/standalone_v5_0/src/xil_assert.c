/******************************************************************************
*
* Copyright (C) 2009 - 2014 Xilinx, Inc. All rights reserved.
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
* @file xil_assert.c
*
* This file contains basic assert related functions for Xilinx software IP.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date   Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a hbm  07/14/09 Initial release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Variable Definitions *****************************/

/**
 * This variable allows testing to be done easier with asserts. An assert
 * sets this variable such that a driver can evaluate this variable
 * to determine if an assert occurred.
 */
u32 Xil_AssertStatus;

/**
 * This variable allows the assert functionality to be changed for testing
 * such that it does not wait infinitely. Use the debugger to disable the
 * waiting during testing of asserts.
 */
/*s32 Xil_AssertWait = 1*/

/* The callback function to be invoked when an assert is taken */
static Xil_AssertCallback Xil_AssertCallbackRoutine = NULL;

/************************** Function Prototypes ******************************/

/*****************************************************************************/
/**
*
* Implement assert. Currently, it calls a user-defined callback function
* if one has been set.  Then, it potentially enters an infinite loop depending
* on the value of the Xil_AssertWait variable.
*
* @param    file is the name of the filename of the source
* @param    line is the linenumber within File
*
* @return   None.
*
* @note     None.
*
******************************************************************************/
void Xil_Assert(const char8 *File, s32 Line)
{
	s32 Xil_AssertWait = 1;
	/* if the callback has been set then invoke it */
	if (Xil_AssertCallbackRoutine != 0) {
		(*Xil_AssertCallbackRoutine)(File, Line);
	}

	/* if specified, wait indefinitely such that the assert will show up
	 * in testing
	 */
	while (Xil_AssertWait != 0) {
	}
}

/*****************************************************************************/
/**
*
* Set up a callback function to be invoked when an assert occurs. If there
* was already a callback installed, then it is replaced.
*
* @param    routine is the callback to be invoked when an assert is taken
*
* @return   None.
*
* @note     This function has no effect if NDEBUG is set
*
******************************************************************************/
void Xil_AssertSetCallback(Xil_AssertCallback Routine)
{
	Xil_AssertCallbackRoutine = Routine;
}

/*****************************************************************************/
/**
*
* Null handler function. This follows the XInterruptHandler signature for
* interrupt handlers. It can be used to assign a null handler (a stub) to an
* interrupt controller vector table.
*
* @param    NullParameter is an arbitrary void pointer and not used.
*
* @return   None.
*
* @note     None.
*
******************************************************************************/
void XNullHandler(void *NullParameter)
{
 (void *) NullParameter;
}

