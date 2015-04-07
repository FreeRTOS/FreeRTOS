/******************************************************************************
*
*
* (c) Copyright 2009 Xilinx, Inc. All rights reserved.
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
unsigned int Xil_AssertStatus;

/**
 * This variable allows the assert functionality to be changed for testing
 * such that it does not wait infinitely. Use the debugger to disable the
 * waiting during testing of asserts.
 */
int Xil_AssertWait = TRUE;

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
void Xil_Assert(const char *File, int Line)
{
	/* if the callback has been set then invoke it */
	if (Xil_AssertCallbackRoutine != 0) {
		(*Xil_AssertCallbackRoutine)(File, Line);
	}

	/* if specified, wait indefinitely such that the assert will show up
	 * in testing
	 */
	while (Xil_AssertWait) {
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
 (void) NullParameter;
}

