/******************************************************************************
*
* Copyright (C) 2010 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xscugic_intr.c
*
* This file contains the interrupt processing for the driver for the Xilinx
* Interrupt Controller.  The interrupt processing is partitioned separately such
* that users are not required to use the provided interrupt processing.  This
* file requires other files of the driver to be linked in also.
*
* The interrupt handler, XScuGic_InterruptHandler, uses an input argument which
* is an instance pointer to an interrupt controller driver such that multiple
* interrupt controllers can be supported.  This handler requires the calling
* function to pass it the appropriate argument, so another level of indirection
* may be required.
*
* The interrupt processing may be used by connecting the interrupt handler to
* the interrupt system.  The handler does not save and restore the processor
* context but only handles the processing of the Interrupt Controller. The user
* is encouraged to supply their own interrupt handler when performance tuning is
* deemed necessary.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------------
* 1.00a drg  01/19/10 First release
* 1.01a sdm  11/09/11 XScuGic_InterruptHandler has changed correspondingly
*		      since the HandlerTable has now moved to XScuGic_Config.
*
* </pre>
*
* @internal
*
* This driver assumes that the context of the processor has been saved prior to
* the calling of the Interrupt Controller interrupt handler and then restored
* after the handler returns. This requires either the running RTOS to save the
* state of the machine or that a wrapper be used as the destination of the
* interrupt vector to save the state of the processor and restore the state
* after the interrupt handler returns.
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xscugic.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/*****************************************************************************/
/**
* This function is the primary interrupt handler for the driver.  It must be
* connected to the interrupt source such that it is called when an interrupt of
* the interrupt controller is active. It will resolve which interrupts are
* active and enabled and call the appropriate interrupt handler. It uses
* the Interrupt Type information to determine when to acknowledge the interrupt.
* Highest priority interrupts are serviced first.
*
* This function assumes that an interrupt vector table has been previously
* initialized.  It does not verify that entries in the table are valid before
* calling an interrupt handler.
*
*
* @param	InstancePtr is a pointer to the XScuGic instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XScuGic_InterruptHandler(XScuGic *InstancePtr)
{

    u32 IntID;
	    u32 IntIDFull;
	    XScuGic_VectorTableEntry *TablePtr;

	    /* Assert that the pointer to the instance is valid
	     */
	    Xil_AssertVoid(InstancePtr != NULL);

	    /*
	     * Read the int_ack register to identify the highest priority interrupt ID
	     * and make sure it is valid. Reading Int_Ack will clear the interrupt
	     * in the GIC.
	     */
	    IntIDFull = XScuGic_CPUReadReg(InstancePtr, XSCUGIC_INT_ACK_OFFSET);
	    IntID = IntIDFull & XSCUGIC_ACK_INTID_MASK;

	    if(XSCUGIC_MAX_NUM_INTR_INPUTS < IntID){
		goto IntrExit;
	    }

	    /*
	     * If the interrupt is shared, do some locking here if there are multiple
	     * processors.
	     */
	    /*
	     * If pre-eption is required:
	     * Re-enable pre-emption by setting the CPSR I bit for non-secure ,
	     * interrupts or the F bit for secure interrupts
	     */

	    /*
	     * If we need to change security domains, issue a SMC instruction here.
	     */

	    /*
	     * Execute the ISR. Jump into the Interrupt service routine based on the
	     * IRQSource. A software trigger is cleared by the ACK.
	     */
	        TablePtr = &(InstancePtr->Config->HandlerTable[IntID]);
	        TablePtr->Handler(TablePtr->CallBackRef);

	IntrExit:
	    /*
	     * Write to the EOI register, we are all done here.
	     * Let this function return, the boot code will restore the stack.
	     */
	    XScuGic_CPUWriteReg(InstancePtr, XSCUGIC_EOI_OFFSET, IntIDFull);

	    /*
	     * Return from the interrupt. Change security domains could happen here.
     */
}
