/******************************************************************************
*
* Copyright (C) 2004 - 2014 Xilinx, Inc. All rights reserved.
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
 * @file microblaze_interrupt_handler.c
 *
 * This file contains the standard interrupt handler for the MicroBlaze processor.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Date     Changes
 * ----- -------- -----------------------------------------------
 * 1.00b 10/03/03 First release
 * </pre>
 *
 ******************************************************************************/


/***************************** Include Files *********************************/

#include "xil_exception.h"
#include "microblaze_interrupts_i.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/

void __interrupt_handler( void ) __attribute__( ( interrupt_handler ) );
void microblaze_register_handler( XInterruptHandler Handler,
                                  void * DataPtr );

/************************** Variable Definitions *****************************/

extern MB_InterruptVectorTableEntry MB_InterruptVectorTable;
/*****************************************************************************/

/**
 *
 * This function is the standard interrupt handler used by the MicroBlaze processor.
 * It saves all volatile registers, calls the users top level interrupt handler.
 * When this returns, it restores all registers, and returns using a rtid instruction.
 *
 * @param
 *
 * None
 *
 * @return
 *
 * None.
 *
 * @note
 *
 * None.
 *
 ******************************************************************************/
void __interrupt_handler( void )
{
    /* The compiler saves all volatiles and the MSR */
    ( void ) MB_InterruptVectorTable.Handler( MB_InterruptVectorTable.CallBackRef );
    /* The compiler restores all volatiles and MSR, and returns from interrupt */
}

/****************************************************************************/
/*****************************************************************************/

/**
 *
 * Registers a top-level interrupt handler for the MicroBlaze. The
 * argument provided in this call as the DataPtr is used as the argument
 * for the handler when it is called.
 *
 * @param    Top level handler.
 * @param    DataPtr is a reference to data that will be passed to the handler
 *           when it gets called.
 *
 * @return   None.
 *
 * @note
 *
 * None.
 *
 ****************************************************************************/
void microblaze_register_handler( XInterruptHandler Handler,
                                  void * DataPtr )
{
    MB_InterruptVectorTable.Handler = Handler;
    MB_InterruptVectorTable.CallBackRef = DataPtr;
}
