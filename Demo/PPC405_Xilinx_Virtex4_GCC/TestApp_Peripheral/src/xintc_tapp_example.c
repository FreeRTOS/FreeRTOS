#define TESTAPP_GEN


/* $Id: xintc_tapp_example.c,v 1.1 2007/05/15 07:08:09 mta Exp $ */
/******************************************************************************
*
*       XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS"
*       AS A COURTESY TO YOU, SOLELY FOR USE IN DEVELOPING PROGRAMS AND
*       SOLUTIONS FOR XILINX DEVICES.  BY PROVIDING THIS DESIGN, CODE,
*       OR INFORMATION AS ONE POSSIBLE IMPLEMENTATION OF THIS FEATURE,
*       APPLICATION OR STANDARD, XILINX IS MAKING NO REPRESENTATION
*       THAT THIS IMPLEMENTATION IS FREE FROM ANY CLAIMS OF INFRINGEMENT,
*       AND YOU ARE RESPONSIBLE FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE
*       FOR YOUR IMPLEMENTATION.  XILINX EXPRESSLY DISCLAIMS ANY
*       WARRANTY WHATSOEVER WITH RESPECT TO THE ADEQUACY OF THE
*       IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO ANY WARRANTIES OR
*       REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE FROM CLAIMS OF
*       INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
*       FOR A PARTICULAR PURPOSE.
*
*       (c) Copyright 2002-2006 Xilinx Inc.
*       All rights reserved.
*
*******************************************************************************/
/******************************************************************************/
/**
*
* @file xintc_tapp_example.c
*
* This file contains a self test example using the Interrupt Controller driver
* (XIntc) and hardware device. Please reference other device driver examples to
* see more examples of how the intc and interrupts can be used by a software
* application.
*
* This example shows the use of the Interrupt Controller both with a PowerPC405
* and MicroBlaze processor.
*
* The TestApp Gen utility uses this file to perform the self test and setup
* of intc for interrupts.
*
* @note
*
* None
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- --------------------------------------------------------
* 1.00a sv   06/29/05  Created for Test App Integration
* 1.00c sn   05/09/06  Added Interrupt Setup Function
* </pre>
******************************************************************************/

/***************************** Include Files *********************************/

#include "xparameters.h"
#include "xstatus.h"
#include "xintc.h"
#ifdef __MICROBLAZE__    
#include "mb_interface.h"
#endif
#ifdef __PPC__    
#include "xexception_l.h"
#endif


/************************** Constant Definitions *****************************/

/*
 * The following constants map to the XPAR parameters created in the
 * xparameters.h file. They are defined here such that a user can easily
 * change all the needed parameters in one place. This definition is not
 * included if the example is generated from the TestAppGen test tool.
 */
#ifndef TESTAPP_GEN
#define INTC_DEVICE_ID          XPAR_OPB_INTC_0_DEVICE_ID
#endif

/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/

XStatus IntcSelfTestExample(Xuint16 DeviceId);
XStatus IntcInterruptSetup(XIntc *IntcInstancePtr, Xuint16 DeviceId);

/************************** Variable Definitions *****************************/

static XIntc InterruptController; /* Instance of the Interrupt Controller */


/*****************************************************************************/
/**
*
* This is the main function for the Interrupt Controller example. This
* function is not included if the example is generated from the TestAppGen test
* tool.
*
* @param    None.
*
* @return   XST_SUCCESS to indicate success, otherwise XST_FAILURE.
*
* @note     None.
*
******************************************************************************/
#ifndef TESTAPP_GEN
int main(void)
{
    XStatus Status;

    /*
     *  Run the Intc example , specify the Device ID generated in xparameters.h
     */
    Status = IntcSelfTestExample(INTC_DEVICE_ID);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }

    return XST_SUCCESS;

}
#endif

/*****************************************************************************/
/**
*
* This function runs a self-test on the driver/device. This is a destructive
* test. This function is an example of how to use the interrupt controller
* driver component (XIntc) and the hardware device.  This function is designed
* to work without any hardware devices to cause interrupts.  It may not return
* if the interrupt controller is not properly connected to the processor in
* either software or hardware.
*
* This function relies on the fact that the interrupt controller hardware
* has come out of the reset state such that it will allow interrupts to be
* simulated by the software.
*
* @param    DeviceId is device ID of the Interrupt Controller Device , typically
*           XPAR_<INTC_instance>_DEVICE_ID value from xparameters.h
*
* @return   XST_SUCCESS to indicate success, otherwise XST_FAILURE
*
* @note     None.
*
******************************************************************************/
XStatus IntcSelfTestExample(Xuint16 DeviceId)
{
    XStatus Status;

    /*
     * Initialize the interrupt controller driver so that it is ready to use.
     */
    Status = XIntc_Initialize(&InterruptController, DeviceId);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }


    /*
     * Perform a self-test to ensure that the hardware was built  correctly
     */
    Status = XIntc_SelfTest(&InterruptController);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }
    
    return XST_SUCCESS;
    
}


/*****************************************************************************/
/**
*
* This function is used by the TestAppGen generated application to setup
* the interrupt controller.
*
* @param    IntcInstancePtr is the reference to the Interrupt Controller 
*           instance.
* @param    DeviceId is device ID of the Interrupt Controller Device , typically
*           XPAR_<INTC_instance>_DEVICE_ID value from xparameters.h
*
* @return   XST_SUCCESS to indicate success, otherwise XST_FAILURE
*
* @note     None.
*
******************************************************************************/
XStatus IntcInterruptSetup(XIntc *IntcInstancePtr, Xuint16 DeviceId)
{

    XStatus Status;

    /*
     * Initialize the interrupt controller driver so that it is ready to use.
     */
    Status = XIntc_Initialize(IntcInstancePtr, DeviceId);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }

    /*
     * Perform a self-test to ensure that the hardware was built  correctly.
     */
    Status = XIntc_SelfTest(IntcInstancePtr);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }


#ifdef __MICROBLAZE__     
    /* 
     * Enable the microblaze Interrupts
     */
    microblaze_enable_interrupts();
#endif
    
#ifdef __PPC__ /*PPC*/     
    
    /*
     * Initialize the PPC405 exception table
     */
    XExc_Init();

    /*
     * Register the interrupt controller handler with the exception table
     */
    XExc_RegisterHandler(XEXC_ID_NON_CRITICAL_INT,
                         (XExceptionHandler)XIntc_DeviceInterruptHandler,
                         (void*) 0);

    /*
     * Enable non-critical exceptions
     */
    XExc_mEnableExceptions(XEXC_NON_CRITICAL);
#endif

    
    /*
     * Start the interrupt controller such that interrupts are enabled for
     * all devices that cause interrupts.
     */
    Status = XIntc_Start(IntcInstancePtr, XIN_REAL_MODE);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }
    
    return XST_SUCCESS;

}



