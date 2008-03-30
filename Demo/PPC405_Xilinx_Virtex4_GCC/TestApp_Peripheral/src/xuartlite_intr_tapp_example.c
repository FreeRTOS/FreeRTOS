#define TESTAPP_GEN

/* $Id: xuartlite_intr_tapp_example.c,v 1.1 2007/05/15 07:00:27 mta Exp $ */
/*****************************************************************************
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
* @file xuartlite_intr_tapp_example.c
*
* This file contains a design example using the UartLite driver and
* hardware device using the interrupt mode for transmission of data.
*
* This example works with a PPC processor. Refer the examples of Interrupt
* controller for an example of using interrupts with the MicroBlaze processor.
*
* @note
*
* None.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00b sv   06/08/06 Created for supporting Test App Interrupt examples
* </pre>
******************************************************************************/

/***************************** Include Files *********************************/

#include "xparameters.h"
#include "xuartlite.h"
#include "xintc.h"

#ifdef __MICROBLAZE__
#include "mb_interface.h"
#else
#include "xexception_l.h"
#endif


/************************** Constant Definitions *****************************/

/*
 * The following constants map to the XPAR parameters created in the
 * xparameters.h file. They are defined here such that a user can easily
 * change all the needed parameters in one place.
 */
#ifndef TESTAPP_GEN
#define UARTLITE_DEVICE_ID      XPAR_RS232_UART_DEVICE_ID
#define INTC_DEVICE_ID          XPAR_OPB_INTC_0_DEVICE_ID
#define UARTLITE_IRPT_INTR      XPAR_OPB_INTC_0_RS232_UART_INTERRUPT_INTR
#endif

/*
 * The following constant controls the length of the buffers to be sent
 * and received with the UartLite device.
 */
#define TEST_BUFFER_SIZE            100


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/

XStatus UartLiteIntrExample(XIntc *IntcInstancePtr,
                            XUartLite *UartLiteInstancePtr,
                            Xuint16 UartLiteDeviceId,
                            Xuint16 UartLiteIntrId);


static void UartLiteSendHandler(void *CallBackRef, unsigned int EventData);

static void UartLiteRecvHandler(void *CallBackRef, unsigned int EventData);


static XStatus UartLiteSetupIntrSystem(XIntc *IntcInstancePtr,
                                       XUartLite *UartLiteInstancePtr,
                                       Xuint16 UartLiteIntrId);

static void UartLiteDisableIntrSystem(XIntc *IntrInstancePtr,
                                      Xuint16 UartLiteIntrId);


/************************** Variable Definitions *****************************/

/*
 * The instances to support the device drivers are global such that the
 * are initialized to zero each time the program runs.
 */
#ifndef TESTAPP_GEN
static XIntc IntcInstance;      /* The instance of the Interrupt Controller */
static XUartLite UartLiteInst;  /* The instance of the UartLite Device */
#endif



/*
 * The following variables are shared between non-interrupt processing and
 * interrupt processing such that they must be global.
 */

/*
 * The following buffers are used in this example to send and receive data
 * with the UartLite.
 */
Xuint8 SendBuffer[TEST_BUFFER_SIZE];
Xuint8 ReceiveBuffer[TEST_BUFFER_SIZE];

/*
 * The following counter is used to determine when the entire buffer has
 * been sent.
 */
static volatile int TotalSentCount;


/******************************************************************************/
/**
*
* Main function to call the UartLite interrupt example.
*
* @param    None.
*
* @return   XST_SUCCESS if successful, else XST_FAILURE.
*
* @note     None
*
*******************************************************************************/
#ifndef TESTAPP_GEN
int main(void)
{
    XStatus Status;

    /*
     * Run the UartLite Interrupt example , specify the Device ID that is
     * generated in xparameters.h.
     */
    Status = UartLiteIntrExample(&IntcInstance,
                                 &UartLiteInst,
                                 UARTLITE_DEVICE_ID,
                                 UARTLITE_IRPT_INTR);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }

    return XST_SUCCESS;
}
#endif

/****************************************************************************/
/**
*
* This function does a minimal test on the UartLite device and driver as a
* design example. The purpose of this function is to illustrate how to use
* the XUartLite component.
*
* This function sends data and expects to receive the same data through the
* UartLite. The user must provide a physical loopback such that data which
* is transmitted will be received.
*
* This function uses the interrupt driver mode of the UartLite.  The calls to
* the  UartLite driver in the interrupt handlers, should only use the
* non-blocking calls.
*
* @param    IntcInstancePtr is a pointer to the instance of the INTC component.
* @param    UartLiteInstPtr is a pointer to the instance of UartLite component.
* @param    UartLiteDeviceId is the Device ID of the UartLite Device and is the
*           XPAR_<UARTLITE_instance>_DEVICE_ID value from xparameters.h.
* @param    UartLiteIntrId is the Interrupt ID and is typically
*           XPAR_<INTC_instance>_<UARTLITE_instance>_IP2INTC_IRPT_INTR
*           value from xparameters.h.
*
* @return   XST_SUCCESS if successful, otherwise XST_FAILURE.
*
* @note
*
* This function contains an infinite loop such that if interrupts are not
* working it may never return.
*
****************************************************************************/
XStatus UartLiteIntrExample(XIntc *IntcInstancePtr,
                            XUartLite *UartLiteInstPtr,
                            Xuint16 UartLiteDeviceId,
                            Xuint16 UartLiteIntrId)

{
    XStatus Status;
    Xuint32 Index;

    /*
     * Initialize the UartLite driver so that it's ready to use.
     */
    Status = XUartLite_Initialize(UartLiteInstPtr, UartLiteDeviceId);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }

    /*
     * Perform a self-test to ensure that the hardware was built correctly.
     */
    Status = XUartLite_SelfTest(UartLiteInstPtr);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }

    /*
     * Connect the UartLite to the interrupt subsystem such that interrupts can
     * occur. This function is application specific.
     */
    Status = UartLiteSetupIntrSystem(IntcInstancePtr,
                                     UartLiteInstPtr,
                                     UartLiteIntrId);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }

    /*
     * Setup the handlers for the UartLite that will be called from the
     * interrupt context when data has been sent and received,
     * specify a pointer to the UartLite driver instance as the callback
     * reference so the handlers are able to access the instance data.
     */
    XUartLite_SetSendHandler(UartLiteInstPtr, UartLiteSendHandler,
                             UartLiteInstPtr);
    XUartLite_SetRecvHandler(UartLiteInstPtr, UartLiteRecvHandler,
                             UartLiteInstPtr);

    /*
     * Enable the interrupt of the UartLite so that the interrupts will occur.
     */
    XUartLite_EnableInterrupt(UartLiteInstPtr);

    /*
     * Initialize the send buffer bytes with a pattern to send.
     */
    for (Index = 0; Index < TEST_BUFFER_SIZE; Index++)
    {
        SendBuffer[Index] = Index;
    }

    /*
     * Send the buffer using the UartLite.
     */
    XUartLite_Send(UartLiteInstPtr, SendBuffer, TEST_BUFFER_SIZE);

    /*
     * Wait for the entire buffer to be transmitted,  the function may get
     * locked up in this loop if the interrupts are not working correctly.
     */
    while ((TotalSentCount != TEST_BUFFER_SIZE))
    {
    }


    UartLiteDisableIntrSystem(IntcInstancePtr, UartLiteIntrId);

    return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function is the handler which performs processing to send data to the
* UartLite. It is called from an interrupt context such that the amount of
* processing performed should be minimized. It is called when the transmit
* FIFO of the UartLite is empty and more data can be sent through the UartLite.
*
* This handler provides an example of how to handle data for the UartLite, but
* is application specific.
*
* @param    CallBackRef contains a callback reference from the driver.
*           In this case it is the instance pointer for the UartLite driver.
* @param    EventData contains the number of bytes sent or received for sent and
*           receive events.
*
* @return   None.
*
* @note     None.
*
****************************************************************************/
static void UartLiteSendHandler(void *CallBackRef, unsigned int EventData)
{
    TotalSentCount = EventData;
}

/****************************************************************************/
/**
*
* This function is the handler which performs processing to receive data from
* the UartLite. It is called from an interrupt context such that the amount of
* processing performed should be minimized. It is called when any data is
* present in the receive FIFO of the UartLite such that the data can be
* retrieved from the UartLite. The amount of data present in the FIFO is not
* known when this function is called.
*
* This handler provides an example of how to handle data for the UartLite, but
* is application specific.
*
* @param    CallBackRef contains a callback reference from the driver, in this
*           case  it is the instance pointer for the UartLite driver.
* @param    EventData contains the number of bytes sent or received for sent and
*           receive events.
*
* @return   None.
*
* @note     None.
*
****************************************************************************/
static void UartLiteRecvHandler(void *CallBackRef, unsigned int EventData)
{

}

/****************************************************************************/
/**
*
* This function setups the interrupt system such that interrupts can occur
* for the UartLite. This function is application specific since the actual
* system may or may not have an interrupt controller. The UartLite could be
* directly connected to a processor without an interrupt controller. The
* user should modify this function to fit the application.
*
* @param    IntcInstancePtr is a pointer to the instance of the INTC component.
* @param    UartLiteInstPtr is a pointer to the instance of UartLite component.
*           XPAR_<UARTLITE_instance>_DEVICE_ID value from xparameters.h.
* @param    UartLiteIntrId is the Interrupt ID and is typically
*           XPAR_<INTC_instance>_<UARTLITE_instance>_IP2INTC_IRPT_INTR
*           value from xparameters.h.
*
* @return   XST_SUCCESS if successful, otherwise XST_FAILURE.
*
* @note     None.
*
****************************************************************************/
XStatus UartLiteSetupIntrSystem(XIntc *IntcInstancePtr,
                                XUartLite *UartLiteInstPtr,
                                Xuint16 UartLiteIntrId)
{
    XStatus Status;

#ifndef TESTAPP_GEN
    /*
     * Initialize the interrupt controller driver so that it is ready to use.
     */
    Status = XIntc_Initialize(IntcInstancePtr, INTC_DEVICE_ID);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }
#endif

    /*
     * Connect a device driver handler that will be called when an interrupt
     * for the device occurs, the device driver handler performs the specific
     * interrupt processing for the device.
     */
    Status = XIntc_Connect(IntcInstancePtr, UartLiteIntrId,
                           (XInterruptHandler)XUartLite_InterruptHandler,
                           (void *)UartLiteInstPtr);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }

#ifndef TESTAPP_GEN
    /*
     * Start the interrupt controller such that interrupts are enabled for
     * all devices that cause interrupts, specific real mode so that
     * the UART can cause interrupts thru the interrupt controller.
     */
    Status = XIntc_Start(IntcInstancePtr, XIN_REAL_MODE);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }
#endif

    /*
     * Enable the interrupt for the UartLite.
     */
    XIntc_Enable(IntcInstancePtr, UartLiteIntrId);

#ifndef TESTAPP_GEN

    /*
     * Initialize the PPC exception table.
     */
    XExc_Init();

    /*
     * Register the interrupt controller handler with the exception table.
     */
    XExc_RegisterHandler(XEXC_ID_NON_CRITICAL_INT,
                        (XExceptionHandler)XIntc_InterruptHandler,
                        IntcInstancePtr);

    /*
     * Enable non-critical exceptions.
     */
    XExc_mEnableExceptions(XEXC_NON_CRITICAL);


#endif /* TESTAPP_GEN */

    return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function disables the interrupts that occur for the UartLite.
*
* @param    IntcInstancePtr is a pointer to the instance of the INTC component.
* @param    UartLiteIntrId is the Interrupt ID and is typically
*           XPAR_<INTC_instance>_<UARTLITE_instance>_IP2INTC_IRPT_INTR
*           value from xparameters.h.
*
* @return   None.
*
* @note     None.
*
******************************************************************************/
static void UartLiteDisableIntrSystem(XIntc *IntcInstancePtr,
                                      Xuint16 UartLiteIntrId)
{

    /*
     * Disconnect and disable the interrupt for the UartLite
     */
    XIntc_Disconnect(IntcInstancePtr, UartLiteIntrId);

}


