#define TESTAPP_GEN

/* $Id: xemaclite_intr_example.c,v 1.1.2.2 2010/08/06 15:11:04 anirudh Exp $
*/
/******************************************************************************
*
* (c) Copyright 2003-2010 Xilinx, Inc. All rights reserved.
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
2* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
*
******************************************************************************/
/*****************************************************************************/
/**
* @file xemaclite_intr_example.c
*
* This file contains an example for using the EmacLite hardware and driver.
* This file contains an interrupt example outlining the use of interrupts and
* callbacks in the transmission/reception of an Ethernet frame of 1000 bytes of
* payload.
*
* If the MDIO interface is NOT configured in the EmacLite core then this example
* will transmit a frame.
* If the MDIO interface is configured in the EmacLite core then this example
* will enable the MAC loopback in the PHY device, then transmit the frame and
* compare the received frame.
*
* @note
*
* None
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.01a ecm  05/21/04 First release
* 1.01a sv   06/06/05 Minor changes to comply to Doxygen and coding guidelines
* 1.01a sv   06/06/06 Minor changes for supporting Test App Interrupt examples
* 2.00a ktn  02/25/09 Updated to use PHY loop back if MDIO is configured in
*		      core
* 3.00a ktn  10/22/09 Updated the example to use the HAL APIs/macros.
*		      Updated example to use the macros that have been changed
*		      in the driver to remove _m from the name of the macro.
* 3.01a ktn  07/08/10 Updated example to support Little Endian MicroBlaze.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xemaclite_example.h"
#include "xintc.h"
#include "xil_exception.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/

#ifndef TESTAPP_GEN
/*
 * The following constants map to the XPAR parameters created in the
 * xparameters.h file. They are defined here such that a user can easily
 * change all the needed parameters in one place.
 */
#define INTC_DEVICE_ID		XPAR_INTC_0_DEVICE_ID
#define INTC_EMACLITE_ID	XPAR_INTC_0_EMACLITE_0_VEC_ID
#endif

/*
 * The Size of the Test Frame.
 */
#define EMACLITE_TEST_FRAME_SIZE	1000

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

int EmacLiteIntrExample(XIntc *IntcInstancePtr,
			XEmacLite *EmacLiteInstPtr,
			u16 EmacLiteDeviceId,
			u16 EmacLiteIntrId);

static int EmacLiteSendFrame(XEmacLite *EmacLiteInstPtr,
					 u32 PayloadSize);
static int EmacLiteRecvFrame(u32 PayloadSize);
static void EmacLiteRecvHandler(void *CallBackRef);
static void EmacLiteSendHandler(void *CallBackRef);
static void EmacLiteDisableIntrSystem(XIntc *IntcInstancePtr,
						 u16 EmacLiteIntrId);
static int EmacLiteSetupIntrSystem(XIntc *IntcInstancePtr,
			 XEmacLite *EmacLiteInstPtr, u16 EmacLiteIntrId);

/************************** Variable Definitions *****************************/

XIntc IntcInstance;		/* Instance of the Interrupt Controller */

/*
 * Set up valid local and remote MAC addresses. This loop back test uses the
 * LocalAddress both as a source and destination MAC address.
 */
static u8 RemoteAddress[XEL_MAC_ADDR_SIZE] =
{
	0x00, 0x10, 0xa4, 0xb6, 0xfd, 0x09
};
static u8 LocalAddress[XEL_MAC_ADDR_SIZE] =
{
	0x00, 0x0A, 0x35, 0x01, 0x02, 0x03
};

/****************************************************************************/
/**
*
* This function is the main function of the EmacLite interrupt example.
*
* @param	None.
*
* @return	XST_SUCCESS if successful, otherwise XST_FAILURE.
*
* @note		None.
*
*****************************************************************************/
#ifndef TESTAPP_GEN
int main()
{
	int Status;

	/*
	 * Run the EmacLite interrupt example , specify the parameters
	 * generated in xparameters.h.
	 */
	Status = EmacLiteIntrExample(&IntcInstance,
				 &EmacLiteInstance,
				 EMAC_DEVICE_ID,
				 INTC_EMACLITE_ID);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;

}
#endif

/*****************************************************************************/
/**
*
* The main entry point for the EmacLite driver example in interrupt mode.

* This function will transmit/receive the Ethernet frames and verify the
* data in the received frame (if the MDIO interface is configured in the
* EmacLite core).
* This function simply transmits a frame if the MDIO interface is not
* configured in the EmacLite core.
*
* @param	IntcInstancePtr is a pointer to the instance of the Intc.
* @param	EmacLiteInstPtr is a pointer to the instance of the EmacLite.
* @param	EmacLiteDeviceId is device ID of the XEmacLite Device ,
*		typically XPAR_<EMACLITE_instance>_DEVICE_ID value from
*		xparameters.h.
* @param	EmacLiteIntrId is the interrupt ID and is typically
*		XPAR_<INTC_instance>_<EMACLITE_instance>_VEC_ID value from
*		xparameters.h.
*
* @return	XST_SUCCESS if successful, otherwise XST_FAILURE.
*
* @note		None.
*
******************************************************************************/
int EmacLiteIntrExample(XIntc *IntcInstancePtr,
			XEmacLite *EmacLiteInstPtr,
			u16 EmacLiteDeviceId,
			u16 EmacLiteIntrId)
{
	int Status;
	u32 PhyAddress = 0;
	XEmacLite_Config *ConfigPtr;

	/*
	 * Initialize the EmacLite device.
	 */
	ConfigPtr = XEmacLite_LookupConfig(EmacLiteDeviceId);
	if (ConfigPtr == NULL) {
		return XST_FAILURE;
	}
	Status = XEmacLite_CfgInitialize(EmacLiteInstPtr,
					ConfigPtr,
					ConfigPtr->BaseAddress);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	/*
	 * Set the MAC address.
	 */
	XEmacLite_SetMacAddress(EmacLiteInstPtr, LocalAddress);

	/*
	 * Empty any existing receive frames.
	 */
	XEmacLite_FlushReceive(EmacLiteInstPtr);


	/*
	 * Check if there is a Tx buffer available, if there isn't it is an
	 * error.
	 */
	if (XEmacLite_TxBufferAvailable(EmacLiteInstPtr) != TRUE) {
		return XST_FAILURE;
	}


	/*
	 * Set up the interrupt infrastructure.
	 */
	Status = EmacLiteSetupIntrSystem(IntcInstancePtr,
					 EmacLiteInstPtr,
					 EmacLiteIntrId);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	/*
	 * Setup the EmacLite handlers.
	 */
	XEmacLite_SetRecvHandler((EmacLiteInstPtr), (void *)(EmacLiteInstPtr),
				 (XEmacLite_Handler)EmacLiteRecvHandler);
	XEmacLite_SetSendHandler((EmacLiteInstPtr), (void *)(EmacLiteInstPtr),
				 (XEmacLite_Handler)EmacLiteSendHandler);


	/*
	 * Enable the interrupts in the EmacLite controller.
	 */
	XEmacLite_EnableInterrupts(EmacLiteInstPtr);
	RecvFrameLength = 0;

	/*
	 * If the MDIO is configured in the device.
	 */
	if (XEmacLite_IsMdioConfigured(EmacLiteInstPtr)) {
		/*
		 * Detect the PHY device and enable the MAC Loop back
		 * in the PHY.
		 */
		PhyAddress = EmacLitePhyDetect(EmacLiteInstPtr);
		Status = EmacLiteEnablePhyLoopBack(EmacLiteInstPtr,
							 PhyAddress);
		if (Status != XST_SUCCESS) {
			XEmacLite_DisableInterrupts(EmacLiteInstPtr);
			EmacLiteDisableIntrSystem(IntcInstancePtr,
							 EmacLiteIntrId);
			return XST_FAILURE;
		}
	}

	/*
	 * Transmit an Ethernet frame.
	 */
	Status = EmacLiteSendFrame(EmacLiteInstPtr,
				   EMACLITE_TEST_FRAME_SIZE);
	if (Status != XST_SUCCESS) {
		if (XEmacLite_IsMdioConfigured(EmacLiteInstPtr)) {
			/*
			 * Disable the MAC Loop back in the PHY and
			 * disable/disconnect the EmacLite Interrupts.
			 */
			EmacLiteDisablePhyLoopBack(EmacLiteInstPtr,
							 PhyAddress);
			XEmacLite_DisableInterrupts(EmacLiteInstPtr);
			EmacLiteDisableIntrSystem(IntcInstancePtr,
							 EmacLiteIntrId);
			return XST_FAILURE;
		}
	}

	/*
	 * Wait for the frame to be transmitted.
	 */
	while (TransmitComplete == FALSE);

	/*
	 * If the MDIO is not configured in the core then return XST_SUCCESS
	 * as the frame has been transmitted.
	 */
	if (!XEmacLite_IsMdioConfigured(EmacLiteInstPtr)) {

		/*
		 * Disable and disconnect the EmacLite Interrupts.
		 */
		XEmacLite_DisableInterrupts(EmacLiteInstPtr);
		EmacLiteDisableIntrSystem(IntcInstancePtr, EmacLiteIntrId);
		return XST_SUCCESS;
	}

	/*
	 * Wait for the frame to be received.
	 */
	while (RecvFrameLength == 0);

	/*
	 * Check the received frame.
	 */
	Status = EmacLiteRecvFrame(EMACLITE_TEST_FRAME_SIZE);

	/*
	 *  Diasble the Loop Back.
	 */
	if (XEmacLite_IsMdioConfigured(EmacLiteInstPtr)) {
		/*
		 * Disable the MAC Loop back in the PHY.
		 */
		 Status |= EmacLiteDisablePhyLoopBack(EmacLiteInstPtr,
		 PhyAddress);
	}

	/*
	 * Disable and disconnect the EmacLite Interrupts.
	 */
	XEmacLite_DisableInterrupts(EmacLiteInstPtr);
	EmacLiteDisableIntrSystem(IntcInstancePtr, EmacLiteIntrId);
	if ((Status != XST_SUCCESS) && (Status != XST_NO_DATA)) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/******************************************************************************/
/**
*
* This function sends a frame of given size. This function assumes interrupt
* mode and sends the frame.
*
* @param	EmacLiteInstPtr is a pointer to the EmacLite instance.
* @param	PayloadSize is the size of the frame to create. The size only
*		reflects the payload size, it does not include the Ethernet
*		header size (14 bytes) nor the Ethernet CRC size (4 bytes).
*
* @return	XST_SUCCESS if successful, else XST_FAILURE.
*
* @note		None.
*
******************************************************************************/
static int EmacLiteSendFrame(XEmacLite *EmacLiteInstPtr,  u32 PayloadSize)
{
	int Status;
	u8 *FramePtr;
	u32 Index;

	/*
	 * Set the Complete flag to false.
	 */
	TransmitComplete = FALSE;

	/*
	 * Assemble the frame with a destination address and the source address.
	 */
	FramePtr = (u8 *)TxFrame;

	/*
	 * Set up the destination address as the local address for
	 * Phy Loopback and Internal loopback.
	 */
	if (XEmacLite_IsMdioConfigured(EmacLiteInstPtr) ||
		XEmacLite_IsLoopbackConfigured(EmacLiteInstPtr)) {

		*FramePtr++ = LocalAddress[0];
		*FramePtr++ = LocalAddress[1];
		*FramePtr++ = LocalAddress[2];
		*FramePtr++ = LocalAddress[3];
		*FramePtr++ = LocalAddress[4];
		*FramePtr++ = LocalAddress[5];
	} else {
		/*
		 * Fill in the valid Destination MAC address if
		 * the Loopback is not enabled.
		 */
		*FramePtr++ = RemoteAddress[0];
		*FramePtr++ = RemoteAddress[1];
		*FramePtr++ = RemoteAddress[2];
		*FramePtr++ = RemoteAddress[3];
		*FramePtr++ = RemoteAddress[4];
		*FramePtr++ = RemoteAddress[5];
	}

	/*
	 * Fill in the source MAC address.
	 */
	*FramePtr++ = LocalAddress[0];
	*FramePtr++ = LocalAddress[1];
	*FramePtr++ = LocalAddress[2];
	*FramePtr++ = LocalAddress[3];
	*FramePtr++ = LocalAddress[4];
	*FramePtr++ = LocalAddress[5];

	/*
	 * Set up the type/length field - be sure its in network order.
	 */
    *((u16 *)FramePtr) = Xil_Htons(PayloadSize);
    FramePtr++;
	FramePtr++;

	/*
	 * Now fill in the data field with known values so we can verify them.
	 */
	for (Index = 0; Index < PayloadSize; Index++) {
		*FramePtr++ = (u8)Index;
	}

	/*
	 * Now send the frame.
	 */
	Status = XEmacLite_Send(EmacLiteInstPtr, (u8 *)TxFrame,
				PayloadSize + XEL_HEADER_SIZE);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/******************************************************************************/
/**
*
* This function receives a frame of given size. This function assumes interrupt
* mode, receives the frame and verifies its contents.
*
* @param	PayloadSize is the size of the frame to receive.
*		The size only reflects the payload size, it does not include the
*		Ethernet header size (14 bytes) nor the Ethernet CRC size (4
*		bytes).
*
* @return	XST_SUCCESS if successful, a driver-specific return code if not.
*
* @note		None.
*
******************************************************************************/
static int EmacLiteRecvFrame(u32 PayloadSize)
{
	u8 *FramePtr;

	/*
	 * This assumes MAC does not strip padding or CRC.
	 */
	if (RecvFrameLength != 0) {
		int Index;

		/*
		 * Verify length, which should be the payload size.
		 */
		if ((RecvFrameLength- (XEL_HEADER_SIZE + XEL_FCS_SIZE)) !=
				PayloadSize) {
			return XST_LOOPBACK_ERROR;
		}

		/*
		 * Verify the contents of the Received Frame.
		 */
		FramePtr = (u8 *)RxFrame;
		FramePtr += XEL_HEADER_SIZE;	/* Get past the header */

		for (Index = 0; Index < PayloadSize; Index++) {
			if (*FramePtr++ != (u8)Index) {
				return XST_LOOPBACK_ERROR;
			}
		}
	}

	return XST_SUCCESS;
}


/******************************************************************************/
/**
*
* This function handles the receive callback from the EmacLite driver.
*
* @param	CallBackRef is the call back reference provided to the Handler.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void EmacLiteRecvHandler(void *CallBackRef)
{
	XEmacLite *XEmacInstancePtr;

	/*
	 * Convert the argument to something useful.
	 */
	XEmacInstancePtr = (XEmacLite *)CallBackRef;

	/*
	 * Handle the Receive callback.
	 */
	RecvFrameLength = XEmacLite_Recv(XEmacInstancePtr, (u8 *)RxFrame);

}

/******************************************************************************/
/**
*
* This function handles the transmit callback from the EmacLite driver.
*
* @param	CallBackRef is the call back reference provided to the Handler.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void EmacLiteSendHandler(void *CallBackRef)
{
	XEmacLite *XEmacInstancePtr;

	/*
	 * Convert the argument to something useful.
	 */
	XEmacInstancePtr = (XEmacLite *)CallBackRef;

	/*
	 * Handle the Transmit callback.
	 */
	TransmitComplete = TRUE;

}

/*****************************************************************************/
/**
*
* This function setups the interrupt system such that interrupts can occur
* for the EmacLite device. This function is application specific since the
* actual system may or may not have an interrupt controller.  The EmacLite
* could be directly connected to a processor without an interrupt controller.
* The user should modify this function to fit the application.
*
* @param	IntcInstancePtr is a pointer to the instance of the Intc.
* @param	EmacLiteInstPtr is a pointer to the instance of the EmacLite.
* @param	EmacLiteIntrId is the interrupt ID and is typically
*		XPAR_<INTC_instance>_<EMACLITE_instance>_VEC_ID
*		value from xparameters.h
*
* @return	XST_SUCCESS if successful, otherwise XST_FAILURE.
*
* @note		None.
*
******************************************************************************/
static int EmacLiteSetupIntrSystem(XIntc *IntcInstancePtr,
			 XEmacLite *EmacLiteInstPtr, u16 EmacLiteIntrId)
{
	int Status;

#ifndef TESTAPP_GEN
	/*
	 * Initialize the interrupt controller driver so that it is ready to
	 * use.
	 */
	Status = XIntc_Initialize(IntcInstancePtr, INTC_DEVICE_ID);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}
#endif
	/*
	 * Connect a device driver handler that will be called when an interrupt
	 * for the device occurs, the device driver handler performs the
	 * specific interrupt processing for the device.
	 */
	Status = XIntc_Connect(IntcInstancePtr,
				EmacLiteIntrId,
				XEmacLite_InterruptHandler,
				(void *)(EmacLiteInstPtr));
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

#ifndef TESTAPP_GEN
	/*
	 * Start the interrupt controller such that interrupts are enabled for
	 * all devices that cause interrupts, specific real mode so that
	 * the EmacLite can cause interrupts thru the interrupt controller.
	 */
	Status = XIntc_Start(IntcInstancePtr, XIN_REAL_MODE);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}
#endif

	/*
	 * Enable the interrupt for the EmacLite in the Interrupt controller.
	 */
	XIntc_Enable(IntcInstancePtr, EmacLiteIntrId);

#ifndef TESTAPP_GEN

	/*
	 * Initialize the exception table.
	 */
	Xil_ExceptionInit();

	/*
	 * Register the interrupt controller handler with the exception table.
	 */
	Xil_ExceptionRegisterHandler(XIL_EXCEPTION_ID_INT,
				(Xil_ExceptionHandler) XIntc_InterruptHandler,
				IntcInstancePtr);

	/*
	 * Enable non-critical exceptions.
	 */
	Xil_ExceptionEnable();

#endif /* TESTAPP_GEN */

	return XST_SUCCESS;
}


/*****************************************************************************/
/**
*
* This function disables the interrupts that occur for the EmacLite device.
*
* @param	IntcInstancePtr is the pointer to the instance of the INTC
*		component.
* @param	EmacLiteIntrId is the interrupt ID and is typically
*		XPAR_<INTC_instance>_<EMACLITE_instance>_VEC_ID
*		value from xparameters.h.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void EmacLiteDisableIntrSystem(XIntc *IntcInstancePtr,
							 u16 EmacLiteIntrId)
{
	/*
	 * Disconnect and disable the interrupts for the EmacLite device.
	 */
	XIntc_Disconnect(IntcInstancePtr, EmacLiteIntrId);

}






