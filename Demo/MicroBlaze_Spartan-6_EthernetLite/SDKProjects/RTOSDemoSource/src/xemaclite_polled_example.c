#define TESTAPP_GEN

/* $Id: xemaclite_polled_example.c,v 1.1.2.2 2010/08/06 15:11:04 anirudh Exp $
*/
/******************************************************************************
*
* (c) Copyright 2004-2010 Xilinx, Inc. All rights reserved.
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
******************************************************************************/
/*****************************************************************************/
/**
* @file xemaclite_polled_example.c
*
* This file contains an example for using the EmacLite hardware and driver.
* This file contains an polled mode example outlining the transmission/reception
* of an Ethernet frame of 1000 bytes of payload.
*
* If the MDIO interface is NOT configured in the EmacLite core then this example
* will only transmit a frame.
* If the MDIO interface is configured in the EmacLite core then this example
* will enable the MAC loopback in the PHY device, then transmit the frame and
* compare the received frame.
*
* @note
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.01a ecm  21/05/04 First release
* 1.01a sv   06/06/05 Minor changes to comply to Doxygen and coding guidelines
* 2.00a ktn  02/25/09 Updated to use PHY loop back if MDIO is configured in
*		      core and updated to be used in Test App
* 3.00a ktn  10/22/09 Updated example to use the macros that have been changed
*		      in the driver to remove _m from the name of the macro.
* 3.01a ktn  07/08/10 Updated example to support Little Endian MicroBlaze.
*
* </pre>
*
*****************************************************************************/

/***************************** Include Files *********************************/

#include "xemaclite_example.h"

/************************** Constant Definitions *****************************/

/*
 * The Size of the Test Frame.
 */
#define EMACLITE_TEST_FRAME_SIZE	1000

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

int EmacLitePolledExample(u16 DeviceId);

static int EmacLiteSendFrame(XEmacLite *InstancePtr, u32 PayloadSize);

static int EmacLiteRecvFrame(u32 PayloadSize);

/************************** Variable Definitions *****************************/

/*
 * Set up valid local and remote MAC addresses. This loop back test uses the
 * LocalAddress both as a source and destination MAC address.
 */
static u8 LocalAddress[XEL_MAC_ADDR_SIZE] =
{
	0x00, 0x0A, 0x35, 0x01, 0x02, 0x03
};
static u8 RemoteAddress[XEL_MAC_ADDR_SIZE] =
{
	0x00, 0x10, 0xa4, 0xb6, 0xfd, 0x09
};

/****************************************************************************/
/**
*
* This function is the main function of the EmacLite polled example.
*
* @param	None.
*
* @return	XST_SUCCESS to indicate success, otherwise XST_FAILURE .
*
* @note		None.
*
*****************************************************************************/
#ifndef TESTAPP_GEN
int main()
{
	int Status;

	/*
	 * Run the EmacLite Polled example, specify the Device ID that is
	 * generated in xparameters.h.
	 */
	Status = EmacLitePolledExample(EMAC_DEVICE_ID);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}
#endif

/*****************************************************************************/
/**
*
* The main entry point for the EmacLite driver example in polled mode.
*
* This function will transmit/receive the Ethernet frames and verify the
* data in the received frame (if the MDIO interface is configured in the
* EmacLite core).
* This function simply transmits a frame if the MDIO interface is not
* configured in the EmacLite core.
*
* @param	DeviceId is device ID of the XEmacLite Device , typically
*		XPAR_<EMAC_instance>_DEVICE_ID value from xparameters.h.
*
* @return	XST_SUCCESS to indicate success, XST_FAILURE otherwise.
*
* @note		None.
*
******************************************************************************/
int EmacLitePolledExample(u16 DeviceId)
{
	int Status;
	XEmacLite *EmacLiteInstPtr = &EmacLiteInstance;
	u32 PhyAddress = 0;
	RecvFrameLength = 0;
	XEmacLite_Config *ConfigPtr;

	/*
	 * Initialize the EmacLite device.
	 */
	ConfigPtr = XEmacLite_LookupConfig(DeviceId);
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
	 * Check if there is a TX buffer available, if there isn't it is an
	 * error.
	 */
	if (XEmacLite_TxBufferAvailable(EmacLiteInstPtr) != TRUE) {
		return XST_FAILURE;
	}

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
			return XST_FAILURE;
		}
	}


	/*
	 * Reset the receive frame length to zero.
	 */
	RecvFrameLength = 0;
	Status = EmacLiteSendFrame(EmacLiteInstPtr, EMACLITE_TEST_FRAME_SIZE);
	if (Status != XST_SUCCESS) {
		if (XEmacLite_IsMdioConfigured(EmacLiteInstPtr)) {
			/*
			 * Disable the MAC Loop back in the PHY.
			 */
			EmacLiteDisablePhyLoopBack(EmacLiteInstPtr,
							 PhyAddress);
			return XST_FAILURE;
		}
	}

	/*
	 * If the MDIO is not configured in the core then return XST_SUCCESS
	 * as the frame has been transmitted.
	 */
	if (!XEmacLite_IsMdioConfigured(EmacLiteInstPtr)) {
		return XST_SUCCESS;
	}


	/*
	 * Poll for receive packet.
	 */
	while ((volatile u32)RecvFrameLength == 0)  {
		RecvFrameLength = XEmacLite_Recv(EmacLiteInstPtr,
						(u8 *)RxFrame);
	}

	/*
	 * Check the received frame.
	 */
	Status = EmacLiteRecvFrame(EMACLITE_TEST_FRAME_SIZE);
	if ((Status != XST_SUCCESS) && (Status != XST_NO_DATA)) {
		/*
		 * Disable the MAC Loop back in the PHY.
		 */
		EmacLiteDisablePhyLoopBack(EmacLiteInstPtr, PhyAddress);
		return XST_FAILURE;
	}


	/*
	 * Disable the MAC Loop back in the PHY.
	 */
	EmacLiteDisablePhyLoopBack(EmacLiteInstPtr, PhyAddress);

	return XST_SUCCESS;
}

/******************************************************************************/
/**
*
* This function sends a frame of given size.
*
* @param	XEmacInstancePtr is a pointer to the XEmacLite instance.
* @param	PayloadSize is the size of the frame to create. The size only
*		reflects the payload size, it does not include the Ethernet
*		header size (14 bytes) nor the Ethernet CRC size (4 bytes).
*
* @return	XST_SUCCESS if successful, else a driver-specific return code.
*
* @note		None.
*
******************************************************************************/
static int EmacLiteSendFrame(XEmacLite *InstancePtr, u32 PayloadSize)
{
	u8 *FramePtr;
	int Index;
	FramePtr = (u8 *)TxFrame;

	/*
	 * Set up the destination address as the local address for
	 * Phy Loopback.
	 */
	if (XEmacLite_IsMdioConfigured(InstancePtr)) {

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
	 * Now fill in the data field with known values so we can verify them
	 * on receive.
	 */
	for (Index = 0; Index < PayloadSize; Index++) {
		*FramePtr++ = (u8)Index;
	}

	/*
	 * Now send the frame.
	 */
	return XEmacLite_Send(InstancePtr, (u8 *)TxFrame,
				PayloadSize + XEL_HEADER_SIZE);

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






