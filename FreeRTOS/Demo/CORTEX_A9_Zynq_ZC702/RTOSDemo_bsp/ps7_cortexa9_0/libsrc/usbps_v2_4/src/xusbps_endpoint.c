/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
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
/******************************************************************************/
/**
 * @file xusbps_endpoint.c
* @addtogroup usbps_v2_4
* @{
 *
 * Endpoint specific function implementations.
 *
 * @note     None.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- --------------------------------------------------------
 * 1.00a jz  10/10/10 First release
 * 1.03a nm  09/21/12 Fixed CR#678977. Added proper sequence for setup packet
 *                    handling.
 * 1.04a nm  11/02/12 Fixed CR#683931. Mult bits are set properly in dQH.
 * 2.00a kpc 04/03/14 Fixed CR#777763. Updated the macro names 
 * 2.1   kpc 04/28/14 Added XUsbPs_EpBufferSendWithZLT api and merged common
 *		      code to XUsbPs_EpQueueRequest.
 * 2.3   bss 01/19/16 Modified XUsbPs_EpQueueRequest function to fix CR#873972
 *            (moving of dTD Head/Tail Pointers)and CR#873974(invalidate
 *            Caches After Buffer Receive in Endpoint Buffer Handler...)
 * </pre>
 ******************************************************************************/

/***************************** Include Files **********************************/

#include <string.h> /* for bzero() */
#include <stdio.h>

#include "xusbps.h"
#include "xusbps_endpoint.h"

/************************** Constant Definitions ******************************/

/**************************** Type Definitions ********************************/

/************************** Variable Definitions ******************************/

/************************** Function Prototypes ******************************/

static void XUsbPs_EpListInit(XUsbPs_DeviceConfig *DevCfgPtr);
static void XUsbPs_dQHInit(XUsbPs_DeviceConfig *DevCfgPtr);
static int  XUsbPs_dTDInit(XUsbPs_DeviceConfig *DevCfgPtr);
static int  XUsbPs_dTDAttachBuffer(XUsbPs_dTD *dTDPtr,
					const u8 *BufferPtr, u32 BufferLen);

static void XUsbPs_dQHSetMaxPacketLenISO(XUsbPs_dQH *dQHPtr, u32 Len);

/* Functions to reconfigure endpoint upon host's set alternate interface
 * request.
 */
static void XUsbPs_dQHReinitEp(XUsbPs_DeviceConfig *DevCfgPtr,
					int EpNum, unsigned short NewDirection);
static int XUsbPs_dTDReinitEp(XUsbPs_DeviceConfig *DevCfgPtr,
					int EpNum, unsigned short NewDirection);
static int XUsbPs_EpQueueRequest(XUsbPs *InstancePtr, u8 EpNum,
				const u8 *BufferPtr, u32 BufferLen, u8 ReqZero);

/******************************* Functions ************************************/

/*****************************************************************************/
/**
 *
 * This function configures the DEVICE side of the controller. The caller needs
 * to pass in the desired configuration (e.g. number of endpoints) and a
 * DMAable buffer that will hold the Queue Head List and the Transfer
 * Descriptors. The required size for this buffer can be obtained by the caller
 * using the: XUsbPs_DeviceMemRequired() macro.
 *
 * @param	InstancePtr is a pointer to the XUsbPs instance of the
 *		controller.
 * @param	CfgPtr is a pointer to the configuration structure that contains
 *		the desired DEVICE side configuration.
 *
 * @return
 *		- XST_SUCCESS: The operation completed successfully.
 *		- XST_FAILURE: An error occured.
 *
 * @note
 * 		The caller may configure the controller for both, DEVICE and
 * 		HOST side.
 *
 ******************************************************************************/
int XUsbPs_ConfigureDevice(XUsbPs *InstancePtr,
			    const XUsbPs_DeviceConfig *CfgPtr)
{
	int	Status;
	u32 ModeValue = 0x0;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(CfgPtr      != NULL);

	/* Copy the configuration data over into the local instance structure */
	InstancePtr->DeviceConfig = *CfgPtr;


	/* Align the buffer to a 2048 byte (XUSBPS_dQH_BASE_ALIGN) boundary.*/
	InstancePtr->DeviceConfig.PhysAligned =
		(InstancePtr->DeviceConfig.DMAMemPhys +
					 XUSBPS_dQH_BASE_ALIGN) &
						~(XUSBPS_dQH_BASE_ALIGN -1);

	/* Initialize the endpoint pointer list data structure. */
	XUsbPs_EpListInit(&InstancePtr->DeviceConfig);


	/* Initialize the Queue Head structures in DMA memory. */
	XUsbPs_dQHInit(&InstancePtr->DeviceConfig);


	/* Initialize the Transfer Descriptors in DMA memory.*/
	Status = XUsbPs_dTDInit(&InstancePtr->DeviceConfig);
	if (XST_SUCCESS != Status) {
		return XST_FAILURE;
	}

	/* Changing the DEVICE mode requires a controller RESET. */
	if (XST_SUCCESS != XUsbPs_Reset(InstancePtr)) {
		return XST_FAILURE;
	}

	/* Set the Queue Head List address. */
	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress,
				XUSBPS_EPLISTADDR_OFFSET,
				InstancePtr->DeviceConfig.PhysAligned);

	/* Set the USB mode register to configure DEVICE mode.
	 *
	 * XUSBPS_MODE_SLOM_MASK note:
	 *   Disable Setup Lockout. Setup Lockout is not required as we
	 *   will be using the tripwire mechanism when handling setup
	 *   packets.
	 */
	ModeValue = XUSBPS_MODE_CM_DEVICE_MASK | XUSBPS_MODE_SLOM_MASK;

	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress,
				XUSBPS_MODE_OFFSET, ModeValue);

	XUsbPs_SetBits(InstancePtr, XUSBPS_OTGCSR_OFFSET,
				XUSBPS_OTGSC_OT_MASK);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
* This function sends a given data buffer.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	EpNum is the number of the endpoint to receive data from.
* @param	BufferPtr is a pointer to the buffer to send.
* @param	BufferLen is the Buffer length.
*
* @return
*		- XST_SUCCESS: The operation completed successfully.
*		- XST_FAILURE: An error occured.
*		- XST_USB_BUF_TOO_BIG: Provided buffer is too big (>16kB).
*		- XST_USB_NO_DESC_AVAILABLE: No TX descriptor is available.
*
******************************************************************************/
int XUsbPs_EpBufferSend(XUsbPs *InstancePtr, u8 EpNum,
				const u8 *BufferPtr, u32 BufferLen)
{
	Xil_AssertNonvoid(InstancePtr  != NULL);
	Xil_AssertNonvoid(EpNum < InstancePtr->DeviceConfig.NumEndpoints);

	return XUsbPs_EpQueueRequest(InstancePtr, EpNum, BufferPtr,
					BufferLen, FALSE);
}

/*****************************************************************************/
/**
* This function sends a given data buffer and also zero length packet if the
* Bufferlen is in multiples of endpoint max packet size.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	EpNum is the number of the endpoint to receive data from.
* @param	BufferPtr is a pointer to the buffer to send.
* @param	BufferLen is the Buffer length.
*
* @return
*		- XST_SUCCESS: The operation completed successfully.
*		- XST_FAILURE: An error occured.
*		- XST_USB_BUF_TOO_BIG: Provided buffer is too big (>16kB).
*		- XST_USB_NO_DESC_AVAILABLE: No TX descriptor is available.
*
******************************************************************************/
int XUsbPs_EpBufferSendWithZLT(XUsbPs *InstancePtr, u8 EpNum,
				const u8 *BufferPtr, u32 BufferLen)
{
	u8 ReqZero = FALSE;
	XUsbPs_EpSetup *Ep;

	Xil_AssertNonvoid(InstancePtr  != NULL);
	Xil_AssertNonvoid(EpNum < InstancePtr->DeviceConfig.NumEndpoints);

	Ep = &InstancePtr->DeviceConfig.EpCfg[EpNum].In;

	if ((BufferLen >= Ep->MaxPacketSize) &&
		(BufferLen % Ep->MaxPacketSize == 0)) {
		ReqZero = TRUE;
	}

	return XUsbPs_EpQueueRequest(InstancePtr, EpNum, BufferPtr,
						BufferLen, ReqZero);
}

/*****************************************************************************/
/**
* This function sends a given data buffer and also sends ZLT packet if it is
* requested.
*
* @param	InstancePtr is a pointer to XUsbPs instance of the controller.
* @param	EpNum is the number of the endpoint to receive data from.
* @param	BufferPtr is a pointer to the buffer to send.
* @param	BufferLen is the Buffer length.
* @param	ReqZero is the
*
* @return
*		- XST_SUCCESS: The operation completed successfully.
*		- XST_FAILURE: An error occured.
*		- XST_USB_BUF_TOO_BIG: Provided buffer is too big (>16kB).
*		- XST_USB_NO_DESC_AVAILABLE: No TX descriptor is available.
*
******************************************************************************/
static int XUsbPs_EpQueueRequest(XUsbPs *InstancePtr, u8 EpNum,
				const u8 *BufferPtr, u32 BufferLen, u8 ReqZero)
{
	int		Status;
	u32		Token;
	XUsbPs_EpIn	*Ep;
	XUsbPs_dTD	*DescPtr;
	u32 		Length;
	u32		PipeEmpty = 1;
	u32		Mask = 0x00010000;
	u32		BitMask = Mask << EpNum;
	u32		RegValue;
	u32		Temp;
	u32 exit = 1;


	/* Locate the next available buffer in the ring. A buffer is available
	 * if its descriptor is not active.
	 */
	Ep = &InstancePtr->DeviceConfig.Ep[EpNum].In;

	Xil_DCacheFlushRange((unsigned int)BufferPtr, BufferLen);

	if(Ep->dTDTail != Ep->dTDHead) {
		PipeEmpty = 0;
	}
	XUsbPs_dTDInvalidateCache(Ep->dTDHead);

	/* Tell the caller if we do not have any descriptors available. */
	if (XUsbPs_dTDIsActive(Ep->dTDHead)) {
		return XST_USB_NO_DESC_AVAILABLE;
	}

	/* Remember the current head. */
	DescPtr = Ep->dTDHead;

	do {

		/* Tell the caller if we do not have any descriptors available. */
		if (XUsbPs_dTDIsActive(Ep->dTDHead)) {
			return XST_USB_NO_DESC_AVAILABLE;
		}

		Length = (BufferLen > XUSBPS_dTD_BUF_MAX_SIZE) ? XUSBPS_dTD_BUF_MAX_SIZE : BufferLen;
		/* Attach the provided buffer to the current descriptor.*/
		Status = XUsbPs_dTDAttachBuffer(Ep->dTDHead, BufferPtr, Length);
		if (XST_SUCCESS != Status) {
			return XST_FAILURE;
		}
		BufferLen -= Length;
		BufferPtr += Length;

		XUsbPs_dTDSetActive(Ep->dTDHead);
		if (BufferLen == 0 && (ReqZero == FALSE)) {
			XUsbPs_dTDSetIOC(Ep->dTDHead);
			exit = 0;
		}
		XUsbPs_dTDClrTerminate(Ep->dTDHead);
		XUsbPs_dTDFlushCache(Ep->dTDHead);

		/* Advance the head descriptor pointer to the next descriptor. */
		Ep->dTDHead = XUsbPs_dTDGetNLP(Ep->dTDHead);
		/* Terminate the next descriptor and flush the cache.*/
		XUsbPs_dTDInvalidateCache(Ep->dTDHead);

		if (ReqZero && BufferLen == 0) {
			ReqZero = FALSE;
		}

	} while(BufferLen || exit);

	XUsbPs_dTDSetTerminate(Ep->dTDHead);
	XUsbPs_dTDFlushCache(Ep->dTDHead);

	if(!PipeEmpty) {
		/* Read the endpoint prime register. */
		RegValue = XUsbPs_ReadReg(InstancePtr->Config.BaseAddress, XUSBPS_EPPRIME_OFFSET);
		if(RegValue & BitMask) {
			return XST_SUCCESS;
		}

		do {
			RegValue = XUsbPs_ReadReg(InstancePtr->Config.BaseAddress, XUSBPS_CMD_OFFSET);
			XUsbPs_WriteReg(InstancePtr->Config.BaseAddress, XUSBPS_CMD_OFFSET,
						RegValue | XUSBPS_CMD_ATDTW_MASK);
			Temp = XUsbPs_ReadReg(InstancePtr->Config.BaseAddress, XUSBPS_EPRDY_OFFSET)
						& BitMask;
		} while(!(XUsbPs_ReadReg(InstancePtr->Config.BaseAddress, XUSBPS_CMD_OFFSET) &
				XUSBPS_CMD_ATDTW_MASK));

		RegValue = XUsbPs_ReadReg(InstancePtr->Config.BaseAddress, XUSBPS_CMD_OFFSET);
		XUsbPs_WriteReg(InstancePtr->Config.BaseAddress, XUSBPS_CMD_OFFSET,
					RegValue & ~XUSBPS_CMD_ATDTW_MASK);

		if(Temp) {
			return XST_SUCCESS;
		}
	}

	/* Check, if the DMA engine is still running. If it is running, we do
	 * not clear Queue Head fields.
	 *
	 * Same cache rule as for the Transfer Descriptor applies for the Queue
	 * Head.
	 */
	XUsbPs_dQHInvalidateCache(Ep->dQH);
	/* Add the dTD to the dQH */
	XUsbPs_WritedQH(Ep->dQH, XUSBPS_dQHdTDNLP, DescPtr);
	Token = XUsbPs_ReaddQH(Ep->dQH, XUSBPS_dQHdTDTOKEN);
	Token &= ~(XUSBPS_dTDTOKEN_ACTIVE_MASK | XUSBPS_dTDTOKEN_HALT_MASK);
	XUsbPs_WritedQH(Ep->dQH, XUSBPS_dQHdTDTOKEN, Token);

	XUsbPs_dQHFlushCache(Ep->dQH);

	Status = XUsbPs_EpPrime(InstancePtr, EpNum, XUSBPS_EP_DIRECTION_IN);

	return Status;
}

/*****************************************************************************/
/**
 * This function receives a data buffer from the endpoint of the given endpoint
 * number.
 *
 * @param	InstancePtr is a pointer to the XUsbPs instance of the
 *		controller.
 * @param	EpNum is the number of the endpoint to receive data from.
 * @param	BufferPtr (OUT param) is a pointer to the buffer pointer to hold
 *		the reference of the data buffer.
 * @param	BufferLenPtr (OUT param) is a pointer to the integer that will
 *		hold the buffer length.
 * @param	Handle is the opaque handle to be used when the buffer is
 *		released.
 *
 * @return
 *		- XST_SUCCESS: The operation completed successfully.
 *		- XST_FAILURE: An error occured.
 *		- XST_USB_NO_BUF: No buffer available.
 *
 * @note
 * 		After handling the data in the buffer, the user MUST release
 * 		the buffer using the Handle by calling the
 * 		XUsbPs_EpBufferRelease() function.
 *
 ******************************************************************************/
int XUsbPs_EpBufferReceive(XUsbPs *InstancePtr, u8 EpNum,
				u8 **BufferPtr, u32 *BufferLenPtr, u32 *Handle)
{
	XUsbPs_EpOut	*Ep;
	XUsbPs_EpSetup	*EpSetup;
	u32 length = 0;

	Xil_AssertNonvoid(InstancePtr  != NULL);
	Xil_AssertNonvoid(BufferPtr    != NULL);
	Xil_AssertNonvoid(BufferLenPtr != NULL);
	Xil_AssertNonvoid(Handle       != NULL);
	Xil_AssertNonvoid(EpNum < InstancePtr->DeviceConfig.NumEndpoints);

	/* Locate the next available buffer in the ring. A buffer is available
	 * if its descriptor is not active.
	 */
	Ep = &InstancePtr->DeviceConfig.Ep[EpNum].Out;

	XUsbPs_dTDInvalidateCache(Ep->dTDCurr);

	if (XUsbPs_dTDIsActive(Ep->dTDCurr)) {
		return XST_USB_NO_BUF;
	}

	/* The buffer is not active which means that it has been processed by
	 * the DMA engine and contains valid data.
	 */
	EpSetup = &InstancePtr->DeviceConfig.EpCfg[EpNum].Out;


	/* Use the buffer pointer stored in the "user data" field of the
	 * Transfer Descriptor.
	 */
	*BufferPtr = (u8 *) XUsbPs_ReaddTD(Ep->dTDCurr,
						XUSBPS_dTDUSERDATA);

	length = EpSetup->BufSize -
			XUsbPs_dTDGetTransferLen(Ep->dTDCurr);

	if(length > 0) {
		*BufferLenPtr = length;
	}else {
		*BufferLenPtr = 0;
	}

	*Handle	= (u32) Ep->dTDCurr;


	/* Reset the descriptor's BufferPointer0 and Transfer Length fields to
	 * their original value. Note that we can not yet re-activate the
	 * descriptor as the caller will be using the attached buffer. Once the
	 * caller releases the buffer by calling XUsbPs_EpBufferRelease(), we
	 * can re-activate the descriptor.
	 */
	XUsbPs_WritedTD(Ep->dTDCurr, XUSBPS_dTDBPTR0, *BufferPtr);
	XUsbPs_dTDSetTransferLen(Ep->dTDCurr, EpSetup->BufSize);

	XUsbPs_dTDFlushCache(Ep->dTDCurr);

	return XST_SUCCESS;
}


/*****************************************************************************/
/**
* This function returns a previously received data buffer to the driver.
*
* @param	Handle is a pointer to the buffer that is returned.
*
* @return	None.
*
******************************************************************************/
void XUsbPs_EpBufferRelease(u32 Handle)
{
	XUsbPs_dTD		*dTDPtr;

	/* Perform sanity check on Handle.*/
	Xil_AssertVoid((0 != Handle) && (0 == (Handle % XUSBPS_dTD_ALIGN)));

	/* Activate the descriptor and clear the Terminate bit. Make sure to do
	 * the proper cache handling.
	 */
	dTDPtr = (XUsbPs_dTD *) Handle;

	XUsbPs_dTDInvalidateCache(dTDPtr);

	XUsbPs_dTDClrTerminate(dTDPtr);
	XUsbPs_dTDSetActive(dTDPtr);
	XUsbPs_dTDSetIOC(dTDPtr);

	XUsbPs_dTDFlushCache(dTDPtr);

}


/*****************************************************************************/
/**
 * This function sets the handler for endpoint events.
 *
 * @param	InstancePtr is a pointer to the XUsbPs instance of the
 *		controller.
 * @param	EpNum is the number of the endpoint to receive data from.
 * @param	Direction is the direction of the endpoint (bitfield):
 * 			- XUSBPS_EP_DIRECTION_OUT
 * 			- XUSBPS_EP_DIRECTION_IN
 * @param	CallBackFunc is the Handler callback function.
 *		Can be NULL if the user wants to disable the handler entry.
 * @param	CallBackRef is the user definable data pointer that will be
 *		passed back if the handler is called. May be NULL.
 *
 * @return
 *		- XST_SUCCESS: The operation completed successfully.
 *		- XST_FAILURE: An error occured.
 *		- XST_INVALID_PARAM: Invalid parameter passed.
 *
 * @note
 * 		The user can disable a handler by setting the callback function
 * 		pointer to NULL.
 *
 ******************************************************************************/
int XUsbPs_EpSetHandler(XUsbPs *InstancePtr, u8 EpNum, u8 Direction,
			 XUsbPs_EpHandlerFunc CallBackFunc,
			 void *CallBackRef)
{
	XUsbPs_Endpoint	*Ep;

	Xil_AssertNonvoid(InstancePtr  != NULL);
	Xil_AssertNonvoid(CallBackFunc != NULL);
	Xil_AssertNonvoid(EpNum < InstancePtr->DeviceConfig.NumEndpoints);

	Ep = &InstancePtr->DeviceConfig.Ep[EpNum];

	if(Direction & XUSBPS_EP_DIRECTION_OUT) {
		Ep->Out.HandlerFunc	= CallBackFunc;
		Ep->Out.HandlerRef	= CallBackRef;
	}

	if(Direction & XUSBPS_EP_DIRECTION_IN) {
		Ep->In.HandlerFunc	= CallBackFunc;
		Ep->In.HandlerRef	= CallBackRef;
	}

	return XST_SUCCESS;
}


/*****************************************************************************/
/**
* This function primes an endpoint.
*
* @param	InstancePtr is pointer to the XUsbPs instance.
* @param	EpNum is the number of the endpoint to receive data from.
* @param	Direction is the direction of the endpoint (bitfield):
* 			- XUSBPS_EP_DIRECTION_OUT
* 			- XUSBPS_EP_DIRECTION_IN
*
* @return
*		- XST_SUCCESS: The operation completed successfully.
*		- XST_FAILURE: An error occured.
*		- XST_INVALID_PARAM: Invalid parameter passed.
*
* @note		None.
*
******************************************************************************/
int XUsbPs_EpPrime(XUsbPs *InstancePtr, u8 EpNum, u8 Direction)
{
	u32	Mask;

	Xil_AssertNonvoid(InstancePtr  != NULL);
	Xil_AssertNonvoid(EpNum < InstancePtr->DeviceConfig.NumEndpoints);

	/* Get the right bit mask for the endpoint direction. */
	switch (Direction) {

	case XUSBPS_EP_DIRECTION_OUT:
		Mask = 0x00000001;
		break;

	case XUSBPS_EP_DIRECTION_IN:
		Mask = 0x00010000;
		break;

	default:
		return XST_INVALID_PARAM;
	}

	/* Write the endpoint prime register. */
	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress,
				XUSBPS_EPPRIME_OFFSET, Mask << EpNum);

	return XST_SUCCESS;
}


/*****************************************************************************/
/**
* This function extracts the Setup Data from a given endpoint.
*
* @param	InstancePtr is a pointer to the XUsbPs instance of the
*		controller.
* @param	EpNum is the number of the endpoint to receive data from.
* @param	SetupDataPtr is a pointer to the setup data structure to be
*		filled.
*
* @return
*		- XST_SUCCESS: The operation completed successfully.
*		- XST_FAILURE: An error occured.
*
* @note		None.
******************************************************************************/
int XUsbPs_EpGetSetupData(XUsbPs *InstancePtr, int EpNum,
				XUsbPs_SetupData *SetupDataPtr)
{
	XUsbPs_EpOut	*Ep;

	u32	Data[2];
	u8	*p;

	int Timeout;

	Xil_AssertNonvoid(InstancePtr  != NULL);
	Xil_AssertNonvoid(SetupDataPtr != NULL);
	Xil_AssertNonvoid(EpNum < InstancePtr->DeviceConfig.NumEndpoints);

	Ep = &InstancePtr->DeviceConfig.Ep[EpNum].Out;


	/* Get the data from the Queue Heads Setup buffer into local variables
	 * so we can extract the setup data values.
	 */
	do {
		/* Arm the tripwire. The tripwire will tell us if a new setup
		 * packet arrived (in which case the tripwire bit will be
		 * cleared) while we were reading the buffer. If a new setup
		 * packet arrived the buffer is corrupted and we continue
		 * reading.
		 */
		XUsbPs_SetSetupTripwire(InstancePtr);

		XUsbPs_dQHInvalidateCache(Ep->dQH);

		Data[0] = XUsbPs_ReaddQH(Ep->dQH, XUSBPS_dQHSUB0);
		Data[1] = XUsbPs_ReaddQH(Ep->dQH, XUSBPS_dQHSUB1);
	} while (FALSE == XUsbPs_SetupTripwireIsSet(InstancePtr));

	/* Clear the pending endpoint setup stat bit.
	 */
	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress,
				XUSBPS_EPSTAT_OFFSET, 1 << EpNum);

	/* Clear the Tripwire bit and continue.
	 */
	XUsbPs_ClrSetupTripwire(InstancePtr);


	/* Data in the setup buffer is being converted by the core to big
	 * endian format. We have to take care of proper byte swapping when
	 * reading the setup data values.
	 *
	 * Need to check if there is a smarter way to do this and take the
	 * processor/memory-controller endianess into account?
	 */
	p = (u8 *) Data;

	SetupDataPtr->bmRequestType	= p[0];
	SetupDataPtr->bRequest		= p[1];
	SetupDataPtr->wValue		= (p[3] << 8) | p[2];
	SetupDataPtr->wIndex		= (p[5] << 8) | p[4];
	SetupDataPtr->wLength		= (p[7] << 8) | p[6];

	/* Before we leave we need to make sure that the endpoint setup bit has
	 * cleared. It needs to be 0 before the endpoint can be re-primed.
	 *
	 * Note: According to the documentation this endpoint setup bit should
	 * clear within 1-2us after it has been written above. This means that
	 * we should never catch it being 1 here. However, we still need to
	 * poll it to make sure. Just in case, we use a counter 'Timeout' so we
	 * won't hang here if the bit is stuck for some reason.
	 */
	Timeout = XUSBPS_TIMEOUT_COUNTER;
	while ((XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
				XUSBPS_EPSTAT_OFFSET) &
				(1 << EpNum)) && --Timeout) {
		/* NOP */
	}
	if (0 == Timeout) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}


/*****************************************************************************/
/**
*
* This function initializes the endpoint pointer data structure.
*
* The function sets up the local data structure with the aligned addresses for
* the Queue Head and Transfer Descriptors.
*
* @param	DevCfgPtr is pointer to the XUsbPs DEVICE configuration
*		structure.
*
* @return	none
*
* @note
* 		Endpoints of type XUSBPS_EP_TYPE_NONE are not used in the
* 		system. Therefore no memory is reserved for them.
*
******************************************************************************/
static void XUsbPs_EpListInit(XUsbPs_DeviceConfig *DevCfgPtr)
{
	int	EpNum;
	u8	*p;

	XUsbPs_Endpoint	*Ep;
	XUsbPs_EpConfig	*EpCfg;

	/* Set up the XUsbPs_Endpoint array. This array is used to define the
	 * location of the Queue Head list and the Transfer Descriptors in the
	 * block of DMA memory that has been passed into the driver.
	 *
	 * 'p' is used to set the pointers in the local data structure.
	 * Initially 'p' is pointed to the beginning of the DMAable memory
	 * block. As pointers are assigned, 'p' is incremented by the size of
	 * the respective object.
	 */
	Ep	= DevCfgPtr->Ep;
	EpCfg	= DevCfgPtr->EpCfg;

	/* Start off with 'p' pointing to the (aligned) beginning of the DMA
	 * buffer.
	 */
	p = (u8 *) DevCfgPtr->PhysAligned;


	/* Initialize the Queue Head pointer list.
	 *
	 * Each endpoint has two Queue Heads. One for the OUT direction and one
	 * for the IN direction. An OUT Queue Head is always followed by an IN
	 * Queue Head.
	 *
	 * Queue Head alignment is XUSBPS_dQH_ALIGN.
	 *
	 * Note that we have to reserve space here for unused endpoints.
	 */
	for (EpNum = 0; EpNum < DevCfgPtr->NumEndpoints; ++EpNum) {
		/* OUT Queue Head */
		Ep[EpNum].Out.dQH = (XUsbPs_dQH *) p;
		p += XUSBPS_dQH_ALIGN;

		/* IN Queue Head */
		Ep[EpNum].In.dQH = (XUsbPs_dQH *) p;
		p += XUSBPS_dQH_ALIGN;
	}


	/* 'p' now points to the first address after the Queue Head list. The
	 * Transfer Descriptors start here.
	 *
	 * Each endpoint has a variable number of Transfer Descriptors
	 * depending on user configuration.
	 *
	 * Transfer Descriptor alignment is XUSBPS_dTD_ALIGN.
	 */
	for (EpNum = 0; EpNum < DevCfgPtr->NumEndpoints; ++EpNum) {
		/* OUT Descriptors.
		 */
		if (XUSBPS_EP_TYPE_NONE != EpCfg[EpNum].Out.Type) {
			Ep[EpNum].Out.dTDs		= (XUsbPs_dTD *) p;
			Ep[EpNum].Out.dTDCurr	= (XUsbPs_dTD *) p;
			p += XUSBPS_dTD_ALIGN * EpCfg[EpNum].Out.NumBufs;
		}

		/* IN Descriptors.
		 */
		if (XUSBPS_EP_TYPE_NONE != EpCfg[EpNum].In.Type) {
			Ep[EpNum].In.dTDs		= (XUsbPs_dTD *) p;
			Ep[EpNum].In.dTDHead	= (XUsbPs_dTD *) p;
			Ep[EpNum].In.dTDTail	= (XUsbPs_dTD *) p;
			p += XUSBPS_dTD_ALIGN * EpCfg[EpNum].In.NumBufs;
		}
	}


	/* 'p' now points to the first address after the Transfer Descriptors.
	 * The data buffers for the OUT Transfer Desciptors start here.
	 *
	 * Note that IN (TX) Transfer Descriptors are not assigned buffers at
	 * this point. Buffers will be assigned when the user calls the send()
	 * function.
	 */
	for (EpNum = 0; EpNum < DevCfgPtr->NumEndpoints; ++EpNum) {

		if (XUSBPS_EP_TYPE_NONE != EpCfg[EpNum].Out.Type) {
			/* If BufSize for this endpoint is set to 0 it means
			 * that we do not need to attach a buffer to this
			 * descriptor. We also initialize it's buffer pointer
			 * to NULL.
			 */
			if (0 == EpCfg[EpNum].Out.BufSize) {
				Ep[EpNum].Out.dTDBufs = NULL;
				continue;
			}

			Ep[EpNum].Out.dTDBufs = p;
			p += EpCfg[EpNum].Out.BufSize * EpCfg[EpNum].Out.NumBufs;
		}
	}


	/* Initialize the endpoint event handlers to NULL.
	 */
	for (EpNum = 0; EpNum < DevCfgPtr->NumEndpoints; ++EpNum) {
		Ep[EpNum].Out.HandlerFunc = NULL;
		Ep[EpNum].In.HandlerFunc  = NULL;
	}
}


/*****************************************************************************/
/**
*
* This function initializes the Queue Head List in memory.
*
* @param	DevCfgPtr is a pointer to the XUsbPs DEVICE configuration
*		structure.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static void XUsbPs_dQHInit(XUsbPs_DeviceConfig *DevCfgPtr)
{
	int	EpNum;

	XUsbPs_Endpoint	*Ep;
	XUsbPs_EpConfig	*EpCfg;

	/* Setup pointers for simpler access. */
	Ep	= DevCfgPtr->Ep;
	EpCfg	= DevCfgPtr->EpCfg;


	/* Go through the list of Queue Head entries and:
	 *
	 * - Set Transfer Descriptor addresses
	 * - Set Maximum Packet Size
	 * - Disable Zero Length Termination (ZLT) for non-isochronous transfers
	 * - Enable Interrupt On Setup (IOS)
	 *
	 */
	for (EpNum = 0; EpNum < DevCfgPtr->NumEndpoints; ++EpNum) {

		/* OUT Queue Heads.*/
		if (XUSBPS_EP_TYPE_NONE != EpCfg[EpNum].Out.Type) {
			XUsbPs_WritedQH(Ep[EpNum].Out.dQH,
					XUSBPS_dQHCPTR, Ep[EpNum].Out.dTDs);

			/* For isochronous, ep max packet size translates to different
			 * values in queue head than other types.
			 * Also	enable ZLT for isochronous.
			 */
			if(XUSBPS_EP_TYPE_ISOCHRONOUS == EpCfg[EpNum].Out.Type) {
				XUsbPs_dQHSetMaxPacketLenISO(Ep[EpNum].Out.dQH,
                        EpCfg[EpNum].Out.MaxPacketSize);
				XUsbPs_dQHEnableZLT(Ep[EpNum].Out.dQH);
			}else {
				XUsbPs_dQHSetMaxPacketLen(Ep[EpNum].Out.dQH,
					    EpCfg[EpNum].Out.MaxPacketSize);
				XUsbPs_dQHDisableZLT(Ep[EpNum].Out.dQH);
			}

			/* Only control OUT needs this */
			if(XUSBPS_EP_TYPE_CONTROL == EpCfg[EpNum].Out.Type) {
				XUsbPs_dQHSetIOS(Ep[EpNum].Out.dQH);
			}

			/* Set up the overlay next dTD pointer. */
			XUsbPs_WritedQH(Ep[EpNum].Out.dQH,
					XUSBPS_dQHdTDNLP, Ep[EpNum].Out.dTDs);

			XUsbPs_dQHFlushCache(Ep[EpNum].Out.dQH);
		}


		/* IN Queue Heads. */
		if (XUSBPS_EP_TYPE_NONE != EpCfg[EpNum].In.Type) {
			XUsbPs_WritedQH(Ep[EpNum].In.dQH,
				  XUSBPS_dQHCPTR, Ep[EpNum].In.dTDs);


			/* Isochronous ep packet size can be larger than 1024.*/
			if(XUSBPS_EP_TYPE_ISOCHRONOUS == EpCfg[EpNum].In.Type) {
				XUsbPs_dQHSetMaxPacketLenISO(Ep[EpNum].In.dQH,
						EpCfg[EpNum].In.MaxPacketSize);
				XUsbPs_dQHEnableZLT(Ep[EpNum].In.dQH);
			}else {
				XUsbPs_dQHSetMaxPacketLen(Ep[EpNum].In.dQH,
					    EpCfg[EpNum].In.MaxPacketSize);
				XUsbPs_dQHDisableZLT(Ep[EpNum].In.dQH);
			}

			XUsbPs_dQHFlushCache(Ep[EpNum].In.dQH);
		}
	}
}


/*****************************************************************************/
/**
 *
 * This function initializes the Transfer Descriptors lists in memory.
 *
 * @param	DevCfgPtr is a pointer to the XUsbPs DEVICE configuration
 *		structure.
 *
 * @return
 *		- XST_SUCCESS: The operation completed successfully.
 *		- XST_FAILURE: An error occured.
 *
 ******************************************************************************/
static int XUsbPs_dTDInit(XUsbPs_DeviceConfig *DevCfgPtr)
{
	int	EpNum;

	XUsbPs_Endpoint	*Ep;
	XUsbPs_EpConfig	*EpCfg;

	/* Setup pointers for simpler access. */
	Ep	= DevCfgPtr->Ep;
	EpCfg	= DevCfgPtr->EpCfg;


	/* Walk through the list of endpoints and initialize their Transfer
	 * Descriptors.
	 */
	for (EpNum = 0; EpNum < DevCfgPtr->NumEndpoints; ++EpNum) {
		int	Td;
		int	NumdTD;

		XUsbPs_EpOut	*Out = &Ep[EpNum].Out;
		XUsbPs_EpIn	*In  = &Ep[EpNum].In;


		/* OUT Descriptors
		 * ===============
		 *
		 * + Set the next link pointer
		 * + Set the interrupt complete and the active bit
		 * + Attach the buffer to the dTD
		 */
		if (XUSBPS_EP_TYPE_NONE != EpCfg[EpNum].Out.Type) {
			NumdTD = EpCfg[EpNum].Out.NumBufs;
		}
		else {
			NumdTD = 0;
		}

		for (Td = 0; Td < NumdTD; ++Td) {
			int	Status;

			int NextTd = (Td + 1) % NumdTD;

			XUsbPs_dTDInvalidateCache(&Out->dTDs[Td]);

			/* Set NEXT link pointer. */
			XUsbPs_WritedTD(&Out->dTDs[Td], XUSBPS_dTDNLP,
					  &Out->dTDs[NextTd]);

			/* Set the OUT descriptor ACTIVE and enable the
			 * interrupt on complete.
			 */
			XUsbPs_dTDSetActive(&Out->dTDs[Td]);
			XUsbPs_dTDSetIOC(&Out->dTDs[Td]);


			/* Set up the data buffer with the descriptor. If the
			 * buffer pointer is NULL it means that we do not need
			 * to attach a buffer to this descriptor.
			 */
			if (NULL == Out->dTDBufs) {
				XUsbPs_dTDFlushCache(&Out->dTDs[Td]);
				continue;
			}

			Status = XUsbPs_dTDAttachBuffer(
					&Out->dTDs[Td],
					Out->dTDBufs +
						(Td * EpCfg[EpNum].Out.BufSize),
					EpCfg[EpNum].Out.BufSize);
			if (XST_SUCCESS != Status) {
				return XST_FAILURE;
			}

			XUsbPs_dTDFlushCache(&Out->dTDs[Td]);
		}


		/* IN Descriptors
		 * ==============
		 *
		 * + Set the next link pointer
		 * + Set the Terminate bit to mark it available
		 */
		if (XUSBPS_EP_TYPE_NONE != EpCfg[EpNum].In.Type) {
			NumdTD = EpCfg[EpNum].In.NumBufs;
		}
		else {
			NumdTD = 0;
		}

		for (Td = 0; Td < NumdTD; ++Td) {
			int NextTd = (Td + 1) % NumdTD;

			XUsbPs_dTDInvalidateCache(&In->dTDs[Td]);

			/* Set NEXT link pointer. */
			XUsbPs_WritedTD(In->dTDs[Td], XUSBPS_dTDNLP,
					  In->dTDs[NextTd]);

			/* Set the IN descriptor's TERMINATE bits. */
			XUsbPs_dTDSetTerminate(In->dTDs[Td]);

			XUsbPs_dTDFlushCache(&In->dTDs[Td]);
		}
	}

	return XST_SUCCESS;
}


/*****************************************************************************/
/**
 *
 * This function associates a buffer with a Transfer Descriptor. The function
 * will take care of splitting the buffer into multiple 4kB aligned segments if
 * the buffer happens to span one or more 4kB pages.
 *
 * @param	dTDIndex is a pointer to the Transfer Descriptor
 * @param	BufferPtr is pointer to the buffer to link to the descriptor.
 * @param	BufferLen is the length of the buffer.
 *
 * @return
 *		- XST_SUCCESS: The operation completed successfully.
 *		- XST_FAILURE: An error occured.
 *		- XST_USB_BUF_TOO_BIG: The provided buffer is bigger than tha
 *		maximum allowed buffer size (16k).
 *
 * @note
 * 		Cache invalidation and flushing needs to be handler by the
 * 		caller of this function.
 *
 ******************************************************************************/
static int XUsbPs_dTDAttachBuffer(XUsbPs_dTD *dTDPtr,
					const u8 *BufferPtr, u32 BufferLen)
{
	u32	BufAddr;
	u32	BufEnd;
	u32	PtrNum;

	Xil_AssertNonvoid(dTDPtr    != NULL);

	/* Check if the buffer is smaller than 16kB. */
	if (BufferLen > XUSBPS_dTD_BUF_MAX_SIZE) {
		return XST_USB_BUF_TOO_BIG;
	}

	/* Get a u32 of the buffer pointer to avoid casting in the following
	 * logic operations.
	 */
	BufAddr = (u32) BufferPtr;


	/* Set the buffer pointer 0. Buffer pointer 0 can point to any location
	 * in memory. It does not need to be 4kB aligned. However, if the
	 * provided buffer spans one or more 4kB boundaries, we need to set up
	 * the subsequent buffer pointers which must be 4kB aligned.
	 */
	XUsbPs_WritedTD(dTDPtr, XUSBPS_dTDBPTR(0), BufAddr);

	/* Check if the buffer spans a 4kB boundary.
	 *
	 * Only do this check, if we are not sending a 0-length buffer.
	 */
	if (BufferLen > 0) {
		BufEnd = BufAddr + BufferLen -1;
		PtrNum = 1;

		while ((BufAddr & 0xFFFFF000) != (BufEnd & 0xFFFFF000)) {
			/* The buffer spans at least one boundary, let's set
			 * the next buffer pointer and repeat the procedure
			 * until the end of the buffer and the pointer written
			 * are in the same 4kB page.
			 */
			BufAddr = (BufAddr + 0x1000) & 0xFFFFF000;
			XUsbPs_WritedTD(dTDPtr, XUSBPS_dTDBPTR(PtrNum),
								BufAddr);
			PtrNum++;
		}
	}

	/* Set the length of the buffer. */
	XUsbPs_dTDSetTransferLen(dTDPtr, BufferLen);


	/* We remember the buffer pointer in the user data field (reserved
	 * field in the dTD). This makes it easier to reset the buffer pointer
	 * after a buffer has been received on the endpoint. The buffer pointer
	 * needs to be reset because the DMA engine modifies the buffer pointer
	 * while receiving.
	 */
	XUsbPs_WritedTD(dTDPtr, XUSBPS_dTDUSERDATA, BufferPtr);

	return XST_SUCCESS;
}


/*****************************************************************************/
/**
 * This function set the Max PacketLen for the queue head for isochronous EP.
 *
 * If the max packet length is greater than XUSBPS_MAX_PACKET_SIZE, then
 * Mult bits are set to reflect that.
 *
 * @param	dQHPtr is a pointer to the dQH element.
 * @param	Len is the Length to be set.
 *
 ******************************************************************************/
static void XUsbPs_dQHSetMaxPacketLenISO(XUsbPs_dQH *dQHPtr, u32 Len)
{
	u32 Mult = (Len & ENDPOINT_MAXP_MULT_MASK) >> ENDPOINT_MAXP_MULT_SHIFT;
	u32 MaxPktSize = (Mult > 1) ? ENDPOINT_MAXP_LENGTH : Len;

	if (MaxPktSize > XUSBPS_MAX_PACKET_SIZE) {
		return;
	}

	if (Mult > 3) {
		return;
	}

	/* Set Max packet size */
	XUsbPs_WritedQH(dQHPtr, XUSBPS_dQHCFG,
		(XUsbPs_ReaddQH(dQHPtr, XUSBPS_dQHCFG) &
			~XUSBPS_dQHCFG_MPL_MASK) |
			(MaxPktSize << XUSBPS_dQHCFG_MPL_SHIFT));

	/* Set Mult to tell hardware how many transactions in each microframe */
	XUsbPs_WritedQH(dQHPtr, XUSBPS_dQHCFG,
		(XUsbPs_ReaddQH(dQHPtr, XUSBPS_dQHCFG) &
			~XUSBPS_dQHCFG_MULT_MASK) |
			(Mult << XUSBPS_dQHCFG_MULT_SHIFT));

}

/*****************************************************************************/
/**
* This function reconfigures one Ep corresponding to host's request of setting
* alternate interface. The endpoint has been disabled before this call.
*
* Both QH and dTDs are updated for the new configuration.
*
* @param	InstancePtr is a pointer to the XUsbPs instance of the
*		controller.
* @param	CfgPtr
* 		Pointer to the updated XUsbPs DEVICE configuration structure.
*
* @param	EpNum
*		The endpoint to be reconfigured.
*
* @param NewDirection
*		The new transfer direction the endpoint.
*
* @param DirectionChanged
*		A boolean value indicate whether the transfer direction has changed.
*
* @return
*	XST_SUCCESS upon success, XST_FAILURE otherwise.
*
******************************************************************************/
int XUsbPs_ReconfigureEp(XUsbPs *InstancePtr, XUsbPs_DeviceConfig *CfgPtr,
				int EpNum, unsigned short NewDirection,
				int DirectionChanged) {

	int Status = XST_SUCCESS;
	XUsbPs_Endpoint *Ep;
	XUsbPs_EpConfig *EpCfg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(CfgPtr      != NULL);

	Ep = CfgPtr->Ep;
	EpCfg = CfgPtr->EpCfg;

	/* If transfer direction changes, dTDs has to be reset
	 * Number of buffers are preset and should not to be changed.
	 */
	if(DirectionChanged) {
		if(NewDirection == XUSBPS_EP_DIRECTION_OUT) {
			u8 *p;

			/* Swap the pointer to the dTDs.
			 */
			Ep[EpNum].Out.dTDs = Ep[EpNum].In.dTDs;
			p = (u8 *)(Ep[EpNum].Out.dTDs + XUSBPS_dTD_ALIGN * EpCfg[EpNum].Out.NumBufs);

			/* Set the OUT buffer if buffer size is not zero
			 */
			if(EpCfg[EpNum].Out.BufSize > 0) {
				Ep[EpNum].Out.dTDBufs = p;
			}
		} else if(NewDirection == XUSBPS_EP_DIRECTION_IN) {
			Ep[EpNum].In.dTDs = Ep[EpNum].Out.dTDs;
		}
	}

	/* Reset dTD progress tracking pointers
	 */
	if(NewDirection == XUSBPS_EP_DIRECTION_IN) {
		Ep[EpNum].In.dTDHead = Ep[EpNum].In.dTDTail = Ep[EpNum].In.dTDs;
	} else if(NewDirection == XUSBPS_EP_DIRECTION_OUT) {
		Ep[EpNum].Out.dTDCurr = Ep[EpNum].Out.dTDs;
	}

	/* Reinitialize information in QH
	 */
	XUsbPs_dQHReinitEp(CfgPtr, EpNum, NewDirection);

	/* Reinitialize the dTD linked list, and flush the cache
	 */
	Status = XUsbPs_dTDReinitEp(CfgPtr, EpNum, NewDirection);
	if(Status != XST_SUCCESS) {
		return Status;
	}

	return XST_SUCCESS;
}


/*****************************************************************************/
/**
 * This function re-initializes the Queue Head List in memory.
 * The endpoint 1 has been disabled before this call.
 *
 * @param	DevCfgPtr
 * 		Pointer to the updated XUsbPs DEVICE configuration structure.
 *
 * @param	EpNum
 *		The endpoint to be reconfigured.
 *
 * @param	NewDirection
 *		The new transfer direction of endpoint 1
 *
 * @return	none
 *
 ******************************************************************************/
static void XUsbPs_dQHReinitEp(XUsbPs_DeviceConfig *DevCfgPtr,
int EpNum, unsigned short NewDirection)
{
	XUsbPs_Endpoint	*Ep;
	XUsbPs_EpConfig	*EpCfg;

	/* Setup pointers for simpler access.
	 */
	Ep	= DevCfgPtr->Ep;
	EpCfg	= DevCfgPtr->EpCfg;


	/* Go through the list of Queue Head entries and:
	 *
	 * - Set Transfer Descriptor addresses
	 * - Set Maximum Packet Size
	 * - Disable Zero Length Termination (ZLT) for non-isochronous transfers
	 * - Enable Interrupt On Setup (IOS)
	 *
	 */
	if(NewDirection == XUSBPS_EP_DIRECTION_OUT) {
		/* OUT Queue Heads.
		 */
		XUsbPs_WritedQH(Ep[EpNum].Out.dQH,
			XUSBPS_dQHCPTR, Ep[EpNum].Out.dTDs);

		/* For isochronous, ep max packet size translates to different
		 * values in queue head than other types.
		 * Also	enable ZLT for isochronous.
		 */
		if(XUSBPS_EP_TYPE_ISOCHRONOUS == EpCfg[EpNum].Out.Type) {
			XUsbPs_dQHSetMaxPacketLenISO(Ep[EpNum].Out.dQH,
   					EpCfg[EpNum].Out.MaxPacketSize);
			XUsbPs_dQHEnableZLT(Ep[EpNum].Out.dQH);
		}else {
			XUsbPs_dQHSetMaxPacketLen(Ep[EpNum].Out.dQH,
				    EpCfg[EpNum].Out.MaxPacketSize);
			XUsbPs_dQHDisableZLT(Ep[EpNum].Out.dQH);
		}

		XUsbPs_dQHSetIOS(Ep[EpNum].Out.dQH);

		/* Set up the overlay next dTD pointer.
		 */
		XUsbPs_WritedQH(Ep[EpNum].Out.dQH,
				XUSBPS_dQHdTDNLP, Ep[EpNum].Out.dTDs);

		XUsbPs_dQHFlushCache(Ep[EpNum].Out.dQH);

	} else if(NewDirection == XUSBPS_EP_DIRECTION_IN) {

		/* IN Queue Heads.
		 */
		XUsbPs_WritedQH(Ep[EpNum].In.dQH,
			  XUSBPS_dQHCPTR, Ep[EpNum].In.dTDs);

		/* Isochronous ep packet size can be larger than 1024. */
		if(XUSBPS_EP_TYPE_ISOCHRONOUS == EpCfg[EpNum].In.Type) {
			XUsbPs_dQHSetMaxPacketLenISO(Ep[EpNum].In.dQH,
   				EpCfg[EpNum].In.MaxPacketSize);
			XUsbPs_dQHEnableZLT(Ep[EpNum].In.dQH);
		}else {
			XUsbPs_dQHSetMaxPacketLen(Ep[EpNum].In.dQH,
			    EpCfg[EpNum].In.MaxPacketSize);
			XUsbPs_dQHDisableZLT(Ep[EpNum].In.dQH);
		}

		XUsbPs_dQHSetIOS(Ep[EpNum].In.dQH);

		XUsbPs_dQHFlushCache(Ep[EpNum].In.dQH);
	}

}

/*****************************************************************************/
/**
 *
 * This function re-initializes the Transfer Descriptors lists in memory.
 * The endpoint has been disabled before the call. The transfer descriptors
 * list pointer has been initialized too.
 *
 * @param	DevCfgPtr
 * 		Pointer to the XUsbPs DEVICE configuration structure.
 *
 * @param	EpNum
 *		The endpoint to be reconfigured.
 *
 * @param	NewDirection
 *		The new transfer direction of endpoint 1
 *
 * @return
 *		- XST_SUCCESS: The operation completed successfully.
 *		- XST_FAILURE: An error occured.
 *
 ******************************************************************************/
static int XUsbPs_dTDReinitEp(XUsbPs_DeviceConfig *DevCfgPtr,
int EpNum, unsigned short NewDirection)
{
	XUsbPs_Endpoint	*Ep;
	XUsbPs_EpConfig	*EpCfg;
	int	Td;
	int	NumdTD;


	/* Setup pointers for simpler access.
	 */
	Ep	= DevCfgPtr->Ep;
	EpCfg	= DevCfgPtr->EpCfg;


	if(NewDirection == XUSBPS_EP_DIRECTION_OUT) {
		XUsbPs_EpOut	*Out = &Ep[EpNum].Out;

		/* OUT Descriptors
		 * ===============
		 *
		 * + Set the next link pointer
		 * + Set the interrupt complete and the active bit
		 * + Attach the buffer to the dTD
		 */
		NumdTD = EpCfg[EpNum].Out.NumBufs;

		for (Td = 0; Td < NumdTD; ++Td) {
			int	Status;

			int NextTd = (Td + 1) % NumdTD;

			XUsbPs_dTDInvalidateCache(&Out->dTDs[Td]);

			/* Set NEXT link pointer.
			 */
			XUsbPs_WritedTD(&Out->dTDs[Td], XUSBPS_dTDNLP,
					  &Out->dTDs[NextTd]);

			/* Set the OUT descriptor ACTIVE and enable the
			 * interrupt on complete.
			 */
			XUsbPs_dTDSetActive(&Out->dTDs[Td]);
			XUsbPs_dTDSetIOC(&Out->dTDs[Td]);

			/* Set up the data buffer with the descriptor. If the
			 * buffer pointer is NULL it means that we do not need
			 * to attach a buffer to this descriptor.
			 */
			if (Out->dTDBufs != NULL) {

				Status = XUsbPs_dTDAttachBuffer(
						&Out->dTDs[Td],
						Out->dTDBufs +
							(Td * EpCfg[EpNum].Out.BufSize),
						EpCfg[EpNum].Out.BufSize);
				if (Status != XST_SUCCESS) {
					return XST_FAILURE;
				}
			}
			XUsbPs_dTDFlushCache(&Out->dTDs[Td]);
		}
	} else if(NewDirection == XUSBPS_EP_DIRECTION_IN) {
		XUsbPs_EpIn	*In  = &Ep[EpNum].In;

		/* IN Descriptors
		 * ==============
		 *
		 * + Set the next link pointer
		 * + Set the Terminate bit to mark it available
		 */
		NumdTD = EpCfg[EpNum].In.NumBufs;

		for (Td = 0; Td < NumdTD; ++Td) {
			int NextTd = (Td + 1) % NumdTD;

			XUsbPs_dTDInvalidateCache(&In->dTDs[Td]);

			/* Set NEXT link pointer.
			 */
			XUsbPs_WritedTD(&In->dTDs[Td], XUSBPS_dTDNLP,
					  &In->dTDs[NextTd]);

			/* Set the IN descriptor's TERMINATE bits.
			 */
			XUsbPs_dTDSetTerminate(&In->dTDs[Td]);

			XUsbPs_dTDFlushCache(&In->dTDs[Td]);
		}
	}

	return XST_SUCCESS;
}

/** @} */
