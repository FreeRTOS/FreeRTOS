/******************************************************************************
*
* Copyright (C) 2015 Xilinx, Inc.  All rights reserved.
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
* @file xusbpsu_controltransfers.c
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a bss  01/22/15 First release
* 1.00a bss  03/18/15 Modified u32 pointer casts to UINTPTR.
*
* </pre>
*
*****************************************************************************/

/***************************** Include Files *********************************/

#include "xusbpsu.h"

/************************** Constant Definitions *****************************/

#define USB_DIR_OUT				0		/* to device */
#define USB_DIR_IN				0x80	/* to host */

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/****************************************************************************/
/**
* Initiates DMA on Control Endpoint 0 to receive Setup packet.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	XST_SUCCESS else XST_FAILURE.
*
* @note		None.
*
*****************************************************************************/
int XUsbPsu_RecvSetup(struct XUsbPsu *InstancePtr)
{
	struct XUsbPsu_EpParams *Params;
	struct XUsbPsu_Trb	*TrbPtr;
	struct XUsbPsu_Ep	*Ept;
	int	Ret;

	Xil_AssertNonvoid(InstancePtr != NULL);

	Params = XUsbPsu_GetEpParams(InstancePtr);
	/* Setup packet always on EP0 */
	Ept = &InstancePtr->eps[0];
	if (Ept->EpStatus & XUSBPSU_EP_BUSY) {
		return XST_FAILURE;
	}

	TrbPtr = &InstancePtr->Ep0_Trb;

	TrbPtr->BufferPtrLow = (UINTPTR)&InstancePtr->SetupData;
	TrbPtr->BufferPtrHigh = ((UINTPTR)&InstancePtr->SetupData >> 16) >> 16;
	TrbPtr->Size = 8;
	TrbPtr->Ctrl = XUSBPSU_TRBCTL_CONTROL_SETUP;

	TrbPtr->Ctrl |= (XUSBPSU_TRB_CTRL_HWO
			| XUSBPSU_TRB_CTRL_LST
			| XUSBPSU_TRB_CTRL_IOC
			| XUSBPSU_TRB_CTRL_ISP_IMI);

	Xil_DCacheFlushRange(TrbPtr, sizeof(struct XUsbPsu_Trb));

	Params->Param0 = 0;
	Params->Param1 = (UINTPTR)TrbPtr;

	InstancePtr->Ep0State = XUSBPSU_EP0_SETUP_PHASE;

	Ept->Cmd = XUSBPSU_DEPCMD_STARTTRANSFER;
	Ret = XUsbPsu_SendEpCmd(InstancePtr, 0, XUSBPSU_EP_DIR_OUT,
				XUSBPSU_DEPCMD_STARTTRANSFER, Params);
	if (Ret < 0) {
		return Ret;
	}

	Ept->EpStatus |= XUSBPSU_EP_BUSY;
	Ept->ResourceIndex = XUsbPsu_EpGetTransferIndex(InstancePtr,
						Ept->UsbEpNum, Ept->Direction);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Stalls Control Endpoint and restarts to receive Setup packet.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	None
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_Ep0StallRestart(struct XUsbPsu *InstancePtr)
{
	struct XUsbPsu_Ep		*Ept;

	Xil_AssertVoid(InstancePtr != NULL);

	/* reinitialize physical ep1 */
	Ept = &InstancePtr->eps[1];
	Ept->EpStatus = XUSBPSU_EP_ENABLED;

	/* stall is always issued on EP0 */
	XUsbPsu_EpSetStall(InstancePtr, 0, XUSBPSU_EP_DIR_OUT);

	Ept = &InstancePtr->eps[0];
	Ept->EpStatus = XUSBPSU_EP_ENABLED;
	InstancePtr->Ep0State = XUSBPSU_EP0_SETUP_PHASE;
	XUsbPsu_RecvSetup(InstancePtr);
}

/****************************************************************************/
/**
* Changes State of Core to USB configured State.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Ctrl is a pointer to the Setup packet data.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note		None.
*
*****************************************************************************/
int XUsbPsu_SetConfiguration(struct XUsbPsu *InstancePtr, SetupPacket *Ctrl)
{
	u8 State;
	int Ret;
	u32 RegVal;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(Ctrl != NULL);

	State = InstancePtr->State;
	InstancePtr->IsConfigDone = 0;

	switch (State) {
	case XUSBPSU_STATE_DEFAULT:
		return XST_FAILURE;
		break;

	case XUSBPSU_STATE_ADDRESS:
		InstancePtr->State = XUSBPSU_STATE_CONFIGURED;
		break;

	case XUSBPSU_STATE_CONFIGURED:
		break;

	default:
		Ret = XST_FAILURE;
		break;
	}

	return Ret;
}

/****************************************************************************/
/**
* Checks the Data Phase and calls user Endpoint handler.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Event is a pointer to the Endpoint event occured in core.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_Ep0DataDone(struct XUsbPsu *InstancePtr,
						 const struct XUsbPsu_Event_Epevt *Event)
{
	struct XUsbPsu_Ep	*Ept;
	struct XUsbPsu_Trb	*TrbPtr;
	u32	Status;
	u32	Length;
	u32	EpNum;
	u8	Dir;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Event != NULL);

	EpNum = Event->Epnumber;
	Dir = !!EpNum;
	Ept = &InstancePtr->eps[EpNum];
	TrbPtr = &InstancePtr->Ep0_Trb;

	Xil_DCacheInvalidateRange(TrbPtr, sizeof(struct XUsbPsu_Trb));

	Status = XUSBPSU_TRB_SIZE_TRBSTS(TrbPtr->Size);
	if (Status == XUSBPSU_TRBSTS_SETUP_PENDING) {
		return;
	}

	Length = TrbPtr->Size & XUSBPSU_TRB_SIZE_MASK;

	if (Length && Dir) { /* IN */
		Ept->BytesTxed = Ept->RequestedBytes - Length;
	}

	if (!Length) {
		Ept->BytesTxed = Ept->RequestedBytes;
	}

	if (Length && !Dir) { /* OUT */
		/* may be  wLength < Maxpacketsize */
		if (InstancePtr->UnalignedTx) {
			Ept->BytesTxed = Ept->RequestedBytes;
			InstancePtr->UnalignedTx = 0;
		}
	}

	if (!Dir) {
		/* Invalidate Cache */
		Xil_DCacheInvalidateRange(Ept->BufferPtr, Ept->BytesTxed);
	}

	if (Ept->Handler) {
		Ept->Handler(InstancePtr, Ept->RequestedBytes, Ept->BytesTxed);
	}
}

/****************************************************************************/
/**
* Checks the Status Phase and starts next Control transfer.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Event is a pointer to the Endpoint event occured in core.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_Ep0StatusDone(struct XUsbPsu *InstancePtr,
		const struct XUsbPsu_Event_Epevt *Event)
{
	struct XUsbPsu_Trb	*TrbPtr;
	u32	Status;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Event != NULL);

	TrbPtr = &InstancePtr->Ep0_Trb;

	if (InstancePtr->IsInTestMode) {
		int Ret;

		Ret = XUsbPsu_SetTestMode(InstancePtr,
					InstancePtr->TestMode);
		if (Ret < 0) {
			XUsbPsu_Ep0StallRestart(InstancePtr);
			return;
		}
	}
	Xil_DCacheInvalidateRange(TrbPtr, sizeof(struct XUsbPsu_Trb));
	Status = XUSBPSU_TRB_SIZE_TRBSTS(TrbPtr->Size);
	/* There is nothing driver can do for Setup Pending received */

	XUsbPsu_RecvSetup(InstancePtr);
}

/****************************************************************************/
/**
* Handles Transfer complete event of Control Endpoints EP0 OUT and EP0 IN.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Event is a pointer to the Endpoint event occured in core.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_Ep0XferComplete(struct XUsbPsu *InstancePtr,
							 const struct XUsbPsu_Event_Epevt *Event)
{
	struct XUsbPsu_Ep *Ept;
	SetupPacket *Ctrl;
	u16 Length;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Event != NULL);

	Ept = &InstancePtr->eps[Event->Epnumber];
	Ctrl = &InstancePtr->SetupData;

	Ept->EpStatus &= ~XUSBPSU_EP_BUSY;
	Ept->ResourceIndex = 0;

	switch (InstancePtr->Ep0State) {
	case XUSBPSU_EP0_SETUP_PHASE:
		Xil_DCacheInvalidateRange(&InstancePtr->SetupData,
					sizeof(InstancePtr->SetupData));
		Length = Ctrl->wLength;
		if (!Length) {
			InstancePtr->IsThreeStage = 0;
			InstancePtr->ControlDir = XUSBPSU_EP_DIR_OUT;
		} else {
			InstancePtr->IsThreeStage = 1;
			InstancePtr->ControlDir = !!(Ctrl->bRequestType &
							USB_DIR_IN);
		}

		if (InstancePtr->Chapter9 == NULL) {
				/* ? */
		} else {
			InstancePtr->Chapter9(InstancePtr,
									&InstancePtr->SetupData);
		}
		break;

	case XUSBPSU_EP0_DATA_PHASE:
		XUsbPsu_Ep0DataDone(InstancePtr, Event);
		break;

	case XUSBPSU_EP0_STATUS_PHASE:
		XUsbPsu_Ep0StatusDone(InstancePtr, Event);
		break;

	default:
		break;
	}
}

/****************************************************************************/
/**
* Starts Status Phase of Control Transfer
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Event is a pointer to the Endpoint event occured in core.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note		None.
*
*****************************************************************************/
int XUsbPsu_Ep0StartStatus(struct XUsbPsu *InstancePtr,
				const struct XUsbPsu_Event_Epevt *Event)
{
	struct XUsbPsu_Ep  *Ept;
	struct XUsbPsu_EpParams *Params;
	struct XUsbPsu_Trb *TrbPtr;
	u32 Type;
	int Ret;
	u8 Dir;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(Event != NULL);

	Ept = &InstancePtr->eps[Event->Epnumber];
	Params = XUsbPsu_GetEpParams(InstancePtr);
	if (Ept->EpStatus & XUSBPSU_EP_BUSY) {
		return XST_FAILURE;
	}

	Type = InstancePtr->IsThreeStage ? XUSBPSU_TRBCTL_CONTROL_STATUS3
					: XUSBPSU_TRBCTL_CONTROL_STATUS2;
	TrbPtr = &InstancePtr->Ep0_Trb;
	/* we use same TrbPtr for setup packet */
	TrbPtr->BufferPtrLow = (UINTPTR)&InstancePtr->SetupData;
	TrbPtr->BufferPtrHigh = ((UINTPTR)&InstancePtr->SetupData >> 16) >> 16;
	TrbPtr->Size = 0;
	TrbPtr->Ctrl = Type;

	TrbPtr->Ctrl |= (XUSBPSU_TRB_CTRL_HWO
			| XUSBPSU_TRB_CTRL_LST
			| XUSBPSU_TRB_CTRL_IOC
			| XUSBPSU_TRB_CTRL_ISP_IMI);

	Xil_DCacheFlushRange(TrbPtr, sizeof(struct XUsbPsu_Trb));

	Params->Param0 = 0;
	Params->Param1 = (UINTPTR)TrbPtr;

	InstancePtr->Ep0State = XUSBPSU_EP0_STATUS_PHASE;

	/*
	 * Control OUT transfer - Status stage happens on EP0 IN - EP1
	 * Control IN transfer - Status stage happens on EP0 OUT - EP0
	 */
	Dir = !InstancePtr->ControlDir;
	Ept->Cmd = XUSBPSU_DEPCMD_STARTTRANSFER;
	Ret = XUsbPsu_SendEpCmd(InstancePtr, 0, Dir,
							XUSBPSU_DEPCMD_STARTTRANSFER, Params);
	if (Ret != XST_SUCCESS) {
		return XST_FAILURE;
	}

	Ept->EpStatus |= XUSBPSU_EP_BUSY;
	Ept->ResourceIndex = XUsbPsu_EpGetTransferIndex(InstancePtr,
							Ept->UsbEpNum, Ept->Direction);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Ends Data Phase - used incase of error.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Dep is a pointer to the Endpoint structure.
*
* @return	None
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_Ep0_EndControlData(struct XUsbPsu *InstancePtr,
								struct XUsbPsu_Ep *Ept)
{
	struct XUsbPsu_EpParams *Params;
	u32	Cmd;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Ept != NULL);

	if (!Ept->ResourceIndex)
		return;

	Params = XUsbPsu_GetEpParams(InstancePtr);
	Cmd = XUSBPSU_DEPCMD_ENDTRANSFER;
	Cmd |= XUSBPSU_DEPCMD_PARAM(Ept->ResourceIndex);
	Ept->Cmd = XUSBPSU_DEPCMD_ENDTRANSFER;
	XUsbPsu_SendEpCmd(InstancePtr, Ept->UsbEpNum, Ept->Direction,
						Cmd, Params);
	Ept->ResourceIndex = 0;
	usleep(200);
}

/****************************************************************************/
/**
* Handles Transfer Not Ready event of Control Endpoints EP0 OUT and EP0 IN.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Event is a pointer to the Endpoint event occured in core.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_Ep0XferNotReady(struct XUsbPsu *InstancePtr,
							 const struct XUsbPsu_Event_Epevt *Event)
{
	struct XUsbPsu_Ep *Ept;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Event != NULL);

	Ept = &InstancePtr->eps[Event->Epnumber];

	switch (Event->Status) {
	case DEPEVT_STATUS_CONTROL_DATA:
		/*
		 * We already have a DATA transfer in the controller's cache,
		 * if we receive a XferNotReady(DATA) we will ignore it, unless
		 * it's for the wrong direction.
		 *
		 * In that case, we must issue END_TRANSFER command to the Data
		 * Phase we already have started and issue SetStall on the
		 * control endpoint.
		 */
		if (Event->Epnumber != InstancePtr->ControlDir) {
			XUsbPsu_Ep0_EndControlData(InstancePtr, Ept);
			XUsbPsu_Ep0StallRestart(InstancePtr);
		}
		break;

	case DEPEVT_STATUS_CONTROL_STATUS:
		XUsbPsu_Ep0StartStatus(InstancePtr, Event);
		break;
	}
}

/****************************************************************************/
/**
* Handles Interrupts of Control Endpoints EP0 OUT and EP0 IN.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Event is a pointer to the Endpoint event occured in core.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_Ep0Intr(struct XUsbPsu *InstancePtr,
		const struct XUsbPsu_Event_Epevt *Event)
{
	u32 EpNum;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Event != NULL);

	EpNum = Event->Epnumber;
	switch (Event->Endpoint_Event) {
	case XUSBPSU_DEPEVT_XFERCOMPLETE:
		XUsbPsu_Ep0XferComplete(InstancePtr, Event);
		break;

	case XUSBPSU_DEPEVT_XFERNOTREADY:
		XUsbPsu_Ep0XferNotReady(InstancePtr, Event);
		break;

	case XUSBPSU_DEPEVT_XFERINPROGRESS:
	case XUSBPSU_DEPEVT_STREAMEVT:
	case XUSBPSU_DEPEVT_EPCMDCMPLT:
		break;
	}
}

/****************************************************************************/
/**
* Initiates DMA to send data on Control Endpoint EP0 IN to Host.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	BufferPtr is pointer to data.
* @param	BufferLen is Length of data buffer.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note		None.
*
*****************************************************************************/
int XUsbPsu_Ep0Send(struct XUsbPsu *InstancePtr, u8 *BufferPtr, u32 BufferLen)
{
	/* Control IN - EP1 */
	struct XUsbPsu_EpParams *Params;
	struct XUsbPsu_Ep 	*Ept;
	struct XUsbPsu_Trb	*TrbPtr;
	u32 Type;
	int Ret;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(BufferPtr != NULL);

	Ept = &InstancePtr->eps[1];
	Params = XUsbPsu_GetEpParams(InstancePtr);
	if (Ept->EpStatus & XUSBPSU_EP_BUSY) {
		return XST_FAILURE;
	}

	Ept->RequestedBytes = BufferLen;
	Ept->BytesTxed = 0;
	Ept->BufferPtr = BufferPtr;

	TrbPtr = &InstancePtr->Ep0_Trb;

	TrbPtr->BufferPtrLow  = (UINTPTR)BufferPtr;
	TrbPtr->BufferPtrHigh  = ((UINTPTR)BufferPtr >> 16) >> 16;
	TrbPtr->Size = BufferLen;
	TrbPtr->Ctrl = XUSBPSU_TRBCTL_CONTROL_DATA;

	TrbPtr->Ctrl |= (XUSBPSU_TRB_CTRL_HWO
			| XUSBPSU_TRB_CTRL_LST
			| XUSBPSU_TRB_CTRL_IOC
			| XUSBPSU_TRB_CTRL_ISP_IMI);

	Params->Param0 = 0;
	Params->Param1 = (UINTPTR)TrbPtr;

	Xil_DCacheFlushRange(TrbPtr, sizeof(struct XUsbPsu_Trb));
	Xil_DCacheFlushRange(BufferPtr, BufferLen);

	InstancePtr->Ep0State = XUSBPSU_EP0_DATA_PHASE;

	Ept->Cmd = XUSBPSU_DEPCMD_STARTTRANSFER;
	Ret = XUsbPsu_SendEpCmd(InstancePtr, 0, XUSBPSU_EP_DIR_IN,
							XUSBPSU_DEPCMD_STARTTRANSFER, Params);
	if (Ret != XST_SUCCESS) {
		return XST_FAILURE;
	}

	Ept->EpStatus |= XUSBPSU_EP_BUSY;
	Ept->ResourceIndex = XUsbPsu_EpGetTransferIndex(InstancePtr,
						Ept->UsbEpNum, Ept->Direction);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Initiates DMA to receive data on Control Endpoint EP0 OUT from Host.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	BufferPtr is pointer to data.
* @param	Length is Length of data to be received.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note		None.
*
*****************************************************************************/
int XUsbPsu_Ep0Recv(struct XUsbPsu *InstancePtr, u8 *BufferPtr, u32 Length)
{
	struct XUsbPsu_EpParams *Params;
	struct XUsbPsu_Ep 	*Ept;
	struct XUsbPsu_Trb	*TrbPtr;
	u32 Type;
	u32 Size;
	int Ret;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(BufferPtr != NULL);

	Ept = &InstancePtr->eps[0];
	Params = XUsbPsu_GetEpParams(InstancePtr);
	if (Ept->EpStatus & XUSBPSU_EP_BUSY) {
		return XST_FAILURE;
	}

	Size = Ept->RequestedBytes = Length;
	Ept->BytesTxed = 0;
	Ept->BufferPtr = BufferPtr;

	/*
	 * 8.2.5 - An OUT transfer size (Total TRB buffer allocation)
	 * must be a multiple of MaxPacketSize even if software is expecting a
	 * fixed non-multiple of MaxPacketSize transfer from the Host.
	 */
	if (!IS_ALIGNED(Length, Ept->MaxSize)) {
		Size = roundup(Length, Ept->MaxSize);
		InstancePtr->UnalignedTx = 1;
	}

	TrbPtr = &InstancePtr->Ep0_Trb;

	TrbPtr->BufferPtrLow = (UINTPTR)BufferPtr;
	TrbPtr->BufferPtrHigh = ((UINTPTR)BufferPtr >> 16) >> 16;
	TrbPtr->Size = Size;
	TrbPtr->Ctrl = XUSBPSU_TRBCTL_CONTROL_DATA;

	TrbPtr->Ctrl |= (XUSBPSU_TRB_CTRL_HWO
			| XUSBPSU_TRB_CTRL_LST
			| XUSBPSU_TRB_CTRL_IOC
			| XUSBPSU_TRB_CTRL_ISP_IMI);

	Xil_DCacheFlushRange(TrbPtr, sizeof(struct XUsbPsu_Trb));

	Params->Param0 = 0;
	Params->Param1 = (UINTPTR)TrbPtr;

	InstancePtr->Ep0State = XUSBPSU_EP0_DATA_PHASE;

	Ept->Cmd = XUSBPSU_DEPCMD_STARTTRANSFER;
	Ret = XUsbPsu_SendEpCmd(InstancePtr, 0, XUSBPSU_EP_DIR_OUT,
				XUSBPSU_DEPCMD_STARTTRANSFER, Params);
	if (Ret < 0) {
		return Ret;
	}

	Ept->EpStatus |= XUSBPSU_EP_BUSY;
	Ept->ResourceIndex = XUsbPsu_EpGetTransferIndex(InstancePtr,
							Ept->UsbEpNum, Ept->Direction);

	return XST_SUCCESS;
}
