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
*****************************************************************************/
/****************************************************************************/
/**
*
* @file xusbpsu_endpoint.c
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a bss  01/22/15 First release
* 1.00a bss  03/18/15 Added XUsbPsu_EpXferComplete function to handle Non
*					  control endpoint interrupt.
*
* </pre>
*
*****************************************************************************/

/***************************** Include Files *********************************/

#include "xusbpsu.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/

/* return Physical EP number as dwc3 mapping */
#define PhysicalEp(epnum, direction)	((epnum) << 1 ) | (direction)

/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/****************************************************************************/
/**
* Returns zeroed parameters to be used by Endpoint commands
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	Zeroed Params structure pointer.
*
* @note		None.
*
*****************************************************************************/
struct XUsbPsu_EpParams *XUsbPsu_GetEpParams(struct XUsbPsu *InstancePtr)
{
	Xil_AssertNonvoid(InstancePtr != NULL);

	InstancePtr->EpParams.Param0 = 0x00;
	InstancePtr->EpParams.Param1 = 0x00;
	InstancePtr->EpParams.Param2 = 0x00;

	return &InstancePtr->EpParams;
}

/****************************************************************************/
/**
* Returns Transfer Index assigned by Core for an Endpoint transfer.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	UsbEpNum is USB endpoint number.
* @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT
*
* @return	Transfer Resource Index.
*
* @note		None.
*
*****************************************************************************/
u32 XUsbPsu_EpGetTransferIndex(struct XUsbPsu *InstancePtr, u8 UsbEpNum,
								u8 Dir)
{
	u8 PhyEpNum;
	u32 ResourceIndex;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(UsbEpNum >= 0 && UsbEpNum <= 16);
	Xil_AssertNonvoid((Dir == XUSBPSU_EP_DIR_IN) ||
						(Dir == XUSBPSU_EP_DIR_OUT));

	PhyEpNum = PhysicalEp(UsbEpNum, Dir);
	ResourceIndex = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DEPCMD(PhyEpNum));

	return XUSBPSU_DEPCMD_GET_RSC_IDX(ResourceIndex);
}

/****************************************************************************/
/**
* Sends Endpoint command to Endpoint.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	UsbEpNum is USB endpoint number.
* @param	Dir is direction of endpoint
*			- XUSBPSU_EP_DIR_IN/ XUSBPSU_EP_DIR_OUT.
* @param	Cmd is Endpoint command.
* @param	Params is Endpoint command parameters.
*
* @return	XST_SUCCESS else XST_FAILURE.
*
* @note		None.
*
*****************************************************************************/
int XUsbPsu_SendEpCmd(struct XUsbPsu *InstancePtr, u8 UsbEpNum, u8 Dir,
					  u32 Cmd, struct XUsbPsu_EpParams *Params)
{
	u32	RegVal;
	u32	PhyEpnum;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(UsbEpNum >= 0 && UsbEpNum <= 16);
	Xil_AssertNonvoid((Dir == XUSBPSU_EP_DIR_IN) ||
					  (Dir == XUSBPSU_EP_DIR_OUT));

	PhyEpnum = PhysicalEp(UsbEpNum, Dir);

	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DEPCMDPAR0(PhyEpnum),
					 Params->Param0);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DEPCMDPAR1(PhyEpnum),
					 Params->Param1);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DEPCMDPAR2(PhyEpnum),
					 Params->Param2);

	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DEPCMD(PhyEpnum),
			Cmd | XUSBPSU_DEPCMD_CMDACT);

	if (XUsbPsu_Wait_Clear_Timeout(InstancePtr, XUSBPSU_DEPCMD(PhyEpnum),
			XUSBPSU_DEPCMD_CMDACT, 500) == XST_FAILURE) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Sends Start New Configuration command to Endpoint.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	UsbEpNum is USB endpoint number.
* @param	Dir is direction of endpoint
*			- XUSBPSU_EP_DIR_IN/ XUSBPSU_EP_DIR_OUT.
*
* @return	XST_SUCCESS else XST_FAILURE.
*
* @note
* 			As per data book this command should be issued by software
*			under these conditions:
*				1. After power-on-reset with XferRscIdx=0 before starting
*				   to configure Physical Endpoints 0 and 1.
*				2. With XferRscIdx=2 before starting to configure
*				   Physical Endpoints > 1
*				3. This command should always be issued to
*				   Endpoint 0 (DEPCMD0).
*
*****************************************************************************/
int XUsbPsu_StartEpConfig(struct XUsbPsu *InstancePtr, u32 UsbEpNum, u8 Dir)
{
	struct XUsbPsu_EpParams *Params;
	u32	Cmd;
	u8 PhyEpNum;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(UsbEpNum >= 0 && UsbEpNum <= 16);
	Xil_AssertNonvoid((Dir == XUSBPSU_EP_DIR_IN) ||
					  (Dir == XUSBPSU_EP_DIR_OUT));

	PhyEpNum = PhysicalEp(UsbEpNum, Dir);
	Params =  XUsbPsu_GetEpParams(InstancePtr);

	if (PhyEpNum != 1) {
		Cmd = XUSBPSU_DEPCMD_DEPSTARTCFG;
		/* XferRscIdx == 0 for EP0 and 2 for the remaining */
		if (PhyEpNum > 1) {
			if (InstancePtr->IsConfigDone)
				return XST_SUCCESS;
			InstancePtr->IsConfigDone = 1;
			Cmd |= XUSBPSU_DEPCMD_PARAM(2);
		}
		InstancePtr->eps[0].Cmd = XUSBPSU_DEPCMD_DEPSTARTCFG;
		return XUsbPsu_SendEpCmd(InstancePtr, 0, XUSBPSU_EP_DIR_OUT,
								 Cmd, Params);
	}

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Sends Set Endpoint Configuration command to Endpoint.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	UsbEpNum is USB endpoint number.
* @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT.
* @param	Size is size of Endpoint size.
* @param	Type is Endpoint type Control/Bulk/Interrupt/Isoc.
*
* @return	XST_SUCCESS else XST_FAILURE.
*
* @note		None.
*
*****************************************************************************/
int XUsbPsu_SetEpConfig(struct XUsbPsu *InstancePtr, u8 UsbEpNum, u8 Dir,
						u16 Size, u8 Type)
{
	struct XUsbPsu_EpParams *Params;
	u8 PhyEpnum;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(UsbEpNum >= 0 && UsbEpNum <= 16);
	Xil_AssertNonvoid((Dir == XUSBPSU_EP_DIR_IN) ||
						(Dir == XUSBPSU_EP_DIR_OUT));
	Xil_AssertNonvoid(Size >= 64 && Size <= 1024);

	Params = XUsbPsu_GetEpParams(InstancePtr);
	PhyEpnum = PhysicalEp(UsbEpNum , Dir);

	Params->Param0 = XUSBPSU_DEPCFG_EP_TYPE(Type)
		| XUSBPSU_DEPCFG_MAX_PACKET_SIZE(Size);

	Params->Param1 = XUSBPSU_DEPCFG_XFER_COMPLETE_EN
		| XUSBPSU_DEPCFG_XFER_NOT_READY_EN;

	/*
	 * We are doing 1:1 mapping for endpoints, meaning
	 * Physical Endpoints 2 maps to Logical Endpoint 2 and
	 * so on. We consider the direction bit as part of the physical
	 * endpoint number. So USB endpoint 0x81 is 0x03.
	 */
	Params->Param1 |= XUSBPSU_DEPCFG_EP_NUMBER(PhyEpnum);

	if (Dir)
		 Params->Param0 |= XUSBPSU_DEPCFG_FIFO_NUMBER(PhyEpnum >> 1);

	InstancePtr->eps[PhyEpnum].Cmd = XUSBPSU_DEPCMD_SETEPCONFIG;

	return XUsbPsu_SendEpCmd(InstancePtr, UsbEpNum, Dir,
							 XUSBPSU_DEPCMD_SETEPCONFIG, Params);
}

/****************************************************************************/
/**
* Sends Set Transfer Resource command to Endpoint.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	UsbEpNum is USB endpoint number.
* @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/
*											XUSBPSU_EP_DIR_OUT.
*
* @return	XST_SUCCESS else XST_FAILURE.
*
* @note		None.
*
*****************************************************************************/
int XUsbPsu_SetXferResource(struct XUsbPsu *InstancePtr, u8 UsbEpNum, u8 Dir)
{
	struct XUsbPsu_EpParams *Params;
	u8 PhyEpnum;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(UsbEpNum >= 0 && UsbEpNum <= 16);
	Xil_AssertNonvoid((Dir == XUSBPSU_EP_DIR_IN) ||
						(Dir == XUSBPSU_EP_DIR_OUT));

	PhyEpnum = PhysicalEp(UsbEpNum , Dir);
	Params = XUsbPsu_GetEpParams(InstancePtr);

	Params->Param0 = XUSBPSU_DEPXFERCFG_NUM_XFER_RES(1);

	InstancePtr->eps[PhyEpnum].Cmd = XUSBPSU_DEPCMD_SETTRANSFRESOURCE;

	return XUsbPsu_SendEpCmd(InstancePtr, UsbEpNum, Dir,
							 XUSBPSU_DEPCMD_SETTRANSFRESOURCE, Params);
}

/****************************************************************************/
/**
* Enables Endpoint for sending/receiving data.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	UsbEpNum is USB endpoint number.
* @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT.
* @param	Maxsize is size of Endpoint size.
* @param	Type is Endpoint type Control/Bulk/Interrupt/Isoc.
*
* @return	XST_SUCCESS else XST_FAILURE.
*
* @note		None.
*
****************************************************************************/
int XUsbPsu_EpEnable(struct XUsbPsu *InstancePtr, u8 UsbEpNum, u8 Dir,
			u16 Maxsize, u8 Type)
{
	struct XUsbPsu_Ep *Ept;
	u32 RegVal;
	int Ret = XST_FAILURE;
	u32 PhyEpnum;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(UsbEpNum >= 0 && UsbEpNum <= 16);
	Xil_AssertNonvoid((Dir == XUSBPSU_EP_DIR_IN) ||
					  (Dir == XUSBPSU_EP_DIR_OUT));
	Xil_AssertNonvoid(Maxsize >= 64 && Maxsize <= 1024);

	PhyEpnum = PhysicalEp(UsbEpNum , Dir);
	Ept = &InstancePtr->eps[PhyEpnum];

	Ept->UsbEpNum	= UsbEpNum;
	Ept->Direction	= Dir;
	Ept->Type	= Type;
	Ept->MaxSize	= Maxsize;
	Ept->PhyEpNum	= PhyEpnum;

	if (!(Ept->EpStatus & XUSBPSU_EP_ENABLED)) {
		Ret = XUsbPsu_StartEpConfig(InstancePtr, UsbEpNum, Dir);
		if (Ret)
			return Ret;
	}

	Ret = XUsbPsu_SetEpConfig(InstancePtr, UsbEpNum, Dir, Maxsize, Type);
	if (Ret)
		return Ret;

	if (!(Ept->EpStatus & XUSBPSU_EP_ENABLED)) {
		Ret = XUsbPsu_SetXferResource(InstancePtr, UsbEpNum, Dir);
		if (Ret)
			return Ret;

		Ept->EpStatus |= XUSBPSU_EP_ENABLED;

		RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DALEPENA);
		RegVal |= XUSBPSU_DALEPENA_EP(Ept->PhyEpNum);
		XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DALEPENA, RegVal);
	}

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Disables Endpoint.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	UsbEpNum is USB endpoint number.
* @param	Dir is direction of endpoint
*			- XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT.
*
* @return	XST_SUCCESS else XST_FAILURE.
*
* @note		None.
*
****************************************************************************/
int XUsbPsu_EpDisable(struct XUsbPsu *InstancePtr, u8 UsbEpNum, u8 Dir)
{
	u32	RegVal;
	u8	PhyEpNum;
	struct XUsbPsu_Ep *Ept;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(UsbEpNum >= 0 && UsbEpNum <= 16);
	Xil_AssertNonvoid((Dir == XUSBPSU_EP_DIR_IN) ||
						(Dir == XUSBPSU_EP_DIR_OUT));

	PhyEpNum = PhysicalEp(UsbEpNum , Dir);
	Ept = &InstancePtr->eps[PhyEpNum];

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DALEPENA);
	RegVal &= ~XUSBPSU_DALEPENA_EP(PhyEpNum);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DALEPENA, RegVal);

	Ept->Type = 0;
	Ept->EpStatus = 0;
	Ept->MaxSize = 0;

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Enables USB Control Endpoint i.e., EP0OUT and EP0IN of Core.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Size is control endpoint size.
*
* @return	XST_SUCCESS else XST_FAILURE.
*
* @note		None.
*
****************************************************************************/
int XUsbPsu_EnableControlEp(struct XUsbPsu *InstancePtr, u16 Size)
{
	int RetVal;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(Size >= 64 && Size <= 512);

	RetVal = XUsbPsu_EpEnable(InstancePtr, 0, XUSBPSU_EP_DIR_OUT, Size,
				USB_ENDPOINT_XFER_CONTROL);
	if (RetVal) {
		return XST_FAILURE;
	}

	RetVal = XUsbPsu_EpEnable(InstancePtr, 0, XUSBPSU_EP_DIR_IN, Size,
				USB_ENDPOINT_XFER_CONTROL);
	if (RetVal) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Initializes Endpoints. All OUT endpoints are even numbered and all IN
* endpoints are odd numbered. EP0 is for Control OUT and EP1 is for
* Control IN.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void XUsbPsu_InitializeEps(struct XUsbPsu *InstancePtr)
{
	struct XUsbPsu_Ep	*Ept;
	u8  i;
	u8 epnum;

	Xil_AssertVoid(InstancePtr != NULL);

	for (i = 0; i < InstancePtr->NumOutEps; i++) {
		epnum = (i << 1) | XUSBPSU_EP_DIR_OUT;
		InstancePtr->eps[epnum].PhyEpNum = epnum;
		InstancePtr->eps[epnum].Direction = XUSBPSU_EP_DIR_OUT;
	}
	for (i = 0; i < InstancePtr->NumInEps; i++) {
		epnum = (i << 1) | XUSBPSU_EP_DIR_IN;
		InstancePtr->eps[epnum].PhyEpNum = epnum;
		InstancePtr->eps[epnum].Direction = XUSBPSU_EP_DIR_IN;
	}
}

/****************************************************************************/
/**
* Stops transfer on Endpoint.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	UsbEpNum is USB endpoint number.
* @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void XUsbPsu_StopTransfer(struct XUsbPsu *InstancePtr, u8 UsbEpNum, u8 Dir)
{
	struct XUsbPsu_Ep *Ept;
	struct XUsbPsu_EpParams *Params;
	u8 PhyEpNum;
	u32 Cmd;
	int Ret;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(UsbEpNum >= 0 && UsbEpNum <= 16);
	Xil_AssertVoid((Dir == XUSBPSU_EP_DIR_IN) || (Dir == XUSBPSU_EP_DIR_OUT));

	PhyEpNum = PhysicalEp(UsbEpNum, Dir);
	Params = XUsbPsu_GetEpParams(InstancePtr);
	Ept = &InstancePtr->eps[PhyEpNum];

	if (!Ept->ResourceIndex)
		return;

	/*
	 * - Issue EndTransfer WITH CMDIOC bit set
	 * - Wait 100us
	 */
	Cmd = XUSBPSU_DEPCMD_ENDTRANSFER;
	Cmd |= XUSBPSU_DEPCMD_CMDIOC;
	Cmd |= XUSBPSU_DEPCMD_PARAM(Ept->ResourceIndex);
	Ept->Cmd = XUSBPSU_DEPCMD_ENDTRANSFER;
	Ret = XUsbPsu_SendEpCmd(InstancePtr, Ept->PhyEpNum, Ept->Direction,
							Cmd, Params);
	Ept->ResourceIndex = 0;
	Ept->EpStatus &= ~XUSBPSU_EP_BUSY;
	usleep(100);
}

/****************************************************************************/
/**
* Clears Stall on all endpoints.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void XUsbPsu_ClearStalls(struct XUsbPsu *InstancePtr)
{
	struct XUsbPsu_EpParams *Params;
	u32 epnum;
	struct XUsbPsu_Ep *Ept;

	Xil_AssertVoid(InstancePtr != NULL);

	Params = XUsbPsu_GetEpParams(InstancePtr);
	for (epnum = 1; epnum < XUSBPSU_ENDPOINTS_NUM; epnum++) {

		Ept = &InstancePtr->eps[epnum];
		if (!Ept)
			continue;

		if (!(Ept->EpStatus & XUSBPSU_EP_STALL))
			continue;

		Ept->EpStatus &= ~XUSBPSU_EP_STALL;

		Ept->Cmd = XUSBPSU_DEPCMD_CLEARSTALL;
		XUsbPsu_SendEpCmd(InstancePtr, Ept->PhyEpNum,
						  Ept->Direction, XUSBPSU_DEPCMD_CLEARSTALL,
						  Params);
	}
}

/****************************************************************************/
/**
* Initiates DMA to send data on endpoint to Host.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	UsbEp is USB endpoint number.
* @param	BufferPtr is pointer to data.
* @param	BufferLen is length of data buffer.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note		None.
*
*****************************************************************************/
int XUsbPsu_EpBufferSend(struct XUsbPsu *InstancePtr, u8 UsbEp,
						 u8 *BufferPtr, u32 BufferLen)
{
	u8	PhyEpNum;
	int	RetVal;
	struct XUsbPsu_Trb	*TrbPtr;
	struct XUsbPsu_Ep *Ept;
	struct XUsbPsu_EpParams *Params;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(UsbEp >= 0 && UsbEp <= 16);
	Xil_AssertNonvoid(BufferPtr != NULL);

	PhyEpNum = PhysicalEp(UsbEp, XUSBPSU_EP_DIR_IN);
	if (PhyEpNum == 1)
	{
		RetVal = XUsbPsu_Ep0Send(InstancePtr, BufferPtr, BufferLen);
		return RetVal;
	}

	Ept = &InstancePtr->eps[PhyEpNum];

	if (Ept->Direction != XUSBPSU_EP_DIR_IN) {
		return XST_FAILURE;
	}

	Ept->RequestedBytes = BufferLen;
	Ept->BytesTxed = 0;
	Ept->BufferPtr = BufferPtr;

	TrbPtr = &Ept->EpTrb;

	TrbPtr->BufferPtrLow  = (UINTPTR)BufferPtr;
	TrbPtr->BufferPtrHigh  = ((UINTPTR)BufferPtr >> 16) >> 16;
	TrbPtr->Size = BufferLen & XUSBPSU_TRB_SIZE_MASK;
	TrbPtr->Ctrl = XUSBPSU_TRBCTL_NORMAL;

	TrbPtr->Ctrl |= (XUSBPSU_TRB_CTRL_HWO
					| XUSBPSU_TRB_CTRL_LST
					| XUSBPSU_TRB_CTRL_IOC
					| XUSBPSU_TRB_CTRL_ISP_IMI);

	Xil_DCacheFlushRange(TrbPtr, sizeof(struct XUsbPsu_Trb));
	Xil_DCacheFlushRange(BufferPtr, BufferLen);

	Params = XUsbPsu_GetEpParams(InstancePtr);
	Params->Param0 = 0;
	Params->Param1 = (UINTPTR)TrbPtr;

	Ept->Cmd = XUSBPSU_DEPCMD_STARTTRANSFER;
	RetVal = XUsbPsu_SendEpCmd(InstancePtr, UsbEp, Ept->Direction,
								XUSBPSU_DEPCMD_STARTTRANSFER, Params);
	if (RetVal != XST_SUCCESS) {
		return XST_FAILURE;
	}
	Ept->ResourceIndex = XUsbPsu_EpGetTransferIndex(InstancePtr,
													Ept->UsbEpNum,
													Ept->Direction);
	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Initiates DMA to receive data on Endpoint from Host.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	EpNum is USB endpoint number.
* @param	BufferPtr is pointer to data.
* @param	Length is length of data to be received.
*
* @return	XST_SUCCESS else XST_FAILURE
*
* @note		None.
*
*****************************************************************************/
int XUsbPsu_EpBufferRecv(struct XUsbPsu *InstancePtr, u8 UsbEp,
						 u8 *BufferPtr, u32 Length)
{
	u8	PhyEpNum;
	u32 Size;
	int	RetVal;
	struct XUsbPsu_Trb	*TrbPtr;
	struct XUsbPsu_Ep *Ept;
	struct XUsbPsu_EpParams *Params;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(UsbEp >= 0 && UsbEp <= 16);
	Xil_AssertNonvoid(BufferPtr != NULL);

	PhyEpNum = PhysicalEp(UsbEp, XUSBPSU_EP_DIR_OUT);
	if (PhyEpNum == 0)
	{
		RetVal = XUsbPsu_Ep0Recv(InstancePtr, BufferPtr, Length);
		return RetVal;
	}

	Ept = &InstancePtr->eps[PhyEpNum];

	if (Ept->Direction != XUSBPSU_EP_DIR_OUT) {
		return XST_FAILURE;
	}

	Params = XUsbPsu_GetEpParams(InstancePtr);

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
		Ept->UnalignedTx = 1;
	}

	TrbPtr = &Ept->EpTrb;

	TrbPtr->BufferPtrLow  = (UINTPTR)BufferPtr;
	TrbPtr->BufferPtrHigh = ((UINTPTR)BufferPtr >> 16) >> 16;
	TrbPtr->Size = Size;
	TrbPtr->Ctrl = XUSBPSU_TRBCTL_NORMAL;

	TrbPtr->Ctrl |= (XUSBPSU_TRB_CTRL_HWO
					| XUSBPSU_TRB_CTRL_LST
					| XUSBPSU_TRB_CTRL_IOC
					| XUSBPSU_TRB_CTRL_ISP_IMI);

	Params->Param0 = 0;
	Params->Param1 = (UINTPTR)TrbPtr;

	Xil_DCacheFlushRange(TrbPtr, sizeof(struct XUsbPsu_Trb));

	Params = XUsbPsu_GetEpParams(InstancePtr);
	Params->Param0 = 0;
	Params->Param1 = (UINTPTR)TrbPtr;

	Ept->Cmd = XUSBPSU_DEPCMD_STARTTRANSFER;

	RetVal = XUsbPsu_SendEpCmd(InstancePtr, UsbEp, Ept->Direction,
								XUSBPSU_DEPCMD_STARTTRANSFER, Params);
	if (RetVal != XST_SUCCESS) {
		return XST_FAILURE;
	}
	Ept->ResourceIndex = XUsbPsu_EpGetTransferIndex(InstancePtr,
													Ept->UsbEpNum,
													Ept->Direction);
	return XST_SUCCESS;
}

/****************************************************************************/
/**
* Stalls an Endpoint.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	EpNum is USB endpoint number.
* @param	Dir	is direction.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_EpSetStall(struct XUsbPsu *InstancePtr, u8 Epnum, u8 Dir)
{
	u8	PhyEpNum;
	struct XUsbPsu_Ep *Ept;
	struct XUsbPsu_EpParams *Params;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Epnum >= 0 && Epnum <= 16);
	Xil_AssertVoid((Dir == XUSBPSU_EP_DIR_IN) || (Dir == XUSBPSU_EP_DIR_OUT));

	PhyEpNum = PhysicalEp(Epnum, Dir);
	Params = XUsbPsu_GetEpParams(InstancePtr);

	if ((PhyEpNum == 0) || (PhyEpNum == 1)) {
		/* Control Endpoint stall is issued on EP0 */
		Ept = &InstancePtr->eps[0];
	}

	Ept->Cmd = XUSBPSU_DEPCMD_SETSTALL;
	XUsbPsu_SendEpCmd(InstancePtr, Ept->PhyEpNum, Ept->Direction,
							XUSBPSU_DEPCMD_SETSTALL, Params);

	Ept->EpStatus |= XUSBPSU_EP_STALL;
}

/****************************************************************************/
/**
* Clears Stall on an Endpoint.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	EpNum is USB endpoint number.
* @param	Dir	is direction.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_EpClearStall(struct XUsbPsu *InstancePtr, u8 Epnum, u8 Dir)
{
	u8	PhyEpNum;
	struct XUsbPsu_Ep *Ept;
	struct XUsbPsu_EpParams *Params;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Epnum >= 0 && Epnum <= 16);
	Xil_AssertVoid((Dir == XUSBPSU_EP_DIR_IN) || (Dir == XUSBPSU_EP_DIR_OUT));

	PhyEpNum = PhysicalEp(Epnum, Dir);
	Params = XUsbPsu_GetEpParams(InstancePtr);

	if ((PhyEpNum == 0) || (PhyEpNum == 1)) {
		/* Control Endpoint stall is issued on EP0 */
		Ept = &InstancePtr->eps[0];
	}

	Ept->Cmd = XUSBPSU_DEPCMD_CLEARSTALL;
	XUsbPsu_SendEpCmd(InstancePtr, Ept->PhyEpNum, Ept->Direction,
							XUSBPSU_DEPCMD_CLEARSTALL, Params);

	Ept->EpStatus &= ~XUSBPSU_EP_STALL;
}

/****************************************************************************/
/**
* Sets an user handler to be called after data is sent/received by an Endpoint
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	EpNum is USB endpoint number.
* @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT.
* @param	Handler is user handler to be called.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_SetEpHandler(struct XUsbPsu *InstancePtr, u8 Epnum,
			u8 Dir, void (*Handler)(void *, u32, u32))
{
	u8 PhyEpNum;
	struct XUsbPsu_Ep *Ept;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Epnum >= 0 && Epnum <= 16);
	Xil_AssertVoid((Dir == XUSBPSU_EP_DIR_IN) || (Dir == XUSBPSU_EP_DIR_OUT));

	PhyEpNum = PhysicalEp(Epnum, Dir);
	Ept = &InstancePtr->eps[PhyEpNum];
	Ept->Handler = Handler;
}

/****************************************************************************/
/**
* Returns status of endpoint - Stalled or not
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	EpNum is USB endpoint number.
* @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT.
*
* @return
*			1 - if stalled
*			0 - if not stalled
*
* @note		None.
*
*****************************************************************************/
int XUsbPsu_IsEpStalled(struct XUsbPsu *InstancePtr, u8 Epnum, u8 Dir)
{
	u8 PhyEpNum;
	struct XUsbPsu_Ep *Ept;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Epnum >= 0 && Epnum <= 16);
	Xil_AssertVoid((Dir == XUSBPSU_EP_DIR_IN) || (Dir == XUSBPSU_EP_DIR_OUT));

	PhyEpNum = PhysicalEp(Epnum, Dir);
	Ept = &InstancePtr->eps[PhyEpNum];

	return !!(Ept->EpStatus & XUSBPSU_EP_STALL);
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
void XUsbPsu_EpXferComplete(struct XUsbPsu *InstancePtr,
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
	Ept = &InstancePtr->eps[EpNum];
	Dir = Ept->Direction;
	TrbPtr = &Ept->EpTrb;

	Xil_DCacheInvalidateRange(TrbPtr, sizeof(struct XUsbPsu_Trb));

	Status = XUSBPSU_TRB_SIZE_TRBSTS(TrbPtr->Size);
	Length = TrbPtr->Size & XUSBPSU_TRB_SIZE_MASK;

	if (Length && Dir) { /* IN */
		Ept->BytesTxed = Ept->RequestedBytes - Length;
	}

	if (!Length) {
		Ept->BytesTxed = Ept->RequestedBytes;
	}

	if (Length && !Dir) { /* OUT */
		if (Ept->UnalignedTx == 1) {
			Ept->BytesTxed = Ept->RequestedBytes;
			Ept->UnalignedTx = 0;
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
