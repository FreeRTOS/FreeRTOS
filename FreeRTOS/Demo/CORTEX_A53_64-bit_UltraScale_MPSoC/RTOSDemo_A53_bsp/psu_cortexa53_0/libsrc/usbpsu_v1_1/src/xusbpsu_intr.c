/******************************************************************************
*
* Copyright (C) 2016 Xilinx, Inc.  All rights reserved.
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
* @file xusbpsu_intr.c
* @addtogroup usbpsu_v1_0
* @{
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 1.0   sg  06/06/16 First release
*
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xusbpsu.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/****************************************************************************/
/**
* Endpoint interrupt handler.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Event is endpoint Event occured in the core.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_EpInterrupt(struct XUsbPsu *InstancePtr,
		const struct XUsbPsu_Event_Epevt *Event)
{
	struct XUsbPsu_Ep *Ept;
	u32 Epnum;

	Epnum = Event->Epnumber;
	Ept = &InstancePtr->eps[Epnum];

	if ((Ept->EpStatus & XUSBPSU_EP_ENABLED) == (u32)0U) {
		return;
	}

	if ((Epnum == (u32)0) || (Epnum == (u32)1)) {
		XUsbPsu_Ep0Intr(InstancePtr, Event);
		return;
	}

	/* Handle other end point events */
	switch (Event->Endpoint_Event) {
		case XUSBPSU_DEPEVT_XFERCOMPLETE:
			XUsbPsu_EpXferComplete(InstancePtr, Event);
			break;

		case XUSBPSU_DEPEVT_XFERNOTREADY:
			break;

		default:
			/* Made for Misra-C Compliance. */
			break;
	}
}

/****************************************************************************/
/**
* Disconnect Interrupt handler.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_DisconnectIntr(struct XUsbPsu *InstancePtr)
{
	u32 RegVal;

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCTL);
	RegVal &= ~XUSBPSU_DCTL_INITU1ENA;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, RegVal);

	RegVal &= ~XUSBPSU_DCTL_INITU2ENA;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, RegVal);

	InstancePtr->IsConfigDone = 0U;
	InstancePtr->Speed = XUSBPSU_SPEED_UNKNOWN;
}

/****************************************************************************/
/**
* Reset Interrupt handler.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_ResetIntr(struct XUsbPsu *InstancePtr)
{
	u32	RegVal;
	u32	Index;

	InstancePtr->State = XUSBPSU_STATE_DEFAULT;

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCTL);
	RegVal &= ~XUSBPSU_DCTL_TSTCTRL_MASK;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCTL, RegVal);
	InstancePtr->TestMode = 0U;

	for (Index = 0U; Index < (InstancePtr->NumInEps + InstancePtr->NumOutEps);
			Index++)
	{
		InstancePtr->eps[Index].EpStatus = 0U;
	}

	InstancePtr->IsConfigDone = 0U;

	/* Reset device address to zero */
	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DCFG);
	RegVal &= ~(XUSBPSU_DCFG_DEVADDR_MASK);
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_DCFG, RegVal);
}

/****************************************************************************/
/**
* Connection Done Interrupt handler.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_ConnDoneIntr(struct XUsbPsu *InstancePtr)
{
	u32			RegVal;
	u16			Size;
	u8			Speed;

	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_DSTS);
	Speed = (u8)(RegVal & XUSBPSU_DSTS_CONNECTSPD);
	InstancePtr->Speed = Speed;

	switch (Speed) {
	case XUSBPSU_DCFG_SUPERSPEED:
#ifdef XUSBPSU_DEBUG
		xil_printf("Super Speed\r\n");
#endif
		Size = 512U;
		InstancePtr->Speed = XUSBPSU_SPEED_SUPER;
		break;

	case XUSBPSU_DCFG_HIGHSPEED:
#ifdef XUSBPSU_DEBUG
		xil_printf("High Speed\r\n");
#endif
		Size = 64U;
		InstancePtr->Speed = XUSBPSU_SPEED_HIGH;
		break;

	case XUSBPSU_DCFG_FULLSPEED2:
	case XUSBPSU_DCFG_FULLSPEED1:
#ifdef XUSBPSU_DEBUG
		xil_printf("Full Speed\r\n");
#endif
		Size = 64U;
		InstancePtr->Speed = XUSBPSU_SPEED_FULL;
		break;

	case XUSBPSU_DCFG_LOWSPEED:
#ifdef XUSBPSU_DEBUG
		xil_printf("Low Speed\r\n");
#endif
		Size = 64U;
		InstancePtr->Speed = XUSBPSU_SPEED_LOW;
		break;
	default :
		Size = 64U;
		break;
	}

	(void)XUsbPsu_EnableControlEp(InstancePtr, Size);
	(void)XUsbPsu_RecvSetup(InstancePtr);
}

/****************************************************************************/
/**
* Link Status Change Interrupt handler.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	EvtInfo is Event information.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_LinkStsChangeIntr(struct XUsbPsu *InstancePtr, u32 EvtInfo)
{
	u32	State = EvtInfo & (u32)XUSBPSU_LINK_STATE_MASK;
	InstancePtr->LinkState = (u8)State;
}

/****************************************************************************/
/**
* Interrupt handler for device specific events.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Event is the Device Event occured in core.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_DevInterrupt(struct XUsbPsu *InstancePtr,
		const struct XUsbPsu_Event_Devt *Event)
{

	switch (Event->Type) {
		case XUSBPSU_DEVICE_EVENT_DISCONNECT:
			XUsbPsu_DisconnectIntr(InstancePtr);
			break;

		case XUSBPSU_DEVICE_EVENT_RESET:
			XUsbPsu_ResetIntr(InstancePtr);
			break;

		case XUSBPSU_DEVICE_EVENT_CONNECT_DONE:
			XUsbPsu_ConnDoneIntr(InstancePtr);
			break;

		case XUSBPSU_DEVICE_EVENT_WAKEUP:
			break;

		case XUSBPSU_DEVICE_EVENT_HIBER_REQ:
			break;

		case XUSBPSU_DEVICE_EVENT_LINK_STATUS_CHANGE:
			XUsbPsu_LinkStsChangeIntr(InstancePtr,
					Event->Event_Info);
			break;

		case XUSBPSU_DEVICE_EVENT_EOPF:
			break;

		case XUSBPSU_DEVICE_EVENT_SOF:
			break;

		case XUSBPSU_DEVICE_EVENT_ERRATIC_ERROR:
			break;

		case XUSBPSU_DEVICE_EVENT_CMD_CMPL:
			break;

		case XUSBPSU_DEVICE_EVENT_OVERFLOW:
			break;

		default:
			/* Made for Misra-C Compliance. */
			break;
	}
}

/****************************************************************************/
/**
* Processes an Event entry in Event Buffer.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Event is the Event entry.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_EventHandler(struct XUsbPsu *InstancePtr,
			const union XUsbPsu_Event *Event)
{

	if (Event->Type.Is_DevEvt == 0U) {
		/* End point Specific Event */
		XUsbPsu_EpInterrupt(InstancePtr, &Event->Epevt);
		return;
	}

	switch (Event->Type.Type) {
	case XUSBPSU_EVENT_TYPE_DEV:
		/* Device Specific Event */
		XUsbPsu_DevInterrupt(InstancePtr, &Event->Devt);
		break;
	/* Carkit and I2C events not supported now */
	default:
		/* Made for Misra-C Compliance. */
		break;
	}
}

/****************************************************************************/
/**
* Processes events in an Event Buffer.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @bus		Event buffer number.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_EventBufferHandler(struct XUsbPsu *InstancePtr)
{
	struct XUsbPsu_EvtBuffer *Evt;
	union XUsbPsu_Event Event = {0};

	Evt = &InstancePtr->Evt;

	Xil_DCacheInvalidateRange((INTPTR)Evt->BuffAddr,
                              (u32)XUSBPSU_EVENT_BUFFERS_SIZE);

	while (Evt->Count > 0) {
		Event.Raw = *(UINTPTR *)(Evt->BuffAddr + Evt->Offset);

		/*
         * Process the event received
         */
        XUsbPsu_EventHandler(InstancePtr, &Event);

		Evt->Offset = (Evt->Offset + 4U) % XUSBPSU_EVENT_BUFFERS_SIZE;
		Evt->Count -= 4;
		XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GEVNTCOUNT(0), 4U);
	}

	Evt->Flags &= ~XUSBPSU_EVENT_PENDING;
}

/****************************************************************************/
/**
* Main Interrupt Handler.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUsbPsu_IntrHandler(void *XUsbPsuInstancePtr)
{
	struct XUsbPsu	*InstancePtr;
	struct XUsbPsu_EvtBuffer *Evt;
	u32 Count;
	u32 RegVal;

	InstancePtr = XUsbPsuInstancePtr;

	Evt = &InstancePtr->Evt;

	Count = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_GEVNTCOUNT(0));
	Count &= XUSBPSU_GEVNTCOUNT_MASK;
	/*
	 * As per data book software should only process Events if Event count
	 * is greater than zero.
	 */
	if (Count == 0U) {
		return;
	}

	Evt->Count = Count;
	Evt->Flags |= XUSBPSU_EVENT_PENDING;

	/* Mask event interrupt */
	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_GEVNTSIZ(0));
	RegVal |= XUSBPSU_GEVNTSIZ_INTMASK;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GEVNTSIZ(0), RegVal);

	/* Processes events in an Event Buffer */
	XUsbPsu_EventBufferHandler(InstancePtr);

	/* Unmask event interrupt */
	RegVal = XUsbPsu_ReadReg(InstancePtr, XUSBPSU_GEVNTSIZ(0));
	RegVal &= ~XUSBPSU_GEVNTSIZ_INTMASK;
	XUsbPsu_WriteReg(InstancePtr, XUSBPSU_GEVNTSIZ(0), RegVal);
}

/** @} */
