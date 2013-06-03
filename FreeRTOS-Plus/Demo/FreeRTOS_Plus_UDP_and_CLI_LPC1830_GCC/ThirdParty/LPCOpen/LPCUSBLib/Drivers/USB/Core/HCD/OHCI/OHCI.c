/*
 * @brief Open Host Controller Interface
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

/*=======================================================================*/
/*        I N C L U D E S                                                */
/*=======================================================================*/
#define  __INCLUDE_FROM_USB_DRIVER
#include "../../USBMode.h"

#if (defined(USB_CAN_BE_HOST) && defined(__LPC_OHCI__))

#define __LPC_OHCI_C__
#include "../../../../../Common/Common.h"
#include "../../USBTask.h"
#include "../HCD.h"
#include "OHCI.h"

PRAGMA_ALIGN_256
OHCI_HOST_DATA_T ohci_data[MAX_USB_CORE] __BSS(USBRAM_SECTION) ATTR_ALIGNED(256);

/*=======================================================================*/
/*  G L O B A L   S Y M B O L   D E C L A R A T I O N S                  */
/*=======================================================================*/
void USB_Host_Enumerate (uint8_t HostID);

void USB_Host_DeEnumerate(uint8_t HostID);

/*********************************************************************
 *								IMPLEMENTATION
 **********************************************************************/
HCD_STATUS HcdGetDeviceSpeed(uint8_t HostID, HCD_USB_SPEED *DeviceSpeed)
{
	if ( USB_REG(HostID)->RhPortStatus1 & HC_RH_PORT_STATUS_CurrentConnectStatus) {	/* If device is connected */
		*DeviceSpeed =
			( USB_REG(HostID)->RhPortStatus1 & HC_RH_PORT_STATUS_LowSpeedDeviceAttached) ? LOW_SPEED : FULL_SPEED;
		return HCD_STATUS_OK;
	}
	else {
		return HCD_STATUS_DEVICE_DISCONNECTED;
	}
}

uint32_t HcdGetFrameNumber(uint8_t HostID)
{
	return ohci_data[HostID].hcca.HccaFrameNumber;
}

HCD_STATUS HcdRhPortReset(uint8_t HostID)
{
	HcdDelayMS(400);// TODO delay should be on Host_LPC
	USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_PortResetStatus;	/* SetPortReset */
	/* should have time-out */
	while ( USB_REG(HostID)->RhPortStatus1 & HC_RH_PORT_STATUS_PortResetStatus) {}

	USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_PortResetStatusChange;/* Clear Port Reset Status Change */

	HcdDelayMS(400);// TODO delay should be on Host_LPC
	return HCD_STATUS_OK;
}

HCD_STATUS HcdRhPortEnable(uint8_t HostID)
{
	USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_PowerEnableStatus;/* SetPortEnable */

	return HCD_STATUS_OK;
}

HCD_STATUS HcdRhPortDisable(uint8_t HostID)
{
	USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_CurrentConnectStatus;	/* ClearPortEnable */

	return HCD_STATUS_OK;
}

HCD_STATUS HcdInitDriver(uint8_t HostID)
{
	USB_REG(HostID)->OTGClkCtrl = 0x00000019;			/* enable Host clock, OTG clock and AHB clock */
	while ((USB_REG(HostID)->OTGClkSt & 0x00000019) != 0x00000019) ;
#if defined(__LPC175X_6X__)
	USB_REG(HostID)->StCtrl = 0x3;					/* ??? */
#elif defined(__LPC177X_8X__) || defined(__LPC407X_8X__)
	USB_REG(HostID)->StCtrl = 0x1;					/* Port 1 is host */
#endif
	OHciHostReset(HostID);	/* Software Reset */
	return OHciHostInit(HostID);
}

HCD_STATUS HcdDeInitDriver(uint8_t HostID)
{
	USB_REG(HostID)->StCtrl = 0;
	return HCD_STATUS_OK;
}

HCD_STATUS HcdOpenPipe(uint8_t HostID,
					   uint8_t DeviceAddr,
					   HCD_USB_SPEED DeviceSpeed,
					   uint8_t EndpointNumber,
					   HCD_TRANSFER_TYPE TransferType,
					   HCD_TRANSFER_DIR TransferDir,
					   uint16_t MaxPacketSize,
					   uint8_t Interval,
					   uint8_t Mult,
					   uint8_t HSHubDevAddr,
					   uint8_t HSHubPortNum,
					   uint32_t *const PipeHandle)
{
	uint32_t EdIdx;
	uint8_t ListIdx;

	(void) Mult; (void) HSHubDevAddr; (void) HSHubPortNum;	/* Disable compiler warnings */

#if !ISO_LIST_ENABLE
	if ( TransferType == ISOCHRONOUS_TRANSFER ) {
		ASSERT_STATUS_OK_MESSAGE(HCD_STATUS_TRANSFER_TYPE_NOT_SUPPORTED, "Please set ISO_LIST_ENABLE to YES");
	}
#endif

#if !INTERRUPT_LIST_ENABLE
	if ( TransferType == INTERRUPT_TRANSFER ) {
		ASSERT_STATUS_OK_MESSAGE(HCD_STATUS_TRANSFER_TYPE_NOT_SUPPORTED, "Please set INTERRUPT_LIST_ENABLE to YES");
	}
#endif

	/********************************* Parameters Verify *********************************/
	ASSERT_STATUS_OK(OpenPipe_VerifyParameters(HostID, DeviceAddr, DeviceSpeed, EndpointNumber, TransferType,
											   TransferDir, MaxPacketSize, Interval, 0) );

	EndpointNumber &= 0xF;	/* Endpoint number is in range 0-15 */
	MaxPacketSize &= 0x3FF;	/* Max Packet Size is in range 0-1024 */

	switch (TransferType) {
	case CONTROL_TRANSFER:
		ListIdx = CONTROL_LIST_HEAD;
		break;

	case BULK_TRANSFER:
		ListIdx = BULK_LIST_HEAD;
		break;

	case INTERRUPT_TRANSFER:
		// ListIdx = FindInterruptTransferListIndex(Interval);
		ListIdx = INTERRUPT_1ms_LIST_HEAD;
		break;

	case ISOCHRONOUS_TRANSFER:
		ListIdx = ISO_LIST_HEAD;
		break;
	default :							// just to clear warning
		ListIdx = 0xFF;
		break;
	}
	
	if(ListIdx == 0xFF) return HCD_STATUS_PARAMETER_INVALID;

	ASSERT_STATUS_OK(AllocEd(DeviceAddr, DeviceSpeed, EndpointNumber, TransferType, TransferDir, MaxPacketSize,
							 Interval, &EdIdx) );

	/* Add new ED to the EDs List */
	HcdED(EdIdx)->ListIndex  = ListIdx;
	InsertEndpoint(HostID, EdIdx, ListIdx);

	PipehandleCreate(PipeHandle, HostID, EdIdx);
	return HCD_STATUS_OK;
}

HCD_STATUS HcdCancelTransfer(uint32_t PipeHandle)
{
	uint8_t HostID, EdIdx;

	ASSERT_STATUS_OK(PipehandleParse(PipeHandle, &HostID, &EdIdx) );

	HcdED(EdIdx)->hcED.Skip = 1;

	/* Clear SOF and wait for the next frame */
	USB_REG(HostID)->InterruptStatus = HC_INTERRUPT_StartofFrame;
	while ( !(USB_REG(HostID)->InterruptStatus & HC_INTERRUPT_StartofFrame) )/* TODO Should have timeout */

		/* ISO TD & General TD have the same offset for nextTD, we can use GTD as pointer to travel on TD list */
		while ( Align16(HcdED(EdIdx)->hcED.HeadP.HeadTD) != Align16(HcdED(EdIdx)->hcED.TailP) ) {
			uint32_t HeadTD = Align16(HcdED(EdIdx)->hcED.HeadP.HeadTD);
			if ( IsIsoEndpoint(EdIdx) ) {
				HcdED(EdIdx)->hcED.HeadP.HeadTD = ((PHCD_IsoTransferDescriptor) HeadTD)->NextTD;
				FreeItd( (PHCD_IsoTransferDescriptor) HeadTD);
			}
			else {
				HcdED(EdIdx)->hcED.HeadP.HeadTD = ((PHCD_GeneralTransferDescriptor) HeadTD)->hcGTD.NextTD;
				FreeGtd((PHCD_GeneralTransferDescriptor) HeadTD);
			}
		}
	HcdED(EdIdx)->hcED.HeadP.HeadTD = Align16(HcdED(EdIdx)->hcED.TailP);/*-- Toggle Carry/Halted are also set to 0 --*/
	HcdED(EdIdx)->hcED.HeadP.ToggleCarry = 0;

	HcdED(EdIdx)->hcED.Skip = 0;
	return HCD_STATUS_OK;
}

HCD_STATUS HcdClosePipe(uint32_t PipeHandle)
{
	uint8_t HostID, EdIdx;

	ASSERT_STATUS_OK(PipehandleParse(PipeHandle, &HostID, &EdIdx) );

	ASSERT_STATUS_OK(HcdCancelTransfer(PipeHandle) );

	HcdED(EdIdx)->hcED.Skip = 1;/* no need for delay, it is already delayed in cancel transfer */
	RemoveEndpoint(HostID, EdIdx);

	FreeED(EdIdx);

	return HCD_STATUS_OK;
}

HCD_STATUS HcdClearEndpointHalt(uint32_t PipeHandle)
{
	uint8_t HostID, EdIdx;
	ASSERT_STATUS_OK(PipehandleParse(PipeHandle, &HostID, &EdIdx) );
	/* TODO should we call HcdCancelTrnasfer ? */
	HcdED(EdIdx)->hcED.HeadP.Halted = 0;
	HcdED(EdIdx)->hcED.HeadP.ToggleCarry = 0;

	HcdED(EdIdx)->status = HCD_STATUS_OK;

	return HCD_STATUS_OK;
}

HCD_STATUS HcdControlTransfer(uint32_t PipeHandle,
							  const USB_Request_Header_t *const pDeviceRequest,
							  uint8_t *const buffer)
{
	uint8_t HostID, EdIdx;

	if ((pDeviceRequest == NULL) || (buffer == NULL)) {
		ASSERT_STATUS_OK_MESSAGE(HCD_STATUS_PARAMETER_INVALID, "Device Request or Data Buffer is NULL");
	}

	ASSERT_STATUS_OK(PipehandleParse(PipeHandle, &HostID, &EdIdx) );

	/************************************************************************/
	/* Setup Stage                                                          */
	/************************************************************************/
	ASSERT_STATUS_OK(QueueOneGTD(EdIdx, (uint8_t *) pDeviceRequest, 8, 0, 2, 0) );			/* Setup TD: DirectionPID=00 - DataToggle=10b (always DATA0) */

	/************************************************************************/
	/* Data Stage                                                           */
	/************************************************************************/
	if (pDeviceRequest->wLength) {	/* Could have problem if the wLength is larger than pipe size */
		ASSERT_STATUS_OK(QueueOneGTD(EdIdx, buffer, pDeviceRequest->wLength,
									 (pDeviceRequest->bmRequestType & 0x80) ? 2 : 1, 3, 0) );											/* DataToggle=11b (always DATA1) */
	}
	/************************************************************************/
	/* Status Stage                                                                     */
	/************************************************************************/
	ASSERT_STATUS_OK(QueueOneGTD(EdIdx, NULL, 0, (pDeviceRequest->bmRequestType & 0x80) ? 1 : 2, 3, 1) );	/* Status TD: Direction=opposite of data direction - DataToggle=11b (always DATA1) */

	/* set control list filled */
	USB_REG(HostID)->CommandStatus |= HC_COMMAND_STATUS_ControlListFilled;

	HcdED(EdIdx)->status = HCD_STATUS_TRANSFER_QUEUED;

	/* wait for semaphore compete TDs */
	ASSERT_STATUS_OK(WaitForTransferComplete(EdIdx) );

	return HCD_STATUS_OK;
}

static HCD_STATUS QueueOneITD(uint32_t EdIdx, uint8_t *dataBuff, uint32_t TDLen, uint16_t StartingFrame)
{
	uint32_t i;
	PHCD_IsoTransferDescriptor pItd = (PHCD_IsoTransferDescriptor) Align16(HcdED(EdIdx)->hcED.TailP);

	pItd->StartingFrame = StartingFrame;
	pItd->FrameCount =
		(TDLen / HcdED(EdIdx)->hcED.MaxPackageSize) + (TDLen % HcdED(EdIdx)->hcED.MaxPackageSize ? 1 : 0) - 1;
	pItd->BufferPage0 = Align4k( (uint32_t) dataBuff);
	pItd->BufferEnd = (uint32_t) (dataBuff + TDLen - 1);

	for (i = 0; TDLen > 0 && i < 8; i++) {
		uint32_t XactLen = MIN(TDLen, HcdED(EdIdx)->hcED.MaxPackageSize);

		pItd->OffsetPSW[i] =
			(HCD_STATUS_TRANSFER_NotAccessed <<
		12) | (Align4k((uint32_t) dataBuff) != Align4k(pItd->BufferPage0) ? _BIT(12) : 0) |
			Offset4k((uint32_t) dataBuff);					/*-- FIXME take into cross page account later 15-12: ConditionCode, 11-0: offset --*/

		TDLen -= XactLen;
		dataBuff += XactLen;
	}

	/* Create a new place holder TD & link setup TD to the new place holder */
	ASSERT_STATUS_OK(AllocItdForEd(EdIdx) );

	return HCD_STATUS_OK;
}

static HCD_STATUS QueueITDs(uint32_t EdIdx, uint8_t *dataBuff, uint32_t xferLen)
{
	uint32_t FrameIdx;
	uint32_t MaxDataSize;

#if 0	/* Maximum bandwidth (Interval = 1) regardless of Interval value */
	uint8_t MaxXactPerITD, FramePeriod;
	if (HcdED(EdIdx)->Interval < 4) {	/*-- Period < 8 --*/
		MaxXactPerITD = 1 << ( 4 - HcdED(EdIdx)->Interval );	/*-- Interval 1 => 8, 2 => 4, 3 => 2 --*/
		FramePeriod = 1;
	}
	else {
		MaxXactPerITD = 1;
		FramePeriod = 1 << ( HcdED(EdIdx)->Interval - 4 );	/*-- Frame step 4 => 1, 5 => 2, 6 => 3 --*/
	}
#else
	#define MaxXactPerITD   8
	#define FramePeriod     1
#endif

	MaxDataSize = MaxXactPerITD * HcdED(EdIdx)->hcED.MaxPackageSize;
	FrameIdx = HcdGetFrameNumber(0) + 1;	/* FIXME dual controller */

	while (xferLen > 0) {
		uint16_t TdLen;
		uint32_t MaxTDLen = TD_MAX_XFER_LENGTH - Offset4k((uint32_t) dataBuff);
		MaxTDLen = MIN(MaxDataSize, MaxTDLen);

		TdLen = MIN(xferLen, MaxTDLen);
		xferLen -= TdLen;

		/*---------- Fill data to Place hodler TD ----------*/
		ASSERT_STATUS_OK(QueueOneITD(EdIdx, dataBuff, TdLen, FrameIdx) );

		FrameIdx = (FrameIdx + FramePeriod) % (1 << 16);
		dataBuff += TdLen;
	}
	return HCD_STATUS_OK;
}

HCD_STATUS HcdDataTransfer(uint32_t PipeHandle,
						   uint8_t *const buffer,
						   uint32_t const length,
						   uint16_t *const pActualTransferred)
{
	uint8_t HostID, EdIdx;
	uint32_t ExpectedLength;

	if ((buffer == NULL) || (length == 0)) {
		ASSERT_STATUS_OK_MESSAGE(HCD_STATUS_PARAMETER_INVALID, "Data Buffer is NULL or Transfer Length is 0");
	}

	ASSERT_STATUS_OK(PipehandleParse(PipeHandle, &HostID, &EdIdx) );
	ASSERT_STATUS_OK(HcdED(EdIdx)->hcED.HeadP.Halted ? HCD_STATUS_TRANSFER_Stall : HCD_STATUS_OK);

	ExpectedLength = (length != HCD_ENDPOINT_MAXPACKET_XFER_LEN) ? length : HcdED(EdIdx)->hcED.MaxPackageSize;

	if ( IsIsoEndpoint(EdIdx) ) {	/* Iso Transfer */
		ASSERT_STATUS_OK(QueueITDs(EdIdx, buffer, ExpectedLength) );
	}
	else {
		ASSERT_STATUS_OK(QueueGTDs(EdIdx, buffer, ExpectedLength, 0) );
		if (HcdED(EdIdx)->ListIndex == BULK_LIST_HEAD) {
			USB_REG(HostID)->CommandStatus |= HC_COMMAND_STATUS_BulkListFilled;
		}
	}

	HcdED(EdIdx)->status = HCD_STATUS_TRANSFER_QUEUED;
	HcdED(EdIdx)->pActualTransferCount = pActualTransferred;/* TODO refractor Actual length transfer */

	return HCD_STATUS_OK;
}

HCD_STATUS HcdGetPipeStatus(uint32_t PipeHandle)
{
	uint8_t HostID, EdIdx;

	ASSERT_STATUS_OK(PipehandleParse(PipeHandle, &HostID, &EdIdx) );

	return (HCD_STATUS)HcdED(EdIdx)->status;
}

static void OHciRhStatusChangeIsr(uint8_t HostID, uint32_t deviceConnect)
{
	if (deviceConnect) {/* Device Attached */
		USB_Host_Enumerate(HostID);
	}
	else {	/* Device detached */
		USB_Host_DeEnumerate(HostID);
	}
}

static void ProcessDoneQueue(uint8_t HostID, uint32_t donehead)
{
	PHC_GTD pCurTD = (PHC_GTD) donehead;
	PHC_GTD pTDList = NULL;

	/* do nothing if done queue is empty */
	if (!donehead) {
		return;
	}

	/* reverse done queue order */
	do {
		uint32_t nextTD = pCurTD->NextTD;
		pCurTD->NextTD = (uint32_t) pTDList;
		pTDList = pCurTD;
		pCurTD = (PHC_GTD) nextTD;
	} while (pCurTD);

	while (pTDList != NULL) {
		uint32_t EdIdx;

		pCurTD  = pTDList;
		pTDList = (PHC_GTD) pTDList->NextTD;

		/* TODO Cannot determine EdIdx because GTD and ITD have different offsets for EdIdx  */
		if ( ((uint32_t) pCurTD) <=  ((uint32_t) HcdITD(MAX_ITD - 1)) ) {	/* ISO TD address range */
			PHCD_IsoTransferDescriptor pItd = (PHCD_IsoTransferDescriptor) pCurTD;
			EdIdx = pItd->EdIdx;
		}
		else {	/* GTD */
			PHCD_GeneralTransferDescriptor pGtd = (PHCD_GeneralTransferDescriptor) pCurTD;
			EdIdx = pGtd->EdIdx;

			if (pGtd->hcGTD.CurrentBufferPointer) {
				pGtd->TransferCount -=
					( Align4k( ((uint32_t) pGtd->hcGTD.BufferEnd) ^
							   ((uint32_t) pGtd->hcGTD.CurrentBufferPointer) ) ? 0x00001000 : 0 ) +
					Offset4k((uint32_t) pGtd->hcGTD.BufferEnd) - Offset4k(
						(uint32_t) pGtd->hcGTD.CurrentBufferPointer) + 1;
			}
			if (HcdED(EdIdx)->pActualTransferCount) {
				*(HcdED(EdIdx)->pActualTransferCount) = pGtd->TransferCount;/* increase usb request transfer count */

			}
		}

		if (pCurTD->DelayInterrupt != TD_NoInterruptOnComplete) {	/* Update ED status if Interrupt on Complete is set */
			HcdED(EdIdx)->status = pCurTD->ConditionCode;
		}

		if ( pCurTD->ConditionCode ) {	/* also update ED status if TD complete with error */
			HcdED(EdIdx)->status =
				(HcdED(EdIdx)->hcED.HeadP.Halted == 1) ? HCD_STATUS_TRANSFER_Stall : pCurTD->ConditionCode;
			HcdED(EdIdx)->hcED.HeadP.Halted = 0;
			hcd_printf("Error on Endpoint 0x%X has HCD_STATUS code %d\r\n",
					   HcdED(EdIdx)->hcED.FunctionAddr | (HcdED(EdIdx)->hcED.Direction == 2 ? 0x80 : 0x00),
					   pCurTD->ConditionCode);
		}

		/* remove completed TD from usb request list, if request list is now empty complete usb request */
		if (IsIsoEndpoint(EdIdx)) {
			FreeItd( (PHCD_IsoTransferDescriptor) pCurTD);
		}
		else {
			FreeGtd( (PHCD_GeneralTransferDescriptor) pCurTD);
		}

		/* Post Semaphore to signal TDs are transfer */
	}
}

#if SCHEDULING_OVRERRUN_INTERRUPT
static void OHciSchedulingOverrunIsr(uint8_t HostID)
{}

#endif

#if SOF_INTERRUPT
static void OHciStartofFrameIsr(uint8_t HostID)
{}

#endif

#if RESUME_DETECT_INTERRUPT
static void OHciResumeDetectedIsr(uint8_t HostID)
{}

#endif

#if UNRECOVERABLE_ERROR_INTERRUPT
static void OHciUnrecoverableErrorIsr(uint8_t HostID)
{}

#endif

#if FRAMENUMBER_OVERFLOW_INTERRUPT
static void OHciFramenumberOverflowIsr(uint8_t HostID)
{}

#endif

#if OWNERSHIP_CHANGE_INTERRUPT
static void OHciOwnershipChangeIsr(uint8_t HostID)
{}

#endif

void HcdIrqHandler(uint8_t HostID)
{
	uint32_t IntStatus;

	IntStatus = USB_REG(HostID)->InterruptStatus;
	/* Clear status after read immediately.
		 Then it will be able to record a new status. */
	USB_REG(HostID)->InterruptStatus = IntStatus;/* Clear HcInterruptStatus */
	IntStatus &= USB_REG(HostID)->InterruptEnable;
	if (IntStatus == 0) {
		return;
	}

	/* disable all interrupt for processing */
	USB_REG(HostID)->InterruptDisable = HC_INTERRUPT_MasterInterruptEnable;

	/* Process RootHub Status Change */
	if (IntStatus & HC_INTERRUPT_RootHubStatusChange) {
		for(;USB_REG(HostID)->RhPortStatus1 & HC_RH_PORT_STATUS_StatusChangeMask;){
			/* only 1 port/host --> skip to get the number of ports */
			if (USB_REG(HostID)->RhPortStatus1 & HC_RH_PORT_STATUS_ConnectStatusChange) {
				if (USB_REG(HostID)->RhStatus & HC_RH_STATUS_DeviceRemoteWakeupEnable) {	/* means a remote wakeup event */

				}
				else {}

				USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_ConnectStatusChange;	/* clear CSC bit */
				OHciRhStatusChangeIsr(HostID, USB_REG(HostID)->RhPortStatus1 & HC_RH_PORT_STATUS_CurrentConnectStatus);
			}

			if (USB_REG(HostID)->RhPortStatus1 & HC_RH_PORT_STATUS_PortEnableStatusChange) {
				USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_PortEnableStatusChange;	/* clear PESC */
			}

			if (USB_REG(HostID)->RhPortStatus1 & HC_RH_PORT_STATUS_PortSuspendStatusChange) {
				USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_PortSuspendStatusChange;			/* clear PSSC */
			}

			if (USB_REG(HostID)->RhPortStatus1 & HC_RH_PORT_STATUS_OverCurrentIndicatorChange) {	/* Over-current handler to avoid physical damage */
				USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_OverCurrentIndicatorChange;			/* clear OCIC */
			}

			if (USB_REG(HostID)->RhPortStatus1 & HC_RH_PORT_STATUS_PortResetStatusChange) {
				USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_PortResetStatusChange;			/* clear PRSC */
			}
		}
	}

	if (IntStatus & HC_INTERRUPT_WritebackDoneHead) {
		ProcessDoneQueue(HostID, Align16(ohci_data[HostID].hcca.HccaDoneHead) );
	}

#if SCHEDULING_OVRERRUN_INTERRUPT
	if (USB_REG(HostID)->HcInterruptStatus & HC_INTERRUPT_SchedulingOverrun) {
		OHciSchedulingOverrunIsr(HostID);
	}
#endif

#if SOF_INTERRUPT
	if (USB_REG(HostID)->HcInterruptStatus & HC_INTERRUPT_StartofFrame) {
		OHciStartofFrameIsr(HostID);
	}
#endif

#if RESUME_DETECT_INTERRUPT
	if (USB_REG(HostID)->HcInterruptStatus & HC_INTERRUPT_ResumeDetected) {
		OHciResumeDetectedIsr(HostID);
	}
#endif

#if UNRECOVERABLE_ERROR_INTERRUPT
	if (USB_REG(HostID)->HcInterruptStatus & HC_INTERRUPT_UnrecoverableError) {
		OHciUnrecoverableErrorIsr(HostID);
	}
#endif

#if FRAMENUMBER_OVERFLOW_INTERRUPT
	if (USB_REG(HostID)->HcInterruptStatus & HC_INTERRUPT_FrameNumberOverflow) {
		OHciFramenumberOverflowIsr(HostID);
	}
#endif

#if OWNERSHIP_CHANGE_INTERRUPT
	if (USB_REG(HostID)->HcInterruptStatus & HC_INTERRUPT_OwnershipChange) {
		OHciOwnershipChangeIsr(HostID);
	}
#endif
	USB_REG(HostID)->InterruptEnable = HC_INTERRUPT_MasterInterruptEnable;
	
}

static HCD_STATUS QueueOneGTD(uint32_t EdIdx,
							  uint8_t *const CurrentBufferPointer,
							  uint32_t xferLen,
							  uint8_t DirectionPID,
							  uint8_t DataToggle,
							  uint8_t IOC)
{
	PHCD_GeneralTransferDescriptor TailP;

	TailP = ( (PHCD_GeneralTransferDescriptor) HcdED(EdIdx)->hcED.TailP );
	TailP->hcGTD.DirectionPID = DirectionPID;
	TailP->hcGTD.DataToggle = DataToggle;
	TailP->hcGTD.CurrentBufferPointer = CurrentBufferPointer;
	TailP->hcGTD.BufferEnd = (xferLen) ? (CurrentBufferPointer + xferLen - 1) : NULL;
	TailP->TransferCount = xferLen;
	if (!IOC) {
		TailP->hcGTD.DelayInterrupt = TD_NoInterruptOnComplete;	/* Delay Interrupt with  */
	}

	/* Create a new place holder TD & link setup TD to the new place holder */
	ASSERT_STATUS_OK(AllocGtdForEd(EdIdx) );

	return HCD_STATUS_OK;
}

static HCD_STATUS QueueGTDs(uint32_t EdIdx, uint8_t *dataBuff, uint32_t xferLen, uint8_t Direction)
{
	while (xferLen > 0) {
		uint16_t TdLen;
		uint32_t MaxTDLen   = TD_MAX_XFER_LENGTH - Offset4k((uint32_t) dataBuff);

		TdLen = MIN(xferLen, MaxTDLen);
		xferLen -= TdLen;

		ASSERT_STATUS_OK(QueueOneGTD(EdIdx, dataBuff, TdLen, Direction, 0, (xferLen ? 0 : 1)) );
		dataBuff += TdLen;
	}
	return HCD_STATUS_OK;
}

static HCD_STATUS WaitForTransferComplete(uint8_t EdIdx)
{
#ifndef __TEST__
	while ( HcdED(EdIdx)->status == HCD_STATUS_TRANSFER_QUEUED ) {}
	return (HCD_STATUS) HcdED(EdIdx)->status;
#else
	return HCD_STATUS_OK;
#endif
}

static __INLINE HCD_STATUS InsertEndpoint(uint8_t HostID, uint32_t EdIdx, uint8_t ListIndex)
{
	PHC_ED list_head;
	list_head = &(ohci_data[HostID].staticEDs[ListIndex]);

	HcdED(EdIdx)->hcED.NextED = list_head->NextED;
	list_head->NextED = (uint32_t) HcdED(EdIdx);

	//  if ( IsInterruptEndpoint(EdIdx) )
	//  {
	//      OHCI_HOST_DATA->staticEDs[ListIndex].TailP += HcdED(EdIdx)->hcED.MaxPackageSize;	/* increase the bandwidth for the found list */
	//  }

	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS RemoveEndpoint(uint8_t HostID, uint32_t EdIdx)
{
	PHCD_EndpointDescriptor prevED;

	prevED = (PHCD_EndpointDescriptor) & (ohci_data[HostID].staticEDs[HcdED(EdIdx)->ListIndex]);
	while (prevED->hcED.NextED != (uint32_t) HcdED(EdIdx) ) {
		prevED = (PHCD_EndpointDescriptor) (prevED->hcED.NextED);
	}

	//  if ( IsInterruptEndpoint(EdIdx) )
	//  {
	//      OHCI_HOST_DATA->staticEDs[HcdED(EdIdx)->ListIndex].TailP -= HcdED(EdIdx)->hcED.MaxPackageSize;	/* decrease the bandwidth for the removed list */
	//  }
	prevED->hcED.NextED = HcdED(EdIdx)->hcED.NextED;

	return HCD_STATUS_OK;
}

#if 0	/* We dont need to manage bandwidth this hard */

__INLINE uint8_t FindInterruptTransferListIndex(uint8_t HostID, uint8_t Interval)
{
	uint8_t ListLeastBandwidth;
	uint8_t ListEnd;
	uint8_t ListIdx = INTERRUPT_32ms_LIST_HEAD;

	/* Find the correct interval list with right power of 2, i.e: 1,2,4,8,16,32 ms */
	while ( (ListIdx >= Interval) && (ListIdx >>= 1) ) {}
	ListEnd = ListIdx << 1;

	/* Find the least bandwidth in the same interval */
	/* Note: For Interrupt Static ED (0 to 62), TailP is used to store the accumulated bandwidth of the list */
	for (ListLeastBandwidth = ListIdx; ListIdx <= ListEnd; ListIdx++ )
		if ( ohci_data[HostID].staticEDs[ListIdx].TailP < ohci_data[HostID].staticEDs[ListLeastBandwidth].TailP ) {
			ListLeastBandwidth = ListIdx;
		}
	return ListLeastBandwidth;
}

static __INLINE void BuildPeriodicStaticEdTree(uint8_t HostID)
{
#if INTERRUPT_LIST_ENABLE
	/* Build full binary tree for interrupt list */
	uint32_t idx, count;
	uint32_t Balance[16] = {0x0, 0x8, 0x4, 0xC, 0x2, 0xA, 0x6, 0xE, 0x1, 0x9, 0x5, 0xD, 0x3, 0xB, 0x7, 0xF};

	/* build static tree for 1 -> 16 ms */
	OHCI_HOST_DATA->staticEDs[0].NextED = 0;
	for (idx = 1; idx < INTERRUPT_32ms_LIST_HEAD; idx++)
		OHCI_HOST_DATA->staticEDs[idx].NextED = (uint32_t) &(OHCI_HOST_DATA->staticEDs[(idx - 1) / 2]);
	/* create 32ms EDs which will be assigned to HccaInterruptTable */
	for (count = 0, idx = INTERRUPT_32ms_LIST_HEAD; count < 32; count++, idx++)
		OHCI_HOST_DATA->staticEDs[idx].NextED =
			(uint32_t) &(OHCI_HOST_DATA->staticEDs[Balance[count & 0xF] + INTERRUPT_16ms_LIST_HEAD]);
	/* Hook to HCCA interrupt Table */
	for (idx = 0; idx < 32; idx++)
		OHCI_HOST_DATA->hcca.HccaIntTable[idx] = (uint32_t) &(OHCI_HOST_DATA->staticEDs[idx + INTERRUPT_32ms_LIST_HEAD]);
	OHCI_HOST_DATA->staticEDs[INTERRUPT_1ms_LIST_HEAD].NextED = (uint32_t) &(OHCI_HOST_DATA->staticEDs[ISO_LIST_HEAD]);
#elif ISO_LIST_ENABLE
	for (idx = 0; idx < 32; idx++)
		OHCI_HOST_DATA->hcca.HccaIntTable[idx] = (uint32_t) &(OHCI_HOST_DATA->staticEDs[ISO_LIST_HEAD]);

#endif
}

#else

static __INLINE void BuildPeriodicStaticEdTree(uint8_t HostID)
{
	/* Treat all interrupt interval as 1ms (maximum rate) */
	uint32_t idx;
	for (idx = 0; idx < 32; idx++)
		ohci_data[HostID].hcca.HccaIntTable[idx] = (uint32_t) &(ohci_data[HostID].staticEDs[INTERRUPT_1ms_LIST_HEAD]);
	/* ISO_LIST_HEAD is an alias for INTERRUPT_1ms_LIST_HEAD */
}

#endif

static __INLINE uint32_t Align16(uint32_t Value)
{
	return Value & 0xFFFFFFF0UL;	/* Bit 31 .. 4 */
}

static __INLINE PHCD_EndpointDescriptor HcdED(uint8_t idx)
{
	return &(ohci_data[0 /*HostID*/].EDs[idx]);
}

static __INLINE PHCD_GeneralTransferDescriptor HcdGTD(uint8_t idx)
{
	return &(ohci_data[0 /*HostID*/].gTDs[idx]);
}

static __INLINE PHCD_IsoTransferDescriptor HcdITD(uint8_t idx)
{
#if ISO_LIST_ENABLE
	return &(ohci_data[0 /*HostID*/].iTDs[idx]);
#else
	return 0;
#endif
}

static __INLINE Bool IsIsoEndpoint(uint8_t EdIdx)
{
	return (HcdED(EdIdx)->hcED.Format ==0 ? FALSE : TRUE);
}

#if 0 	// just to clear warning
static __INLINE Bool IsInterruptEndpoint(uint8_t EdIdx)
{
	return (HcdED(EdIdx)->ListIndex < CONTROL_LIST_HEAD) && !IsIsoEndpoint(EdIdx);
}
#endif

static void PipehandleCreate(uint32_t *pPipeHandle, uint8_t HostID, uint8_t EdIdx)
{
	*pPipeHandle = ((uint32_t) (HostID << 8)) + EdIdx;
}

static HCD_STATUS PipehandleParse(uint32_t Pipehandle, uint8_t *HostID, uint8_t *EdIdx)
{
	*HostID = Pipehandle >> 8;
	*EdIdx = Pipehandle & 0xFF;
	if ((*HostID >= MAX_USB_CORE) || (*EdIdx >= MAX_ED) || (HcdED(*EdIdx)->inUse == 0)) {
		return HCD_STATUS_PIPEHANDLE_INVALID;
	}
	else {
		return HCD_STATUS_OK;
	}
}

static __INLINE HCD_STATUS AllocEd(uint8_t DeviceAddr,
								   HCD_USB_SPEED DeviceSpeed,
								   uint8_t EndpointNumber,
								   HCD_TRANSFER_TYPE TransferType,
								   HCD_TRANSFER_DIR TransferDir,
								   uint16_t MaxPacketSize,
								   uint8_t Interval,
								   uint32_t *pEdIdx)
{
	/* Looking for free EDs */
	for ((*pEdIdx) = 0; ((*pEdIdx) < MAX_ED) && HcdED((*pEdIdx))->inUse; (*pEdIdx)++) {}
	if ((*pEdIdx) >= MAX_ED) {
		return HCD_STATUS_NOT_ENOUGH_ENDPOINT;
	}

	/* Init Data for new ED */
	memset(HcdED(*pEdIdx), 0, sizeof(HCD_EndpointDescriptor) );

	HcdED((*pEdIdx))->inUse = 1;

	HcdED((*pEdIdx))->hcED.FunctionAddr = DeviceAddr;
	HcdED((*pEdIdx))->hcED.EndpointNumber = EndpointNumber;	/* Endpoint number only has 4 bits */
	HcdED((*pEdIdx))->hcED.Direction = (TransferType == CONTROL_TRANSFER) ? 0 : ((TransferDir == OUT_TRANSFER) ? 1 : 2 );
	HcdED((*pEdIdx))->hcED.Speed = (DeviceSpeed == FULL_SPEED) ? 0 : 1;
	HcdED((*pEdIdx))->hcED.Skip = 0;
	HcdED((*pEdIdx))->hcED.Format = (TransferType == ISOCHRONOUS_TRANSFER) ? 1 : 0;
	HcdED((*pEdIdx))->hcED.MaxPackageSize = MaxPacketSize;
	HcdED((*pEdIdx))->Interval = Interval;

	/* Allocate Place Holder TD as suggested by OHCI 5.2.8 */
	if (TransferType != ISOCHRONOUS_TRANSFER) {
		ASSERT_STATUS_OK(AllocGtdForEd(*pEdIdx) );
	}
	else {
		ASSERT_STATUS_OK(AllocItdForEd(*pEdIdx) );
	}

	return HCD_STATUS_OK;
}

static HCD_STATUS AllocGtdForEd(uint8_t EdIdx)
{
	uint32_t GtdIdx;

	/* Allocate new GTD */
	for (GtdIdx = 0; (GtdIdx < MAX_GTD) && HcdGTD(GtdIdx)->inUse; GtdIdx++) {}

	if (GtdIdx < MAX_GTD) {
		/***************    Control (word 0) ****************/
		/* Buffer rounding:    R = 1b (yes)                 */
		/* Direction/PID:      DP = 00b (SETUP)             */
		/* Delay Interrupt:    DI = 000b (interrupt)		*/
		/* Data Toggle:        DT = 00b (from ED)		    */
		/* Error Count:        EC = 00b                     */
		/* Condition Code:     CC = 1110b (not accessed)    */
		/****************************************************/
		memset(HcdGTD(GtdIdx), 0, sizeof(HCD_GeneralTransferDescriptor));

		HcdGTD(GtdIdx)->inUse = 1;
		HcdGTD(GtdIdx)->EdIdx = EdIdx;

		HcdGTD(GtdIdx)->hcGTD.BufferRounding = 1;
		HcdGTD(GtdIdx)->hcGTD.ConditionCode = (uint32_t) HCD_STATUS_TRANSFER_NotAccessed;

		/* link new GTD to the Endpoint */
		if (HcdED(EdIdx)->hcED.TailP) {	/* already have place holder */
			( (PHCD_GeneralTransferDescriptor) HcdED(EdIdx)->hcED.TailP )->hcGTD.NextTD = (uint32_t) HcdGTD(GtdIdx);
		}
		else {	/* have no dummy TD attached to the ED */
			HcdED(EdIdx)->hcED.HeadP.HeadTD = ((uint32_t) HcdGTD(GtdIdx));
		}
		HcdED(EdIdx)->hcED.TailP = (uint32_t) HcdGTD(GtdIdx);

		return HCD_STATUS_OK;
	}
	else {
		return HCD_STATUS_NOT_ENOUGH_GTD;
	}

}

static HCD_STATUS AllocItdForEd(uint8_t EdIdx)
{
	uint32_t ItdIdx;

	for (ItdIdx = 0; (ItdIdx < MAX_ITD) && HcdITD(ItdIdx)->inUse; ItdIdx++) {}

	if (ItdIdx < MAX_ITD) {
		memset(HcdITD(ItdIdx), 0, sizeof(HCD_IsoTransferDescriptor) );
		HcdITD(ItdIdx)->inUse = 1;
		HcdITD(ItdIdx)->EdIdx = EdIdx;

		HcdITD(ItdIdx)->ConditionCode = (uint32_t) HCD_STATUS_TRANSFER_NotAccessed;

		/* link new ITD to the Endpoint */
		if (HcdED(EdIdx)->hcED.TailP) {	/* already have place holder */
			( (PHCD_IsoTransferDescriptor) HcdED(EdIdx)->hcED.TailP )->NextTD = (uint32_t) HcdITD(ItdIdx);
		}
		else {	/* have no dummy TD attached to the ED */
			HcdED(EdIdx)->hcED.HeadP.HeadTD = ((uint32_t) HcdITD(ItdIdx));
		}
		HcdED(EdIdx)->hcED.TailP = (uint32_t) HcdITD(ItdIdx);

		return HCD_STATUS_OK;
	}
	else {
		return HCD_STATUS_NOT_ENOUGH_ITD;
	}
}

static __INLINE HCD_STATUS FreeED(uint8_t EdIdx)
{
	/* Remove Place holder TD */
	if ( IsIsoEndpoint(EdIdx) ) {
		FreeItd( (PHCD_IsoTransferDescriptor) HcdED(EdIdx)->hcED.TailP);
	}
	else {
		FreeGtd( (PHCD_GeneralTransferDescriptor) HcdED(EdIdx)->hcED.TailP);
	}

	HcdED(EdIdx)->status = HCD_STATUS_TRANSFER_NotAccessed;
	HcdED(EdIdx)->inUse = 0;

	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS FreeGtd(PHCD_GeneralTransferDescriptor pGtd)
{
	pGtd->inUse = 0;
	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS FreeItd(PHCD_IsoTransferDescriptor pItd)
{
	pItd->inUse = 0;
	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS OHciHostInit(uint8_t HostID)
{
	uint32_t idx,tem;

	if ( sizeof(OHCI_HOST_DATA_T) > 0x4000 ) {	/* Host data exceed 16 KB */
		ASSERT_STATUS_OK(HCD_STATUS_NOT_ENOUGH_MEMORY);
	}

	memset(&ohci_data[HostID], 0, sizeof(OHCI_HOST_DATA_T));
	/* Skip writing 1s to HcHCCA, assume it is 256 aligned */

	/* set skip bit for all static EDs */
	for (idx = 0; idx < MAX_STATIC_ED; idx++)
		ohci_data[HostID].staticEDs[idx].Skip = 1;

	/* Periodic List Initialization */
	BuildPeriodicStaticEdTree(HostID);

	/* Initialize OHCI registers */
	USB_REG(HostID)->Control = 0;
	OHciHostOperational(HostID);/* have to turn HC to operational mode before setting up below registers*/

	USB_REG(HostID)->FmInterval = HC_FMINTERVAL_DEFAULT;
	USB_REG(HostID)->PeriodicStart = PERIODIC_START;

	USB_REG(HostID)->ControlHeadED = (uint32_t) &(ohci_data[HostID].staticEDs[CONTROL_LIST_HEAD]);
	USB_REG(HostID)->BulkHeadED = (uint32_t) &(ohci_data[HostID].staticEDs[BULK_LIST_HEAD]);

	USB_REG(HostID)->HCCA = (uint32_t) &(ohci_data[HostID].hcca);	/* Hook Hcca */

	/* Set up HcControl */
	USB_REG(HostID)->Control |= CONTROL_BULK_SERVICE_RATIO |
								   (INTERRUPT_ROUTING ? HC_CONTROL_InterruptRouting : 0) |
								   (REMOTE_WAKEUP_CONNECTED ? HC_CONTROL_RemoteWakeupConnected : 0) |
								   (REMOTE_WAKEUP_ENABLE ? HC_CONTROL_RemoteWakeupEnable : 0) |
								   HC_CONTROL_ControlListEnable | HC_CONTROL_BulkListEnable |
								   (ISO_LIST_ENABLE ? (HC_CONTROL_PeriodListEnable | HC_CONTROL_IsochronousEnable) :
									(INTERRUPT_LIST_ENABLE ? HC_CONTROL_PeriodListEnable : 0));

	/* Set Global Power */
	USB_REG(HostID)->RhStatus = HC_RH_STATUS_LocalPowerStatusChange;

	// HcInterrupt Registers Init
        tem = USB_REG(HostID)->InterruptStatus;        // just to clear warning
	USB_REG(HostID)->InterruptStatus |= tem;	/* Clear Interrupt Status */
	USB_REG(HostID)->InterruptDisable = HC_INTERRUPT_ALL;/* Disable all interrupts */
	/* Enable necessary Interrupts */
	USB_REG(HostID)->InterruptEnable = HC_INTERRUPT_MasterInterruptEnable | HC_INTERRUPT_WritebackDoneHead |
										  HC_INTERRUPT_RootHubStatusChange |
										  (SCHEDULING_OVRERRUN_INTERRUPT ? HC_INTERRUPT_SchedulingOverrun : 0 ) |
										  (SOF_INTERRUPT ? HC_INTERRUPT_StartofFrame : 0) |
										  (RESUME_DETECT_INTERRUPT ? HC_INTERRUPT_ResumeDetected : 0) |
										  (UNRECOVERABLE_ERROR_INTERRUPT ? HC_INTERRUPT_UnrecoverableError : 0) |
										  (FRAMENUMBER_OVERFLOW_INTERRUPT ? HC_INTERRUPT_FrameNumberOverflow : 0) |
										  (OWNERSHIP_CHANGE_INTERRUPT ? HC_INTERRUPT_OwnershipChange : 0 );

	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS OHciHostReset(uint8_t HostID)
{
	USB_REG(HostID)->CommandStatus = HC_COMMAND_STATUS_HostControllerReset;
	while ( USB_REG(HostID)->CommandStatus & HC_COMMAND_STATUS_HostControllerReset) {}	/* FIXME Wait indefinitely (may need a time-out here) */

	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS OHciHostOperational(uint8_t HostID)
{
	USB_REG(HostID)->Control =
		(USB_REG(HostID)->Control & (~HC_CONTROL_HostControllerFunctionalState)) | (HC_HOST_OPERATIONAL << 6);
	return HCD_STATUS_OK;
}

#if 0		// just to clear warning
static __INLINE HCD_STATUS OHciHostSuspend(uint8_t HostID)
{
	USB_REG(HostID)->Control =
		(USB_REG(HostID)->Control & (~HC_CONTROL_HostControllerFunctionalState)) | (HC_HOST_SUSPEND << 6);
	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS OHciRhPortPowerOn(uint8_t HostID, uint8_t uPortNumber)
{
	USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_PortPowerStatus;	/* SetPortPower */
	HcdDelayMS(2 * ( (USB_REG(HostID)->RhDescriptorA & HC_RH_DESCRIPTORA_PowerOnToPowerGoodTime) >> 24 ) );	/* FIXME need to delay here POTPGT */

	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS OHciRhPortPowerOff(uint8_t HostID, uint8_t uPortNumber)
{
	USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_LowSpeedDeviceAttached;	/* ClearPortPower */
	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS OHciRhPortSuspend(uint8_t HostID, uint8_t uPortNumber)
{
	if ( USB_REG(HostID)->RhPortStatus1 & HC_RH_PORT_STATUS_CurrentConnectStatus) {	/* If device is connected */
		USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_PortSuspendStatus;/* SetPortSuspend */
	}
	HcdDelayMS(3);	/* FIXME 3ms for device to suspend */

	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS OHciRhPortResume(uint8_t HostID, uint8_t uPortNumber)
{
	if ( USB_REG(HostID)->RhPortStatus1 & HC_RH_PORT_STATUS_CurrentConnectStatus) {	/* If port is currently suspended */
		USB_REG(HostID)->RhPortStatus1 = HC_RH_PORT_STATUS_PortOverCurrentIndicator;	/* ClearSuspendStatus */
	}
	HcdDelayMS(20);	/* FIXME 20ms for device to resume */

	return HCD_STATUS_OK;
}
#endif

void HcdSetStreamPacketSize(uint32_t PipeHandle, uint16_t packetsize)
{
}

#endif
