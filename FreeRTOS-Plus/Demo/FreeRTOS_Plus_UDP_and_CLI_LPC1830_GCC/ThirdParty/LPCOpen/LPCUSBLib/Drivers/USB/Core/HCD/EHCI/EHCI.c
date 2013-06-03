/*
 * @brief Enhanced Host Controller Interface
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

#if (defined(USB_CAN_BE_HOST) && defined(__LPC_EHCI__))

#define __LPC_EHCI_C__
#include "../../../../../Common/Common.h"
#include "../../USBTask.h"
#include "../HCD.h"
#include "EHCI.h"

// === TODO: Unify USBRAM Section ===
PRAGMA_ALIGN_32
EHCI_HOST_DATA_T ehci_data[MAX_USB_CORE] __BSS(USBRAM_SECTION);
// EHCI_HOST_DATA_T ehci_data __BSS(USBRAM_SECTION);
PRAGMA_ALIGN_4096
NextLinkPointer PeriodFrameList0[FRAME_LIST_SIZE] ATTR_ALIGNED(4096) __BSS(USBRAM_SECTION);		/* Period Frame List */
PRAGMA_ALIGN_4096
NextLinkPointer PeriodFrameList1[FRAME_LIST_SIZE] ATTR_ALIGNED(4096) __BSS(USBRAM_SECTION);		/* Period Frame List */
Pipe_Stream_Handle_T PipeStreaming[MAX_USB_CORE];
/*=======================================================================*/
/* G L O B A L   F U N C T I O N S                                       */
/*=======================================================================*/
HCD_STATUS HcdInitDriver(uint8_t HostID)
{
	EHciHostReset(HostID);
	return EHciHostInit(HostID);
}

HCD_STATUS HcdDeInitDriver(uint8_t HostID)
{
	USB_REG(HostID)->USBSTS_H = 0xFFFFFFFF;				/* clear all current interrupts */
	USB_REG(HostID)->PORTSC1_H &= ~(1 << 12);			/* clear port power */
	USB_REG(HostID)->USBMODE_H =   (1 << 0);				/* set USB mode reserve */

	return HCD_STATUS_OK;
}

HCD_STATUS HcdRhPortEnable(uint8_t HostID)
{
	return HCD_STATUS_OK;
}

HCD_STATUS HcdRhPortDisable(uint8_t HostID)
{
	return HCD_STATUS_OK;
}

HCD_STATUS HcdRhPortReset(uint8_t HostID)
{
	HcdDelayMS(PORT_RESET_PERIOD_MS);

	USB_REG(HostID)->PORTSC1_H &= ~EHC_PORTSC_PortEnable;	/* Disable Port first */
	USB_REG(HostID)->PORTSC1_H |= EHC_PORTSC_PortReset;	/* Reset port */

	/* should have time-out */
	while (USB_REG(HostID)->PORTSC1_H & EHC_PORTSC_PortReset) {}

	/* PortEnable is always set - Deviation from EHCI */

	HcdDelayMS(PORT_RESET_PERIOD_MS);
	return HCD_STATUS_OK;
}

HCD_STATUS HcdClearEndpointHalt(uint32_t PipeHandle)// FIXME not implemented
{
	return HCD_STATUS_OK;
}

uint32_t   HcdGetFrameNumber(uint8_t HostID)
{
	return USB_REG(HostID)->FRINDEX_H;
}

HCD_STATUS HcdGetDeviceSpeed(uint8_t HostID, HCD_USB_SPEED *DeviceSpeed)
{
	if ( USB_REG(HostID)->PORTSC1_H & EHC_PORTSC_CurrentConnectStatus) {/* If device is connected */
		*DeviceSpeed = (HCD_USB_SPEED) ( (USB_REG(HostID)->PORTSC1_H & EHC_PORTSC_PortSpeed) >> 26 );	/* TODO magic number */
		return HCD_STATUS_OK;
	}
	else {
		return HCD_STATUS_DEVICE_DISCONNECTED;
	}
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
					   uint32_t *const pPipeHandle)
{
	uint32_t HeadIdx;

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
											   TransferDir, MaxPacketSize, Interval, Mult) );

	EndpointNumber &= 0xF;	/* Endpoint number is in range 0-15 */
	MaxPacketSize &= 0x3FF;	/* Max Packet Size is in range 0-1024 */

	switch (TransferType) {	// TODO should unify more, perharps later
	case CONTROL_TRANSFER:
	case BULK_TRANSFER:
		ASSERT_STATUS_OK(AllocQhd(HostID, DeviceAddr, DeviceSpeed, EndpointNumber, TransferType, TransferDir,
								  MaxPacketSize, Interval, Mult, HSHubDevAddr, HSHubPortNum, &HeadIdx) );
		DisableAsyncSchedule(HostID);
		InsertLinkPointer(&HcdAsyncHead(HostID)->Horizontal, &HcdQHD(HostID, HeadIdx)->Horizontal, QHD_TYPE);
		EnableAsyncSchedule(HostID);
		break;

	case INTERRUPT_TRANSFER:
		ASSERT_STATUS_OK(AllocQhd(HostID, DeviceAddr, DeviceSpeed, EndpointNumber, TransferType, TransferDir,
								  MaxPacketSize, Interval, Mult, HSHubDevAddr, HSHubPortNum, &HeadIdx) );
		DisablePeriodSchedule(HostID);
		InsertLinkPointer(&HcdIntHead(HostID)->Horizontal, &HcdQHD(HostID, HeadIdx)->Horizontal, QHD_TYPE);
		EnablePeriodSchedule(HostID);
		memset(&PipeStreaming[HostID], 0, sizeof(Pipe_Stream_Handle_T));
		break;

	case ISOCHRONOUS_TRANSFER:
#ifndef __TEST__
		if (( DeviceSpeed == HIGH_SPEED) || ( TransferDir == IN_TRANSFER) ) {	/* TODO currently not support HS due to lack of device for testing */
			ASSERT_STATUS_OK_MESSAGE(HCD_STATUS_TRANSFER_TYPE_NOT_SUPPORTED,
									 "Highspeed ISO and ISO IN is not supported yet, due to lack of testing");
		}
#endif
		ASSERT_STATUS_OK(AllocQhd(HostID, DeviceAddr, DeviceSpeed, EndpointNumber, TransferType, TransferDir,
								  MaxPacketSize, Interval, Mult, HSHubDevAddr, HSHubPortNum, &HeadIdx) );
		EnablePeriodSchedule(HostID);
		break;
	}

	PipehandleCreate(pPipeHandle, HostID, TransferType, HeadIdx);
	return HCD_STATUS_OK;
}

HCD_STATUS HcdClosePipe(uint32_t PipeHandle)
{
	uint8_t HostID, HeadIdx;
	HCD_TRANSFER_TYPE XferType;

	ASSERT_STATUS_OK(HcdCancelTransfer(PipeHandle) );
	ASSERT_STATUS_OK(PipehandleParse(PipeHandle, &HostID, &XferType, &HeadIdx) );

	switch (XferType) {
	case CONTROL_TRANSFER:
	case BULK_TRANSFER:
	case INTERRUPT_TRANSFER:
		RemoveQueueHead(HostID, HeadIdx);
		USB_REG(HostID)->USBCMD_H |= EHC_USBCMD_IntAsyncAdvanceDoorbell;	/* DoorBell Handshake: Queue Head will only be free in AsyncAdvanceIsr */
		break;

	case ISOCHRONOUS_TRANSFER:
		FreeQhd(HostID, HeadIdx);
		DisablePeriodSchedule(HostID);
		break;
	}
	return HCD_STATUS_OK;
}

HCD_STATUS HcdCancelTransfer(uint32_t PipeHandle)
{
	uint8_t HostID, HeadIdx;
	HCD_TRANSFER_TYPE XferType;

	ASSERT_STATUS_OK(PipehandleParse(PipeHandle, &HostID, &XferType, &HeadIdx) );

	DisableSchedule(HostID, (XferType == INTERRUPT_TRANSFER) || (XferType == ISOCHRONOUS_TRANSFER) ? 1 : 0);

	if (XferType == ISOCHRONOUS_TRANSFER) {	/* ISOCHRONOUS_TRANSFER */
		uint32_t i;
		for (i = 0; i < FRAME_LIST_SIZE; i++) {	/*-- Foreach link in Period List Base --*/
			NextLinkPointer *pNextPointer = &EHCI_FRAME_LIST(HostID)[i];

			/*-- Foreach Itd/SItd in the link--*/
			while ( isValidLink(pNextPointer->Link) && pNextPointer->Type != QHD_TYPE) {
				if (pNextPointer->Type == ITD_TYPE) {	/*-- Highspeed ISO --*/
					PHCD_HS_ITD pItd = (PHCD_HS_ITD) Align32(pNextPointer->Link);

					if (HeadIdx == pItd->IhdIdx) {
						/*-- remove matched ITD --*/
						pNextPointer->Link = pItd->Horizontal.Link;
						FreeHsItd(pItd);
						continue;	/*-- skip advance pNextPointer due to TD removal --*/
					}
				}
				else if (pNextPointer->Type == SITD_TYPE) {	/*-- Split ISO --*/
					PHCD_SITD pSItd = (PHCD_SITD) Align32(pNextPointer->Link);

					if (HeadIdx == pSItd->IhdIdx) {
						/*-- removed matched SITD --*/
						pNextPointer->Link = pSItd->Horizontal.Link;
						FreeSItd(pSItd);
						continue;	/*-- skip advance pNextPointer due to TD removal --*/
					}
				}
				pNextPointer = (NextLinkPointer *) Align32(pNextPointer->Link);
			}
		}
	}
	else {	/*-- Bulk / Control / Interrupt --*/
		uint32_t TdLink = HcdQHD(HostID, HeadIdx)->FirstQtd;

		/*-- Foreach Qtd in Qhd --*/ /*---------- Deactivate all queued TDs ----------*/
		while ( isValidLink(TdLink) ) {
			PHCD_QTD pQtd = (PHCD_QTD) Align32(TdLink);
			TdLink = pQtd->NextQtd;

			pQtd->Active = 0;
			pQtd->IntOnComplete = 0;/* no interrupt scenario on this TD */
			FreeQtd(pQtd);
		}
		HcdQHD(HostID, HeadIdx)->FirstQtd = LINK_TERMINATE;
	}

	EnableSchedule(HostID, (XferType == INTERRUPT_TRANSFER) || (XferType == ISOCHRONOUS_TRANSFER) ? 1 : 0);
	return HCD_STATUS_OK;
}

HCD_STATUS HcdControlTransfer(uint32_t PipeHandle,
							  const USB_Request_Header_t *const pDeviceRequest,
							  uint8_t *const buffer)
{
	uint8_t HostID, QhdIdx;
	HCD_TRANSFER_TYPE XferType;
	uint32_t SetupTdIdx, DataTdIdx, StatusTdIdx;
	uint8_t direction;
	uint32_t Datalength;

	if ((pDeviceRequest == NULL) || (buffer == NULL)) {
		ASSERT_STATUS_OK_MESSAGE(HCD_STATUS_PARAMETER_INVALID, "Device Request or Data Buffer is NULL");
	}

	ASSERT_STATUS_OK(PipehandleParse(PipeHandle, &HostID, &XferType, &QhdIdx) );

	Datalength = pDeviceRequest->wLength;
	direction =  pDeviceRequest->bmRequestType & 0x80;

	/*---------- Setup Stage ----------*/
	ASSERT_STATUS_OK(AllocQTD(HostID, &SetupTdIdx, (uint8_t *) pDeviceRequest, 8, SETUP_TRANSFER, 0, 0) );			/* Setup TD: DirectionPID=00 - DataToggle=10b (always DATA0) */

	/*---------- Data Stage ----------*/
	if (Datalength) {
		ASSERT_STATUS_OK(AllocQTD(HostID, &DataTdIdx, buffer, Datalength, direction ? IN_TRANSFER : OUT_TRANSFER, 1, 0) );
	}
	else {
		DataTdIdx = SetupTdIdx;	/* Data TD is skipped */
	}

	/*---------- Status Stage ----------*/
	ASSERT_STATUS_OK(AllocQTD(HostID, &StatusTdIdx, NULL, 0, direction ? OUT_TRANSFER : IN_TRANSFER, 1, 1) );	/* Status TD: Direction=opposite of data direction - DataToggle=11b (always DATA1) */

	/* Hook TDs Together */
	HcdQTD(HostID, SetupTdIdx)->NextQtd = (uint32_t) HcdQTD(HostID, DataTdIdx);
	HcdQTD(HostID, DataTdIdx)->NextQtd = (uint32_t) HcdQTD(HostID, StatusTdIdx);

	HcdQHD(HostID, QhdIdx)->status = (uint32_t) HCD_STATUS_TRANSFER_QUEUED;

	/* Hook TDs to QHD */
	HcdQHD(HostID, QhdIdx)->FirstQtd = Align32( (uint32_t) HcdQTD(HostID, SetupTdIdx) );
	HcdQHD(HostID, QhdIdx)->Overlay.NextQtd = (uint32_t) HcdQTD(HostID, SetupTdIdx);

	/* wait for semaphore compete TDs */
	ASSERT_STATUS_OK(WaitForTransferComplete(HostID, QhdIdx) );

	return HCD_STATUS_OK;
}

HCD_STATUS HcdDataTransfer(uint32_t PipeHandle,
						   uint8_t *const buffer,
						   uint32_t const length,
						   uint16_t *const pActualTransferred)
{
	uint8_t HostID, HeadIdx;
	HCD_TRANSFER_TYPE XferType;
	uint32_t DataTdIdx;
	uint32_t ExpectedLength;

	if ((buffer == NULL) || (length == 0)) {
		ASSERT_STATUS_OK_MESSAGE(HCD_STATUS_PARAMETER_INVALID, "Data Buffer is NULL or Transfer Length is 0");
	}

	ASSERT_STATUS_OK(PipehandleParse(PipeHandle, &HostID, &XferType, &HeadIdx) );

	ExpectedLength = (length != HCD_ENDPOINT_MAXPACKET_XFER_LEN) ? length : HcdQHD(HostID, HeadIdx)->MaxPackageSize;

	HcdQHD(HostID, HeadIdx)->status = (uint32_t) HCD_STATUS_TRANSFER_QUEUED;

	if (XferType == ISOCHRONOUS_TRANSFER) {
		if ( HcdQHD(HostID, HeadIdx)->EndpointSpeed == HIGH_SPEED ) {	/*-- Highspeed ISO --*/
			ASSERT_STATUS_OK(QueueITDs(HostID, HeadIdx, buffer, ExpectedLength) );
		}
		else {	/*-- Full/Low Speed ISO --*/
			ASSERT_STATUS_OK(QueueSITDs(HostID, HeadIdx, buffer, ExpectedLength) );
		}
	}
	else {	/*-- Control / Bulk / Interrupt --*/
		if(XferType == BULK_TRANSFER)
		{
			ASSERT_STATUS_OK( QueueQTDs(HostID, &DataTdIdx, buffer, ExpectedLength,
									HcdQHD(HostID,HeadIdx)->Direction ? IN_TRANSFER : OUT_TRANSFER, 0) );
		}
		else
		{
			ASSERT_STATUS_OK(AllocQTD(HostID, &DataTdIdx, buffer, ExpectedLength,
								  HcdQHD(HostID, HeadIdx)->Direction ? IN_TRANSFER : OUT_TRANSFER, 0, 1) );
		}
		/*---------- Hook to Queue Head ----------*/
		HcdQHD(HostID, HeadIdx)->FirstQtd = Align32( (uint32_t) HcdQTD(HostID, DataTdIdx) );	/* used as TD head to clean up TD chain when transfer done */
		HcdQHD(HostID, HeadIdx)->Overlay.NextQtd = (uint32_t) HcdQTD(HostID, DataTdIdx);
	}

	HcdQHD(HostID, HeadIdx)->pActualTransferCount = pActualTransferred;	/* TODO Actual Length get rid of this */
	if (HcdQHD(HostID, HeadIdx)->pActualTransferCount) {
		*(HcdQHD(HostID, HeadIdx)->pActualTransferCount) = ExpectedLength;
	}

	return HCD_STATUS_OK;
}

HCD_STATUS HcdGetPipeStatus(uint32_t PipeHandle)/* TODO can be implemented based on overlay */
{
	uint8_t HostID, HeadIdx;
	HCD_TRANSFER_TYPE XferType;

	ASSERT_STATUS_OK(PipehandleParse(PipeHandle, &HostID, &XferType, &HeadIdx) );

	return (HCD_STATUS)HcdQHD(HostID, HeadIdx)->status;
}

static void FreeQhd(uint8_t HostID, uint8_t QhdIdx)
{
	HcdQHD(HostID, QhdIdx)->status = HCD_STATUS_STRUCTURE_IS_FREE;
	HcdQHD(HostID, QhdIdx)->Horizontal.Link |= LINK_TERMINATE;
	HcdQHD(HostID, QhdIdx)->inUse = 0;
}

static HCD_STATUS AllocQhd(uint8_t HostID,
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
						   uint32_t *pQhdIdx)
{
	/* Looking for a free QHD */
	for ( (*pQhdIdx) = 0; (*pQhdIdx) < HCD_MAX_QTD && HcdQHD(HostID, *pQhdIdx)->inUse; (*pQhdIdx)++) {}

	if ((*pQhdIdx) == HCD_MAX_QTD ) {
		return HCD_STATUS_NOT_ENOUGH_ENDPOINT;
	}

	memset(HcdQHD(HostID, *pQhdIdx), 0, sizeof(HCD_QHD) );

	/* Init Data For Queue Head */
	HcdQHD(HostID, *pQhdIdx)->inUse = 1;
	HcdQHD(HostID, *pQhdIdx)->Direction = (TransferDir == IN_TRANSFER) ? 1 : 0;		/* Control Endpoint should not use this parameter */
	HcdQHD(HostID, *pQhdIdx)->Interval = Interval;
	HcdQHD(HostID, *pQhdIdx)->status = HCD_STATUS_OK;
	HcdQHD(HostID, *pQhdIdx)->FirstQtd = LINK_TERMINATE;

	HcdQHD(HostID, *pQhdIdx)->Horizontal.Link = LINK_TERMINATE;
	HcdQHD(HostID, *pQhdIdx)->DeviceAddress = DeviceAddr;

	HcdQHD(HostID, *pQhdIdx)->InActiveOnNextTransaction = 0;
	HcdQHD(HostID, *pQhdIdx)->EndpointNumber = EndpointNumber;
	HcdQHD(HostID, *pQhdIdx)->EndpointSpeed = (uint32_t) DeviceSpeed;
	HcdQHD(HostID, *pQhdIdx)->DataToggleControl = (TransferType == CONTROL_TRANSFER) ? 1 : 0;
	HcdQHD(HostID, *pQhdIdx)->HeadReclamationFlag = 0;
	HcdQHD(HostID, *pQhdIdx)->MaxPackageSize = MaxPacketSize;
	HcdQHD(HostID,
		   *pQhdIdx)->ControlEndpointFlag = (DeviceSpeed != HIGH_SPEED && TransferType == CONTROL_TRANSFER) ? 1 : 0;
	HcdQHD(HostID, *pQhdIdx)->NakCountReload = 0;	/* infinite NAK/NYET */

	/*-- Currently All interrupt endpoints will be served as 1 (micro)frame polling, thus Interval parameter is ignored --*/
	/*-- For High Speed Interval should be used to compute the uFrameSMask --*/
	HcdQHD(HostID,
		   *pQhdIdx)->uFrameSMask =
		(TransferType == INTERRUPT_TRANSFER) ? (DeviceSpeed == HIGH_SPEED ? 0xFF : 0x01) : 0;
	HcdQHD(HostID,
		   *pQhdIdx)->uFrameCMask = (DeviceSpeed != HIGH_SPEED && TransferType == INTERRUPT_TRANSFER) ? 0x1C : 0;			/*-- Schedule Complete Split at uFrame2, uFrame3 and uFrame4 --*/
	HcdQHD(HostID, *pQhdIdx)->HubAddress = HSHubDevAddr;
	HcdQHD(HostID, *pQhdIdx)->PortNumber = HSHubPortNum;
	HcdQHD(HostID, *pQhdIdx)->Mult = (DeviceSpeed == HIGH_SPEED ? Mult : 1);

	HcdQHD(HostID, *pQhdIdx)->Overlay.NextQtd = LINK_TERMINATE;
	HcdQHD(HostID, *pQhdIdx)->Overlay.AlterNextQtd = LINK_TERMINATE;
	HcdQHD(HostID, *pQhdIdx)->FirstQtd = LINK_TERMINATE;

	HcdQHD(HostID,
		   *pQhdIdx)->Overlay.PingState_Err =
		(DeviceSpeed == HIGH_SPEED && TransferType != INTERRUPT_TRANSFER && TransferDir == OUT_TRANSFER) ? 1 : 0;

	return HCD_STATUS_OK;
}

static HCD_STATUS InsertLinkPointer(NextLinkPointer *pList, NextLinkPointer *pNew, uint8_t type)
{
	pNew->Link = pList->Link;
	pList->Link = Align32( (uint32_t) pNew);
	pList->Type = type;
	return HCD_STATUS_OK;
}

static HCD_STATUS RemoveQueueHead(uint8_t HostID, uint8_t QhdIdx)
{
	PHCD_QHD pQhd = IsInterruptQhd(HostID, QhdIdx) ? HcdIntHead(HostID) : HcdAsyncHead(HostID);
	/*-- Foreach Qhd in async list --*/
	while ( isValidLink(pQhd->Horizontal.Link) &&
			Align32(pQhd->Horizontal.Link) != (uint32_t) HcdQHD(HostID, QhdIdx) &&
			Align32(pQhd->Horizontal.Link) != (uint32_t) HcdAsyncHead(HostID) ) {
		pQhd = (PHCD_QHD) Align32(pQhd->Horizontal.Link);
	}
	if (  Align32(pQhd->Horizontal.Link) != (uint32_t) HcdQHD(HostID, QhdIdx) ) {
		return HCD_STATUS_PARAMETER_INVALID;
	}

	HcdQHD(HostID, QhdIdx)->status = (uint32_t) HCD_STATUS_TO_BE_REMOVED;	/* Will be remove in AsyncAdvanceIsr - make use of IAAD */
	pQhd->Horizontal.Link = HcdQHD(HostID, QhdIdx)->Horizontal.Link;

	return HCD_STATUS_OK;
}

/*---------- Queue TD Routines ----------*/
static void FreeQtd(PHCD_QTD pQtd)
{
	pQtd->NextQtd |= LINK_TERMINATE;
	pQtd->inUse = 0;
}

/** Direction, DataToggle parameter only has meaning for control transfer, for other transfer use 0 for these paras */
static HCD_STATUS AllocQTD(uint8_t HostID,
						   uint32_t *pTdIdx,
						   uint8_t *const BufferPointer,
						   uint32_t xferLen,
						   HCD_TRANSFER_DIR PIDCode,
						   uint8_t DataToggle,
						   uint8_t IOC)
{
	for ((*pTdIdx) = 0; (*pTdIdx) < HCD_MAX_QTD && HcdQTD(HostID, *pTdIdx)->inUse; (*pTdIdx)++) {}

	if ((*pTdIdx) < HCD_MAX_QTD) {
		uint8_t idx = 1;
		uint32_t BytesInPage;

		memset(HcdQTD(HostID, *pTdIdx), 0, sizeof(HCD_QTD));

		HcdQTD(HostID, *pTdIdx)->NextQtd = 1;

		HcdQTD(HostID, *pTdIdx)->AlterNextQtd = LINK_TERMINATE;
		HcdQTD(HostID, *pTdIdx)->inUse = 1;

		HcdQTD(HostID, *pTdIdx)->Active = 1;
		HcdQTD(HostID, *pTdIdx)->PIDCode = (PIDCode == SETUP_TRANSFER) ? 2 : (PIDCode == IN_TRANSFER ? 1 : 0);
		HcdQTD(HostID, *pTdIdx)->TotalBytesToTransfer = xferLen;
		HcdQTD(HostID, *pTdIdx)->DataToggle = DataToggle;
		HcdQTD(HostID, *pTdIdx)->IntOnComplete = IOC;

		HcdQTD(HostID, *pTdIdx)->BufferPointer[0] = (uint32_t) BufferPointer;
		BytesInPage = 0x1000 - Offset4k((uint32_t) BufferPointer);
		xferLen -= MIN(xferLen, BytesInPage);	/*-- Trim down xferlen to be multiple of 4k --*/

		for (idx = 1; idx <= 4 && xferLen > 0; idx++) {
			HcdQTD(HostID,
				   *pTdIdx)->BufferPointer[idx] = Align4k(HcdQTD(HostID, (*pTdIdx))->BufferPointer[idx - 1]) + 0x1000;
			xferLen -= MIN(xferLen, 0x1000);
		}
		return HCD_STATUS_OK;
	}
	else {
		return HCD_STATUS_NOT_ENOUGH_QTD;
	}
}

static HCD_STATUS QueueQTDs (uint8_t HostID,
							 uint32_t* pTdIdx,
							 uint8_t* dataBuff,
							 uint32_t xferLen,
							 HCD_TRANSFER_DIR PIDCode,
							 uint8_t DataToggle)
{
	uint32_t TailTdIdx=0xFFFFFFFF;

	while (xferLen > 0)
	{
		uint32_t TdLen;
		uint32_t MaxTDLen = QTD_MAX_XFER_LENGTH - Offset4k((uint32_t)dataBuff);

		if(PipeStreaming[HostID].PacketSize > 0)
			TdLen = MIN(xferLen, PipeStreaming[HostID].PacketSize);
		else
			TdLen = MIN(xferLen, MaxTDLen);
		xferLen -= TdLen;

		if (TailTdIdx == 0xFFFFFFFF)
		{
			ASSERT_STATUS_OK ( AllocQTD(HostID, pTdIdx, dataBuff, TdLen, PIDCode, DataToggle, (xferLen==0) ? 1 : 0) );
			TailTdIdx = *pTdIdx;
		}
		else
		{
			uint32_t NewTdIDx;
			if(HCD_STATUS_OK == AllocQTD(HostID, &NewTdIDx, dataBuff, TdLen, PIDCode, DataToggle, (xferLen==0) ? 1 : 0))
			{
				HcdQTD(HostID,TailTdIdx)->NextQtd = Align32((uint32_t) HcdQTD(HostID,NewTdIDx));
				TailTdIdx = NewTdIDx;
			}
			else
			{
				PipeStreaming[HostID].BufferAddress = (uint32_t)dataBuff;
				PipeStreaming[HostID].RemainBytes = xferLen + TdLen;
				PipeStreaming[HostID].DataToggle = DataToggle;
				HcdQTD(HostID,HCD_MAX_QTD - 1)->IntOnComplete = 1;
				break;
			}
		}
		if(DataToggle == 1) DataToggle = 0;
		else DataToggle = 1;
		dataBuff += TdLen;
	}
	if(xferLen == 0)
	{
		memset(&PipeStreaming[HostID], 0, sizeof(Pipe_Stream_Handle_T));
	}
	return HCD_STATUS_OK;
}

static void FreeHsItd(PHCD_HS_ITD pItd)
{
	pItd->Horizontal.Link |= LINK_TERMINATE;
	pItd->inUse = 0;
}

HCD_STATUS AllocHsItd(uint8_t HostID,
					  uint32_t *pTdIdx,
					  uint8_t IhdIdx,
					  uint8_t *dataBuff,
					  uint32_t TDLen,
					  uint8_t XactPerITD,
					  uint8_t IntOnComplete)
{
	for ((*pTdIdx) = 0; (*pTdIdx) < HCD_MAX_HS_ITD && HcdHsITD(HostID, *pTdIdx)->inUse; (*pTdIdx)++) {}
	if ((*pTdIdx) < HCD_MAX_HS_ITD) {
		uint8_t i;
		uint8_t XactStep = 8 / XactPerITD;
		uint32_t MaxXactLen = HcdQHD(HostID, IhdIdx)->MaxPackageSize * HcdQHD(HostID, IhdIdx)->Mult;

		memset(HcdHsITD(HostID, *pTdIdx), 0, sizeof(HCD_HS_ITD));

		HcdHsITD(HostID, *pTdIdx)->inUse = 1;
		HcdHsITD(HostID, *pTdIdx)->IhdIdx = IhdIdx;

		HcdHsITD(HostID, *pTdIdx)->Horizontal.Link = LINK_TERMINATE;
		for (i = 0; TDLen > 0 && i < 8; i += XactStep) {
			uint32_t XactLen = MIN(TDLen, MaxXactLen);
			TDLen -= XactLen;

			HcdHsITD(HostID, *pTdIdx)->BufferPointer[i] = Align4k( (uint32_t) dataBuff);

			HcdHsITD(HostID, *pTdIdx)->Transaction[i].Offset = ( (uint32_t) dataBuff ) & 4095;
			HcdHsITD(HostID, *pTdIdx)->Transaction[i].PageSelect = i;
			HcdHsITD(HostID, *pTdIdx)->Transaction[i].IntOnComplete = (IntOnComplete && TDLen == 0) ? 1 : 0;
			HcdHsITD(HostID, *pTdIdx)->Transaction[i].Length = XactLen;
			HcdHsITD(HostID, *pTdIdx)->Transaction[i].Active = 1;

			dataBuff += XactLen;
		}

		HcdHsITD(HostID, *pTdIdx)->BufferPointer[0] |= (HcdQHD(HostID, IhdIdx)->EndpointNumber << 8) | HcdQHD(HostID,
																											  IhdIdx)->
													   DeviceAddress;
		HcdHsITD(HostID,
				 *pTdIdx)->BufferPointer[1] |=
			(HcdQHD(HostID, IhdIdx)->Direction << 1) | HcdQHD(HostID, IhdIdx)->MaxPackageSize;
		HcdHsITD(HostID, *pTdIdx)->BufferPointer[2] |= HcdQHD(HostID, IhdIdx)->Mult;

		return HCD_STATUS_OK;
	}
	else {
		return HCD_STATUS_NOT_ENOUGH_HS_ITD;
	}
}

static HCD_STATUS QueueITDs(uint8_t HostID, uint8_t IhdIdx, uint8_t *dataBuff, uint32_t xferLen)
{
	uint32_t MaxTDLen;
	uint32_t FrameIdx;

#if 0	/* Maximum bandwidth (Interval = 1) regardless of Interval value */
	uint8_t XactPerITD;
	uint32_t FramePeriod;
	if (HcdQHD(IhdIdx)->Interval < 4) {	/*-- Period < 8 --*/
		XactPerITD = 1 << ( 4 - HcdQHD(IhdIdx)->Interval );		/*-- Interval 1 => 8, 2 => 4, 3 => 2 --*/
		FramePeriod = 1;
	}
	else {
		XactPerITD = 1;
		FramePeriod = 1 << ( HcdQHD(IhdIdx)->Interval - 4 );	/*-- Frame step 4 => 1, 5 => 2, 6 => 3 --*/
	}
#else
	#define XactPerITD      8
	#define FramePeriod     1
#endif

	MaxTDLen = XactPerITD * HcdQHD(HostID, IhdIdx)->MaxPackageSize * HcdQHD(HostID, IhdIdx)->Mult;
	FrameIdx = USB_REG(HostID)->FRINDEX_H >> 3;

	if (xferLen > MaxTDLen * FRAME_LIST_SIZE) {	/*-- Data length overflow the Period FRAME LIST  --*/
		ASSERT_STATUS_OK_MESSAGE(
			HCD_STATUS_DATA_OVERFLOW,
			"ISO data length overflows the Period Frame List size, Please increase size by FRAMELIST_SIZE_BITS or reduce data length");
	}

	while (xferLen > 0) {
		uint32_t TdIdx;
		uint32_t TDLen;

		TDLen = MIN(xferLen, MaxTDLen);
		xferLen -= TDLen;

		ASSERT_STATUS_OK(AllocHsItd(HostID, &TdIdx, IhdIdx, dataBuff, TDLen, XactPerITD, xferLen ? 0 : 1) );

		FrameIdx = (FrameIdx + FramePeriod) % FRAME_LIST_SIZE;
		/*-- Hook ITD to Period List Base --*/
		InsertLinkPointer(&EHCI_FRAME_LIST(HostID)[FrameIdx], &HcdHsITD(HostID, TdIdx)->Horizontal, ITD_TYPE);
		dataBuff += TDLen;
	}

	return HCD_STATUS_OK;
}

static void FreeSItd(PHCD_SITD pSItd)
{
	pSItd->Horizontal.Link |= LINK_TERMINATE;
	pSItd->inUse = 0;
}

static HCD_STATUS AllocSItd(uint8_t HostID,
							uint32_t *pTdIdx,
							uint8_t HeadIdx,
							uint8_t *dataBuff,
							uint32_t TDLen,
							uint8_t IntOnComplete)
{
#define TCount_Pos 0
#define TPos_Pos 3

	for ((*pTdIdx) = 0; (*pTdIdx) < HCD_MAX_SITD && HcdSITD(HostID, *pTdIdx)->inUse; (*pTdIdx)++) {}

	if ((*pTdIdx) < HCD_MAX_SITD) {
		uint8_t TCount = TDLen / SPLIT_MAX_LEN_UFRAME + (TDLen % SPLIT_MAX_LEN_UFRAME ? 1 : 0);	/*-- Number of Split Transactions --*/

		memset(HcdSITD(HostID, *pTdIdx), 0, sizeof(HCD_SITD) );

		HcdSITD(HostID, *pTdIdx)->inUse = 1;
		HcdSITD(HostID, *pTdIdx)->IhdIdx = HeadIdx;

		/*-- Word 1 --*/
		HcdSITD(HostID, *pTdIdx)->Horizontal.Link = LINK_TERMINATE;
		/*-- Word 2 --*/
		HcdSITD(HostID, *pTdIdx)->DeviceAddress = HcdQHD(HostID, HeadIdx)->DeviceAddress;
		HcdSITD(HostID, *pTdIdx)->EndpointNumber = HcdQHD(HostID, HeadIdx)->EndpointNumber;
		HcdSITD(HostID, *pTdIdx)->HubAddress = HcdQHD(HostID, HeadIdx)->HubAddress;
		HcdSITD(HostID, *pTdIdx)->PortNumber = HcdQHD(HostID, HeadIdx)->PortNumber;
		HcdSITD(HostID, *pTdIdx)->Direction = HcdQHD(HostID, HeadIdx)->Direction;
		/*-- Word 3 --*/
		HcdSITD(HostID, *pTdIdx)->uFrameSMask = (1 << TCount) - 1;
		HcdSITD(HostID, *pTdIdx)->uFrameCMask = 0;
		/*-- Word 4 --*/
		HcdSITD(HostID, *pTdIdx)->Active = 1;
		HcdSITD(HostID, *pTdIdx)->TotalBytesToTransfer = TDLen;
		HcdSITD(HostID, *pTdIdx)->IntOnComplete = IntOnComplete;
		/*-- Word 5 --*/
		HcdSITD(HostID, *pTdIdx)->BufferPointer[0] = (uint32_t) dataBuff;
		/*-- Word 6 --*/
		HcdSITD(HostID, *pTdIdx)->BufferPointer[1] = Align4k( ((uint32_t) dataBuff) + TDLen);

		HcdSITD(HostID, *pTdIdx)->BufferPointer[1] |= TCount << TCount_Pos;
		HcdSITD(HostID, *pTdIdx)->BufferPointer[1] |= (TCount > 1 ? 1 : 0 ) << TPos_Pos;/*-- TPosition - More than 1 split --> Begin Encoding, Otherwise All Encoding  --*/

		// HcdSITD(*pTdIdx)->TCount = NoSplits;
		// HcdSITD(*pTdIdx)->TPosition = (NoSplits > 1) ? 1 : 0 ; /*-- TPosition - More than 1 split --> Begin Encoding, Otherwise All Encoding  --*/

		/*-- Word 7 --*/
		HcdSITD(HostID, *pTdIdx)->BackPointer = LINK_TERMINATE;

		return HCD_STATUS_OK;
	}
	else {
		return HCD_STATUS_NOT_ENOUGH_SITD;
	}
}

static HCD_STATUS QueueSITDs(uint8_t HostID, uint8_t HeadIdx, uint8_t *dataBuff, uint32_t xferLen)
{
	uint32_t FrameIdx;

#if 0	/* Maximum bandwidth (Interval = 1) regardless of Interval value */
	uint8_t XactPerITD;
	uint32_t FramePeriod;
	if (HcdQHD(IhdIdx)->Interval < 4) {	/*-- Period < 8 --*/
		FramePeriod = 1;
	}
	else {
		FramePeriod = 1 << ( HcdQHD(IhdIdx)->Interval - 4 );	/*-- Frame step 4 => 1, 5 => 2, 6 => 3 --*/
	}
#else
	#define FramePeriod     1
#endif

	if (xferLen > HcdQHD(HostID, HeadIdx)->MaxPackageSize * FRAME_LIST_SIZE) {	/*-- Data length overflow the Period FRAME LIST  --*/
		ASSERT_STATUS_OK_MESSAGE(
			HCD_STATUS_DATA_OVERFLOW,
			"ISO data length overflows the Period Frame List size, Please increase size by FRAMELIST_SIZE_BITS or reduce data length");
	}

	FrameIdx = USB_REG(HostID)->FRINDEX_H >> 3;
	while (xferLen) {
		uint32_t TdIdx;
		uint32_t TDLen;

		TDLen = MIN(xferLen, HcdQHD(HostID, HeadIdx)->MaxPackageSize);
		xferLen -= TDLen;

		ASSERT_STATUS_OK(AllocSItd(HostID, &TdIdx, HeadIdx, dataBuff, TDLen, xferLen ? 0 : 1) );

		FrameIdx = (FrameIdx + FramePeriod) % FRAME_LIST_SIZE;
		/*-- Hook SITD to Period List Base --*/
		InsertLinkPointer(&EHCI_FRAME_LIST(HostID)[FrameIdx], &HcdSITD(HostID, TdIdx)->Horizontal, SITD_TYPE);
		dataBuff += TDLen;
	}
	return HCD_STATUS_OK;
}

static HCD_STATUS WaitForTransferComplete(uint8_t HostID, uint8_t EdIdx)/* TODO indentical to OHCI now */
{

#ifndef __TEST__
	while ( HcdQHD(HostID, EdIdx)->status == HCD_STATUS_TRANSFER_QUEUED ) {
		/* Should have time-out but left blank intentionally for bug catcher */
	}
	return (HCD_STATUS) HcdQHD(HostID, EdIdx)->status;
#else
	return HCD_STATUS_OK;
#endif

}

static HCD_STATUS PipehandleParse(uint32_t Pipehandle, uint8_t *pHostID, HCD_TRANSFER_TYPE *XferType, uint8_t *pIdx)
{
	Pipe_Handle_T *pHandle = (Pipe_Handle_T *) (&Pipehandle);

	if  ((pHandle->HostId >= MAX_USB_CORE) ||
		 ( pHandle->Idx >= HCD_MAX_QTD) ||
		 ( HcdQHD(pHandle->HostId, pHandle->Idx)->inUse == 0) ||
		 ( HcdQHD(pHandle->HostId, pHandle->Idx)->status == HCD_STATUS_TO_BE_REMOVED) ) {
		return HCD_STATUS_PIPEHANDLE_INVALID;
	}

	if (pHostID) {
		*pHostID = pHandle->HostId;
	}
	if (pIdx) {
		*pIdx = pHandle->Idx;
	}
	if (XferType) {
		*XferType = (HCD_TRANSFER_TYPE) pHandle->Type;
	}

	return HCD_STATUS_OK;
}

static void PipehandleCreate(uint32_t *pPipeHandle, uint8_t HostID, HCD_TRANSFER_TYPE XferType, uint8_t idx)
{
	/*---------- HostID | PortNum | Type | Idx ----------*/
	Pipe_Handle_T *pHandle = (Pipe_Handle_T *) pPipeHandle;

	pHandle->HostId = HostID;
	pHandle->PortNumber = 0;
	pHandle->Type = (uint8_t) XferType;
	pHandle->Idx = idx;
}

static __INLINE PHCD_QHD    HcdAsyncHead(uint8_t HostID)
{
	return &(ehci_data[HostID].AsyncHeadQhd);
	//	return &(ehci_data.AsyncHeadQhd);
}

static __INLINE PHCD_QHD    HcdIntHead(uint8_t HostID)
{
	return &(ehci_data[HostID].IntHeadQhd);
	//	return &(ehci_data.IntHeadQhd);
}

// === TODO: Deal with HostID later ===
static __INLINE PHCD_QHD    HcdQHD(uint8_t HostID, uint8_t idx)
{
	return &(ehci_data[HostID].qHDs[idx]);
	//	return &(ehci_data.qHDs[idx]);
}

static __INLINE PHCD_QTD    HcdQTD(uint8_t HostID, uint8_t idx)
{
	return &(ehci_data[HostID].qTDs[idx]);
	//	return &(ehci_data.qTDs[idx]);
}

static __INLINE PHCD_SITD   HcdSITD(uint8_t HostID, uint8_t idx)
{
	return &(ehci_data[HostID].siTDs[idx]);
	//	return &(ehci_data.siTDs[idx]);
}

static __INLINE PHCD_HS_ITD HcdHsITD(uint8_t HostID, uint8_t idx)
{
	return &(ehci_data[HostID].iTDs[idx]);
	//	return &(ehci_data.iTDs[idx]);
}

static __INLINE bool        isValidLink(uint32_t link)
{
	return (link & LINK_TERMINATE) == 0;
}

static __INLINE bool IsInterruptQhd(uint8_t HostID, uint8_t QhdIdx)
{
	return HcdQHD(HostID, QhdIdx)->uFrameSMask;
}

void    HcdIrqHandler(uint8_t HostID)
{
	uint32_t IntStatus;
        uint32_t t = USB_REG(HostID)->USBINTR_H;
	IntStatus = USB_REG(HostID)->USBSTS_H & t;

	if (IntStatus == 0) {
		return;
	}

	/* disable all interrupt for processing */
	/* Acknowledge Interrrupt */
	USB_REG(HostID)->USBSTS_H |= IntStatus;

	/* Process Interrupt Sources */
	if (IntStatus & EHC_USBSTS_PortChangeDetect) {
		uint32_t PortSC = USB_REG(HostID)->PORTSC1_H;
		if (PortSC & EHC_PORTSC_ConnectStatusChange) {
			PortStatusChangeIsr(HostID, PortSC & EHC_PORTSC_CurrentConnectStatus);
			USB_REG(HostID)->PORTSC1_H |= EHC_PORTSC_ConnectStatusChange;	/* Clear PortSC Interrupt Status */
		}
		if (PortSC & EHC_PORTSC_PortEnableChange) {
			USB_REG(HostID)->PORTSC1_H |= EHC_PORTSC_PortEnableChange;		/* Clear PortSC Interrupt Status */
		}
		if (PortSC & EHC_PORTSC_OvercurrentChange) {
			USB_REG(HostID)->PORTSC1_H |= EHC_PORTSC_OvercurrentChange;	/* Clear PortSC Interrupt Status */
		}
		if (PortSC & EHC_PORTSC_ForcePortResume) {
			USB_REG(HostID)->PORTSC1_H |= EHC_PORTSC_ForcePortResume;		/* Clear PortSC Interrupt Status */
		}
	}

	if (IntStatus & EHC_USBSTS_UsbAsyncInt) {
		AsyncScheduleIsr(HostID);
	}

	if (IntStatus & EHC_USBSTS_UsbPeriodInt) {
		PeriodScheduleIsr(HostID);
	}

	if (IntStatus & EHC_USBSTS_UsbErrorInt) {
		UsbErrorIsr(HostID);
	}

	if (IntStatus & EHC_USBSTS_IntAsyncAdvance) {
		AsyncAdvanceIsr(HostID);
	}
	/* Enable Interrupt */
}

static void RemoveCompletedQTD(uint8_t HostID, PHCD_QHD pQhd)
{
	PHCD_QTD pQtd;
	uint32_t TdLink = pQhd->FirstQtd;
	bool is_data_remain = false;

	/*-- Foreach Qtd in Qhd --*/
	while( (isValidLink(TdLink), pQtd = (PHCD_QTD) Align32(TdLink) ) &&
			pQtd->Active == 0)
	{
		TdLink = pQtd->NextQtd;

		if(pQhd->pActualTransferCount)
			*(pQhd->pActualTransferCount) -= pQtd->TotalBytesToTransfer;

		if (pQtd->IntOnComplete)
		{
			if(PipeStreaming[HostID].RemainBytes > 0)
				is_data_remain = true;
			else
				pQhd->status = HCD_STATUS_OK;
		}
		if (pQtd->Halted /*|| pQtd->Babble || pQtd->BufferError || pQtd->TransactionError*/)
		{
			pQhd->status = HCD_STATUS_TRANSFER_Stall;
		}
		FreeQtd(pQtd);
	}
	pQhd->FirstQtd = TdLink;
	if(is_data_remain)
	{
		uint32_t pQtd;
		QueueQTDs(HostID, &pQtd,(uint8_t*)PipeStreaming[HostID].BufferAddress,
				PipeStreaming[HostID].RemainBytes,
				pQhd->Direction ? IN_TRANSFER : OUT_TRANSFER,
				PipeStreaming[HostID].DataToggle);
		pQhd->FirstQtd = Align32( (uint32_t) HcdQTD(HostID,pQtd) );
		pQhd->Overlay.NextQtd = (uint32_t) HcdQTD(HostID,pQtd);
	}	
}

static void RemoveErrorQTD(PHCD_QHD pQhd)
{
	PHCD_QTD pQtd;
	uint32_t TdLink = pQhd->FirstQtd;
	bool errorfound = false;

	/*-- Scan error Qtd in Qhd --*/
	while ( (isValidLink(TdLink), pQtd = (PHCD_QTD) Align32(TdLink) ) &&
			pQtd->Active == 0) {
		TdLink = pQtd->NextQtd;

		if (pQtd->Halted /*|| pQtd->Babble || pQtd->BufferError || pQtd->TransactionError*/) {
			errorfound = true;
			pQhd->status = HCD_STATUS_TRANSFER_Stall;
		}
	}
	/*-- Remove error Qtd in Qhd --*/
	if (errorfound) {
		TdLink = pQhd->FirstQtd;
		while (isValidLink(TdLink)) {
			pQtd = (PHCD_QTD) Align32(TdLink);
			TdLink = pQtd->NextQtd;
			pQtd->Active = 0;
			pQtd->IntOnComplete = 0;
			FreeQtd(pQtd);
		}
		pQhd->FirstQtd = LINK_TERMINATE;
		pQhd->Overlay.Halted = 0;
	}
}

/*---------- Interrupt On Compete has occurred, however we have no clues on which QueueHead it happened. Also IOC TD may be advanced already So we will free all TD which is not Active (transferred already) ----------*/
static void AsyncScheduleIsr(uint8_t HostID)
{
	PHCD_QHD pQhd = HcdAsyncHead(HostID);

	/*-- Foreach Qhd in async list --*/
	while ( isValidLink(pQhd->Horizontal.Link) &&
			Align32(pQhd->Horizontal.Link) != (uint32_t) HcdAsyncHead(HostID) ) {
		pQhd = (PHCD_QHD) Align32(pQhd->Horizontal.Link);
		RemoveCompletedQTD(HostID,pQhd);
	}
}

static void PeriodScheduleIsr(uint8_t HostID)
{
	uint32_t i;

	/*ISOCHRONOUS*/
	for (i = 0; i < FRAME_LIST_SIZE; i++) {	/*-- Foreach link in Period List Base --*/
		NextLinkPointer *pNextPointer = &EHCI_FRAME_LIST(HostID)[i];

		/*-- Foreach Itd/SItd in the link--*/
		while ( isValidLink(pNextPointer->Link) && pNextPointer->Type != QHD_TYPE ) {
			if (pNextPointer->Type == ITD_TYPE) {	/*-- Highspeed ISO --*/
				PHCD_HS_ITD pItd = (PHCD_HS_ITD) Align32(pNextPointer->Link);

				if ((pItd->Transaction[0].Active == 0) && (pItd->Transaction[1].Active == 0) &&
					( pItd->Transaction[2].Active == 0) && ( pItd->Transaction[3].Active == 0) &&
					( pItd->Transaction[4].Active == 0) && ( pItd->Transaction[5].Active == 0) &&
					( pItd->Transaction[6].Active == 0) && ( pItd->Transaction[7].Active == 0) ) {
					if ((pItd->Transaction[0].IntOnComplete == 1) || (pItd->Transaction[1].IntOnComplete == 1) ||
						( pItd->Transaction[2].IntOnComplete == 1) || ( pItd->Transaction[3].IntOnComplete == 1) ||
						( pItd->Transaction[4].IntOnComplete == 1) || ( pItd->Transaction[5].IntOnComplete == 1) ||
						( pItd->Transaction[6].IntOnComplete == 1) || ( pItd->Transaction[7].IntOnComplete == 1) ) {
						/*-- request complete, signal on Iso Head --*/
						HcdQHD(HostID, pItd->IhdIdx)->status = HCD_STATUS_OK;
					}
					/*-- remove executed ITD --*/
					pNextPointer->Link = pItd->Horizontal.Link;
					FreeHsItd(pItd);
					continue;	/*-- skip advance pNextPointer due to TD removal --*/
				}
			}
			else if (pNextPointer->Type == SITD_TYPE) {	/*-- Split ISO --*/
				PHCD_SITD pSItd = (PHCD_SITD) Align32(pNextPointer->Link);

				if (pSItd->Active == 0) {
					if (pSItd->IntOnComplete) {
						/*-- request complete, signal on Iso Head --*/
						HcdQHD(HostID, pSItd->IhdIdx)->status = HCD_STATUS_OK;
					}

					/*-- removed executed SITD --*/
					pNextPointer->Link = pSItd->Horizontal.Link;
					FreeSItd(pSItd);
					continue;	/*-- skip advance pNextPointer due to TD removal --*/
				}
			}

			pNextPointer = (NextLinkPointer *) Align32(pNextPointer->Link);
		}
	}

	/*INTERRUPT*/
	{
		PHCD_QHD pQhd = HcdIntHead(HostID);

		/*-- Foreach Qhd in list --*/
		while ( isValidLink(pQhd->Horizontal.Link) ) {
			pQhd = (PHCD_QHD) Align32(pQhd->Horizontal.Link);
			RemoveCompletedQTD(HostID,pQhd);
		}
	}
}

static void UsbErrorIsr(uint8_t HostID)
{
	PHCD_QHD pQhd = HcdAsyncHead(HostID);

	/*-- Foreach Qhd in async list --*/
	while ( isValidLink(pQhd->Horizontal.Link) &&
			Align32(pQhd->Horizontal.Link) != (uint32_t) HcdAsyncHead(HostID) ) {
		pQhd = (PHCD_QHD) Align32(pQhd->Horizontal.Link);
		RemoveErrorQTD(pQhd);
	}
}

static HCD_STATUS PortStatusChangeIsr(uint8_t HostID, uint32_t deviceConnect)
{
	if (deviceConnect) {/* Device Attached */
		USB_Host_Enumerate(HostID);
	}
	else {	/* Device detached */
		USB_Host_DeEnumerate(HostID);
	}
	return HCD_STATUS_OK;
}

static void AsyncAdvanceIsr(uint8_t HostID)
{
	uint32_t QhdIdx;

	for (QhdIdx = 0; QhdIdx < HCD_MAX_QHD; QhdIdx++)
		if ((HcdQHD(HostID, QhdIdx)->inUse == 1) && (HcdQHD(HostID, QhdIdx)->status == HCD_STATUS_TO_BE_REMOVED)) {
			FreeQhd(HostID, QhdIdx);
		}
}

static __INLINE HCD_STATUS EHciHostRun(uint8_t HostID)
{
	USB_REG(HostID)->USBCMD_H |= EHC_USBCMD_RunStop;
	while (USB_REG(HostID)->USBSTS_H & EHC_USBSTS_HCHalted) {}
	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS EHciHostStop(uint8_t HostID)
{
	USB_REG(HostID)->USBCMD_H &= ~EHC_USBCMD_RunStop;
	while ( !(USB_REG(HostID)->USBSTS_H & EHC_USBSTS_HCHalted) ) {}
	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS EHciHostReset(uint8_t HostID)
{
	if (USB_REG(HostID)->USBSTS_H & EHC_USBSTS_HCHalted) {
		EHciHostStop(HostID);
	}

	USB_REG(HostID)->USBCMD_H |= EHC_USBCMD_HostReset;
	while ( USB_REG(HostID)->USBCMD_H & EHC_USBCMD_HostReset ) {}

	/* Program the controller to be the USB host controller, this can only be done after Reset */
	USB_REG(HostID)->USBMODE_H = 0x23;	// USBMODE_HostController | USBMODE_VBusPowerSelect_High;
	return HCD_STATUS_OK;
}

static __INLINE HCD_STATUS EHciHostInit(uint8_t HostID)
{
	uint32_t idx;

	/*---------- Host Data Structure Init ----------*/
	//	memset(&ehci_data[HostID], 0, sizeof(EHCI_HOST_DATA_T) );

	/*---------- USBINT ----------*/
	USB_REG(HostID)->USBINTR_H &= ~EHC_USBINTR_ALL;	/* Disable All Interrupt */
	USB_REG(HostID)->USBSTS_H  &= ~EHC_USBINTR_ALL;	/* Clear All Interrupt Status */
	USB_REG(HostID)->USBINTR_H =    EHC_USBINTR_UsbAsyncEnable | EHC_USBINTR_UsbPeriodEnable |	/* Enable necessary interrupt source: Async Advance, System Error, Port Change, USB Error, USB Int */
								 EHC_USBINTR_PortChangeIntEnable | EHC_USBINTR_UsbErroIntEnable |
								 EHC_USBINTR_IntAsyncAdvanceEnable |
								 (INT_FRAME_ROLL_OVER_ENABLE ? EHC_USBINTR_FrameListRolloverEnable : 0);

	/*---------- Asynchronous List ----------*/
	/*-- Static Head Qhd with Halted/inactive --*/
	HcdAsyncHead(HostID)->Horizontal.Link = Align32( (uint32_t) HcdAsyncHead(HostID) );
	HcdAsyncHead(HostID)->Horizontal.Type = QHD_TYPE;
	HcdAsyncHead(HostID)->HeadReclamationFlag = 1;
	HcdAsyncHead(HostID)->Overlay.NextQtd = LINK_TERMINATE;		/* Terminate Links */
	HcdAsyncHead(HostID)->Overlay.AlterNextQtd = LINK_TERMINATE;	/* Terminate Links */
	HcdAsyncHead(HostID)->Overlay.Halted = 1;

	USB_REG(HostID)->ASYNCLISTADDR = (uint32_t) HcdAsyncHead(HostID);

	/*---------- Periodic List ----------*/
	/*-- Static Interrupt Qhd (1 ms) --*/
	HcdIntHead(HostID)->Horizontal.Link = LINK_TERMINATE;
	HcdIntHead(HostID)->Overlay.NextQtd = LINK_TERMINATE;		/* Terminate Links */
	HcdIntHead(HostID)->Overlay.AlterNextQtd = LINK_TERMINATE;	/* Terminate Links */
	HcdIntHead(HostID)->Overlay.Halted = 1;
	HcdIntHead(HostID)->uFrameSMask = 1;

	for (idx = 0; idx < FRAME_LIST_SIZE; idx++) {			/* Attach 1 ms Interrupt Qhd to Period Frame List */
		EHCI_FRAME_LIST(HostID)[idx].Link = Align32( (uint32_t) HcdIntHead(HostID) );
		EHCI_FRAME_LIST(HostID)[idx].Type = QHD_TYPE;
	}

	USB_REG(HostID)->PERIODICLISTBASE = Align4k( (uint32_t) EHCI_FRAME_LIST(HostID) );

	/*---------- USBCMD ----------*/
	USB_REG(HostID)->USBCMD_H =    EHC_USBCMD_AsynScheduleEnable |
								 ((FRAMELIST_SIZE_BITS % 4) << 2) | ((FRAMELIST_SIZE_BITS / 4) << 15);

	/*---------- CONFIGFLAG ----------*/
	/* LPC18xx doesn't has CONFIGFLAG register */

	/*---------- Power On RhPort ----------*/
	USB_REG(HostID)->PORTSC1_H |= EHC_PORTSC_PortPowerControl;

	EHciHostRun(HostID);/* Run The HC */

	return HCD_STATUS_OK;
}

static __INLINE void DisableSchedule(uint8_t HostID, uint8_t isPeriod)
{
	uint32_t statusMask = isPeriod ? EHC_USBSTS_PeriodScheduleStatus : EHC_USBSTS_AsyncScheduleStatus;
	uint32_t cmdMask = isPeriod ? EHC_USBCMD_PeriodScheduleEnable : EHC_USBCMD_AsynScheduleEnable;

	if (USB_REG(HostID)->USBSTS_H & statusMask) {
		USB_REG(HostID)->USBCMD_H &= ~cmdMask;
		while (USB_REG(HostID)->USBSTS_H & statusMask) {}	/* TODO Should have time-out */
	}
}

static __INLINE void EnableSchedule(uint8_t HostID, uint8_t isPeriod)
{
	uint32_t statusMask = isPeriod ? EHC_USBSTS_PeriodScheduleStatus : EHC_USBSTS_AsyncScheduleStatus;
	uint32_t cmdMask = isPeriod ? EHC_USBCMD_PeriodScheduleEnable : EHC_USBCMD_AsynScheduleEnable;

	if (!(USB_REG(HostID)->USBSTS_H & statusMask)) {
		USB_REG(HostID)->USBCMD_H |= cmdMask;
		while (!(USB_REG(HostID)->USBSTS_H & statusMask)) {}/* TODO Should have time-out */
	}
}

static void DisableAsyncSchedule(uint8_t HostID)
{
	DisableSchedule(HostID, 0);
}

static void EnableAsyncSchedule(uint8_t HostID)
{
	EnableSchedule(HostID, 0);
}

static void DisablePeriodSchedule(uint8_t HostID)
{
	DisableSchedule(HostID, 1);
}

static void EnablePeriodSchedule(uint8_t HostID)
{
	EnableSchedule(HostID, 1);
}

void HcdSetStreamPacketSize(uint32_t PipeHandle, uint16_t packetsize)
{
	uint8_t HostID = 0, HeadIdx;
	HCD_TRANSFER_TYPE XferType;

	PipehandleParse(PipeHandle, &HostID, &XferType, &HeadIdx);

	PipeStreaming[HostID].PacketSize = packetsize;
}

#endif // __LPC_EHCI__
