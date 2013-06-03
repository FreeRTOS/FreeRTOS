/*
 * @brief USB Pipe definitions for the LPC microcontrollers
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

#define  __INCLUDE_FROM_USB_DRIVER
#include "USBMode.h"

#if defined(USB_CAN_BE_HOST)

#include "Pipe.h"

uint8_t pipeselected[MAX_USB_CORE];
USB_Pipe_Data_t PipeInfo[MAX_USB_CORE][PIPE_TOTAL_PIPES];

HCD_USB_SPEED hostportspeed[MAX_USB_CORE];
uint8_t hostselected;

bool Pipe_ConfigurePipe(const uint8_t corenum,
						const uint8_t Number,
						const uint8_t Type,
						const uint8_t Token,
						const uint8_t EndpointNumber,
						const uint16_t Size,
						const uint8_t Banks)
{
	if ( HCD_STATUS_OK == HcdOpenPipe(corenum,				/* HostID */
									  (( Type == EP_TYPE_CONTROL) &&
									   ( USB_HostState[corenum] <
										 HOST_STATE_Default_PostAddressSet) ) ? 0 : USB_HOST_DEVICEADDRESS,															/* FIXME DeviceAddr */
									  hostportspeed[corenum],	/* DeviceSpeed */
									  EndpointNumber,				/* EndpointNo */
									  (HCD_TRANSFER_TYPE) Type,		/* TransferType */
									  (HCD_TRANSFER_DIR) Token,		/* TransferDir */
									  Size,							/* MaxPacketSize */
									  1,							/* Interval */
									  1,							/* Mult */
									  0,							/* HSHubDevAddr */
									  0,							/* HSHubPortNum */
									  &PipeInfo[corenum][Number].PipeHandle			  /* PipeHandle */)
		 ) {
		PipeInfo[corenum][Number].ByteTransfered = PipeInfo[corenum][Number].StartIdx = 0;
		PipeInfo[corenum][Number].BufferSize = (Type == EP_TYPE_BULK || Type == EP_TYPE_CONTROL) ? PIPE_MAX_SIZE : Size;/* XXX Some devices could have configuration descriptor > 235 bytes (eps speaker, webcame). If not deal with those, not need to have such large pipe size for control */
		PipeInfo[corenum][Number].Buffer = USB_Memory_Alloc(PipeInfo[corenum][Number].BufferSize,0);
		PipeInfo[corenum][Number].EndponitAddress = EndpointNumber;
		if (PipeInfo[corenum][Number].Buffer == NULL) {
			return false;
		}

		return true;
	}
	else {
		return false;
	}
}

void Pipe_ClosePipe(const uint8_t corenum, uint8_t pipenum)
{
	if (pipenum < PIPE_TOTAL_PIPES) {
		HcdClosePipe(PipeInfo[corenum][pipenum].PipeHandle);
		PipeInfo[corenum][pipenum].PipeHandle = 0;
		USB_Memory_Free(PipeInfo[corenum][pipenum].Buffer);
		PipeInfo[corenum][pipenum].Buffer = NULL;
		PipeInfo[corenum][pipenum].BufferSize = 0;
	}
}

void Pipe_ClearPipes(void)
{}

bool Pipe_IsEndpointBound(const uint8_t EndpointAddress)
{
	return false;
}

uint8_t Pipe_WaitUntilReady(const uint8_t corenum)
{
	/*	#if (USB_STREAM_TIMEOUT_MS < 0xFF)
	    uint8_t  TimeoutMSRem = USB_STREAM_TIMEOUT_MS;
	   #else
	    uint16_t TimeoutMSRem = USB_STREAM_TIMEOUT_MS;
	   #endif

	    uint16_t PreviousFrameNumber = USB_Host_GetFrameNumber();*/

	for (;; ) {
		if (Pipe_IsReadWriteAllowed(corenum)) {
			return PIPE_READYWAIT_NoError;
		}

		if (Pipe_IsStalled(corenum)) {
			return PIPE_READYWAIT_PipeStalled;
		}
		else if (USB_HostState[corenum] == HOST_STATE_Unattached) {
			return PIPE_READYWAIT_DeviceDisconnected;
		}

		/*TODO no timeout yet */
		/* uint16_t CurrentFrameNumber = USB_Host_GetFrameNumber();

		   if (CurrentFrameNumber != PreviousFrameNumber)
		   {
		    PreviousFrameNumber = CurrentFrameNumber;

		    if (!(TimeoutMSRem--))
		      return PIPE_READYWAIT_Timeout;
		   }*/
	}
}

bool Pipe_IsINReceived(const uint8_t corenum)
{
	if (HCD_STATUS_OK != HcdGetPipeStatus(PipeInfo[corenum][pipeselected[corenum]].PipeHandle)) {
		return false;
	}

	if (Pipe_BytesInPipe(corenum)) {
		return true;
	}
	else {	/* Empty Pipe */
		HcdDataTransfer(PipeInfo[corenum][pipeselected[corenum]].PipeHandle,
						PipeInfo[corenum][pipeselected[corenum]].Buffer,
						HCD_ENDPOINT_MAXPACKET_XFER_LEN,
						&PipeInfo[corenum][pipeselected[corenum]].ByteTransfered);
		return false;
	}
}

#endif
