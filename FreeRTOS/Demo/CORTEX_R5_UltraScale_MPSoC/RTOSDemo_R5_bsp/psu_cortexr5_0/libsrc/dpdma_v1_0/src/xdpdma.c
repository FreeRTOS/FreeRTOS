/******************************************************************************
*
* Copyright (C) 2010 - 2017 Xilinx, Inc. All rights reserved.
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
* XILINX BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*

*******************************************************************************/
/*****************************************************************************/
/**
 *
 * @file xdpdma.c
 *
 * This file contains the implementation of the interface functions of the
 * XDpDma driver. Refer to xdpdma.h for detailed information.
 *
 * @note	None.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver	Who   Date     Changes
 * ---- ----- -------- ----------------------------------------------------
 * 1.0  aad   04/12/16 Initial release.
 *
 *****************************************************************************/

/***************************** Include Files **********************************/
#include "xdpdma.h"
#include "xavbuf.h"

/************************** Constant Definitions ******************************/
#define XDPDMA_CH_OFFSET		0x100
#define XDPDMA_WAIT_TIMEOUT		10000

#define XDPDMA_AUDIO_ALIGNMENT		128

#define XDPDMA_VIDEO_CHANNEL0		0
#define XDPDMA_VIDEO_CHANNEL1		1
#define XDPDMA_VIDEO_CHANNEL2		2
#define XDPDMA_GRAPHICS_CHANNEL		3
#define XDPDMA_AUDIO_CHANNEL0		4
#define XDPDMA_AUDIO_CHANNEL1		5

#define XDPDMA_DESC_PREAMBLE		0xA5
#define XDPDMA_DESC_IGNR_DONE		0x400
#define XDPDMA_DESC_UPDATE		0x200
#define XDPDMA_DESC_COMP_INTR		0x100
#define XDPDMA_DESC_LAST_FRAME		0x200000
#define XDPDMA_DESC_DONE_SHIFT		31
#define XDPDMA_QOS_MIN			4
#define XDPDMA_QOS_MAX			11

/*************************************************************************/
/**
 *
 * This function returns the number of outstanding transactions on a given
 * channel.
 *
 * @param    InstancePtr is a pointer to the driver instance.
 * @param    ChannelNum is the channel number on which the operation is
 *	     being carried out.
 *
 * @return   Number of pending transactions.
 *
 * @note     None.
 *
 * **************************************************************************/
static int XDpDma_GetPendingTransaction(XDpDma *InstancePtr, u32 ChannelNum)
{
	u32 RegVal;
	RegVal = XDpDma_ReadReg(InstancePtr->Config.BaseAddr,
				XDPDMA_CH0_STATUS + 0x100 * ChannelNum);
	return (RegVal & XDPDMA_CH_STATUS_OTRAN_CNT_MASK);
}

/*************************************************************************/
/**
 *
 * This function waits until the outstanding transactions are completed.
 *
 * @param    InstancePtr is a pointer to the driver instance.
 * @param    ChannelNum is the channel number on which the operation is
 *	     being carried out.
 *
 * @return   XST_SUCCESS when all the pending transactions are complete
 *	     before timeout.
 *	     XST_FAILURE if timeout occurs before pending transactions are
 *	     completed.
 *
 * @note     None.
 *
 * **************************************************************************/
static int XDpDma_WaitPendingTransaction(XDpDma *InstancePtr, u8 ChannelNum)
{
	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ChannelNum <= XDPDMA_AUDIO_CHANNEL1);

	u32 Timeout = 0;
	u32 Count;
	do {
		Count = XDpDma_GetPendingTransaction(InstancePtr, ChannelNum);
		Timeout++;
	} while((Timeout != XDPDMA_WAIT_TIMEOUT) && Count);

	if(Timeout ==  XDPDMA_WAIT_TIMEOUT) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/*************************************************************************/
/**
 *
 * This function controls the hardware channels of the DPDMA.
 *
 *
 * @param    InstancePtr is a pointer to the driver instance.
 * @param    ChannelNum is the physical channel number of the DPDMA.
 * @param    ChannelState is an enum of type XDpDma_ChannelState.
 *
 * @return   XST_SUCCESS when the mentioned channel is enabled successfully.
 *	     XST_FAILURE when the mentioned channel fails to be enabled.
 *
 * @note     None.
 *
 * **************************************************************************/
static int XDpDma_ConfigChannelState(XDpDma *InstancePtr, u8 ChannelNum,
				     XDpDma_ChannelState Enable)
{
	u32 Mask = 0;
	u32 RegVal = 0;
	u32 Status = 0;
	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ChannelNum <= XDPDMA_AUDIO_CHANNEL1);

	Mask = XDPDMA_CH_CNTL_EN_MASK | XDPDMA_CH_CNTL_PAUSE_MASK;
	switch(Enable) {
		case XDPDMA_ENABLE:
			RegVal = XDPDMA_CH_CNTL_EN_MASK;
			break;
		case XDPDMA_DISABLE:
			XDpDma_ConfigChannelState(InstancePtr, ChannelNum,
						  XDPDMA_PAUSE);
			Status = XDpDma_WaitPendingTransaction(InstancePtr,
							       ChannelNum);
			if(Status == XST_FAILURE) {
				return XST_FAILURE;
			}

			RegVal = XDPDMA_DISABLE;
			Mask = XDPDMA_CH_CNTL_EN_MASK;
			break;
		case XDPDMA_IDLE:
			Status = XDpDma_ConfigChannelState(InstancePtr,
							   ChannelNum,
							   XDPDMA_DISABLE);
			if(Status == XST_FAILURE) {
				return XST_FAILURE;
			}

			RegVal = 0;
			break;
		case XDPDMA_PAUSE:
			RegVal = XDPDMA_PAUSE;
			break;
	}
	XDpDma_ReadModifyWrite(InstancePtr->Config.BaseAddr,
			       XDPDMA_CH0_CNTL + XDPDMA_CH_OFFSET * ChannelNum,
			       RegVal, Mask);
	return XST_SUCCESS;
}

/*************************************************************************/
/**
 *
 * This function updates the descriptor that is not currently active on a
 * Video/Graphics channel.
 *
 * @param    InstancePtr is a pointer to the driver instance.
 * @param    Channel is a pointer to the channel on which the operation is
 *	     to be carried out.
 *
 * @return   Descriptor for next operation.
 *
 * @note     None.
 *
 * **************************************************************************/
static XDpDma_Descriptor *XDpDma_UpdateVideoDescriptor(XDpDma_Channel *Channel)
{
	if(Channel->Current == NULL) {
		Channel->Current = &Channel->Descriptor0;
	}
	else if(Channel->Current == &Channel->Descriptor0) {
		Channel->Current = &Channel->Descriptor1;
	}
	else if(Channel->Current == &Channel->Descriptor1) {
		Channel->Current = &Channel->Descriptor0;
	}
	return Channel->Current;
}

/*************************************************************************/
/**
 * This function programs the address of the descriptor about to be active
 *
 * @param    InstancePtr is a pointer to the DPDMA instance.
 * @param    Channel is an enum of the channel for which the descriptor
 *	     address is to be set.
 *
 * @return   Descriptor for next operation.
 *
 * @note     None.
 *
 * **************************************************************************/
static void XDpDma_SetDescriptorAddress(XDpDma *InstancePtr, u8 ChannelNum)
{
	u32 AddrOffset;
	u32 AddrEOffset;
	Xil_AssertVoid(ChannelNum <= XDPDMA_AUDIO_CHANNEL1);
	AddrOffset = XDPDMA_CH0_DSCR_STRT_ADDR +
					(XDPDMA_CH_OFFSET * ChannelNum);
	AddrEOffset = XDPDMA_CH0_DSCR_STRT_ADDRE +
					(XDPDMA_CH_OFFSET * ChannelNum);

	XDpDma_Descriptor *Descriptor = NULL;
	switch(ChannelNum) {
	case XDPDMA_VIDEO_CHANNEL0:
		Descriptor = InstancePtr->Video.Channel[ChannelNum].Current;
		break;
	case XDPDMA_VIDEO_CHANNEL1:
		Descriptor = InstancePtr->Video.Channel[ChannelNum].Current;
		break;
	case XDPDMA_VIDEO_CHANNEL2:
		Descriptor = InstancePtr->Video.Channel[ChannelNum].Current;
		break;
	case XDPDMA_GRAPHICS_CHANNEL:
		Descriptor = InstancePtr->Gfx.Channel.Current;
		break;
	case XDPDMA_AUDIO_CHANNEL0:
		Descriptor = InstancePtr->Audio[0].Current;
		break;
	case XDPDMA_AUDIO_CHANNEL1:
		Descriptor = InstancePtr->Audio[1].Current;
		break;
	}

	XDpDma_WriteReg(InstancePtr->Config.BaseAddr, AddrEOffset,
			(INTPTR) Descriptor >> 32);
	XDpDma_WriteReg(InstancePtr->Config.BaseAddr, AddrOffset,
			(INTPTR) Descriptor);
}

/*************************************************************************/
/**
 *
 * This functions sets the Audio Descriptor for Data Transfer.
 *
 * @param    CurrDesc is a pointer to the descriptor to be initialized
 * @param    DataSize is the payload size of the buffer to be transferred
 * @param    BuffAddr is the payload address
 *
 * @return   None.
 *
 * @note     None.
 *
 * **************************************************************************/
static void XDpDma_SetupAudioDescriptor(XDpDma_Descriptor *CurrDesc,
					u64 DataSize, u64 BuffAddr,
					XDpDma_Descriptor *NextDesc)
{
	Xil_AssertVoid(CurrDesc != NULL);
	Xil_AssertVoid(DataSize != 0);
	Xil_AssertVoid(BuffAddr != 0);

	if(NextDesc == NULL) {
		CurrDesc->Control = XDPDMA_DESC_PREAMBLE |
			XDPDMA_DESC_UPDATE | XDPDMA_DESC_IGNR_DONE |
			XDPDMA_DESC_COMP_INTR;

	}
	else {
		CurrDesc->Control = XDPDMA_DESC_PREAMBLE |
			XDPDMA_DESC_UPDATE | XDPDMA_DESC_IGNR_DONE;
	}
	CurrDesc->DSCR_ID = 0;
	CurrDesc->XFER_SIZE = DataSize;
	CurrDesc->LINE_SIZE_STRIDE = 0;
	CurrDesc->LSB_Timestamp = 0;
	CurrDesc->MSB_Timestamp = 0;
	CurrDesc->ADDR_EXT = ((BuffAddr >> XDPDMA_DESCRIPTOR_SRC_ADDR_WIDTH) <<
			      XDPDMA_DESCRIPTOR_ADDR_EXT_SRC_ADDR_EXT_SHIFT) |
			     ((INTPTR) NextDesc >>
			      XDPDMA_DESCRIPTOR_NEXT_DESR_WIDTH);
	CurrDesc->NEXT_DESR = (INTPTR) NextDesc;
	CurrDesc->SRC_ADDR =  BuffAddr;
}

/*************************************************************************/
/**
 *
 * This functions retrieves the configuration for this DPDMA driver and
 * fills in the InstancePtr->Config structure.
 *
 * @param    InstancePtr is a pointer to the driver instance.
 * @param    ConfigPtr is a pointer to the configuration structure that will
 *           be used to copy the settings from.
 *
 * @return   None.
 *
 * @note     None.
 *
 * **************************************************************************/
void XDpDma_CfgInitialize(XDpDma *InstancePtr, XDpDma_Config *CfgPtr)
{
	InstancePtr->Config.DeviceId = CfgPtr->DeviceId;
	InstancePtr->Config.BaseAddr = CfgPtr->BaseAddr;

	InstancePtr->Video.Channel[XDPDMA_VIDEO_CHANNEL0].Current = NULL;
	InstancePtr->Video.Channel[XDPDMA_VIDEO_CHANNEL1].Current = NULL;
	InstancePtr->Video.Channel[XDPDMA_VIDEO_CHANNEL2].Current = NULL;
	InstancePtr->Video.TriggerStatus = XDPDMA_TRIGGER_DONE;
	InstancePtr->Video.VideoInfo = NULL;
	InstancePtr->Video.FrameBuffer[XDPDMA_VIDEO_CHANNEL0] = NULL;
	InstancePtr->Video.FrameBuffer[XDPDMA_VIDEO_CHANNEL1] = NULL;
	InstancePtr->Video.FrameBuffer[XDPDMA_VIDEO_CHANNEL2] = NULL;

	InstancePtr->Gfx.Channel.Current = NULL;
	InstancePtr->Gfx.TriggerStatus = XDPDMA_TRIGGER_DONE;
	InstancePtr->Gfx.VideoInfo = NULL;
	InstancePtr->Gfx.FrameBuffer = NULL;
}

/*************************************************************************/
/**
 *
 * This functions controls the states in which a channel should go into.
 *
 * @param    InstancePtr is a pointer to the driver instance.
 * @param    ChannelType is an enum of XDpDma_ChannelType.
 * @param    ChannelState is an enum of type XDpDma_ChannelState.
 *
 * @return   XST_SUCCESS when the mentioned channel is enabled successfully.
 *	     XST_FAILURE when the mentioned channel fails to be enabled.
 *
 * @note     None.
 *
 * **************************************************************************/
int XDpDma_SetChannelState(XDpDma *InstancePtr, XDpDma_ChannelType Channel,
					XDpDma_ChannelState ChannelState)
{
	u32 Index = 0;
	u32 NumPlanes = 0;
	u32 Status = 0;
	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);

	switch(Channel) {
	case VideoChan:
		if(InstancePtr->Video.VideoInfo == NULL) {
			return XST_FAILURE;
		}
		else {
			NumPlanes = InstancePtr->Video.VideoInfo->Mode;
			for(Index = 0; Index <= NumPlanes; Index++) {
				Status = XDpDma_ConfigChannelState(InstancePtr,
								Index,
								ChannelState);
				if(Status == XST_FAILURE) {
					return XST_FAILURE;
				}
			}
		}
		break;
	case GraphicsChan:
		if(InstancePtr->Gfx.VideoInfo == NULL) {
			return XST_FAILURE;
		}
		else {
			return	XDpDma_ConfigChannelState(InstancePtr,
					      XDPDMA_GRAPHICS_CHANNEL,
					      ChannelState);
		}
		break;
	case AudioChan0:
		return	XDpDma_ConfigChannelState(InstancePtr,
						  XDPDMA_AUDIO_CHANNEL0,
						  ChannelState);
		break;
	case AudioChan1:
		return XDpDma_ConfigChannelState(InstancePtr,
						 XDPDMA_AUDIO_CHANNEL1,
						 ChannelState);
		break;
	default:
		return XST_FAILURE;
		break;
	}

	return XST_SUCCESS;
}

/*************************************************************************/
/**
 *
 * This function allocates DPDMA Video Channels depending on the number of
 * planes in the video
 *
 * @param	InstancePtr is a pointer to the driver instance.
 * @params	Format is the video format to be used for the DPDMA transfer
 *
 * @return	XST_SUCCESS, When the format is valid Video Format.
 *		XST_FAILURE, When the format is not valid Video Format
 *
 * @note	None.
 *
 * **************************************************************************/
int XDpDma_SetVideoFormat(XDpDma *InstancePtr, XAVBuf_VideoFormat Format)
{
	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);

	InstancePtr->Video.VideoInfo = XAVBuf_GetNLiveVideoAttribute(Format);
	if(InstancePtr->Video.VideoInfo == NULL) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/*************************************************************************/
/**
 *
 * This function allocates DPDMA Graphics Channels.
 *
 * @param	InstancePtr is a pointer to the driver instance.
 * @params	Format is the video format to be used for the DPDMA transfer
 *
 * @return	XST_SUCCESS, When the format is a valid Graphics Format.
 *		XST_FAILURE, When the format is not valid Graphics Format.
 *
 * @note	None.
 *
 * **************************************************************************/
int XDpDma_SetGraphicsFormat(XDpDma *InstancePtr, XAVBuf_VideoFormat Format)
{

	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);

	InstancePtr->Gfx.VideoInfo = XAVBuf_GetNLGraphicsAttribute(Format);
	if(InstancePtr->Gfx.VideoInfo == NULL) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/*************************************************************************/
/**
 *
 * This function starts the operation on the a given channel
 *
 * @param    InstancePtr is a pointer to the driver instance.
 * @param    QOS is the Quality of Service value to be selected.
 *
 * @return   None.
 *
 * @note     .
 *
 * **************************************************************************/
void XDpDma_SetQOS(XDpDma *InstancePtr, u8 QOS)
{
	u8 Index;
	u32 RegVal = 0;

	Xil_AssertVoid(QOS >= XDPDMA_QOS_MIN && QOS <= XDPDMA_QOS_MAX);

	RegVal = ((QOS << XDPDMA_CH_CNTL_QOS_DATA_RD_SHIFT) |
		   (QOS << XDPDMA_CH_CNTL_QOS_DSCR_RD_SHIFT) |
		   (QOS << XDPDMA_CH_CNTL_QOS_DSCR_WR_SHIFT));

	u32 Mask = XDPDMA_CH_CNTL_QOS_DATA_RD_MASK |
		XDPDMA_CH_CNTL_QOS_DSCR_RD_MASK |
		XDPDMA_CH_CNTL_QOS_DSCR_WR_MASK;

	for(Index = 0; Index <= XDPDMA_AUDIO_CHANNEL1; Index++) {
		XDpDma_ReadModifyWrite(InstancePtr->Config.BaseAddr,
				XDPDMA_CH0_CNTL + (XDPDMA_CH_OFFSET * Index),
			        RegVal, Mask);
	}

}

/*************************************************************************/
/**
 *
 * This function Triggers DPDMA to start the transaction.
 *
 * @param	InstancePtr is a pointer to the XDpDma instance.
 * @param	Channel is the XDpDma_ChannelType on which the transaction
 *		is to be triggered.
 *
 * @return	XST_SUCCESS The channel has successfully been Triggered.
 *		XST_FAILURE When the triggering Video and Graphics channel
 *		without setting the Video Formats.
 *
 * @note	None.
 *
 * **************************************************************************/
int XDpDma_Trigger(XDpDma *InstancePtr, XDpDma_ChannelType Channel)
{
	u32 Trigger = 0;
	u8 Index = 0;
	u8 NumPlanes = 0;
	switch(Channel) {
	case VideoChan:
		if(InstancePtr->Video.VideoInfo == NULL) {
			return XST_FAILURE;
		}
		else {
			NumPlanes = InstancePtr->Video.VideoInfo->Mode;
			for(Index = 0; Index <= NumPlanes; Index++) {
				Trigger |= XDPDMA_GBL_TRG_CH0_MASK << Index;
				InstancePtr->Video.TriggerStatus =
					XDPDMA_TRIGGER_DONE;
			}
		}
		break;
	case GraphicsChan:
		if(InstancePtr->Gfx.VideoInfo == NULL) {
			return XST_FAILURE;
		}
		Trigger = XDPDMA_GBL_TRG_CH3_MASK;
		InstancePtr->Gfx.TriggerStatus = XDPDMA_TRIGGER_DONE;
		break;
	case AudioChan0:
		Trigger = XDPDMA_GBL_TRG_CH4_MASK;
		InstancePtr->Audio[0].TriggerStatus = XDPDMA_TRIGGER_DONE;
		break;
	case AudioChan1:
		Trigger = XDPDMA_GBL_TRG_CH5_MASK;
		InstancePtr->Audio[1].TriggerStatus = XDPDMA_TRIGGER_DONE;
		break;
	}
	XDpDma_WriteReg(InstancePtr->Config.BaseAddr, XDPDMA_GBL, Trigger);

	return XST_SUCCESS;

}

/*************************************************************************/
/**
 *
 * This function Retriggers DPDMA to fetch data from new descriptor.
 *
 * @param	InstancePtr is a pointer to the XDpDma instance.
 * @param	Channel is the XDpDma_ChannelType on which the transaction
 *		is to be retriggered.
 *
 * @return	XST_SUCCESS The channel has successfully been Triggered.
 *		XST_FAILURE When the triggering Video and Graphics channel
 *		without setting the Video Formats.
 *
 * @note	None.
 *
 * **************************************************************************/
int XDpDma_ReTrigger(XDpDma *InstancePtr, XDpDma_ChannelType Channel)
{
	u32 Trigger = 0;
	u8 NumPlanes;
	u8 Index;
	switch(Channel) {
	case VideoChan:
		if(InstancePtr->Video.VideoInfo == NULL) {
			return XST_FAILURE;
		}
		else {
			NumPlanes = InstancePtr->Video.VideoInfo->Mode;
			for(Index = 0; Index <= NumPlanes; Index++) {
				Trigger |= XDPDMA_GBL_RTRG_CH0_MASK << Index;
				InstancePtr->Video.TriggerStatus =
					XDPDMA_RETRIGGER_DONE;
			}
		}
		break;
	case GraphicsChan:
		if(InstancePtr->Gfx.VideoInfo == NULL) {
			return XST_FAILURE;
		}
		Trigger = XDPDMA_GBL_RTRG_CH3_MASK;
		InstancePtr->Gfx.TriggerStatus = XDPDMA_RETRIGGER_DONE;
		break;
	case AudioChan0:
		Trigger = XDPDMA_GBL_RTRG_CH4_MASK;
		InstancePtr->Audio[0].TriggerStatus = XDPDMA_RETRIGGER_DONE;
		break;
	case AudioChan1:
		Trigger = XDPDMA_GBL_RTRG_CH5_MASK;
		InstancePtr->Audio[1].TriggerStatus = XDPDMA_RETRIGGER_DONE;
		break;
	}
	XDpDma_WriteReg(InstancePtr->Config.BaseAddr, XDPDMA_GBL, Trigger);

	return XST_SUCCESS;
}

/*************************************************************************/
/**
 *
 * This function intializes Video Descriptor for Video and Graphics channel
 *
 * @param    Channel is a pointer to the current Descriptor of Video or
 *	     Graphics Channel.
 * @param    FrameBuffer is a pointer to the Frame Buffer structure
 *
 * @return   None.
 *
 * @note     None.
 *
 * **************************************************************************/
void XDpDma_InitVideoDescriptor(XDpDma_Descriptor *CurrDesc,
				XDpDma_FrameBuffer *FrameBuffer)
{
	Xil_AssertVoid(CurrDesc != NULL);
	Xil_AssertVoid(FrameBuffer != NULL);
	Xil_AssertVoid((FrameBuffer->Stride) % XDPDMA_DESCRIPTOR_ALIGN == 0);
	CurrDesc->Control = XDPDMA_DESC_PREAMBLE | XDPDMA_DESC_IGNR_DONE |
			    XDPDMA_DESC_LAST_FRAME;
	CurrDesc->DSCR_ID = 0;
	CurrDesc->XFER_SIZE = FrameBuffer->Size;
	CurrDesc->LINE_SIZE_STRIDE = ((FrameBuffer->Stride >> 4) <<
				XDPDMA_DESCRIPTOR_LINE_SIZE_STRIDE_SHIFT) |
				(FrameBuffer->LineSize);
	CurrDesc->ADDR_EXT = (((FrameBuffer->Address >>
				XDPDMA_DESCRIPTOR_SRC_ADDR_WIDTH) <<
			       XDPDMA_DESCRIPTOR_ADDR_EXT_SRC_ADDR_EXT_SHIFT) |
				((INTPTR) CurrDesc >>
				 XDPDMA_DESCRIPTOR_NEXT_DESR_WIDTH));
	CurrDesc->NEXT_DESR = (INTPTR) CurrDesc;
	CurrDesc->SRC_ADDR = FrameBuffer->Address;
}

/*************************************************************************/
/**
 *
 * This function intializes Descriptors for transactions on Audio Channel
 *
 * @param    Channel is a pointer to the XDpDma_AudioChannel instance
 *
 * @param    AudioBuffer is a pointer to the Audio Buffer structure
 *
 * @return   None.
 *
 * @note     None.
 *
 * **************************************************************************/
void XDpDma_InitAudioDescriptor(XDpDma_AudioChannel *Channel,
			       XDpDma_AudioBuffer *AudioBuffer)
{
	u32 Size;
	u64 Address;
	Xil_AssertVoid(Channel != NULL);
	Xil_AssertVoid(AudioBuffer != NULL);
	Xil_AssertVoid((AudioBuffer->Size) % XDPDMA_AUDIO_ALIGNMENT == 0);
	Xil_AssertVoid((AudioBuffer->Address) % XDPDMA_AUDIO_ALIGNMENT == 0);

	Size = AudioBuffer->Size / 4;
	Address = AudioBuffer->Address;
	if(Channel->Current == &Channel->Descriptor4) {
		XDpDma_SetupAudioDescriptor(&Channel->Descriptor4, Size,
					    Address,
					    &Channel->Descriptor5);
		XDpDma_SetupAudioDescriptor(&Channel->Descriptor5, Size,
					    Address + Size,
					    &Channel->Descriptor6);
		XDpDma_SetupAudioDescriptor(&Channel->Descriptor6, Size,
					    Address + (Size * 2),
					    &Channel->Descriptor7);
		XDpDma_SetupAudioDescriptor(&Channel->Descriptor7, Size,
					    Address + (Size * 3), NULL);
	}

	else if(Channel->Current == &Channel->Descriptor0) {
		XDpDma_SetupAudioDescriptor(&Channel->Descriptor0, Size,
					    Address,
					    &Channel->Descriptor1);
		XDpDma_SetupAudioDescriptor(&Channel->Descriptor1, Size,
					    Address + Size,
					    &Channel->Descriptor2);
		XDpDma_SetupAudioDescriptor(&Channel->Descriptor2, Size,
					    Address + (Size * 2),
					    &Channel->Descriptor3);
		XDpDma_SetupAudioDescriptor(&Channel->Descriptor3, Size,
					    Address + (Size * 3), NULL);

	}
}

/*************************************************************************/
/**
 *
 * This function sets the next Frame Buffers to be displayed on the Video
 * Channel.
 *
 * @param    InstancePtr is pointer to the instance of DPDMA.
 * @param    Plane0 is a pointer to the Frame Buffer structure.
 * @param    Plane1 is a pointer to the Frame Buffer structure.
 * @param    Plane2 is a pointer to the Frame Buffer structure.
 *
 * @return   None.
 *
 * @note     For interleaved mode use Plane0.
 *	     For semi-planar mode use Plane0 and Plane1.
 *	     For planar mode use Plane0, Plane1 and Plane2
 *
 * **************************************************************************/
void  XDpDma_DisplayVideoFrameBuffer(XDpDma *InstancePtr,
				     XDpDma_FrameBuffer *Plane0,
				     XDpDma_FrameBuffer *Plane1,
				     XDpDma_FrameBuffer *Plane2)
{
	u8 NumPlanes;
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->Video.VideoInfo != NULL);

	NumPlanes = InstancePtr->Video.VideoInfo->Mode;

	switch(NumPlanes) {
		case XDPDMA_VIDEO_CHANNEL2:
			Xil_AssertVoid(Plane2 != NULL);
			InstancePtr->Video.FrameBuffer[XDPDMA_VIDEO_CHANNEL2] =
				Plane2;
		case XDPDMA_VIDEO_CHANNEL1:
			Xil_AssertVoid(Plane1 != NULL);
			InstancePtr->Video.FrameBuffer[XDPDMA_VIDEO_CHANNEL1] =
				Plane1;
		case XDPDMA_VIDEO_CHANNEL0:
			Xil_AssertVoid(Plane0 != NULL);
			InstancePtr->Video.FrameBuffer[XDPDMA_VIDEO_CHANNEL0] =
				Plane0;
			break;
	}

	if(InstancePtr->Video.Channel[XDPDMA_VIDEO_CHANNEL0].Current == NULL) {
		InstancePtr->Video.TriggerStatus = XDPDMA_TRIGGER_EN;
	}
	else {
		InstancePtr->Video.TriggerStatus = XDPDMA_RETRIGGER_EN;
	}
}

/*************************************************************************/
/**
 *
 * This function sets the next Frame Buffers to be displayed on the Graphics
 * Channel.
 *
 * @param    InstancePtr is pointer to the instance of DPDMA.
 * @param    Plane is a pointer to the Frame Buffer structure.
 *
 * @return   None.
 *
 * @note     None.
 *
 **************************************************************************/
void XDpDma_DisplayGfxFrameBuffer(XDpDma *InstancePtr,
				  XDpDma_FrameBuffer *Plane)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Plane != NULL);

	InstancePtr->Gfx.FrameBuffer = Plane;

	if(InstancePtr->Gfx.Channel.Current == NULL) {
		InstancePtr->Gfx.TriggerStatus = XDPDMA_TRIGGER_EN;
	}
	else {
		InstancePtr->Gfx.TriggerStatus = XDPDMA_RETRIGGER_EN;
	}
}
/*************************************************************************/
/**
 *
 * This function sets the next Audio Buffer to be played on Audio Channel 0
 *
 * @param    InstancePtr is pointer to the instance of DPDMA.
 * @param    Buffer is a pointer to the attributes of the Audio information
 *	     to be played.
 * @param    ChannelNum selects between Audio Channel 0 and Audio Channel 1
 *
 * @return   XST_SUCCESS when the play audio request is successful.
 *	     XST_FAILURE when the play audio request fails, user has to
 *	     retry to play the audio.
 *
 * @note     The user has to schedule new audio buffer before half the audio
 *	     information is consumed by DPDMA to have a seamless playback.
 *
 **************************************************************************/
int XDpDma_PlayAudio(XDpDma *InstancePtr, XDpDma_AudioBuffer *Buffer,
		      u8 ChannelNum)
{
	XDpDma_AudioChannel *Channel;
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(Buffer != NULL);
	Xil_AssertNonvoid(Buffer->Size >= 512);
	Xil_AssertNonvoid(Buffer->Size % 128 == 0);
	Xil_AssertNonvoid(Buffer->Address % 128 == 0);

	Channel = &InstancePtr->Audio[ChannelNum];
	Channel->Buffer = Buffer;

	if(Channel->Current == NULL) {
		Channel->TriggerStatus = XDPDMA_TRIGGER_EN;
		Channel->Current = &Channel->Descriptor0;
		Channel->Used = 0;
	}

else if(Channel->Current == &Channel->Descriptor0) {
		/* Check if descriptor chain can be updated */
		if(Channel->Descriptor1.MSB_Timestamp >>
		   XDPDMA_DESC_DONE_SHIFT) {
			Channel->Current = NULL;
			return XST_FAILURE;
		}
		else if(Channel->Descriptor7.MSB_Timestamp >>
			XDPDMA_DESC_DONE_SHIFT || !(Channel->Used)) {
			Channel->Descriptor3.Control = XDPDMA_DESC_PREAMBLE |
				XDPDMA_DESC_UPDATE | XDPDMA_DESC_IGNR_DONE;
			Channel->Descriptor3.NEXT_DESR =
				(INTPTR) &Channel->Descriptor4;
			Channel->Descriptor3.ADDR_EXT &=
				~XDPDMA_DESCRIPTOR_ADDR_EXT_DSC_NXT_MASK;
			Channel->Descriptor3.ADDR_EXT |=
				(INTPTR) &Channel->Descriptor4 >> 32;
			Channel->Current = &Channel->Descriptor4;
			Channel->Used = 1;
			XDpDma_InitAudioDescriptor(Channel, Buffer);
		}
		else {
			return XST_FAILURE;
		}
	}

	else if(Channel->Current == &Channel->Descriptor4)  {
		/* Check if descriptor chain can be updated */
		if(Channel->Descriptor5.MSB_Timestamp >>
		   XDPDMA_DESC_DONE_SHIFT) {
			Channel->Current = NULL;
			return XST_FAILURE;
		}
		else if(Channel->Descriptor3.MSB_Timestamp >>
			XDPDMA_DESC_DONE_SHIFT) {
			Channel->Descriptor7.Control = XDPDMA_DESC_PREAMBLE |
				XDPDMA_DESC_UPDATE | XDPDMA_DESC_IGNR_DONE;
			Channel->Descriptor7.NEXT_DESR =
				(INTPTR) &Channel->Descriptor0;
			Channel->Descriptor7.ADDR_EXT &=
				~XDPDMA_DESCRIPTOR_ADDR_EXT_DSC_NXT_MASK;
			Channel->Descriptor7.ADDR_EXT |=
				(INTPTR) &Channel->Descriptor0 >> 32;
			Channel->Current = &Channel->Descriptor0;
			XDpDma_InitAudioDescriptor(Channel, Buffer);
		}
		else {
			return XST_FAILURE;
		}
	}

	return XST_SUCCESS;

}
/*************************************************************************/
/**
 *
 * This function sets the channel with the latest framebuffer and the
 * available descriptor for transfer on the next Vsync.
 *
 * @param    InstancePtr is pointer to the instance of DPDMA.
 * @param    Channel indicates which channels are being setup for transfer.
 *
 * @return   None.
 *
 * @note     None.
 *
 **************************************************************************/
void XDpDma_SetupChannel(XDpDma *InstancePtr, XDpDma_ChannelType Channel)
{
	XDpDma_Channel *Chan;
	XDpDma_AudioChannel *AudChan;
	XDpDma_FrameBuffer *FB;
	XDpDma_AudioBuffer *AudioBuffer;
	u8 Index, NumPlanes;
	Xil_AssertVoid(InstancePtr != NULL);

	switch(Channel) {
		case VideoChan:
			Xil_AssertVoid(InstancePtr->Video.VideoInfo != NULL);
			Xil_AssertVoid(InstancePtr->Video.FrameBuffer != NULL);
			NumPlanes = InstancePtr->Video.VideoInfo->Mode;
			for(Index = 0; Index <= NumPlanes; Index++) {
				Chan = &InstancePtr->Video.Channel[Index];
				FB = InstancePtr->Video.FrameBuffer[Index];
				XDpDma_UpdateVideoDescriptor(Chan);
				XDpDma_InitVideoDescriptor(Chan->Current, FB);
				XDpDma_SetDescriptorAddress(InstancePtr,
							    Index);
			}
			break;

		case GraphicsChan:
			Xil_AssertVoid(InstancePtr->Gfx.VideoInfo != NULL);
			Xil_AssertVoid(InstancePtr->Gfx.FrameBuffer != NULL);
			Chan = &InstancePtr->Gfx.Channel;
			FB = InstancePtr->Gfx.FrameBuffer;
			XDpDma_UpdateVideoDescriptor(Chan);
			XDpDma_InitVideoDescriptor(Chan->Current, FB);
			XDpDma_SetDescriptorAddress(InstancePtr,
						    XDPDMA_GRAPHICS_CHANNEL);
			break;

		case AudioChan0:
			Xil_AssertVoid(InstancePtr->Audio[0].Buffer != NULL);
			AudChan = &InstancePtr->Audio[0];
			AudioBuffer = InstancePtr->Audio[0].Buffer;
			XDpDma_InitAudioDescriptor(AudChan, AudioBuffer);
			XDpDma_SetDescriptorAddress(InstancePtr,
						    XDPDMA_AUDIO_CHANNEL0);
			break;
		case AudioChan1:
			Xil_AssertVoid(InstancePtr->Audio[1].Buffer != NULL);
			AudChan = &InstancePtr->Audio[1];
			AudioBuffer = InstancePtr->Audio[1].Buffer;
			XDpDma_InitAudioDescriptor(AudChan, AudioBuffer);
			XDpDma_SetDescriptorAddress(InstancePtr,
						    XDPDMA_AUDIO_CHANNEL1);
			break;
	}
}
