/*******************************************************************************
 *
 * Copyright (C) 2017 Xilinx, Inc.  All rights reserved.
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
/******************************************************************************/
/**
 *
 * @file xavbuf.c
 *
 * This file implements all the functions related to the Video Pipeline of the
 * DisplayPort Subsystem. See xavbuf.h for the detailed description of the
 * driver.
 *
 * @note	None.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- -----------------------------------------------
 * 1.0   aad  06/24/17 Initial release.
 * 2.0   aad  10/08/17 Some APIs to use enums instead of Macros.
 *		       Some bug fixes.
 * </pre>
 *
*******************************************************************************/
/******************************* Include Files ********************************/
#include "xavbuf.h"
#include "xstatus.h"

/**************************** Constant Definitions ****************************/
const XAVBuf_VideoAttribute XAVBuf_SupportedFormats[XAVBUF_NUM_SUPPORTED];

/******************************************************************************/
/**
 * This function sets the scaling factors depending on the source video stream.
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 * @param	RegOffset is the register offset of the SF0 register from the
 *		DP BaseAddress.
 * @param	Scaling Factors is a pointer to the scaling factors needed for
 *		scaling colors to 12 BPC.
 *
 * @return	None.
 *
 * @note	None.
 *
*******************************************************************************/
static void XAVBuf_SetScalingFactors(XAVBuf *InstancePtr, u32 RegOffset,
				     u32 *ScalingFactors)
{
	u32 Index = 0;
	for (Index = 0; Index < 3; Index++) {
		XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
				RegOffset + (Index * 4), ScalingFactors[Index]);
	}

}

/******************************************************************************/
/**
 * This function sets the Layer Control for Video and Graphics layers.
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 * @param	RegOffset is the register offset of Video Layer or Graphics
 *		Layer from the base address
 * @param	Video is a pointer to the XAVBuf_VideoAttribute struct which
 *		has been configured for the particular layer
 *
 * @return	None.
 *
 * @note	None.
 *
*******************************************************************************/
static void XAVBuf_SetLayerControl(XAVBuf *InstancePtr, u32 RegOffset,
					   XAVBuf_VideoAttribute *Video)
{
	u32 RegVal = 0;

	RegVal = (Video->IsRGB <<
		  XAVBUF_V_BLEND_LAYER0_CONTROL_RGB_MODE_SHIFT) |
		  Video->SamplingEn;

	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, RegOffset, RegVal);
}

/******************************************************************************/
/**
 * This function applies Attributes for Live source(Video/Graphics).
 *
 * @param	InstancePtr is an pointer to the XAVBuf Instance.
 * @param	RegConfig is a register offset for Video or Graphics config
 *		register
 * @param	Video is a pointer to the attributes of the video to be applied
 *
 * @return	None.
 *
 * @note	Live source can be live Video or Live Graphics.
******************************************************************************/
static void XAVBuf_SetLiveVideoAttributes(XAVBuf *InstancePtr, u32 RegConfig,
						XAVBuf_VideoAttribute *Video)
{
	u32 RegVal = 0;

	RegVal |= Video->Value << XAVBUF_BUF_LIVE_VID_CFG_FORMAT_SHIFT;
	RegVal |= Video->BPP/6 - 3;
	RegVal |= Video->Swap << XAVBUF_BUF_LIVE_VID_CFG_CB_FIRST_SHIFT;
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, RegConfig, RegVal);
}

/******************************************************************************/
/**
 * This function applies Attributes for Non - Live source(Video/Graphics).
 *
 * @param	InstancePtr is an pointer to the XAVBuf Instance.
 * @param	VideoSrc is the source of the Non-Live Video
 * @param	Video is a pointer to the attributes of the video to be applied
 *
 * @return	None.
 *
 * @note	Non Live source can be Non Live Video or Non Live Graphics.
******************************************************************************/
static void XAVBuf_SetNonLiveVideoAttributes(XAVBuf *InstancePtr, u32 VideoSrc,
					     XAVBuf_VideoAttribute *Video)
{
	u32 RegVal = 0;

	RegVal = XAVBuf_ReadReg(InstancePtr->Config.BaseAddr,
							XAVBUF_BUF_FORMAT);
	if(VideoSrc == XAVBUF_VIDSTREAM1_NONLIVE) {
		RegVal &= ~XAVBUF_BUF_FORMAT_NL_VID_FORMAT_MASK;
		RegVal |= Video->Value;
	}
	else if (VideoSrc == XAVBUF_VIDSTREAM2_NONLIVE_GFX) {
		RegVal &= ~XAVBUF_BUF_FORMAT_NL_GRAPHX_FORMAT_MASK;
		RegVal |= (Video->Value) <<
			XAVBUF_BUF_FORMAT_NL_GRAPHX_FORMAT_SHIFT;
	}

	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_BUF_FORMAT,
			RegVal);
}

/******************************************************************************/
/**
 * This function programs the coeffitients for Color Space Conversion.
 *
 * @param	InstancePtr is an pointer to the XAVBuf Instance.
 * @param	RegOffset is a register offset for Video or Graphics config
 *		register
 * @param	Video is a pointer to the XAVBuf_Attribute structure
 *
 * @return	None.
 *
 * @note	None.
******************************************************************************/
static void XAVBuf_InConvertToRGB(XAVBuf *InstancePtr, u32 RegOffset,
						XAVBuf_VideoAttribute *Video)
{
	u16 Index;
	u16 *CSCMatrix;
	u16 *OffsetMatrix;

	/* SDTV Coefficients */
	u16 CSCCoeffs[] = { 0x1000, 0x0000, 0x166F,
			    0x1000, 0x7A7F, 0x7493,
			    0x1000, 0x1C5A, 0x0000 };
	u16 CSCOffset[] = { 0x0000, 0x1800, 0x1800 };
	u16 RGBCoeffs[] = { 0x1000, 0x0000, 0x0000,
			    0x0000, 0x1000, 0x0000,
			    0x0000, 0x0000, 0x1000 };
	u16 RGBOffset[] = { 0x0000, 0x0000, 0x0000 };
	if(Video->IsRGB) {
		CSCMatrix = RGBCoeffs;
		OffsetMatrix = RGBOffset;
	}
	else {
		CSCMatrix = CSCCoeffs;
		OffsetMatrix = CSCOffset;
	}
	/* Program Colorspace conversion coefficients */
	for (Index = 9; Index < 12; Index++) {
		XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
				RegOffset + (Index * 4),
				OffsetMatrix[Index - 9]);
	}

	/* Program Colorspace conversion matrix */
	for (Index = 0; Index < 9; Index++) {
		XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
				RegOffset + (Index * 4), CSCMatrix[Index]);
	}

}

/******************************************************************************/
/**
 * This function converts the Blender output to the desired output format.
 *
 * @param	InstancePtr is an pointer to the XAVBuf Instance.
 * @param	RegConfig is a register offset for Video or Graphics config
 *		register
 * @param	Video is a pointer to the XAVBuf_Attribute structure
 *
 * @return	None.
 *
 * @note	None.
******************************************************************************/
static void XAVBuf_InConvertToOutputFormat(XAVBuf *InstancePtr,
						XAVBuf_VideoAttribute *Video)

{	u32 Index = 0;
	u32 RegOffset = XAVBUF_V_BLEND_RGB2YCBCR_COEFF0;
	u32 ColorOffset = XAVBUF_V_BLEND_LUMA_OUTCSC_OFFSET;
	u8 Value = Video->Value;
	u16 *MatrixCoeff;
	u16 *MatrixOffset;

	/* SDTV Coeffitients */
	u16 CSCCoeffs[] = { 0x04C8, 0x0964, 0x01D3,
			    0x7D4C, 0x7AB4, 0x0800,
			    0x0800, 0x7945, 0x7EB5 };
	u16 CSCOffset[] = { 0x0000, 0x800, 0x800 };
	u16 RGBCoeffs[] = { 0x1000, 0x0000, 0x0000,
			    0x0000, 0x1000, 0x0000,
			    0x0000, 0x0000, 0x1000 };
	u16 RGBOffset[] = { 0x0000, 0x0000, 0x0000 };


	if(Value) {
		MatrixCoeff = CSCCoeffs;
		MatrixOffset = CSCOffset;

	}
	else {
		MatrixCoeff = RGBCoeffs;
		MatrixOffset = RGBOffset;
	}

	for (Index = 0; Index < 9; Index++) {
		XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
			RegOffset + (Index * 4), MatrixCoeff[Index]);
	}
	for (Index = 0; Index < 3; Index++) {
		XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
			ColorOffset + (Index * 4),
			(MatrixOffset[Index] <<
			XAVBUF_V_BLEND_LUMA_IN1CSC_OFFSET_POST_OFFSET_SHIFT));
	}
}
/******************************************************************************/
/**
 * This function configures the Video Pipeline for the selected source
 *
 * @param	InstancePtr is an pointer to the XAVBuf Instance.
 * @param	VideoSrc is a parameter which indicates which Video Source
 *		selected
 *
 * @return	None.
 *
 * @note	None.
******************************************************************************/
static int XAVBuf_ConfigureVideo(XAVBuf *InstancePtr, u8 VideoSrc)
{

	u32 RegConfig = 0;
	u32 ScalingOffset = 0;
	u32 LayerOffset = 0;
	u32 CSCOffset = 0;
	XAVBuf_VideoAttribute *Video = NULL;
	u32 *ScalingFactors = NULL;

	Xil_AssertNonvoid(InstancePtr != NULL);
	switch(VideoSrc) {
		case XAVBUF_VIDSTREAM1_LIVE:
			RegConfig = XAVBUF_BUF_LIVE_VID_CFG;
			ScalingOffset = XAVBUF_BUF_LIVE_VID_COMP0_SF;
			LayerOffset = XAVBUF_V_BLEND_LAYER0_CONTROL;
			CSCOffset = XAVBUF_V_BLEND_IN1CSC_COEFF0;
			Video = InstancePtr->AVMode.LiveVideo;
			ScalingFactors = Video->SF;

			/* Set the Video Attributes */
			XAVBuf_SetLiveVideoAttributes(InstancePtr, RegConfig,
						      Video);
			break;

		case XAVBUF_VIDSTREAM2_LIVE_GFX:
			RegConfig = XAVBUF_BUF_LIVE_GFX_CFG;
			ScalingOffset = XAVBUF_BUF_LIVE_GFX_COMP0_SF;
			LayerOffset = XAVBUF_V_BLEND_LAYER1_CONTROL;
			CSCOffset = XAVBUF_V_BLEND_IN2CSC_COEFF0;
			Video = InstancePtr->AVMode.LiveGraphics;
			ScalingFactors = Video->SF;

			/* Set the Video Attributes */
			XAVBuf_SetLiveVideoAttributes(InstancePtr, RegConfig,
						      Video);
			break;

		case XAVBUF_VIDSTREAM1_NONLIVE:
			RegConfig = XAVBUF_BUF_LIVE_GFX_CFG;
			ScalingOffset = XAVBUF_BUF_VID_COMP0_SCALE_FACTOR;
			LayerOffset = XAVBUF_V_BLEND_LAYER0_CONTROL;
			CSCOffset = XAVBUF_V_BLEND_IN1CSC_COEFF0;
			Video = InstancePtr->AVMode.NonLiveVideo;
			ScalingFactors = Video->SF;

			/* Set the Video Attributes */
			XAVBuf_SetNonLiveVideoAttributes(InstancePtr, VideoSrc,
							 Video);
			break;

		case XAVBUF_VIDSTREAM2_NONLIVE_GFX:
			RegConfig = XAVBUF_BUF_LIVE_GFX_CFG;
			ScalingOffset = XAVBUF_BUF_GRAPHICS_COMP0_SCALE_FACTOR;
			LayerOffset = XAVBUF_V_BLEND_LAYER1_CONTROL;
			CSCOffset = XAVBUF_V_BLEND_IN2CSC_COEFF0;
			Video = InstancePtr->AVMode.NonLiveGraphics;
			ScalingFactors = Video->SF;

			/* Set the Video Attributes */
			XAVBuf_SetNonLiveVideoAttributes(InstancePtr, VideoSrc,
							 Video);
			break;
		case XAVBUF_VIDSTREAM1_TPG:
			RegConfig |= 1 <<
				XAVBUF_V_BLEND_LAYER0_CONTROL_RGB_MODE_SHIFT;
			RegConfig |= 1 <<
				XAVBUF_V_BLEND_LAYER0_CONTROL_BYPASS_SHIFT;
			XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
					XAVBUF_V_BLEND_LAYER0_CONTROL,
					RegConfig);
			break;
		default:
			return XST_FAILURE;
	}
	/* Setting the scaling factors */
	XAVBuf_SetScalingFactors(InstancePtr, ScalingOffset, ScalingFactors);
	/* Layer Control */
	XAVBuf_SetLayerControl(InstancePtr, LayerOffset, Video);
	/* Colorspace conversion */
	XAVBuf_InConvertToRGB(InstancePtr, CSCOffset, Video);
	return XST_SUCCESS;
}

/******************************************************************************/
/**
 * This function intializes the configuration for the AVBuf Instance.
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 * @param	BaseAddr sets the base address of the AVBuf instance
 * @param	Deviceid is the id of the device from the design.
 *
 * @return	None.
 *
 * @note	Base address and DeviceId is same as the DP Core driver.
 *
*******************************************************************************/
void XAVBuf_CfgInitialize(XAVBuf *InstancePtr, u32 BaseAddr, u16 DeviceId)
{
	Xil_AssertVoid(InstancePtr != NULL);

	InstancePtr->Config.DeviceId = DeviceId;
	InstancePtr->Config.BaseAddr = BaseAddr;
}

/******************************************************************************/
/**
 * This function initializes all the data structures of the XAVBuf Instance.
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 *
 * @return	None.
 *
 * @note	None.
 *
*******************************************************************************/
void XAVBuf_Initialize(XAVBuf *InstancePtr)
{
	Xil_AssertVoid(InstancePtr != NULL);

	InstancePtr->AVMode.NonLiveVideo = NULL;
	InstancePtr->AVMode.LiveVideo = NULL;
	InstancePtr->AVMode.LiveGraphics = NULL;
	InstancePtr->AVMode.NonLiveGraphics = NULL;
	InstancePtr->AVMode.VideoSrc = XAVBUF_VIDSTREAM1_NONE;
	InstancePtr->AVMode.GraphicsSrc = XAVBUF_VIDSTREAM2_NONE;
	InstancePtr->AVMode.Audio = NULL;
	InstancePtr->AVMode.GraphicsAudio = NULL;
	InstancePtr->AVMode.AudioSrc1 = XAVBUF_AUDSTREAM1_NO_AUDIO;
	InstancePtr->AVMode.AudioSrc2 = XAVBUF_AUDSTREAM2_NO_AUDIO;

	InstancePtr->Blender.GlobalAlphaEn = 0;
	InstancePtr->Blender.Alpha = 0;
	InstancePtr->Blender.OutputVideo = NULL;

	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_AUD_SOFT_RST, 0);
}

/******************************************************************************/
/**
 * This function selects the source for the Video and Graphics streams that are
 * passed on to the blender block.
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 * @param	VidStream selects the stream coming from the video sources
 * @param	GfxStream selects the stream coming from the graphics sources
 *
 * @return	None.
 *
 * @note	None.
 *
*******************************************************************************/
void XAVBuf_InputVideoSelect(XAVBuf *InstancePtr, XAVBuf_VideoStream VidStream,
			      XAVBuf_GfxStream GfxStream)
{


	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid((VidStream != XAVBUF_VIDSTREAM1_LIVE) |
		       (VidStream != XAVBUF_VIDSTREAM1_NONLIVE) |
		       (VidStream != XAVBUF_VIDSTREAM1_TPG) |
		       (VidStream != XAVBUF_VIDSTREAM1_NONE));
	Xil_AssertVoid((GfxStream != XAVBUF_VIDSTREAM2_DISABLEGFX) |
		       (GfxStream != XAVBUF_VIDSTREAM2_NONLIVE_GFX) |
		       (GfxStream != XAVBUF_VIDSTREAM2_LIVE_GFX) |
		       (GfxStream != XAVBUF_VIDSTREAM2_NONE));

	InstancePtr->AVMode.VideoSrc = VidStream;
	InstancePtr->AVMode.GraphicsSrc = GfxStream;
	u32 RegVal;
	RegVal = XAVBuf_ReadReg(InstancePtr->Config.BaseAddr,
			XAVBUF_BUF_OUTPUT_AUD_VID_SELECT);
	RegVal &= ~(XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_VID_STREAM2_SEL_MASK |
			XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_VID_STREAM1_SEL_MASK);
	RegVal |= VidStream | GfxStream;
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
			XAVBUF_BUF_OUTPUT_AUD_VID_SELECT, RegVal);
}

/******************************************************************************/
/**
 * This function sets the video format for the non-live video
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 * @param	Format is the enum for the non-live video format
 *
 * @return	XST_SUCCESS if the correct format has been set.
 *		XST_FAILURE if the format is invalid.
 *
 * @note	None.
*******************************************************************************/
int XAVBuf_SetInputNonLiveVideoFormat(XAVBuf *InstancePtr,
				       XAVBuf_VideoFormat Format)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((Format >= CbY0CrY1) | (Format <= YV16Ci2_420_10BPC));

	InstancePtr->AVMode.NonLiveVideo =
		XAVBuf_GetNLiveVideoAttribute(Format);
	if(InstancePtr->AVMode.NonLiveVideo == NULL)
		return XST_FAILURE;

	return XST_SUCCESS;
}

/******************************************************************************/
/**
 * This function sets the graphics format for the non-live video
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 * @param	Format is the enum for the non-live video format
 *
 * @return	XST_SUCCESS if the correct format has been set.
 *		XST_FAILURE if the format is invalid.
 *
 * @note	None.
*******************************************************************************/
int XAVBuf_SetInputNonLiveGraphicsFormat(XAVBuf *InstancePtr,
				       XAVBuf_VideoFormat Format)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((Format >= RGBA8888) |( Format <= YOnly));

	InstancePtr->AVMode.NonLiveGraphics =
		XAVBuf_GetNLGraphicsAttribute(Format);
	if(InstancePtr->AVMode.NonLiveGraphics == NULL)
		return XST_FAILURE;

	return XST_SUCCESS;
}

/******************************************************************************/
/**
 * This function sets the video format for the live video
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 * @param	Format is the enum for the non-live video format
 *
 * @return	XST_SUCCESS if the correct format has been set.
 *		XST_FAILURE if the format is invalid.
 *
 * @note	None.
*******************************************************************************/
int XAVBuf_SetInputLiveVideoFormat(XAVBuf *InstancePtr,
				       XAVBuf_VideoFormat Format)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((Format >= RGB_6BPC) | (Format <= YOnly_12BPC));

	InstancePtr->AVMode.LiveVideo = XAVBuf_GetLiveVideoAttribute(Format);
	if(InstancePtr->AVMode.LiveVideo == NULL)
		return XST_FAILURE;

	return XST_SUCCESS;
}

/******************************************************************************/
/**
 * This function sets the graphics format for the live video
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 * @param	Format is the enum for the non-live video format
 *
 * @return	XST_SUCCESS if the correct format has been set.
 *		XST_FAILURE if the format is invalid.
 *
 * @note	None.
*******************************************************************************/
int XAVBuf_SetInputLiveGraphicsFormat(XAVBuf *InstancePtr,
				       XAVBuf_VideoFormat Format)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((Format >= RGB_6BPC) | (Format <= YOnly_12BPC));

	InstancePtr->AVMode.LiveGraphics =
		XAVBuf_GetLiveVideoAttribute(Format);
	if(InstancePtr->AVMode.LiveGraphics == NULL)
		return XST_FAILURE;

	return XST_SUCCESS;
}

/******************************************************************************/
/**
 * This function sets the Output Video Format
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 * @param	Format is the enum for the non-live video format
 *
 * @return	XST_SUCCESS if the correct format has been set.
 *		XST_FAILURE if the format is invalid.
 *
 * @note	None.
*******************************************************************************/
int XAVBuf_SetOutputVideoFormat(XAVBuf *InstancePtr, XAVBuf_VideoFormat Format)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((Format >= RGB_6BPC) | (Format <= YOnly_12BPC));

	InstancePtr->Blender.OutputVideo =
		XAVBuf_GetLiveVideoAttribute(Format);
	if(InstancePtr->Blender.OutputVideo == NULL)
		return XST_FAILURE;
	else
		return XST_SUCCESS;
}

/******************************************************************************/
/**
 * This function sets the Audio and Video Clock Source and the video timing
 * source.
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 * @param	VideoClk selects the Video Clock Source
 * @param	AudioClk selects the Audio Clock Source
 *
 * @return	None.
 *
 * @note	System uses PL Clock for Video when Live source is in use.
 *
*******************************************************************************/
void XAVBuf_SetAudioVideoClkSrc(XAVBuf *InstancePtr, u8 VideoClk, u8 AudioClk)
{

	u32 RegVal = 0;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid((VideoClk != XAVBUF_PS_CLK) |
			(VideoClk!= XAVBUF_PL_CLK));
	Xil_AssertVoid((AudioClk != XAVBUF_PS_CLK) |
		       (AudioClk!= XAVBUF_PL_CLK));

	if((InstancePtr->AVMode.VideoSrc != XAVBUF_VIDSTREAM1_LIVE) &&
	   (InstancePtr->AVMode.GraphicsSrc != XAVBUF_VIDSTREAM2_LIVE_GFX)) {
		RegVal = 1 <<
			XAVBUF_BUF_AUD_VID_CLK_SOURCE_VID_TIMING_SRC_SHIFT;
	}
	else if((InstancePtr->AVMode.VideoSrc == XAVBUF_VIDSTREAM1_LIVE) ||
		(InstancePtr->AVMode.GraphicsSrc ==
		 XAVBUF_VIDSTREAM2_LIVE_GFX)) {
		VideoClk = XAVBUF_PL_CLK;
	}

	RegVal |= (VideoClk <<
			XAVBUF_BUF_AUD_VID_CLK_SOURCE_VID_CLK_SRC_SHIFT) |
		(AudioClk <<
			XAVBUF_BUF_AUD_VID_CLK_SOURCE_AUD_CLK_SRC_SHIFT);
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
			XAVBUF_BUF_AUD_VID_CLK_SOURCE, RegVal);
	/*Soft Reset VideoPipeline when changing the clock source*/
	XAVBuf_SoftReset(InstancePtr);
}

/******************************************************************************/
/**
 * This function applies a soft reset to the Audio Video pipeline.
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 *
 * @return	None.
 *
 * @note	None.
 *
*******************************************************************************/
void XAVBuf_SoftReset(XAVBuf *InstancePtr)
{
	Xil_AssertVoid(InstancePtr != NULL);

	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_BUF_SRST_REG,
					XAVBUF_BUF_SRST_REG_VID_RST_MASK);
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_BUF_SRST_REG, 0);
}

/******************************************************************************/
/**
 * This function looks up if the video format is valid or not for the non-live
 * video datapath and returns a pointer to the attributes of the video.
 *
 * @param	Format takes in the video format for which attributes are being
 *		requested.
 *
 * @return	A pointer to the structure XAVBuf_VideoAttribute if the video
 *		format is valid, else returns NULL.
 * @note	None.
*******************************************************************************/
XAVBuf_VideoAttribute *XAVBuf_GetLiveVideoAttribute(XAVBuf_VideoFormat Format)
{
	u8 Index = 0;
	XAVBuf_VideoAttribute *VideoAttribute;
	Xil_AssertNonvoid((Format >= RGB_6BPC) |  (Format <= YOnly_12BPC));

	for (Index = RGB_6BPC; Index <= YOnly_12BPC; Index++) {
		VideoAttribute = (XAVBuf_VideoAttribute *)
					&XAVBuf_SupportedFormats[Index];
		if(Format == VideoAttribute->VideoFormat) {
			return VideoAttribute;
		}
	}
	return NULL;
}

/******************************************************************************/
/**
 * This function looks up if the video format is valid or not and returns a
 * pointer to the attributes of the video.
 *
 * @param	Format takes in the video format for which attributes are being
 *		requested.
 *
 * @return	A pointer to the structure XAVBuf_VideoAttribute if the video
 *		format is valid, else returns NULL.
 * @note	None.
*******************************************************************************/
XAVBuf_VideoAttribute *XAVBuf_GetNLiveVideoAttribute(XAVBuf_VideoFormat Format)
{
	u8 Index = 0;
	XAVBuf_VideoAttribute *VideoAttribute;

	Xil_AssertNonvoid((Format >= CbY0CrY1) | (Format <= YV16Ci2_420_10BPC));

	for (Index = CbY0CrY1; Index <= YV16Ci2_420_10BPC; Index++) {
		VideoAttribute = (XAVBuf_VideoAttribute *)
					&XAVBuf_SupportedFormats[Index];
		if(Format == VideoAttribute->VideoFormat) {
			return VideoAttribute;
		}
	}
	return NULL;
}

/******************************************************************************/
/**
 * This function looks up if the video format is valid or not and returns a
 * pointer to the attributes of the video.
 *
 * @param	Format takes in the video format for which attributes are being
 *		requested.
 *
 * @return	A pointer to the structure XAVBuf_VideoAttribute if the video
 *		format is valid, else returns NULL.
 * @note	None.
*******************************************************************************/
XAVBuf_VideoAttribute *XAVBuf_GetNLGraphicsAttribute(XAVBuf_VideoFormat Format)
{
	u32 Index = 0;
	XAVBuf_VideoAttribute *VideoAttribute;

	Xil_AssertNonvoid((Format >= RGBA8888) | (Format <= YOnly));

	for(Index = RGBA8888; Index <= YOnly; Index++) {
		VideoAttribute = (XAVBuf_VideoAttribute *)
					&XAVBuf_SupportedFormats[Index];
		if(Format == VideoAttribute->VideoFormat) {
			return VideoAttribute;
		}
	}
	return NULL;
}

/******************************************************************************/
/**
 * This function configures the Video Pipeline
 *
 * @param	InstancePtr is an pointer to the XAVBuf Instance.
 *
 * @return	None.
 *
 * @note	None.
******************************************************************************/
void XAVBuf_ConfigureVideoPipeline(XAVBuf *InstancePtr)
{
	Xil_AssertVoid(InstancePtr != NULL);

	XAVBuf_ConfigureVideo(InstancePtr, InstancePtr->AVMode.VideoSrc);
}

/******************************************************************************/
/**
 * This function configures the Graphics Pipeline
 *
 * @param	InstancePtr is an pointer to the XAVBuf Instance.
 *
 * @return	None.
 *
 * @note	None.
******************************************************************************/
void XAVBuf_ConfigureGraphicsPipeline(XAVBuf *InstancePtr)
{
	Xil_AssertVoid(InstancePtr != NULL);
	XAVBuf_ConfigureVideo(InstancePtr, InstancePtr->AVMode.GraphicsSrc);
}

/******************************************************************************/
/**
 * This function sets the blender background color
 *
 * @param	InstancePtr is an pointer to the XAVBuf Instance.
 * @param	Color is a pointer to the structure XAVBuf_BlenderBgClr
 *
 * @return	None.
 *
 * @note	None.
******************************************************************************/
void XAVBuf_BlendSetBgColor(XAVBuf *InstancePtr, XAVBuf_BlenderBgClr *Color)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Color != NULL);

	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_V_BLEND_BG_CLR_0,
			Color->RCr);
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_V_BLEND_BG_CLR_1,
			Color->GY);
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_V_BLEND_BG_CLR_2,
			Color->BCb);
}

/******************************************************************************/
/**
 * This function enables or disables global alpha
 *
 * @param	InstancePtr is an pointer to the XAVBuf Instance.
 * @param	Enable sets a software flag for global alpha
 * @param	Alpha sets the value for the global alpha blending
 *
 * @return	None.
 *
 * @note	GlobalAlphaEn = 1, enables the global alpha.
 *		GlobalAlphaEn = 0, disables the global alpha.
 *		Alpha = 0, passes stream2
 *		Alpha = 255, passes stream1
******************************************************************************/
void XAVBuf_SetBlenderAlpha(XAVBuf *InstancePtr, u8 Alpha, u8 Enable)
{
	u32 RegVal;
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid((Enable !=0) | (Enable != 1));

	InstancePtr->Blender.GlobalAlphaEn = Enable;
	InstancePtr->Blender.Alpha = Alpha;

	RegVal = Enable;
	RegVal |= Alpha << XAVBUF_V_BLEND_SET_GLOBAL_ALPHA_REG_VALUE_SHIFT;

	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
			XAVBUF_V_BLEND_SET_GLOBAL_ALPHA_REG, RegVal);
}

/******************************************************************************/
/**
 * This function configures the Output of the Video Pipeline
 *
 * @param	InstancePtr is an pointer to the XAVBuf Instance.
 * @param	OutputVideo is a pointer to the XAVBuf_VideoAttribute.
 *
 * @return	None.
 *
 * @note	None.
******************************************************************************/
void XAVBuf_ConfigureOutputVideo(XAVBuf *InstancePtr)
{
	u32 RegVal = 0;
	XAVBuf_VideoAttribute *OutputVideo = InstancePtr->Blender.OutputVideo;

	RegVal |= OutputVideo->SamplingEn <<
			XAVBUF_V_BLEND_OUTPUT_VID_FORMAT_EN_DOWNSAMPLE_SHIFT;
	RegVal |= OutputVideo->Value;
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
			XAVBUF_V_BLEND_OUTPUT_VID_FORMAT, RegVal);

	XAVBuf_InConvertToOutputFormat(InstancePtr, OutputVideo);
}

/******************************************************************************/
/**
 * This function selects the source for audio streams corresponding to the
 * Video and Graphics streams that are passed on to the blender
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 * @param	AudStream1 selects the audio stream source corresponding to
 *		the video source selected
 * @param	AudStream2 selects the audio stream source corresponding to
 *		the graphics source selected.
 *
 * @return	None.
 *
 * @note	None.
 *
*******************************************************************************/
void XAVBuf_InputAudioSelect(XAVBuf *InstancePtr, XAVBuf_AudioStream1 AudStream1,
			      XAVBuf_AudioStream2 AudStream2)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid((AudStream1 != XAVBUF_AUDSTREAM1_NONLIVE) |
		       (AudStream1 != XAVBUF_AUDSTREAM1_LIVE) |
		       (AudStream1 != XAVBUF_AUDSTREAM1_TPG));
	Xil_AssertVoid((AudStream2 != XAVBUF_AUDSTREAM2_NO_AUDIO) |
		       (AudStream2 != XAVBUF_AUDSTREAM2_AUDIOGFX));

	u32 RegVal;
	RegVal = XAVBuf_ReadReg(InstancePtr->Config.BaseAddr,
			XAVBUF_BUF_OUTPUT_AUD_VID_SELECT);
	RegVal &= ~(XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_AUD_STREAM2_SEL_MASK |
			XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_AUD_STREAM1_SEL_MASK);
	RegVal |= AudStream1 | AudStream2;

	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
			XAVBUF_BUF_OUTPUT_AUD_VID_SELECT, RegVal);
}

/******************************************************************************/
/**
 * This function sets up the scaling factor for Audio Mixer Volume Control.
 *
 * @param	InstancePtr is a pointer to the XAVBuf instance.
 * @param	Channel0Volume is the volume to be set for Audio from Channel0
 * @param	Channel1Volume is the volume to be set for Audio from Channel1
 *
 *
 * @return	None.
 *
 * @note	None.
 *
*******************************************************************************/
void XAVBuf_AudioMixerVolumeControl(XAVBuf *InstancePtr, u8 Channel0Volume,
					u8 Channel1Volume)
{
	u32 Val;
	Xil_AssertVoid(InstancePtr != NULL);
	Val = Channel1Volume <<
		XAVBUF_AUD_MIXER_VOLUME_CONTROL_VOL_CTRL_CH1_SHIFT;
	Val |= Channel0Volume;
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
			XAVBUF_AUD_MIXER_VOLUME_CONTROL, Val);
}

/******************************************************************************/
/**
 * This function resets the Audio Pipe.
 *
 * @param	InstancePtr is a  pointer to the XAVBuf Instance.
 *
 * @returns	None.
 *
 * @note	Needed when non-live audio is disabled.
 *
 *
 ******************************************************************************/
void XAVBuf_AudioSoftReset(XAVBuf *InstancePtr)
{
	u32 RegVal = 0;
	Xil_AssertVoid(InstancePtr != NULL);
	RegVal = XAVBuf_ReadReg(InstancePtr->Config.BaseAddr,
				XAVBUF_AUD_SOFT_RST);
	RegVal |= XAVBUF_AUD_SOFT_RST_AUD_SRST_MASK;
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_AUD_SOFT_RST,
			RegVal);
	RegVal &= ~XAVBUF_AUD_SOFT_RST_AUD_SRST_MASK;
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_AUD_SOFT_RST, 0);

}

/******************************************************************************/
/**
 * This function enables End of Line Reset for reduced blanking resolutions.
 *
 * @param	InstancePtr is a  pointer to the XAVBuf Instance.
 * @param	Disable is to be set while using Reduced Blanking Resolutions.
 *
 * @returns	None.
 *
 * @note	None.
 *
 ******************************************************************************/
void XABuf_LineResetDisable(XAVBuf *InstancePtr, u8 Disable)
{
	u32 RegVal = 0;
	Xil_AssertVoid(InstancePtr != NULL);
	RegVal = XAVBuf_ReadReg(InstancePtr->Config.BaseAddr,
				XAVBUF_AUD_SOFT_RST);
	if(Disable)
		RegVal |= XAVBUF_AUD_SOFT_RST_LINE_RST_DISABLE_MASK;
	else
		RegVal &= ~XAVBUF_AUD_SOFT_RST_LINE_RST_DISABLE_MASK;

	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_AUD_SOFT_RST,
			RegVal);
}

/******************************************************************************/
/**
 * This function enables the video channel interface between the DPDMA and the
 * AVBuf
 *
 * @param	InstancePtr is a  pointer to the XAVBuf Instance.
 * @param	Enable sets the corresponding buffers.
 *
 * @returns	None.
 *
 * @note	None.
 *
 ******************************************************************************/
void XAVBuf_EnableVideoBuffers(XAVBuf *InstancePtr, u8 Enable)
{
	u8 Index;
	u32 RegVal = 0;
	u8 NumPlanes = InstancePtr->AVMode.NonLiveVideo->Mode;

	RegVal = (0xF << XAVBUF_CHBUF0_BURST_LEN_SHIFT) |
		(XAVBUF_CHBUF0_FLUSH_MASK);

	for (Index = 0; Index <= NumPlanes; Index++) {
		XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
				XAVBUF_CHBUF0 + (Index * 4), RegVal);
	}
	if(Enable) {
		RegVal = (0xF << XAVBUF_CHBUF0_BURST_LEN_SHIFT) |
		XAVBUF_CHBUF0_EN_MASK;
		for (Index = 0; Index <= NumPlanes; Index++) {
			XAVBuf_WriteReg(InstancePtr->Config.BaseAddr,
					XAVBUF_CHBUF0 + (Index * 4), RegVal);
		}
	}
}
/******************************************************************************/
/**
 * This function enables the graphics interface between the DPDMA and the AVBuf.
 *
 * @param	InstancePtr is a  pointer to the XAVBuf Instance.
 * @param	Enable sets the corresponding buffers.
 *
 * @returns	None.
 *
 * @note	None.
 *
 ******************************************************************************/
void XAVBuf_EnableGraphicsBuffers(XAVBuf *InstancePtr, u8 Enable)
{
	u32 RegVal = 0;

	RegVal = (0xF << XAVBUF_CHBUF3_BURST_LEN_SHIFT) |
		XAVBUF_CHBUF3_FLUSH_MASK;
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_CHBUF3, RegVal);
	if(Enable) {
		RegVal = (0xF << XAVBUF_CHBUF3_BURST_LEN_SHIFT) |
			XAVBUF_CHBUF0_EN_MASK;
		XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_CHBUF3,
				RegVal);
	}
}

/******************************************************************************/
/**
 * This function enables the audio interface between the DPDMA and the AVBuf
 *
 * @param	InstancePtr is a  pointer to the XAVBuf Instance.
 * @param	Enable sets the corresponding buffers.
 *
 * @returns	None.
 *
 * @note	None.
 *
 ******************************************************************************/
void XAVBuf_EnableAudio0Buffers(XAVBuf *InstancePtr, u8 Enable)
{
	u32 RegVal = 0;

	RegVal = (0x3 << XAVBUF_CHBUF4_BURST_LEN_SHIFT) |
		XAVBUF_CHBUF4_FLUSH_MASK;
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_CHBUF4, RegVal);
	if(Enable) {
		RegVal = (0x3 << XAVBUF_CHBUF4_BURST_LEN_SHIFT) |
			XAVBUF_CHBUF4_EN_MASK;
		XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_CHBUF4,
				RegVal);
	}
}

/******************************************************************************/
/**
 * This function enables the audio interface between the DPDMA and the AVBuf
 *
 * @param	InstancePtr is a  pointer to the XAVBuf Instance.
 * @param	Enable sets the corresponding buffers.
 *
 * @returns	None.
 *
 * @note	None.
 *
 ******************************************************************************/
void XAVBuf_EnableAudio1Buffers(XAVBuf *InstancePtr, u8 Enable)
{
	u32 RegVal = 0;

	RegVal = (0x3 << XAVBUF_CHBUF5_BURST_LEN_SHIFT) |
		XAVBUF_CHBUF5_FLUSH_MASK;
	XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_CHBUF5, RegVal);
	if(Enable) {
		RegVal = (0x3 << XAVBUF_CHBUF5_BURST_LEN_SHIFT) |
			XAVBUF_CHBUF5_EN_MASK;
		XAVBuf_WriteReg(InstancePtr->Config.BaseAddr, XAVBUF_CHBUF5,
				RegVal);
	}
}
