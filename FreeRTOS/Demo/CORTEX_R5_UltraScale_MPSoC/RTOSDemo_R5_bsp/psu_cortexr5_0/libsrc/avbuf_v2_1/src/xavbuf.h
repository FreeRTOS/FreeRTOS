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
 * @file xavbuf.h
 *
 * This file implements all the functions related to the Video Pipeline of the
 * DisplayPort Subsystem.
 *
 * Features supported by this driver
 *	- Live Video and Graphics input.
 *	- Non-Live Video Graphics input.
 *	- Output Formats Supported - RGB, YUV444, YUV4222.
 *
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- -----------------------------------------------
 * 1.0   aad  06/24/17 Initial release.
 * 2.0   aad  10/07/17 Added Enums for Video and Audio sources.
 * </pre>
 *
*******************************************************************************/
#ifndef XAVBUF_H_
/* Prevent circular inclusions by using protection macros. */
#define XAVBUF_H_


/******************************* Include Files ********************************/
#include "xavbuf_hw.h"
#include "sleep.h"
/****************************** Type Definitions ******************************/
/**
 * This typedef describes all the Video Formats supported by the driver
 */
typedef enum {
	//Non-Live Video Formats
	CbY0CrY1,
	CrY0CbY1,
	Y0CrY1Cb,
	Y0CbY1Cr,
	YV16,
	YV24,
	YV16Ci,
	MONOCHROME,
	YV16Ci2,
	YUV444,
	RGB888,
	RGBA8880,
	RGB888_10BPC,
	YUV444_10BPC,
	YV16Ci2_10BPC,
	YV16Ci_10BPC,
	YV16_10BPC,
	YV24_10BPC,
	MONOCHROME_10BPC,
	YV16_420,
	YV16Ci_420,
	YV16Ci2_420,
	YV16_420_10BPC,
	YV16Ci_420_10BPC,
	YV16Ci2_420_10BPC,

	// Non-Live Graphics formats
	RGBA8888,
	ABGR8888,
	RGB888_GFX,
	BGR888,
	RGBA5551,
	RGBA4444,
	RGB565,
	BPP8,
	BPP4,
	BPP2,
	BPP1,
	YUV422,
	YOnly,

	//Live Input/Output Video/Graphics Formats
	RGB_6BPC,
	RGB_8BPC,
	RGB_10BPC,
	RGB_12BPC,
	YCbCr444_6BPC,
	YCbCr444_8BPC,
	YCbCr444_10BPC,
	YCbCr444_12BPC,
	YCbCr422_8BPC,
	YCbCr422_10BPC,
	YCbCr422_12BPC,
	YOnly_8BPC,
	YOnly_10BPC,
	YOnly_12BPC,
} XAVBuf_VideoFormat;

/**
 * This data structure describes video planes.
 */
typedef enum {
	Interleaved,
	SemiPlanar,
	Planar
} XAVBuf_VideoModes;

/**
 * This typedef describes the video source list
 */
typedef enum {
	XAVBUF_VIDSTREAM1_LIVE,
	XAVBUF_VIDSTREAM1_NONLIVE,
	XAVBUF_VIDSTREAM1_TPG,
	XAVBUF_VIDSTREAM1_NONE,
} XAVBuf_VideoStream;

/**
 * This typedef describes the graphics source list
 */
typedef enum {
	XAVBUF_VIDSTREAM2_DISABLEGFX = 0x0,
	XAVBUF_VIDSTREAM2_NONLIVE_GFX = 0x4,
	XAVBUF_VIDSTREAM2_LIVE_GFX = 0x8,
	XAVBUF_VIDSTREAM2_NONE = 0xC0,
} XAVBuf_GfxStream;

/**
 * This typedef describes the audio stream 1 source list
 */
typedef enum {
	XAVBUF_AUDSTREAM1_LIVE = 0x00,
	XAVBUF_AUDSTREAM1_NONLIVE = 0x10,
	XAVBUF_AUDSTREAM1_TPG = 0x20,
	XAVBUF_AUDSTREAM1_NO_AUDIO = 0x30,
} XAVBuf_AudioStream1;

/**
 * This typedef describes the audio stream 2 source list
 */
typedef enum {
	XAVBUF_AUDSTREAM2_NO_AUDIO = 0X00,
	XAVBUF_AUDSTREAM2_AUDIOGFX = 0X40,
} XAVBuf_AudioStream2;

/**
 * This typedef describes the attributes associated with the video formats.
 */
typedef struct {
	XAVBuf_VideoFormat VideoFormat;
	u8 Value;
	XAVBuf_VideoModes Mode;
	u32 SF[3];
	u8 SamplingEn;
	u8 IsRGB;
	u8 Swap;
	u8 BPP;
} XAVBuf_VideoAttribute;

/**
 * This typedef stores the attributes of an audio stream
 */
typedef struct {
	u32 Volume;
	u8 SwapLR;
} XAVBuf_AudioAttribute;

/**
 * This typedef stores the data associated with the Audio Video input modes.
 */
typedef struct {
	XAVBuf_VideoAttribute *NonLiveVideo, *NonLiveGraphics;
	XAVBuf_VideoAttribute *LiveVideo, *LiveGraphics;
	XAVBuf_AudioAttribute *Audio, *GraphicsAudio;
	XAVBuf_VideoStream VideoSrc;
        XAVBuf_GfxStream GraphicsSrc;
	XAVBuf_AudioStream1 AudioSrc1;
	XAVBuf_AudioStream2 AudioSrc2;
	u8 AudioClk, VideoClk;
} XAVBuf_AVModes;

/**
 * This structure stores the background color information.
 */
typedef struct {
	u16 RCr;
	u16 GY;
	u16 BCb;
} XAVBuf_BlenderBgClr;

/**
 * This typedef stores the AVBuf Configuration information.
 */
typedef struct {
	u16 DeviceId;
	u32 BaseAddr;
} XAVBuf_Config;

/**
 * This typedef stores all the attributes associated to the Blender block of the
 * DisplayPort Subsystem
 */
typedef struct {
	u8 GlobalAlphaEn;
	u8 Alpha;
	XAVBuf_VideoAttribute *OutputVideo;
} XAVBuf_Blender;

/**
 * The XAVBuf driver instance data. The user is required to allocate a variable
 * of this type for every XAVBUF instance in the system. A pointer to this type
 * is then passed to the driver API functions
 */
typedef struct {
	XAVBuf_Config Config;
	XAVBuf_AVModes AVMode;
	XAVBuf_Blender Blender;
} XAVBuf;


/**************************** Function Prototypes *****************************/

/* xavbuf.c: Setup and initialization functions. */
void XAVBuf_CfgInitialize(XAVBuf *InstancePtr, u32 BaseAddr, u16 DeviceId);

/* xavbuf.c: Functions to setup the Input Video and Audio sources */
void XAVBuf_InputVideoSelect(XAVBuf *InstancePtr, XAVBuf_VideoStream VidStream,
			      XAVBuf_GfxStream GfxStream);
void XAVBuf_InputAudioSelect(XAVBuf *InstancePtr, XAVBuf_AudioStream1 AudStream,
				XAVBuf_AudioStream2 AudioStream2);

/* xavbuf.c: Functions to setup the Video Format attributes */
int XAVBuf_SetInputNonLiveVideoFormat(XAVBuf *InstancePtr,
				       XAVBuf_VideoFormat Format);
int XAVBuf_SetInputNonLiveGraphicsFormat(XAVBuf *InstancePtr,
				       XAVBuf_VideoFormat Format);
int XAVBuf_SetInputLiveVideoFormat(XAVBuf *InstancePtr,
				       XAVBuf_VideoFormat Format);
int XAVBuf_SetInputLiveGraphicsFormat(XAVBuf *InstancePtr,
				       XAVBuf_VideoFormat Format);
int XAVBuf_SetOutputVideoFormat(XAVBuf *InstancePtr, XAVBuf_VideoFormat Format);
XAVBuf_VideoAttribute *XAVBuf_GetLiveVideoAttribute(XAVBuf_VideoFormat Format);
XAVBuf_VideoAttribute *XAVBuf_GetNLiveVideoAttribute(XAVBuf_VideoFormat Format);
XAVBuf_VideoAttribute *XAVBuf_GetNLGraphicsAttribute(XAVBuf_VideoFormat Format);

/* xavbuf.c: Functions to setup the clock sources for video and audio */
void XAVBuf_SetAudioVideoClkSrc(XAVBuf *InstancePtr, u8 VideoClk, u8 AudioClk);

/* xavbuf.c: Functions that setup Video and Graphics pipeline depending on the
 * sources and format selected.
 */
void XAVBuf_ConfigureVideoPipeline(XAVBuf *InstancePtr);
void XAVBuf_ConfigureGraphicsPipeline(XAVBuf *InstancePtr);

/* Functions to setup Blender Properties */
void XAVBuf_BlendSetBgColor(XAVBuf *InstancePtr, XAVBuf_BlenderBgClr *Color);
void XAVBuf_SetBlenderAlpha(XAVBuf *InstancePtr, u8 Alpha, u8 Enable);
void XAVBuf_SoftReset(XAVBuf *InstancePtr);
void XABuf_LineResetDisable(XAVBuf *InstancePtr, u8 Disable);
void XAVBuf_ConfigureOutputVideo(XAVBuf *InstancePtr);

/* Audio Configuration functions */
void XAVBuf_AudioSoftReset(XAVBuf *InstancePtr);
void XAVBuf_AudioMixerVolumeControl(XAVBuf *InstancePtr, u8 Channel0Volume,
					u8 Channel1Volume);

/* DPDMA Interface functions */
void XAVBuf_EnableGraphicsBuffers(XAVBuf *InstancePtr, u8 Enable);
void XAVBuf_EnableVideoBuffers(XAVBuf *InstancePtr, u8 Enable);
void XAVBuf_EnableAudio0Buffers(XAVBuf *InstancePtr, u8 Enable);
void XAVBuf_EnableAudio1Buffers(XAVBuf *InstancePtr, u8 Enable);

#endif //XAVBUF_H_
