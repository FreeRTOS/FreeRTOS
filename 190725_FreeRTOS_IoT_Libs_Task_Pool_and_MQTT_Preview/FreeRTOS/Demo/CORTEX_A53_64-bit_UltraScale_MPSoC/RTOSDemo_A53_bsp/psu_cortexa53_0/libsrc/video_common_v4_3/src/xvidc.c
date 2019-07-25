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
 * XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
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
 * @file xvidc.c
 * @addtogroup video_common_v4_3
 * @{
 *
 * Contains common utility functions that are typically used by video-related
 * drivers and applications.
 *
 * @note	None.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- -----------------------------------------------
 * 1.0   rc,  01/10/15 Initial release.
 *       als
 * 2.2   als  02/01/16 Functions with pointer arguments that don't modify
 *                     contents now const.
 *                     Added ability to insert a custom video timing table.
 *       yh            Added 3D support.
 * 3.0   aad  05/13/16 Added API to search for RB video modes.
 * 3.1   rco  07/26/16 Added extern definition for timing table array
 *                     Added video-in-memory color formats
 *                     Updated XVidC_RegisterCustomTimingModes API signature
 * 4.1   rco  11/23/16 Added new memory formats
 *                     Added new API to get video mode id that matches exactly
 *                     with provided timing information
 *                     Fix c++ warnings
 * 4.2	 jsr  07/22/17 Added new framerates and color formats to support SDI
 *                     Reordered YCBCR422 colorforamt and removed other formats
 *                     that are not needed for SDI which were added earlier.
 *       vyc  10/04/17 Added new streaming alpha formats and new memory formats
 * 4.3   eb   26/01/18 Added API XVidC_GetVideoModeIdExtensive
 *       jsr  02/22/18 Added XVIDC_CSF_YCBCR_420 color space format
 *       vyc  04/04/18 Added BGR8 memory format
 * </pre>
 *
*******************************************************************************/

/******************************* Include Files ********************************/

#include "xil_assert.h"
#include "xstatus.h"
#include "xvidc.h"

/*************************** Variable Declarations ****************************/
extern const XVidC_VideoTimingMode XVidC_VideoTimingModes[XVIDC_VM_NUM_SUPPORTED];

const XVidC_VideoTimingMode *XVidC_CustomTimingModes = NULL;
int XVidC_NumCustomModes = 0;

/**************************** Function Prototypes *****************************/

static const XVidC_VideoTimingMode *XVidC_GetCustomVideoModeData(
		XVidC_VideoMode VmId);
static u8 XVidC_IsVtmRb(const char *VideoModeStr, u8 RbN);

/*************************** Function Definitions *****************************/

/******************************************************************************/
/**
 * This function registers a user-defined custom video mode timing table with
 * video_common. Functions which search the available video modes, or take VmId
 * as an input, will operate on or check the custom video mode timing table in
 * addition to the pre-defined video mode timing table (XVidC_VideoTimingModes).
 *
 * @param	CustomTable is a pointer to the user-defined custom vide mode
 *		timing table to register.
 * @param	NumElems is the number of video modes supported by CustomTable.
 *
 * @return
 *		- XST_SUCCESS if the custom table was successfully registered.
 *		- XST_FAILURE if an existing custom table is already present.
 *
 * @note	IDs in the custom table may not conflict with IDs reserved by
 *		the XVidC_VideoMode enum.
 *
*******************************************************************************/
u32 XVidC_RegisterCustomTimingModes(const XVidC_VideoTimingMode *CustomTable,
		                            u16 NumElems)
{
	u16 Index;

	/* Verify arguments. */
	Xil_AssertNonvoid(CustomTable != NULL);
	for (Index = 0; Index < NumElems; Index++) {
		Xil_AssertNonvoid((CustomTable[Index].VmId > XVIDC_VM_CUSTOM));
		/* The IDs of each video mode in the custom table must not
		 * conflict with IDs reserved by video_common. */
	}

	/* Fail if a custom table is currently already registered. */
	if (XVidC_CustomTimingModes) {
		return XST_FAILURE;
	}

	XVidC_CustomTimingModes = CustomTable;
	XVidC_NumCustomModes    = NumElems;

	return XST_SUCCESS;
}

/******************************************************************************/
/**
 * This function unregisters the user-defined custom video mode timing table
 * previously registered by XVidC_RegisterCustomTimingModes().
 *
 * @return	None.
 *
 * @note	None.
 *
*******************************************************************************/
void XVidC_UnregisterCustomTimingModes(void)
{
	XVidC_CustomTimingModes = NULL;
	XVidC_NumCustomModes    = 0;
}

/******************************************************************************/
/**
 * This function calculates pixel clock based on the inputs.
 *
 * @param	HTotal specifies horizontal total.
 * @param	VTotal specifies vertical total.
 * @param	FrameRate specifies rate at which frames are generated.
 *
 * @return	Pixel clock in Hz.
 *
 * @note	None.
 *
*******************************************************************************/
u32 XVidC_GetPixelClockHzByHVFr(u32 HTotal, u32 VTotal, u8 FrameRate)
{
	return (HTotal * VTotal * FrameRate);
}

/******************************************************************************/
/**
 * This function calculates pixel clock from video mode.
 *
 * @param	VmId specifies the resolution id.
 *
 * @return	Pixel clock in Hz.
 *
 * @note	None.
 *
*******************************************************************************/
u32 XVidC_GetPixelClockHzByVmId(XVidC_VideoMode VmId)
{
	u32 ClkHz;
	const XVidC_VideoTimingMode *VmPtr;

	VmPtr = XVidC_GetVideoModeData(VmId);
	if (!VmPtr) {
		return 0;
	}

	if (XVidC_IsInterlaced(VmId)) {
		/* For interlaced mode, use both frame 0 and frame 1 vertical
		 * totals. */
		ClkHz = VmPtr->Timing.F0PVTotal + VmPtr->Timing.F1VTotal;

		/* Multiply the number of pixels by the frame rate of each
		 * individual frame (half of the total frame rate). */
		ClkHz *= VmPtr->FrameRate / 2;
	}
	else {
		/* For progressive mode, use only frame 0 vertical total. */
		ClkHz = VmPtr->Timing.F0PVTotal;

		/* Multiply the number of pixels by the frame rate. */
		ClkHz *= VmPtr->FrameRate;
	}

	/* Multiply the vertical total by the horizontal total for number of
	 * pixels. */
	ClkHz *= VmPtr->Timing.HTotal;

	return ClkHz;
}

/******************************************************************************/
/**
 * This function checks if the input video mode is interlaced/progressive based
 * on its ID from the video timings table.
 *
 * @param	VmId specifies the resolution ID from the video timings table.
 *
 * @return	Video format.
 *		- XVIDC_VF_PROGRESSIVE
 *		- XVIDC_VF_INTERLACED
 *
 * @note	None.
 *
*******************************************************************************/
XVidC_VideoFormat XVidC_GetVideoFormat(XVidC_VideoMode VmId)
{
	const XVidC_VideoTimingMode *VmPtr;

	VmPtr = XVidC_GetVideoModeData(VmId);
	if (!VmPtr) {
		return XVIDC_VF_UNKNOWN;
	}

	if (VmPtr->Timing.F1VTotal == 0) {
		return (XVIDC_VF_PROGRESSIVE);
	}

	return (XVIDC_VF_INTERLACED);
}

/******************************************************************************/
/**
 * This function checks if the input video mode is interlaced based on its ID
 * from the video timings table.
 *
 * @param	VmId specifies the resolution ID from the video timings table.
 *
 * @return
 *		- 1 if the video timing with the supplied table ID is
 *		  interlaced.
 *		- 0 if the video timing is progressive.
 *
 * @note	None.
 *
*******************************************************************************/
u8 XVidC_IsInterlaced(XVidC_VideoMode VmId)
{
	if (XVidC_GetVideoFormat(VmId) == XVIDC_VF_INTERLACED) {
		return 1;
	}

	return 0;
}

/******************************************************************************/
/**
 * This function returns the Video Mode ID that matches the detected input
 * timing, frame rate and I/P flag
 *
 * @param	Timing is the pointer to timing parameters to match
 * @param	FrameRate specifies refresh rate in HZ
 * @param	IsInterlaced is flag.
 *		      - 0 = Progressive
 *			  - 1 = Interlaced.
 *
 * @return	Id of a supported video mode.
 *
 * @note	This is an extension of XVidC_GetVideoModeId API to include
 *          blanking information in match process. No attempt is made to
 *          search for reduced blanking entries, if any.
 *
*******************************************************************************/
XVidC_VideoMode XVidC_GetVideoModeIdWBlanking(const XVidC_VideoTiming *Timing,
		                                      u32 FrameRate, u8 IsInterlaced)
{
  XVidC_VideoMode VmId;
  XVidC_VideoTiming const *StdTiming = NULL;

  /* First search for ID with matching Width & Height */
  VmId = XVidC_GetVideoModeId(Timing->HActive, Timing->VActive, FrameRate,
		                      IsInterlaced);

  if(VmId == XVIDC_VM_NOT_SUPPORTED) {
	return(VmId);
  } else {

	/* Get standard timing info from default timing table */
	StdTiming = XVidC_GetTimingInfo(VmId);

	/* Match against detected timing parameters */
	if((Timing->HActive        == StdTiming->HActive) &&
	   (Timing->VActive        == StdTiming->VActive) &&
	   (Timing->HTotal         == StdTiming->HTotal) &&
	   (Timing->F0PVTotal      == StdTiming->F0PVTotal) &&
	   (Timing->HFrontPorch    == StdTiming->HFrontPorch) &&
	   (Timing->HSyncWidth     == StdTiming->HSyncWidth) &&
	   (Timing->HBackPorch     == StdTiming->HBackPorch) &&
	   (Timing->F0PVFrontPorch == StdTiming->F0PVFrontPorch) &&
	   (Timing->F0PVSyncWidth  == StdTiming->F0PVSyncWidth) &&
	   (Timing->F0PVBackPorch  == StdTiming->F0PVBackPorch)) {
       return(VmId);
	 } else {
	   return(XVIDC_VM_NOT_SUPPORTED);
	 }
  }
}

/******************************************************************************/
/**
 * This function returns the Video Mode ID that matches the detected input
 * width, height, frame rate and I/P flag
 *
 * @param	Width specifies the number pixels per scanline.
 * @param	Height specifies the number of scanline's.
 * @param	FrameRate specifies refresh rate in HZ
 * @param	IsInterlaced is flag.
 *		- 0 = Progressive
 *		- 1 = Interlaced.
 *
 * @return	Id of a supported video mode.
 *
 * @note	None.
 *
*******************************************************************************/
XVidC_VideoMode XVidC_GetVideoModeId(u32 Width, u32 Height, u32 FrameRate,
					u8 IsInterlaced)
{
	u32 Low;
	u32 High;
	u32 Mid;
	u32 HActive;
	u32 VActive;
	u32 Rate;
	u32 ResFound = (FALSE);
	XVidC_VideoMode Mode;
	u16 Index;

	/* First, attempt a linear search on the custom video timing table. */
	if(XVidC_CustomTimingModes) {
	  for (Index = 0; Index < XVidC_NumCustomModes; Index++) {
		HActive = XVidC_CustomTimingModes[Index].Timing.HActive;
		VActive = XVidC_CustomTimingModes[Index].Timing.VActive;
		Rate = XVidC_CustomTimingModes[Index].FrameRate;
		if ((Width  == HActive) &&
			(Height == VActive) &&
			(FrameRate == Rate)) {
			   return XVidC_CustomTimingModes[Index].VmId;
		}
	  }
	}

	if (IsInterlaced) {
		Low = (XVIDC_VM_INTL_START);
		High = (XVIDC_VM_INTL_END);
	}
	else {
		Low = (XVIDC_VM_PROG_START);
		High = (XVIDC_VM_PROG_END);
	}

	HActive = VActive = Rate = 0;

	/* Binary search finds item in sorted array.
	 * And returns index (zero based) of item
	 * If item is not found returns flag remains
	 * FALSE. Search key is "width or HActive"
	 */
	while (Low <= High) {
		Mid = (Low + High) / 2;
		HActive = XVidC_VideoTimingModes[Mid].Timing.HActive;
		if (Width == HActive) {
			ResFound = (TRUE);
			break;
		}
		else if (Width < HActive) {
			if (Mid == 0) {
				break;
			}
			else {
				High = Mid - 1;
			}
		}
		else {
			Low = Mid + 1;
		}
	}

	 /* HActive matched at middle */
	if (ResFound) {
		/* Rewind to start index of mode with matching width */
		while ((Mid > 0) &&
			(XVidC_VideoTimingModes[Mid - 1].Timing.HActive ==
								Width)) {
			--Mid;
		}

		ResFound = (FALSE);
		VActive = XVidC_VideoTimingModes[Mid].Timing.VActive;
		Rate = XVidC_VideoTimingModes[Mid].FrameRate;

		/* Now do a linear search for matching VActive and Frame
		 * Rate
		 */
		while (HActive == Width) {
			/* check current entry */
			if ((VActive == Height) && (Rate == FrameRate)) {
				ResFound = (TRUE);
				break;
			}
			/* Check next entry */
			else {
				Mid = Mid + 1;
				HActive =
				XVidC_VideoTimingModes[Mid].Timing.HActive;
				VActive =
				XVidC_VideoTimingModes[Mid].Timing.VActive;
				Rate = XVidC_VideoTimingModes[Mid].FrameRate;
			}
		}
		Mode =
		(ResFound) ? (XVidC_VideoMode)Mid : (XVIDC_VM_NOT_SUPPORTED);
	}
	else {
		Mode = (XVIDC_VM_NOT_SUPPORTED);
	}

	return (Mode);
}

/******************************************************************************/
/**
 * This function returns the Video Mode ID that matches the detected input
 * timing, frame rate and I/P flag
 *
 * @param	Timing is the pointer to timing parameters to match
 * @param	FrameRate specifies refresh rate in HZ
 * @param	IsInterlaced is flag.
 *		      - 0 = Progressive
 *			  - 1 = Interlaced.
 * @param	IsExtensive is flag.
 *		      - 0 = Basic matching of timing parameters
 *			  - 1 = Extensive matching of timing parameters
 *
 * @return	Id of a supported video mode.
 *
 * @note	This function attempts to search for reduced blanking entries, if
 *          any.
 *
*******************************************************************************/
XVidC_VideoMode XVidC_GetVideoModeIdExtensive(XVidC_VideoTiming *Timing,
											  u32 FrameRate,
											  u8 IsInterlaced,
											  u8 IsExtensive)
{
	u32 Low;
	u32 High;
	u32 Mid;
	u32 HActive;
	u32 VActive;
	u32 Rate;
	u32 ResFound = (FALSE);
	XVidC_VideoMode Mode;
	u16 Index;

	/* First, attempt a linear search on the custom video timing table. */
	if(XVidC_CustomTimingModes) {
	  for (Index = 0; Index < XVidC_NumCustomModes; Index++) {
		HActive = XVidC_CustomTimingModes[Index].Timing.HActive;
		VActive = XVidC_CustomTimingModes[Index].Timing.VActive;
		Rate = XVidC_CustomTimingModes[Index].FrameRate;
		if ((HActive == Timing->HActive) && (VActive == Timing->VActive) &&
				(Rate == FrameRate) && (IsExtensive == 0 || (
			XVidC_CustomTimingModes[Index].Timing.HTotal == Timing->HTotal &&
			XVidC_CustomTimingModes[Index].Timing.F0PVTotal ==
					Timing->F0PVTotal &&
			XVidC_CustomTimingModes[Index].Timing.HFrontPorch ==
					Timing->HFrontPorch &&
			XVidC_CustomTimingModes[Index].Timing.F0PVFrontPorch ==
					Timing->F0PVFrontPorch &&
			XVidC_CustomTimingModes[Index].Timing.HSyncWidth ==
					Timing->HSyncWidth &&
			XVidC_CustomTimingModes[Index].Timing.F0PVSyncWidth ==
					Timing->F0PVSyncWidth &&
			XVidC_CustomTimingModes[Index].Timing.VSyncPolarity ==
					Timing->VSyncPolarity))) {
				if (!IsInterlaced || IsExtensive == 0 || (
						XVidC_CustomTimingModes[Index].Timing.F1VTotal ==
						Timing->F1VTotal &&
						XVidC_CustomTimingModes[Index].Timing.F1VFrontPorch ==
								Timing->F1VFrontPorch &&
						XVidC_CustomTimingModes[Index].Timing.F1VSyncWidth ==
								Timing->F1VSyncWidth)) {
					return XVidC_CustomTimingModes[Index].VmId;
				}
		}
	  }
	}

	if (IsInterlaced) {
		Low = (XVIDC_VM_INTL_START);
		High = (XVIDC_VM_INTL_END);
	}
	else {
		Low = (XVIDC_VM_PROG_START);
		High = (XVIDC_VM_PROG_END);
	}

	HActive = VActive = Rate = 0;

	/* Binary search finds item in sorted array.
	 * And returns index (zero based) of item
	 * If item is not found returns flag remains
	 * FALSE. Search key is "Timing->HActive or HActive"
	 */
	while (Low <= High) {
		Mid = (Low + High) / 2;
		HActive = XVidC_VideoTimingModes[Mid].Timing.HActive;
		if (Timing->HActive == HActive) {
			ResFound = (TRUE);
			break;
		}
		else if (Timing->HActive < HActive) {
			if (Mid == 0) {
				break;
			}
			else {
				High = Mid - 1;
			}
		}
		else {
			Low = Mid + 1;
		}
	}

	 /* HActive matched at middle */
	if (ResFound) {
		/* Rewind to start index of mode with matching Timing->HActive */
		while ((Mid > 0) &&
			(XVidC_VideoTimingModes[Mid - 1].Timing.HActive ==
								Timing->HActive)) {
			--Mid;
		}

		ResFound = (FALSE);
		VActive = XVidC_VideoTimingModes[Mid].Timing.VActive;
		Rate = XVidC_VideoTimingModes[Mid].FrameRate;

		/* Now do a linear search for matching VActive and Frame
		 * Rate
		 */
		while (HActive == Timing->HActive) {
			/* check current entry */
			if ((VActive == Timing->VActive) && (Rate == FrameRate) &&
					(IsExtensive == 0 ||
					(XVidC_VideoTimingModes[Mid].Timing.HTotal ==
							Timing->HTotal &&
					XVidC_VideoTimingModes[Mid].Timing.F0PVTotal ==
							Timing->F0PVTotal &&
					XVidC_VideoTimingModes[Mid].Timing.HFrontPorch ==
							Timing->HFrontPorch &&
					XVidC_VideoTimingModes[Mid].Timing.F0PVFrontPorch ==
							Timing->F0PVFrontPorch &&
					XVidC_VideoTimingModes[Mid].Timing.HSyncWidth ==
							Timing->HSyncWidth &&
					XVidC_VideoTimingModes[Mid].Timing.F0PVSyncWidth ==
							Timing->F0PVSyncWidth &&
					XVidC_VideoTimingModes[Mid].Timing.VSyncPolarity ==
							Timing->VSyncPolarity))) {
				if (!IsInterlaced || IsExtensive == 0 || (
						XVidC_VideoTimingModes[Mid].Timing.F1VTotal ==
								Timing->F1VTotal &&
						XVidC_VideoTimingModes[Mid].Timing.F1VFrontPorch ==
								Timing->F1VFrontPorch &&
						XVidC_VideoTimingModes[Mid].Timing.F1VSyncWidth ==
								Timing->F1VSyncWidth)) {
					ResFound = (TRUE);
					break;
				}
			}
			/* Check next entry */
			else {
				Mid = Mid + 1;
				HActive =
				XVidC_VideoTimingModes[Mid].Timing.HActive;
				VActive =
				XVidC_VideoTimingModes[Mid].Timing.VActive;
				Rate = XVidC_VideoTimingModes[Mid].FrameRate;
			}
		}
		Mode =
		(ResFound) ? (XVidC_VideoMode)Mid : (XVIDC_VM_NOT_SUPPORTED);
	}
	else {
		Mode = (XVIDC_VM_NOT_SUPPORTED);
	}

	return (Mode);
}

/******************************************************************************/
/**
 * This function returns the video mode ID that matches the detected input
 * width, height, frame rate, interlaced or progressive, and reduced blanking.
 *
 * @param	Width specifies the number pixels per scanline.
 * @param	Height specifies the number of scanline's.
 * @param	FrameRate specifies refresh rate in HZ
 * @param	IsInterlaced specifies interlaced or progressive mode:
 *		- 0 = Progressive
 *		- 1 = Interlaced.
 * @param	RbN specifies the type of reduced blanking:
 *		- 0 = No reduced blanking
 *		- 1 = RB
 *		- 2 = RB2
 *
 * @return	ID of a supported video mode.
 *
 * @note	None.
 *
*******************************************************************************/
XVidC_VideoMode XVidC_GetVideoModeIdRb(u32 Width, u32 Height,
		u32 FrameRate, u8 IsInterlaced, u8 RbN)
{
	XVidC_VideoMode VmId;
	const XVidC_VideoTimingMode *VtmPtr;
	u8 Found = 0;

	VmId = XVidC_GetVideoModeId(Width, Height, FrameRate,
				IsInterlaced);

	VtmPtr = XVidC_GetVideoModeData(VmId);
	if (!VtmPtr) {
		return XVIDC_VM_NOT_SUPPORTED;
	}

	while (!Found) {
		VtmPtr = XVidC_GetVideoModeData(VmId);
		if ((Height != VtmPtr->Timing.VActive) ||
		    (Width != VtmPtr->Timing.HActive) ||
		    (FrameRate != VtmPtr->FrameRate) ||
		    (IsInterlaced && !XVidC_IsInterlaced(VmId))) {
			VmId = XVIDC_VM_NOT_SUPPORTED;
			break;
		}
		Found = XVidC_IsVtmRb(XVidC_GetVideoModeStr(VmId), RbN);
		if (Found) {
			break;
		}
		VmId = (XVidC_VideoMode)((int)VmId + 1);
	}

	return VmId;
}

/******************************************************************************/
/**
 * This function returns the pointer to video mode data at index provided.
 *
 * @param	VmId specifies the resolution id.
 *
 * @return	Pointer to XVidC_VideoTimingMode structure based on the given
 *		video mode.
 *
 * @note	None.
 *
*******************************************************************************/
const XVidC_VideoTimingMode *XVidC_GetVideoModeData(XVidC_VideoMode VmId)
{
	if (VmId < XVIDC_VM_NUM_SUPPORTED) {
		return &XVidC_VideoTimingModes[VmId];
	}

	return XVidC_GetCustomVideoModeData(VmId);
}

/******************************************************************************/
/**
 *
 * This function returns the resolution name for index specified.
 *
 * @param	VmId specifies the resolution id.
 *
 * @return	Pointer to a resolution name string.
 *
 * @note	None.
 *
*******************************************************************************/
const char *XVidC_GetVideoModeStr(XVidC_VideoMode VmId)
{
	const XVidC_VideoTimingMode *VmPtr;

	if (VmId == XVIDC_VM_CUSTOM) {
		return ("Custom video mode");
	}

	VmPtr = XVidC_GetVideoModeData(VmId);
	if (!VmPtr) {
		return ("Video mode not supported");
	}

	return VmPtr->Name;
}

/******************************************************************************/
/**
 * This function returns the frame rate name for index specified.
 *
 * @param	VmId specifies the resolution id.
 *
 * @return	Pointer to a frame rate name string.
 *
 * @note	None.
 *
*******************************************************************************/
const char *XVidC_GetFrameRateStr(XVidC_VideoMode VmId)
{
	const XVidC_VideoTimingMode *VmPtr;

	VmPtr = XVidC_GetVideoModeData(VmId);
	if (!VmPtr) {
		return ("Video mode not supported");
	}

	switch (VmPtr->FrameRate) {
		case (XVIDC_FR_24HZ):   return ("24Hz");
		case (XVIDC_FR_25HZ):   return ("25Hz");
		case (XVIDC_FR_30HZ):   return ("30Hz");
		case (XVIDC_FR_48HZ):   return ("48Hz");
		case (XVIDC_FR_50HZ):   return ("50Hz");
		case (XVIDC_FR_56HZ):   return ("56Hz");
		case (XVIDC_FR_60HZ):   return ("60Hz");
		case (XVIDC_FR_65HZ):   return ("65Hz");
		case (XVIDC_FR_67HZ):   return ("67Hz");
		case (XVIDC_FR_70HZ):   return ("70Hz");
		case (XVIDC_FR_72HZ):   return ("72Hz");
		case (XVIDC_FR_75HZ):   return ("75Hz");
		case (XVIDC_FR_85HZ):   return ("85Hz");
		case (XVIDC_FR_87HZ):   return ("87Hz");
		case (XVIDC_FR_88HZ):   return ("88Hz");
		case (XVIDC_FR_96HZ):   return ("96Hz");
		case (XVIDC_FR_100HZ):  return ("100Hz");
		case (XVIDC_FR_120HZ):  return ("120Hz");

		default:
		     return ("Frame rate not supported");
	}
}

/******************************************************************************/
/**
 * This function returns a string representation of the enumerated type,
 * XVidC_3DFormat.
 *
 * @param	Format specifies the value to convert.
 *
 * @return	Pointer to the converted string.
 *
 * @note	None.
 *
*******************************************************************************/
const char *XVidC_Get3DFormatStr(XVidC_3DFormat Format)
{
	switch (Format) {
		case XVIDC_3D_FRAME_PACKING:
			return ("Frame Packing");

		case XVIDC_3D_FIELD_ALTERNATIVE:
			return ("Field Alternative");

		case XVIDC_3D_LINE_ALTERNATIVE:
			return ("Line Alternative");

		case XVIDC_3D_SIDE_BY_SIDE_FULL:
			return ("Side-by-Side(full)");

		case XVIDC_3D_TOP_AND_BOTTOM_HALF:
			return ("Top-and-Bottom(half)");

		case XVIDC_3D_SIDE_BY_SIDE_HALF:
			return ("Side-by-Side(half)");

		default:
			return ("Unknown");
	}
}

/******************************************************************************/
/**
 * This function returns the color format name for index specified.
 *
 * @param	ColorFormatId specifies the index of color format space.
 *
 * @return	Pointer to a color space name string.
 *
 * @note	None.
 *
*******************************************************************************/
const char *XVidC_GetColorFormatStr(XVidC_ColorFormat ColorFormatId)
{
	switch (ColorFormatId) {
		case XVIDC_CSF_RGB:            return ("RGB");
		case XVIDC_CSF_YCRCB_444:      return ("YUV_444");
		case XVIDC_CSF_YCRCB_422:      return ("YUV_422");
		case XVIDC_CSF_YCRCB_420:      return ("YUV_420");
		case XVIDC_CSF_YONLY:          return ("Y_ONLY");
		case XVIDC_CSF_RGBA:           return ("RGBA");
		case XVIDC_CSF_YCRCBA_444:     return ("YUVA_444");
		case XVIDC_CSF_MEM_RGBX8:      return ("RGBX8");
		case XVIDC_CSF_MEM_YUVX8:      return ("YUVX8");
		case XVIDC_CSF_MEM_YUYV8:      return ("YUYV8");
		case XVIDC_CSF_MEM_RGBA8:      return ("RGBA8");
		case XVIDC_CSF_MEM_YUVA8:      return ("YUVA8");
		case XVIDC_CSF_MEM_RGBX10:     return ("RGBX10");
		case XVIDC_CSF_MEM_YUVX10:     return ("YUVX10");
		case XVIDC_CSF_MEM_RGB565:     return ("RGB565");
		case XVIDC_CSF_MEM_Y_UV8:      return ("Y_UV8");
		case XVIDC_CSF_MEM_Y_UV8_420:  return ("Y_UV8_420");
		case XVIDC_CSF_MEM_RGB8:       return ("RGB8");
		case XVIDC_CSF_MEM_YUV8:       return ("YUV8");
		case XVIDC_CSF_MEM_Y_UV10:     return ("Y_UV10");
		case XVIDC_CSF_MEM_Y_UV10_420: return ("Y_UV10_420");
		case XVIDC_CSF_MEM_Y8:         return ("Y8");
		case XVIDC_CSF_MEM_Y10:        return ("Y10");
		case XVIDC_CSF_MEM_BGRA8:      return ("BGRA8");
		case XVIDC_CSF_MEM_BGRX8:      return ("BGRX8");
		case XVIDC_CSF_MEM_UYVY8:      return ("UYVY8");
		case XVIDC_CSF_MEM_BGR8:       return ("BGR8");
		case XVIDC_CSF_YCBCR_422:      return ("YCBCR_422");
		case XVIDC_CSF_YCBCR_420:      return ("YCBCR_420");
		default:
					       return ("Color space format not supported");
	}
}

/******************************************************************************/
/**
 * This function returns the frame rate for index specified.
 *
 * @param	VmId specifies the resolution id.
 *
 * @return	Frame rate in Hz.
 *
 * @note	None.
 *
*******************************************************************************/
XVidC_FrameRate XVidC_GetFrameRate(XVidC_VideoMode VmId)
{
	const XVidC_VideoTimingMode *VmPtr;

	VmPtr = XVidC_GetVideoModeData(VmId);
	if (!VmPtr) {
		return XVIDC_FR_NUM_SUPPORTED;
	}

	return VmPtr->FrameRate;
}

/******************************************************************************/
/**
 * This function returns the timing parameters for specified resolution.
 *
 * @param	VmId specifies the resolution id.
 *
 * @return	Pointer to a XVidC_VideoTiming structure.
 *
 * @note	None.
 *
*******************************************************************************/
const XVidC_VideoTiming *XVidC_GetTimingInfo(XVidC_VideoMode VmId)
{
	const XVidC_VideoTimingMode *VmPtr;

	VmPtr = XVidC_GetVideoModeData(VmId);
	if (!VmPtr) {
		return NULL;
	}

	return &VmPtr->Timing;
}

/******************************************************************************/
/**
 * This function sets the VideoStream structure for the specified video format.
 *
 * @param	VidStrmPtr is a pointer to the XVidC_VideoStream structure to be
 *		set.
 * @param	VmId specifies the resolution ID.
 * @param	ColorFormat specifies the color format type.
 * @param	Bpc specifies the color depth/bits per color component.
 * @param	Ppc specifies the pixels per clock.
 *
 * @return
 *		- XST_SUCCESS if the timing for the supplied ID was found.
 *		- XST_FAILURE, otherwise.
 *
 * @note	None.
 *
*******************************************************************************/
u32 XVidC_SetVideoStream(XVidC_VideoStream *VidStrmPtr, XVidC_VideoMode VmId,
			 XVidC_ColorFormat ColorFormat, XVidC_ColorDepth Bpc,
			 XVidC_PixelsPerClock Ppc)
{
	const XVidC_VideoTiming *TimingPtr;

	/* Verify arguments. */
	Xil_AssertNonvoid(VidStrmPtr != NULL);
	Xil_AssertNonvoid(ColorFormat < XVIDC_CSF_NUM_SUPPORTED);
	Xil_AssertNonvoid((Bpc == XVIDC_BPC_6)  ||
			  (Bpc == XVIDC_BPC_8)  ||
			  (Bpc == XVIDC_BPC_10) ||
			  (Bpc == XVIDC_BPC_12) ||
			  (Bpc == XVIDC_BPC_14) ||
			  (Bpc == XVIDC_BPC_16) ||
			  (Bpc == XVIDC_BPC_UNKNOWN));
	Xil_AssertNonvoid((Ppc == XVIDC_PPC_1) ||
			  (Ppc == XVIDC_PPC_2) ||
			  (Ppc == XVIDC_PPC_4));

	/* Get the timing from the video timing table. */
	TimingPtr = XVidC_GetTimingInfo(VmId);
	if (!TimingPtr) {
		return XST_FAILURE;
	}
	VidStrmPtr->VmId		= VmId;
	VidStrmPtr->Timing		= *TimingPtr;
	VidStrmPtr->FrameRate		= XVidC_GetFrameRate(VmId);
	VidStrmPtr->IsInterlaced	= XVidC_IsInterlaced(VmId);
	VidStrmPtr->ColorFormatId	= ColorFormat;
	VidStrmPtr->ColorDepth		= Bpc;
	VidStrmPtr->PixPerClk		= Ppc;

	/* Set stream to 2D. */
	VidStrmPtr->Is3D			= FALSE;
	VidStrmPtr->Info_3D.Format		= XVIDC_3D_UNKNOWN;
	VidStrmPtr->Info_3D.Sampling.Method	= XVIDC_3D_SAMPLING_UNKNOWN;
	VidStrmPtr->Info_3D.Sampling.Position	= XVIDC_3D_SAMPPOS_UNKNOWN;

	return XST_SUCCESS;
}

/******************************************************************************/
/**
 * This function sets the VideoStream structure for the specified 3D video
 * format.
 *
 * @param	VidStrmPtr is a pointer to the XVidC_VideoStream structure to be
 *		set.
 * @param	VmId specifies the resolution ID.
 * @param	ColorFormat specifies the color format type.
 * @param	Bpc specifies the color depth/bits per color component.
 * @param	Ppc specifies the pixels per clock.
 * @param	Info3DPtr is a pointer to a XVidC_3DInfo structure.
 *
 * @return
 *		- XST_SUCCESS if the timing for the supplied ID was found.
 *		- XST_FAILURE, otherwise.
 *
 * @return
 *		- XST_SUCCESS
 *		- XST_FAILURE
 *
 * @note	None.
 *
*******************************************************************************/
u32 XVidC_Set3DVideoStream(XVidC_VideoStream *VidStrmPtr, XVidC_VideoMode VmId,
			   XVidC_ColorFormat ColorFormat, XVidC_ColorDepth Bpc,
			   XVidC_PixelsPerClock Ppc, XVidC_3DInfo *Info3DPtr)
{
	u32 Status;
	u16 Vblank0;
	u16 Vblank1;

	/* Verify arguments */
	Xil_AssertNonvoid(Info3DPtr != NULL);

	/* Initialize with info for 2D frame. */
	Status = XVidC_SetVideoStream(VidStrmPtr, VmId, ColorFormat, Bpc, Ppc);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	/* Set stream to 3D. */
	VidStrmPtr->Is3D	= TRUE;
	VidStrmPtr->Info_3D	= *Info3DPtr;

	/* Only 3D format supported is frame packing. */
	if (Info3DPtr->Format != XVIDC_3D_FRAME_PACKING) {
		return XST_FAILURE;
	}

	/* Update the timing based on the 3D format. */

	/* An interlaced format is converted to a progressive frame: */
	/*	3D VActive = (2D VActive * 4) + (2D VBlank field0) +
						(2D Vblank field1 * 2) */
	if (VidStrmPtr->IsInterlaced) {
		Vblank0 = VidStrmPtr->Timing.F0PVTotal -
						VidStrmPtr->Timing.VActive;
		Vblank1 = VidStrmPtr->Timing.F1VTotal -
						VidStrmPtr->Timing.VActive;
		VidStrmPtr->Timing.VActive = (VidStrmPtr->Timing.VActive * 4) +
						Vblank0 + (Vblank1 * 2);

		/* Set VTotal */
		VidStrmPtr->Timing.F0PVTotal *= 2;
		VidStrmPtr->Timing.F0PVTotal += VidStrmPtr->Timing.F1VTotal * 2;

		/* Clear field 1 values. */
		VidStrmPtr->Timing.F1VFrontPorch = 0;
		VidStrmPtr->Timing.F1VSyncWidth  = 0;
		VidStrmPtr->Timing.F1VBackPorch  = 0;
		VidStrmPtr->Timing.F1VTotal      = 0;

		/* Set format to progressive */
		VidStrmPtr->IsInterlaced = FALSE;
	}
	/* Progressive */
	else {
		/* 3D Vactive = (2D VActive * 2) + (2D VBlank) */
		Vblank0 = VidStrmPtr->Timing.F0PVTotal -
						VidStrmPtr->Timing.VActive;
		VidStrmPtr->Timing.VActive = (VidStrmPtr->Timing.VActive * 2) +
						Vblank0;

		/* Set VTotal. */
		VidStrmPtr->Timing.F0PVTotal = VidStrmPtr->Timing.F0PVTotal * 2;
	}

	return XST_SUCCESS;
}

/******************************************************************************/
/**
 * This function prints the stream information on STDIO/UART console.
 *
 * @param	Stream is a pointer to video stream.
 *
 * @return	None.
 *
 * @note	None.
 *
*******************************************************************************/
void XVidC_ReportStreamInfo(const XVidC_VideoStream *Stream)
{
	if (!XVidC_GetVideoModeData(Stream->VmId) &&
			(Stream->VmId != XVIDC_VM_CUSTOM)) {
		xil_printf("\tThe stream ID (%d) is not supported.\r\n",
				Stream->VmId);
		return;
	}

	xil_printf("\tColor Format:     %s\r\n",
			XVidC_GetColorFormatStr(Stream->ColorFormatId));
	xil_printf("\tColor Depth:      %d\r\n", Stream->ColorDepth);
	xil_printf("\tPixels Per Clock: %d\r\n", Stream->PixPerClk);
	xil_printf("\tMode:             %s\r\n",
			Stream->IsInterlaced ? "Interlaced" : "Progressive");

	if (Stream->Is3D) {
		xil_printf("\t3D Format:        %s\r\n",
		XVidC_Get3DFormatStr(Stream->Info_3D.Format));
	}

	if (Stream->VmId == XVIDC_VM_CUSTOM) {
		xil_printf("\tFrame Rate:       %dHz\r\n",
				Stream->FrameRate);
		xil_printf("\tResolution:       %dx%d [Custom Mode]\r\n",
				Stream->Timing.HActive, Stream->Timing.VActive);
		xil_printf("\tPixel Clock:      %d\r\n",
				XVidC_GetPixelClockHzByHVFr(
					Stream->Timing.HTotal,
					Stream->Timing.F0PVTotal,
					Stream->FrameRate));
	}
	else {
		xil_printf("\tFrame Rate:       %s\r\n",
				XVidC_GetFrameRateStr(Stream->VmId));
		xil_printf("\tResolution:       %s\r\n",
				XVidC_GetVideoModeStr(Stream->VmId));
		xil_printf("\tPixel Clock:      %d\r\n",
				XVidC_GetPixelClockHzByVmId(Stream->VmId));
	}
}

/******************************************************************************/
/**
 * This function prints timing information on STDIO/Uart console.
 *
 * @param	Timing is a pointer to Video Timing structure of the stream.
 * @param	IsInterlaced is a TRUE/FALSE flag that denotes the timing
 *		parameter is for interlaced/progressive stream.
 *
 * @return	None.
 *
 * @note	None.
 *
*******************************************************************************/
void XVidC_ReportTiming(const XVidC_VideoTiming *Timing, u8 IsInterlaced)
{
	xil_printf("\r\n\tHSYNC Timing: hav=%04d, hfp=%02d, hsw=%02d(hsp=%d), "
			"hbp=%03d, htot=%04d \n\r", Timing->HActive,
			Timing->HFrontPorch, Timing->HSyncWidth,
			Timing->HSyncPolarity,
			Timing->HBackPorch, Timing->HTotal);

	/* Interlaced */
	if (IsInterlaced) {
		xil_printf("\tVSYNC Timing (Field 0): vav=%04d, vfp=%02d, "
			"vsw=%02d(vsp=%d), vbp=%03d, vtot=%04d\n\r",
			Timing->VActive, Timing->F0PVFrontPorch,
			Timing->F0PVSyncWidth, Timing->VSyncPolarity,
			Timing->F0PVBackPorch, Timing->F0PVTotal);
	xil_printf("\tVSYNC Timing (Field 1): vav=%04d, vfp=%02d, "
			"vsw=%02d(vsp=%d), vbp=%03d, vtot=%04d\n\r",
			Timing->VActive, Timing->F1VFrontPorch,
			Timing->F1VSyncWidth, Timing->VSyncPolarity,
			Timing->F1VBackPorch, Timing->F1VTotal);
	}
	/* Progressive */
	else {
		xil_printf("\tVSYNC Timing: vav=%04d, vfp=%02d, "
			"vsw=%02d(vsp=%d), vbp=%03d, vtot=%04d\n\r",
			Timing->VActive, Timing->F0PVFrontPorch,
			Timing->F0PVSyncWidth, Timing->VSyncPolarity,
			Timing->F0PVBackPorch, Timing->F0PVTotal);
	}
}

/******************************************************************************/
/**
 * This function returns the pointer to video mode data at the provided index
 * of the custom video mode table.
 *
 * @param	VmId specifies the resolution ID.
 *
 * @return	Pointer to XVidC_VideoTimingMode structure based on the given
 *		video mode.
 *
 * @note	None.
 *
*******************************************************************************/
static const XVidC_VideoTimingMode *XVidC_GetCustomVideoModeData(
		XVidC_VideoMode VmId)
{
	u16 Index;

	for (Index = 0; Index < XVidC_NumCustomModes; Index++) {
		if (VmId == (XVidC_CustomTimingModes[Index].VmId)) {
			return &(XVidC_CustomTimingModes[Index]);
		}
	}

	/* ID not found within the custom video mode table. */
	return NULL;
}

/******************************************************************************/
/**
 * This function returns whether or not the video timing mode is a reduced
 * blanking mode or not.
 *
 * @param	VideoModeStr specifies the resolution name string.
 * @param	RbN specifies the type of reduced blanking:
 *		- 0 = No Reduced Blanking
 *		- 1 = RB
 *		- 2 = RB2
 *
 * @return	If the reduced blanking type is compatible with the video mode:
 *		- 0 = Not supported
 *		- 1 = Video mode supports the RB type
 *
 * @note	None.
 *
*******************************************************************************/
static u8 XVidC_IsVtmRb(const char *VideoModeStr, u8 RbN)
{
	while ((*VideoModeStr !='\0') && (*VideoModeStr != 'R')) {
		VideoModeStr++;
	}

	if (*(VideoModeStr + 2) == ')') {
		return RbN == 1;
	}
	if (*(VideoModeStr + 2) == '2') {
		return RbN == 2;
	}
	return 0;
}
/** @} */
