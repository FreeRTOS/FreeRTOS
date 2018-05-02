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
 * @file xvidc_edid.h
 * @addtogroup video_common_v4_2
 * @{
 *
 * Contains macros, definitions, and function declarations related to the
 * Extended Display Identification Data (EDID) structure which is present in all
 * monitors. All content in this file is agnostic of communication interface
 * protocol.
 *
 * @note	None.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- -----------------------------------------------
 * 1.0   als  11/09/14 Initial release.
 * 2.2   als  02/01/16 Functions with pointer arguments that don't modify
 *                     contents now const.
 * 4.0   aad  10/26/16 Functions which return fixed point values instead of
 *		       float
 * </pre>
 *
*******************************************************************************/

#ifndef XVIDC_EDID_H_
/* Prevent circular inclusions by using protection macros. */
#define XVIDC_EDID_H_

#ifdef __cplusplus
extern "C" {
#endif
/******************************* Include Files ********************************/

#include "xstatus.h"
#include "xvidc.h"

/************************** Constant Definitions ******************************/

/** @name Address mapping for the base EDID block.
 * @{
 */
#define XVIDC_EDID_HEADER				0x00
/* Vendor and product identification. */
#define XVIDC_EDID_VPI_ID_MAN_NAME0			0x08
#define XVIDC_EDID_VPI_ID_MAN_NAME1			0x09
#define XVIDC_EDID_VPI_ID_PROD_CODE_LSB			0x0A
#define XVIDC_EDID_VPI_ID_PROD_CODE_MSB			0x0B
#define XVIDC_EDID_VPI_ID_SN0				0x0C
#define XVIDC_EDID_VPI_ID_SN1				0x0D
#define XVIDC_EDID_VPI_ID_SN2				0x0E
#define XVIDC_EDID_VPI_ID_SN3				0x0F
#define XVIDC_EDID_VPI_WEEK_MAN				0x10
#define XVIDC_EDID_VPI_YEAR				0x11
/* EDID structure version and revision. */
#define XVIDC_EDID_STRUCT_VER				0x12
#define XVIDC_EDID_STRUCT_REV				0x13
/* Basic display parameters and features. */
#define XVIDC_EDID_BDISP_VID				0x14
#define XVIDC_EDID_BDISP_H_SSAR				0x15
#define XVIDC_EDID_BDISP_V_SSAR				0x16
#define XVIDC_EDID_BDISP_GAMMA				0x17
#define XVIDC_EDID_BDISP_FEATURE			0x18
/* Color characteristics (display x,y chromaticity coordinates). */
#define XVIDC_EDID_CC_RG_LOW				0x19
#define XVIDC_EDID_CC_BW_LOW				0x1A
#define XVIDC_EDID_CC_REDX_HIGH				0x1B
#define XVIDC_EDID_CC_REDY_HIGH				0x1C
#define XVIDC_EDID_CC_GREENX_HIGH			0x1D
#define XVIDC_EDID_CC_GREENY_HIGH			0x1E
#define XVIDC_EDID_CC_BLUEX_HIGH			0x1F
#define XVIDC_EDID_CC_BLUEY_HIGH			0x20
#define XVIDC_EDID_CC_WHITEX_HIGH			0x21
#define XVIDC_EDID_CC_WHITEY_HIGH			0x22
/* Established timings. */
#define XVIDC_EDID_EST_TIMINGS_I			0x23
#define XVIDC_EDID_EST_TIMINGS_II			0x24
#define XVIDC_EDID_EST_TIMINGS_MAN			0x25
/* Standard timings. */
#define XVIDC_EDID_STD_TIMINGS_H(N)			(0x26 + 2 * (N - 1))
#define XVIDC_EDID_STD_TIMINGS_AR_FRR(N)		(0x27 + 2 * (N - 1))
/* 18 byte descriptors. */
#define XVIDC_EDID_18BYTE_DESCRIPTOR(N)			(0x36 + 18 * (N - 1))
#define XVIDC_EDID_PTM			(XVIDC_EDID_18BYTE_DESCRIPTOR(1))
/* - Detailed timing descriptor (DTD) / Preferred timing mode (PTM). */
#define XVIDC_EDID_DTD_PTM_PIXEL_CLK_KHZ_LSB		0x00
#define XVIDC_EDID_DTD_PTM_PIXEL_CLK_KHZ_MSB		0x01
#define XVIDC_EDID_DTD_PTM_HRES_LSB			0x02
#define XVIDC_EDID_DTD_PTM_HBLANK_LSB			0x03
#define XVIDC_EDID_DTD_PTM_HRES_HBLANK_U4		0x04
#define XVIDC_EDID_DTD_PTM_VRES_LSB			0x05
#define XVIDC_EDID_DTD_PTM_VBLANK_LSB			0x06
#define XVIDC_EDID_DTD_PTM_VRES_VBLANK_U4		0x07
#define XVIDC_EDID_DTD_PTM_HFPORCH_LSB			0x08
#define XVIDC_EDID_DTD_PTM_HSPW_LSB			0x09
#define XVIDC_EDID_DTD_PTM_VFPORCH_VSPW_L4		0x0A
#define XVIDC_EDID_DTD_PTM_XFPORCH_XSPW_U2		0x0B
#define XVIDC_EDID_DTD_PTM_HIMGSIZE_MM_LSB		0x0C
#define XVIDC_EDID_DTD_PTM_VIMGSIZE_MM_LSB		0x0D
#define XVIDC_EDID_DTD_PTM_XIMGSIZE_MM_U4		0x0E
#define XVIDC_EDID_DTD_PTM_HBORDER			0x0F
#define XVIDC_EDID_DTD_PTM_VBORDER			0x10
#define XVIDC_EDID_DTD_PTM_SIGNAL			0x11

/* Extension block count. */
#define XVIDC_EDID_EXT_BLK_COUNT			0x7E
/* Checksum. */
#define XVIDC_EDID_CHECKSUM				0x7F
/* @} */

/******************************************************************************/

/** @name Extended Display Identification Data: Masks, shifts, and values.
 * @{
 */
#define XVIDC_EDID_VPI_ID_MAN_NAME0_CHAR0_SHIFT		2
#define XVIDC_EDID_VPI_ID_MAN_NAME0_CHAR0_MASK		(0x1F << 2)
#define XVIDC_EDID_VPI_ID_MAN_NAME0_CHAR1_MASK		0x03
#define XVIDC_EDID_VPI_ID_MAN_NAME0_CHAR1_POS		3
#define XVIDC_EDID_VPI_ID_MAN_NAME1_CHAR1_SHIFT		5
#define XVIDC_EDID_VPI_ID_MAN_NAME1_CHAR2_MASK		0x1F

/* Basic display parameters and features: Video input definition. */
#define XVIDC_EDID_BDISP_VID_VSI_SHIFT			7
#define XVIDC_EDID_BDISP_VID_VSI_MASK			(0x01 << 7)
#define XVIDC_EDID_BDISP_VID_ANA_SLS_SHIFT		5
#define XVIDC_EDID_BDISP_VID_ANA_SLS_MASK		(0x03 << 5)
#define XVIDC_EDID_BDISP_VID_ANA_SLS_0700_0300_1000	0x0
#define XVIDC_EDID_BDISP_VID_ANA_SLS_0714_0286_1000	0x1
#define XVIDC_EDID_BDISP_VID_ANA_SLS_1000_0400_1400	0x2
#define XVIDC_EDID_BDISP_VID_ANA_SLS_0700_0000_0700	0x3
#define XVIDC_EDID_BDISP_VID_ANA_VID_SETUP_MASK		(0x01 << 4)
#define XVIDC_EDID_BDISP_VID_ANA_SEP_SYNC_HV_MASK	(0x01 << 3)
#define XVIDC_EDID_BDISP_VID_ANA_COMP_SYNC_H_MASK	(0x01 << 2)
#define XVIDC_EDID_BDISP_VID_ANA_COMP_SYNC_G_MASK	(0x01 << 1)
#define XVIDC_EDID_BDISP_VID_ANA_SERR_V_SYNC_MASK	(0x01)
#define XVIDC_EDID_BDISP_VID_DIG_BPC_SHIFT		4
#define XVIDC_EDID_BDISP_VID_DIG_BPC_MASK		(0x7 << 4)
#define XVIDC_EDID_BDISP_VID_DIG_BPC_UNDEF		0x0
#define XVIDC_EDID_BDISP_VID_DIG_BPC_6			0x1
#define XVIDC_EDID_BDISP_VID_DIG_BPC_8			0x2
#define XVIDC_EDID_BDISP_VID_DIG_BPC_10			0x3
#define XVIDC_EDID_BDISP_VID_DIG_BPC_12			0x4
#define XVIDC_EDID_BDISP_VID_DIG_BPC_14			0x5
#define XVIDC_EDID_BDISP_VID_DIG_BPC_16			0x6
#define XVIDC_EDID_BDISP_VID_DIG_VIS_MASK		0xF
#define XVIDC_EDID_BDISP_VID_DIG_VIS_UNDEF		0x0
#define XVIDC_EDID_BDISP_VID_DIG_VIS_DVI		0x1
#define XVIDC_EDID_BDISP_VID_DIG_VIS_HDMIA		0x2
#define XVIDC_EDID_BDISP_VID_DIG_VIS_HDMIB		0x3
#define XVIDC_EDID_BDISP_VID_DIG_VIS_MDDI		0x4
#define XVIDC_EDID_BDISP_VID_DIG_VIS_DP			0x5

/* Basic display parameters and features: Feature support. */
#define XVIDC_EDID_BDISP_FEATURE_PM_STANDBY_MASK	(0x1 << 7)
#define XVIDC_EDID_BDISP_FEATURE_PM_SUSPEND_MASK	(0x1 << 6)
#define XVIDC_EDID_BDISP_FEATURE_PM_OFF_VLP_MASK	(0x1 << 5)
#define XVIDC_EDID_BDISP_FEATURE_ANA_COLORTYPE_SHIFT	3
#define XVIDC_EDID_BDISP_FEATURE_ANA_COLORTYPE_MASK	(0x3 << 3)
#define XVIDC_EDID_BDISP_FEATURE_ANA_COLORTYPE_MCG	0x0
#define XVIDC_EDID_BDISP_FEATURE_ANA_COLORTYPE_RGB	0x1
#define XVIDC_EDID_BDISP_FEATURE_ANA_COLORTYPE_NRGB	0x2
#define XVIDC_EDID_BDISP_FEATURE_ANA_COLORTYPE_UNDEF	0x3
#define XVIDC_EDID_BDISP_FEATURE_DIG_COLORENC_YCRCB444_MASK	(0x1 << 3)
#define XVIDC_EDID_BDISP_FEATURE_DIG_COLORENC_YCRCB422_MASK	(0x1 << 4)
#define XVIDC_EDID_BDISP_FEATURE_SRGB_DEF_MASK		(0x1 << 2)
#define XVIDC_EDID_BDISP_FEATURE_PTM_INC_MASK		(0x1 << 1)
#define XVIDC_EDID_BDISP_FEATURE_CONTFREQ_MASK		(0x1)

/* Color characteristics (display x,y chromaticity coordinates). */
#define XVIDC_EDID_CC_HIGH_SHIFT			2
#define XVIDC_EDID_CC_RBX_LOW_SHIFT			6
#define XVIDC_EDID_CC_RBY_LOW_SHIFT			4
#define XVIDC_EDID_CC_RBY_LOW_MASK			(0x3 << 4)
#define XVIDC_EDID_CC_GWX_LOW_SHIFT			2
#define XVIDC_EDID_CC_GWX_LOW_MASK			(0x3 << 2)
#define XVIDC_EDID_CC_GWY_LOW_MASK			(0x3)
#define XVIDC_EDID_CC_GREENY_HIGH			0x1E
#define XVIDC_EDID_CC_BLUEX_HIGH			0x1F
#define XVIDC_EDID_CC_BLUEY_HIGH			0x20
#define XVIDC_EDID_CC_WHITEX_HIGH			0x21
#define XVIDC_EDID_CC_WHITEY_HIGH			0x22

/* Established timings. */
#define XVIDC_EDID_EST_TIMINGS_I_720x400_70_MASK	(0x1 << 7)
#define XVIDC_EDID_EST_TIMINGS_I_720x400_88_MASK	(0x1 << 6)
#define XVIDC_EDID_EST_TIMINGS_I_640x480_60_MASK	(0x1 << 5)
#define XVIDC_EDID_EST_TIMINGS_I_640x480_67_MASK	(0x1 << 4)
#define XVIDC_EDID_EST_TIMINGS_I_640x480_72_MASK	(0x1 << 3)
#define XVIDC_EDID_EST_TIMINGS_I_640x480_75_MASK	(0x1 << 2)
#define XVIDC_EDID_EST_TIMINGS_I_800x600_56_MASK	(0x1 << 1)
#define XVIDC_EDID_EST_TIMINGS_I_800x600_60_MASK	(0x1)
#define XVIDC_EDID_EST_TIMINGS_II_800x600_72_MASK	(0x1 << 7)
#define XVIDC_EDID_EST_TIMINGS_II_800x600_75_MASK	(0x1 << 6)
#define XVIDC_EDID_EST_TIMINGS_II_832x624_75_MASK	(0x1 << 5)
#define XVIDC_EDID_EST_TIMINGS_II_1024x768_87_MASK	(0x1 << 4)
#define XVIDC_EDID_EST_TIMINGS_II_1024x768_60_MASK	(0x1 << 3)
#define XVIDC_EDID_EST_TIMINGS_II_1024x768_70_MASK	(0x1 << 2)
#define XVIDC_EDID_EST_TIMINGS_II_1024x768_75_MASK	(0x1 << 1)
#define XVIDC_EDID_EST_TIMINGS_II_1280x1024_75_MASK	(0x1)
#define XVIDC_EDID_EST_TIMINGS_MAN_1152x870_75_MASK	(0x1 << 7)
#define XVIDC_EDID_EST_TIMINGS_MAN_MASK			(0x7F)

/* Standard timings. */
#define XVIDC_EDID_STD_TIMINGS_AR_SHIFT			6
#define XVIDC_EDID_STD_TIMINGS_AR_16_10			0x0
#define XVIDC_EDID_STD_TIMINGS_AR_4_3			0x1
#define XVIDC_EDID_STD_TIMINGS_AR_5_4			0x2
#define XVIDC_EDID_STD_TIMINGS_AR_16_9			0x3
#define XVIDC_EDID_STD_TIMINGS_FRR_MASK			(0x3F)

/* Detailed timing descriptor (DTD) / Preferred timing mode (PTM). */
#define XVIDC_EDID_DTD_PTM_XRES_XBLANK_U4_XBLANK_MASK		0x0F
#define XVIDC_EDID_DTD_PTM_XRES_XBLANK_U4_XRES_MASK		0xF0
#define XVIDC_EDID_DTD_PTM_XRES_XBLANK_U4_XRES_SHIFT		4
#define XVIDC_EDID_DTD_PTM_VFPORCH_VSPW_L4_VSPW_MASK		0x0F
#define XVIDC_EDID_DTD_PTM_VFPORCH_VSPW_L4_VFPORCH_MASK		0xF0
#define XVIDC_EDID_DTD_PTM_VFPORCH_VSPW_L4_VFPORCH_SHIFT	4
#define XVIDC_EDID_DTD_PTM_XFPORCH_XSPW_U2_HFPORCH_MASK		0xC0
#define XVIDC_EDID_DTD_PTM_XFPORCH_XSPW_U2_HSPW_MASK		0x30
#define XVIDC_EDID_DTD_PTM_XFPORCH_XSPW_U2_VFPORCH_MASK		0x0C
#define XVIDC_EDID_DTD_PTM_XFPORCH_XSPW_U2_VSPW_MASK		0x03
#define XVIDC_EDID_DTD_PTM_XFPORCH_XSPW_U2_HFPORCH_SHIFT	6
#define XVIDC_EDID_DTD_PTM_XFPORCH_XSPW_U2_HSPW_SHIFT		4
#define XVIDC_EDID_DTD_PTM_XFPORCH_XSPW_U2_VFPORCH_SHIFT	2
#define XVIDC_EDID_DTD_PTM_XIMGSIZE_MM_U4_VIMGSIZE_MM_MASK	0x0F
#define XVIDC_EDID_DTD_PTM_XIMGSIZE_MM_U4_HIMGSIZE_MM_MASK	0xF0
#define XVIDC_EDID_DTD_PTM_XIMGSIZE_MM_U4_HIMGSIZE_MM_SHIFT	4
#define XVIDC_EDID_DTD_PTM_SIGNAL_INTERLACED_MASK		0x80
#define XVIDC_EDID_DTD_PTM_SIGNAL_INTERLACED_SHIFT		7
#define XVIDC_EDID_DTD_PTM_SIGNAL_HPOLARITY_MASK		0x02
#define XVIDC_EDID_DTD_PTM_SIGNAL_VPOLARITY_MASK		0x04
#define XVIDC_EDID_DTD_PTM_SIGNAL_HPOLARITY_SHIFT		1
#define XVIDC_EDID_DTD_PTM_SIGNAL_VPOLARITY_SHIFT		2
/* @} */

/******************* Macros (Inline Functions) Definitions ********************/

#define XVidC_EdidIsHeaderValid(E) \
	!memcmp(E, "\x00\xFF\xFF\xFF\xFF\xFF\xFF\x00", 8)

/* Vendor and product identification: ID manufacturer name. */
/* void XVidC_EdidGetManName(const u8 *EdidRaw, char ManName[4]); */

/* Vendor and product identification: ID product code. */
#define XVidC_EdidGetIdProdCode(E) \
	((u16)((E[XVIDC_EDID_VPI_ID_PROD_CODE_MSB] << 8) | \
	E[XVIDC_EDID_VPI_ID_PROD_CODE_LSB]))

/* Vendor and product identification: ID serial number. */
#define XVidC_EdidGetIdSn(E) \
	((u32)((E[XVIDC_EDID_VPI_ID_SN3] << 24) | \
	(E[XVIDC_EDID_VPI_ID_SN2] << 16) | (E[XVIDC_EDID_VPI_ID_SN1] << 8) | \
	E[XVIDC_EDID_VPI_ID_SN0]))

/* Vendor and product identification: Week and year of manufacture or model
 * year. */
#define XVidC_EdidGetManWeek(E)		(E[XVIDC_EDID_VPI_WEEK_MAN])
#define XVidC_EdidGetModManYear(E)	(E[XVIDC_EDID_VPI_YEAR] + 1990)
#define XVidC_EdidIsYearModel(E)	(XVidC_EdidGetManWeek(E) == 0xFF)
#define XVidC_EdidIsYearMan(E)		(XVidC_EdidGetManWeek(E) != 0xFF)

/* EDID structure version and revision. */
#define XVidC_EdidGetStructVer(E)	(E[XVIDC_EDID_STRUCT_VER])
#define XVidC_EdidGetStructRev(E)	(E[XVIDC_EDID_STRUCT_REV])

/* Basic display parameters and features: Video input definition. */
#define XVidC_EdidIsDigitalSig(E) \
	((E[XVIDC_EDID_BDISP_VID] & XVIDC_EDID_BDISP_VID_VSI_MASK) != 0)
#define XVidC_EdidIsAnalogSig(E) \
	((E[XVIDC_EDID_BDISP_VID] & XVIDC_EDID_BDISP_VID_VSI_MASK) == 0)
#define XVidC_EdidGetAnalogSigLvlStd(E) \
	((E[XVIDC_EDID_BDISP_VID] & XVIDC_EDID_BDISP_VID_ANA_SLS_MASK) >> \
	XVIDC_EDID_BDISP_VID_ANA_SLS_SHIFT)
#define XVidC_EdidGetAnalogSigVidSetup(E) \
	((E[XVIDC_EDID_BDISP_VID] & \
	XVIDC_EDID_BDISP_VID_ANA_VID_SETUP_MASK) != 0)
#define XVidC_EdidSuppAnalogSigSepSyncHv(E) \
	((E[XVIDC_EDID_BDISP_VID] & \
	XVIDC_EDID_BDISP_VID_ANA_SEP_SYNC_HV_MASK) != 0)
#define XVidC_EdidSuppAnalogSigCompSyncH(E) \
	((E[XVIDC_EDID_BDISP_VID] & \
	XVIDC_EDID_BDISP_VID_ANA_COMP_SYNC_H_MASK) != 0)
#define XVidC_EdidSuppAnalogSigCompSyncG(E) \
	((E[XVIDC_EDID_BDISP_VID] & \
	XVIDC_EDID_BDISP_VID_ANA_COMP_SYNC_G_MASK) != 0)
#define XVidC_EdidSuppAnalogSigSerrVsync(E) \
	((E[XVIDC_EDID_BDISP_VID] & \
	XVIDC_EDID_BDISP_VID_ANA_SERR_V_SYNC_MASK) != 0)
/* XVidC_ColorDepth XVidC_EdidGetColorDepth(const u8 *EdidRaw); */
#define XVidC_EdidGetDigitalSigIfaceStd(E) \
	(E[XVIDC_EDID_BDISP_VID] & XVIDC_EDID_BDISP_VID_DIG_VIS_MASK)

/* Basic display parameters and features: Horizontal and vertical screen size or
 * aspect ratio. */
#define XVidC_EdidIsSsArDefined(E) \
	((E[XVIDC_EDID_BDISP_H_SSAR] | E[XVIDC_EDID_BDISP_V_SSAR]) != 0)
#define XVidC_EdidGetSsArH(E)	E[XVIDC_EDID_BDISP_H_SSAR]
#define XVidC_EdidGetSsArV(E)	E[XVIDC_EDID_BDISP_V_SSAR]
#define XVidC_EdidIsSsArSs(E) \
	((XVidC_EdidGetSsArH(E) != 0) && (XVidC_EdidGetSsArV(E) != 0))
#define XVidC_EdidIsSsArArL(E) \
	((XVidC_EdidGetSsArH(E) != 0) && (XVidC_EdidGetSsArV(E) == 0))
#define XVidC_EdidIsSsArArP(E) \
	((XVidC_EdidGetSsArH(E) == 0) && (XVidC_EdidGetSsArV(E) != 0))
#define XVidC_EdidGetSsArArL(E) \
	((float)((XVidC_EdidGetSsArH(E) + 99.0) / 100.0))
#define XVidC_EdidGetSsArArP(E) \
	((float)(100.0 / (XVidC_EdidGetSsArV(E) + 99.0)))

/* Basic display parameters and features: Gamma. */
#define XVidC_EdidIsGammaInExt(E)	(E[XVIDC_EDID_BDISP_GAMMA] == 0xFF)
#define XVidC_EdidGetGamma(E) \
	((float)((E[XVIDC_EDID_BDISP_GAMMA] + 100.0) / 100.0))

/* Basic display parameters and features: Feature support. */
#define XVidC_EdidSuppFeaturePmStandby(E) \
	((E[XVIDC_EDID_BDISP_FEATURE] & \
	XVIDC_EDID_BDISP_FEATURE_PM_STANDBY_MASK) != 0)
#define XVidC_EdidSuppFeaturePmSuspend(E) \
	((E[XVIDC_EDID_BDISP_FEATURE] & \
	XVIDC_EDID_BDISP_FEATURE_PM_SUSPEND_MASK) != 0)
#define XVidC_EdidSuppFeaturePmOffVlp(E) \
	((E[XVIDC_EDID_BDISP_FEATURE] & \
	XVIDC_EDID_BDISP_FEATURE_PM_OFF_VLP_MASK) != 0)
#define XVidC_EdidGetFeatureAnaColorType(E) \
	((E[XVIDC_EDID_BDISP_FEATURE] & \
	XVIDC_EDID_BDISP_FEATURE_ANA_COLORTYPE_MASK) >> \
	XVIDC_EDID_BDISP_FEATURE_ANA_COLORTYPE_SHIFT)
#define XVidC_EdidSuppFeatureDigColorEncYCrCb444(E) \
	((E[XVIDC_EDID_BDISP_FEATURE] & \
	XVIDC_EDID_BDISP_FEATURE_DIG_COLORENC_YCRCB444_MASK) != 0)
#define XVidC_EdidSuppFeatureDigColorEncYCrCb422(E) \
	((E[XVIDC_EDID_BDISP_FEATURE] & \
	XVIDC_EDID_BDISP_FEATURE_DIG_COLORENC_YCRCB422_MASK) != 0)
#define XVidC_EdidIsFeatureSrgbDef(E) \
	((E[XVIDC_EDID_BDISP_FEATURE] & \
	XVIDC_EDID_BDISP_FEATURE_SRGB_DEF_MASK) != 0)
#define XVidC_EdidIsFeaturePtmInc(E) \
	((E[XVIDC_EDID_BDISP_FEATURE] & \
	XVIDC_EDID_BDISP_FEATURE_PTM_INC_MASK) != 0)
#define XVidC_EdidIsFeatureContFreq(E) \
	((E[XVIDC_EDID_BDISP_FEATURE] & \
	XVIDC_EDID_BDISP_FEATURE_CONTFREQ_MASK) != 0)

/* Established timings. */
#define XVidC_EdidSuppEstTimings720x400_70(E) \
	((E[XVIDC_EDID_EST_TIMINGS_I] & \
	XVIDC_EDID_EST_TIMINGS_I_720x400_70_MASK) != 0)
#define XVidC_EdidSuppEstTimings720x400_88(E) \
	((E[XVIDC_EDID_EST_TIMINGS_I] & \
	XVIDC_EDID_EST_TIMINGS_I_720x400_88_MASK) != 0)
#define XVidC_EdidSuppEstTimings640x480_60(E) \
	((E[XVIDC_EDID_EST_TIMINGS_I] & \
	XVIDC_EDID_EST_TIMINGS_I_640x480_60_MASK) != 0)
#define XVidC_EdidSuppEstTimings640x480_67(E) \
	((E[XVIDC_EDID_EST_TIMINGS_I] & \
	XVIDC_EDID_EST_TIMINGS_I_640x480_67_MASK) != 0)
#define XVidC_EdidSuppEstTimings640x480_72(E) \
	((E[XVIDC_EDID_EST_TIMINGS_I] & \
	XVIDC_EDID_EST_TIMINGS_I_640x480_72_MASK) != 0)
#define XVidC_EdidSuppEstTimings640x480_75(E) \
	((E[XVIDC_EDID_EST_TIMINGS_I] & \
	XVIDC_EDID_EST_TIMINGS_I_640x480_75_MASK) != 0)
#define XVidC_EdidSuppEstTimings800x600_56(E) \
	((E[XVIDC_EDID_EST_TIMINGS_I] & \
	XVIDC_EDID_EST_TIMINGS_I_800x600_56_MASK) != 0)
#define XVidC_EdidSuppEstTimings800x600_60(E) \
	((E[XVIDC_EDID_EST_TIMINGS_I] & \
	XVIDC_EDID_EST_TIMINGS_I_800x600_60_MASK) != 0)
#define XVidC_EdidSuppEstTimings800x600_72(E) \
	((E[XVIDC_EDID_EST_TIMINGS_II] & \
	XVIDC_EDID_EST_TIMINGS_II_800x600_72_MASK) != 0)
#define XVidC_EdidSuppEstTimings800x600_75(E) \
	((E[XVIDC_EDID_EST_TIMINGS_II] & \
	XVIDC_EDID_EST_TIMINGS_II_800x600_75_MASK) != 0)
#define XVidC_EdidSuppEstTimings832x624_75(E) \
	((E[XVIDC_EDID_EST_TIMINGS_II] & \
	XVIDC_EDID_EST_TIMINGS_II_832x624_75_MASK) != 0)
#define XVidC_EdidSuppEstTimings1024x768_87(E) \
	((E[XVIDC_EDID_EST_TIMINGS_II] & \
	XVIDC_EDID_EST_TIMINGS_II_1024x768_87_MASK) != 0)
#define XVidC_EdidSuppEstTimings1024x768_60(E) \
	((E[XVIDC_EDID_EST_TIMINGS_II] & \
	XVIDC_EDID_EST_TIMINGS_II_1024x768_60_MASK) != 0)
#define XVidC_EdidSuppEstTimings1024x768_70(E) \
	((E[XVIDC_EDID_EST_TIMINGS_II] & \
	XVIDC_EDID_EST_TIMINGS_II_1024x768_70_MASK) != 0)
#define XVidC_EdidSuppEstTimings1024x768_75(E) \
	((E[XVIDC_EDID_EST_TIMINGS_II] & \
	XVIDC_EDID_EST_TIMINGS_II_1024x768_75_MASK) != 0)
#define XVidC_EdidSuppEstTimings1280x1024_75(E) \
	((E[XVIDC_EDID_EST_TIMINGS_II] & \
	XVIDC_EDID_EST_TIMINGS_II_1280x1024_75_MASK) != 0)
#define XVidC_EdidSuppEstTimings1152x870_75(E) \
	((E[XVIDC_EDID_EST_TIMINGS_MAN] & \
	XVIDC_EDID_EST_TIMINGS_MAN_1152x870_75_MASK) != 0)
#define XVidC_EdidGetTimingsMan(E) \
	(E[XVIDC_EDID_EST_TIMINGS_MAN] & XVIDC_EDID_EST_TIMINGS_MAN_MASK)

/* Standard timings. */
#define XVidC_EdidGetStdTimingsH(E, N) \
	((E[XVIDC_EDID_STD_TIMINGS_H(N)] + 31) * 8)
#define XVidC_EdidGetStdTimingsAr(E, N) \
	(E[XVIDC_EDID_STD_TIMINGS_AR_FRR(N)] >> XVIDC_EDID_STD_TIMINGS_AR_SHIFT)
#define XVidC_EdidGetStdTimingsFrr(E, N) \
	((E[XVIDC_EDID_STD_TIMINGS_AR_FRR(N)] & \
	XVIDC_EDID_STD_TIMINGS_FRR_MASK) + 60)
/* u16 XVidC_EdidGetStdTimingsV(const u8 *EdidRaw, u8 StdTimingsNum); */
#define XVidC_EdidIsDtdPtmInterlaced(E) \
	((E[XVIDC_EDID_PTM + XVIDC_EDID_DTD_PTM_SIGNAL] & \
	XVIDC_EDID_DTD_PTM_SIGNAL_INTERLACED_MASK) >> \
	XVIDC_EDID_DTD_PTM_SIGNAL_INTERLACED_SHIFT)

/* Extension block count. */
#define XVidC_EdidGetExtBlkCount(E)	(E[XVIDC_EDID_EXT_BLK_COUNT])

/* Checksum. */
#define XVidC_EdidGetChecksum(E)	(E[XVIDC_EDID_CHECKSUM])

/**************************** Function Prototypes *****************************/

/* Vendor and product identification: ID manufacturer name. */
void XVidC_EdidGetManName(const u8 *EdidRaw, char ManName[4]);

/* Basic display parameters and features: Video input definition. */
XVidC_ColorDepth XVidC_EdidGetColorDepth(const u8 *EdidRaw);

/* Color characteristics (display x,y chromaticity coordinates). */
int XVidC_EdidGetCcRedX(const u8 *EdidRaw);
int XVidC_EdidGetCcRedY(const u8 *EdidRaw);
int XVidC_EdidGetCcGreenX(const u8 *EdidRaw);
int XVidC_EdidGetCcGreenY(const u8 *EdidRaw);
int XVidC_EdidGetCcBlueX(const u8 *EdidRaw);
int XVidC_EdidGetCcBlueY(const u8 *EdidRaw);
int XVidC_EdidGetCcWhiteX(const u8 *EdidRaw);
int XVidC_EdidGetCcWhiteY(const u8 *EdidRaw);

/* Standard timings. */
u16 XVidC_EdidGetStdTimingsV(const u8 *EdidRaw, u8 StdTimingsNum);

/* Utility functions. */
u32 XVidC_EdidIsVideoTimingSupported(const u8 *EdidRaw,
		const XVidC_VideoTimingMode *VtMode);

#ifdef __cplusplus
}
#endif
#endif /* XVIDC_EDID_H_ */
/** @} */
