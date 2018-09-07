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
 * @file xavbuf_videoformats.c
 * @addtogroup xavbuf_v2_1
 * @{
 *
 * Contains attributes of the video formats mapped to the hardware
 *
 * @note	None.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- -----------------------------------------------
 * 1.0   aad  03/10/17 Initial release.
 * 2.0   aad  02/22/18 Fixed scaling factors and bits per pixel
 * </pre>
 *
*******************************************************************************/

/******************************* Include Files ********************************/

#include "xavbuf.h"


/**************************** Variable Definitions ****************************/
#ifdef __cplusplus
extern "C"
#endif

const XAVBuf_VideoAttribute XAVBuf_SupportedFormats[XAVBUF_NUM_SUPPORTED] =
{
	/* Non - Live Video Formats */
	{ CbY0CrY1, 0, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, FALSE, 16},
	{ CrY0CbY1, 1, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, FALSE, 16},
	{ Y0CrY1Cb, 2, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, FALSE, 16},
	{ Y0CbY1Cr, 3, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, FALSE, 16},
	{ YV16, 4, Planar,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, FALSE, 16},
	{ YV24, 5, Planar,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, FALSE, FALSE, 24},
	{ YV16Ci, 6, SemiPlanar,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, FALSE, 16},
	{ MONOCHROME, 7, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, FALSE, 8},
	{ YV16Ci2, 8, SemiPlanar,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, TRUE, 16},
	{ YUV444, 9, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, FALSE, FALSE, 24},
	{ RGB888, 10, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, TRUE, FALSE, 24},
	{ RGBA8880, 11, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, TRUE, FALSE, 32},
	{ RGB888_10BPC, 12, Interleaved,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		FALSE, TRUE, FALSE, 30},
	{ YUV444_10BPC, 13, Interleaved,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		FALSE, FALSE, FALSE, 30},
	{ YV16Ci2_10BPC, 14, SemiPlanar,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		TRUE, FALSE, TRUE, 20},
	{ YV16Ci_10BPC, 15, SemiPlanar,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		TRUE, FALSE, FALSE, 20},
	{ YV16_10BPC, 16, Planar,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		TRUE, FALSE, FALSE, 20},
	{ YV24_10BPC, 17, Planar,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		FALSE, FALSE, FALSE, 30},
	{ MONOCHROME_10BPC, 18, Interleaved,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		TRUE, FALSE, FALSE, 10},
	{ YV16_420, 19, Planar,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, FALSE, 16},
	{ YV16Ci_420, 20, SemiPlanar,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, FALSE, 16},
	{ YV16Ci2_420, 21, SemiPlanar,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, TRUE, 16},
	{ YV16_420_10BPC, 22, Planar,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		TRUE, FALSE, FALSE, 20},
	{ YV16Ci_420_10BPC, 23, SemiPlanar,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		TRUE, FALSE, FALSE, 20},
	{ YV16Ci2_420_10BPC, 24, SemiPlanar,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		TRUE, FALSE, TRUE, 20},

	/* Non-Live Graphics formats */
	{ RGBA8888, 0, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, TRUE, FALSE, 32},
	{ ABGR8888, 1, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, TRUE, FALSE, 32},
	{ RGB888_GFX, 2, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, TRUE, FALSE, 24},
	{ BGR888, 3, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, TRUE, FALSE, 24},
	{ RGBA5551, 4, Interleaved,
		{XAVBUF_BUF_5BIT_SF, XAVBUF_BUF_5BIT_SF, XAVBUF_BUF_5BIT_SF},
		FALSE, TRUE, FALSE, 16},
	{ RGBA4444, 5, Interleaved,
		{XAVBUF_BUF_4BIT_SF, XAVBUF_BUF_4BIT_SF, XAVBUF_BUF_4BIT_SF},
		FALSE, TRUE, FALSE, 16},
	{ RGB565, 6, Interleaved,
		{XAVBUF_BUF_5BIT_SF, XAVBUF_BUF_6BIT_SF, XAVBUF_BUF_5BIT_SF},
		FALSE, TRUE, FALSE, 16},
	{ BPP8, 7, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, TRUE, FALSE, 8},
	{ BPP4, 8, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, TRUE, FALSE, 4},
	{ BPP2, 9, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, TRUE, FALSE, 2},
	{ BPP1, 10, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, TRUE, FALSE, 1},
	{ YUV422, 11, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, FALSE, FALSE, 24},

	/* Video Formats for Live Video/Graphics input and output sources */
	{ RGB_6BPC, 0, Interleaved,
		{XAVBUF_BUF_6BIT_SF, XAVBUF_BUF_6BIT_SF, XAVBUF_BUF_6BIT_SF},
		FALSE, TRUE, FALSE, 18},
	{ RGB_8BPC, 0, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, TRUE, FALSE, 24},
	{ RGB_10BPC, 0, Interleaved,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		FALSE, TRUE, FALSE, 30},
	{ RGB_12BPC, 0, Interleaved,
		{XAVBUF_BUF_12BIT_SF, XAVBUF_BUF_12BIT_SF, XAVBUF_BUF_12BIT_SF},
		FALSE, TRUE, FALSE, 36},
	{ YCbCr444_6BPC, 1, Interleaved,
		{XAVBUF_BUF_6BIT_SF, XAVBUF_BUF_6BIT_SF, XAVBUF_BUF_6BIT_SF},
		FALSE, FALSE, FALSE, 18},
	{ YCbCr444_8BPC, 1, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		FALSE, FALSE, FALSE, 24},
	{ YCbCr444_10BPC, 1, Interleaved,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		FALSE, FALSE, FALSE, 30},
	{ YCbCr444_12BPC, 1, Interleaved,
		{XAVBUF_BUF_12BIT_SF, XAVBUF_BUF_12BIT_SF, XAVBUF_BUF_12BIT_SF},
		FALSE, FALSE, FALSE, 36},
	{ YCbCr422_8BPC, 2, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, FALSE, 24},
	{ YCbCr422_10BPC, 2, Interleaved,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		TRUE, FALSE, FALSE, 30},
	{ YCbCr422_12BPC, 2, Interleaved,
		{XAVBUF_BUF_12BIT_SF, XAVBUF_BUF_12BIT_SF, XAVBUF_BUF_12BIT_SF},
		TRUE, FALSE, FALSE, 36},
	{ YOnly_8BPC, 3, Interleaved,
		{XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF, XAVBUF_BUF_8BIT_SF},
		TRUE, FALSE, FALSE, 24},
	{ YOnly_10BPC, 3, Interleaved,
		{XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF, XAVBUF_BUF_10BIT_SF},
		TRUE, FALSE, FALSE, 30},
	{ YOnly_12BPC, 3, Interleaved,
		{XAVBUF_BUF_12BIT_SF, XAVBUF_BUF_12BIT_SF, XAVBUF_BUF_12BIT_SF},
		TRUE, FALSE, FALSE, 36},

};

/** @} */
