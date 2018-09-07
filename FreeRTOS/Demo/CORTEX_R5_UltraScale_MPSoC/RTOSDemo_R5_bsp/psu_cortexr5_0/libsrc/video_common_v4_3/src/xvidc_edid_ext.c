/******************************************************************************
*
* Copyright (C) 2017 - 2018 Xilinx, Inc.  All rights reserved.
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
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
* XILINX CONSORTIUM BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xhdmi_edid.h
*
* <b>Software Initalization & Configuration</b>
*
* <b>Interrupts </b>
*
* <b> Virtual Memory </b>
*
* This driver supports Virtual Memory. The RTOS is responsible for calculating
* the correct device base address in Virtual Memory space.
*
* <b> Threads </b>
*
* This driver is not thread safe. Any needs for threads or thread mutual
* exclusion must be satisfied by the layer above this driver.
*
* <b> Asserts </b>
*
* Asserts are used within all Xilinx drivers to enforce constraints on argument
* values. Asserts can be turned off on a system-wide basis by defining at
* compile time, the NDEBUG identifier. By default, asserts are turned on and it
* is recommended that users leave asserts on during development.
*
* <b> Building the driver </b>
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date       Changes
* ----- ---- ---------- --------------------------------------------------
* 1.0   mmo  24-01-2017 EDID Parser capability
* </pre>
*
******************************************************************************/
#include "stdio.h"
#include "string.h"
#include "stdlib.h"
#include "stdbool.h"
#include "xil_types.h"
#include "xstatus.h"
#include "xil_exception.h"
#include "xvidc_edid_ext.h"

static XV_VidC_PicAspectRatio xv_vidc_getPicAspectRatio(u16 hres, u16 vres);

static XV_VidC_PicAspectRatio xv_vidc_getPicAspectRatio(u16 hres, u16 vres) {
    XV_VidC_PicAspectRatio ar;
#define HAS_RATIO_OF(x, y)  (hres == (vres*(x)/(y))&&!((vres*(x))%(y)))
    if (HAS_RATIO_OF(16, 10)) {
        ar.width = 16;
        ar.height = 10;
        return ar;
    }
    if (HAS_RATIO_OF(4, 3)) {
        ar.width = 4;
        ar.height = 3;
        return ar;
    }
    if (HAS_RATIO_OF(5, 4)) {
        ar.width = 5;
        ar.height = 4;
        return ar;
    }
    if (HAS_RATIO_OF(16, 9)) {
        ar.width = 16;
        ar.height = 9;
        return ar;
#undef HAS_RATIO
    } else {
        ar.width = 0;
        ar.height = 0;
        return ar;
    }
}


void XV_VidC_EdidCtrlParamInit (XV_VidC_EdidCntrlParam *EdidCtrlParam) {
	
	/* Verify arguments. */
	Xil_AssertVoid(EdidCtrlParam != NULL);

	(void)memset((void *)EdidCtrlParam,  0,
			sizeof(XV_VidC_EdidCntrlParam));
			
	EdidCtrlParam->IsHdmi                = XVIDC_ISDVI;
    EdidCtrlParam->IsYCbCr444Supp        = XVIDC_NOT_SUPPORTED;
    EdidCtrlParam->IsYCbCr420Supp        = XVIDC_NOT_SUPPORTED;
    EdidCtrlParam->IsYCbCr422Supp        = XVIDC_NOT_SUPPORTED;
    EdidCtrlParam->IsYCbCr444DeepColSupp = XVIDC_NOT_SUPPORTED;
    EdidCtrlParam->Is30bppSupp           = XVIDC_NOT_SUPPORTED;
    EdidCtrlParam->Is36bppSupp           = XVIDC_NOT_SUPPORTED;
    EdidCtrlParam->Is48bppSupp           = XVIDC_NOT_SUPPORTED;
    EdidCtrlParam->IsYCbCr420dc30bppSupp = XVIDC_NOT_SUPPORTED;
    EdidCtrlParam->IsYCbCr420dc36bppSupp = XVIDC_NOT_SUPPORTED;
    EdidCtrlParam->IsYCbCr420dc48bppSupp = XVIDC_NOT_SUPPORTED;
    EdidCtrlParam->IsSCDCReadRequestReady= XVIDC_NOT_SUPPORTED;
    EdidCtrlParam->IsSCDCPresent         = XVIDC_NOT_SUPPORTED;
    EdidCtrlParam->MaxFrameRateSupp      = 0;
    EdidCtrlParam->MaxTmdsMhz            = 0;
}

XV_VidC_TimingParam
XV_VidC_timing
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    XV_VidC_TimingParam timing;

    timing.hres   = xvidc_edid_detailed_timing_horizontal_active(dtb);
    timing.vres   = xvidc_edid_detailed_timing_vertical_active(dtb);
    timing.htotal = timing.hres +
                        xvidc_edid_detailed_timing_horizontal_blanking(dtb);
    timing.vtotal = timing.vres +
                          xvidc_edid_detailed_timing_vertical_blanking(dtb);
    timing.hfp    = xvidc_edid_detailed_timing_horizontal_sync_offset(dtb);
    timing.vfp    = xvidc_edid_detailed_timing_vertical_sync_offset(dtb);
    timing.hsync_width  =
                xvidc_edid_detailed_timing_horizontal_sync_pulse_width(dtb);
    timing.vsync_width  =
                  xvidc_edid_detailed_timing_vertical_sync_pulse_width(dtb);
    timing.pixclk       = xvidc_edid_detailed_timing_pixel_clock(dtb);
    timing.vfreq        = (timing.pixclk / (timing.vtotal * timing.htotal));
    timing.vidfrmt      = (XVidC_VideoFormat) dtb->interlaced;
    timing.aspect_ratio =
                         xv_vidc_getPicAspectRatio (timing.hres, timing.vres);
    timing.hsync_polarity = dtb->signal_pulse_polarity;
    timing.vsync_polarity = dtb->signal_serration_polarity;

    return timing;
}

#if XVIDC_EDID_VERBOSITY > 1
XV_VidC_DoubleRep Double2Int (double in_val) {
	XV_VidC_DoubleRep DR;

	DR.Integer = in_val;
	DR.Decimal = (in_val - DR.Integer) * 10000;

	return (DR);
}
#endif
