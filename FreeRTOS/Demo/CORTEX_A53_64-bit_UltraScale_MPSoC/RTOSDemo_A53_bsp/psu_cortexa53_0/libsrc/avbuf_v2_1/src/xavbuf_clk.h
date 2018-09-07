/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
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
******************************************************************************/
/******************************************************************************/
/**
 *
 * @file xavbuf_clk.h
 *
 * This header file contains the identifiers and low-level driver functions (or
 * macros) that can be used to configure PLL to generate required frequency.
 *
 * @note	None.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- -----------------------------------------------
 * 1.0   mh  06/24/17 Initial release.
 * 2.1   tu  12/29/17 LPD and FPD offsets adjusted
 * </pre>
 *
*******************************************************************************/

#ifndef XAVBUF_CLK_H_
#define XAVBUF_CLK_H_

/******************************* Include Files ********************************/
#include "xavbuf_hw.h"
#include "xstatus.h"
#include "sleep.h"

/****************************** Type Definitions ******************************/
/**
 * This enum enumerates various PLL
 */
enum PLL{
	APLL  = 0,
	DPLL  = 1,
	VPLL  = 2,
	IOPLL = 3,
	RPLL  = 4
};

/**
 * This typedef enumerates various variables used to configure Pll
 */
typedef struct {
	u64 BaseAddress;
	u64 Fractional;
	u64 RefClkFreqhz;
	u32 Divider;
	u8 Offset;
	u8 ClkDividBy2;
	u8 ExtDivider0;
	u8 ExtDivider1;
	u8 ExtDividerCnt;
	u8 DomainSwitchDiv;
	u8 FracIntegerFBDIV;
	u8 IntegerFBDIV;
	u8 InputRefClk;
	u8 Fpd;
	u8 Pll;
}XAVBuf_Pll;

/**************************** Function Prototypes *****************************/
int XAVBuf_SetPixelClock(u64 FreqHz);
int XAVBuf_SetAudioClock(u64 FreqHz);
#endif /* XAVBUF_CLK_H_ */
