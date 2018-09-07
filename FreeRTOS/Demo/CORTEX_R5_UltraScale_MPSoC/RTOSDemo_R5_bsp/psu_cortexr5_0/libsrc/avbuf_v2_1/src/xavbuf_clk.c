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
 * @file xavbuf.c
 *
 * This header file contains PLL configuring functions. These Functions
 * calculates and configures the PLL depending on desired frequency.
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
/******************************* Include Files ********************************/
#include "xavbuf_clk.h"

/**************************** Constant Definitions ****************************/
/*Input Frequency for the PLL with precision upto two decimals*/
#define XAVBUF_INPUT_REF_CLK		3333333333

/*Frequency of VCO before divider to meet jitter requirement*/
#define XAVBUF_PLL_OUT_FREQ		1450000000

/* Precision of Input Ref Frequency for PLL*/
#define XAVBUF_INPUT_FREQ_PRECISION	100

/* 16 bit  fractional shift to get Integer */
#define XAVBUF_PRECISION		16
#define XAVBUF_SHIFT_DECIMAL		(1 <<  XAVBUF_PRECISION)
#define XAVBUF_DECIMAL			(XAVBUF_SHIFT_DECIMAL - 1)
#define XDPSSU_MAX_VIDEO_FREQ		300000000

#define XAVBUF_AUDIO_SAMPLES		512
#define XAVBUF_AUDIO_SAMPLE_RATE_44_1	44100
#define XAVBUF_AUDIO_SAMPLE_RATE_48_0	48000
#define XAVBUF_EXTERNAL_DIVIDER		2

/* Register offsets for address manipulation */
#define XAVBUF_REG_OFFSET		4
#define XAVBUF_FPD_CTRL_OFFSET          12
#define XAVBUF_LPD_CTRL_OFFSET          16
#define MOD_3(a)			((a) % (3))

/*************************** Constant Variable Definitions ********************/
/**
 * This typedef enumerates capacitor resistor and lock values to be programmed.
 */
typedef struct{
	u16 cp;
	u16 res;
	u16 lfhf;
	u16 lock_dly;
	u16 lock_cnt;
}PllConfig;

/* PLL fractional divide programming table*/
static const PllConfig PllFracDivideTable[] = {
		{3,	5,	3,	63,	1000},
		{3,	5,	3,	63,	1000},
		{3,	9,	3,	63,	1000},
		{3,	9,	3,	63,	1000},
		{3,	9,	3,	63,	1000},
		{3,	9,	3,	63,	1000},
		{3,	14,	3,	63,	1000},
		{3,	14,	3,	63,	1000},
		{3,	14,	3,	63,	1000},
		{3,	14,	3,	63,	1000},
		{3,	14,	3,	63,	1000},
		{3,	14,	3,	63,	1000},
		{3,	14,	3,	63,	1000},
		{3,	14,	3,	63,	975},
		{3,	14,	3,	63,	950},
		{3,	14,	3,	63,	925},
		{3,	1,	3,	63,	900},
		{3,	1,	3,	63,	875},
		{3,	1,	3,	63,	850},
		{3,	1,	3,	63,	850},
		{3,	1,	3,	63,	825},
		{3,	1,	3,	63,	800},
		{3,	1,	3,	63,	775},
		{3,	6,	3,	63,	775},
		{3,	6,	3,	63,	750},
		{3,	6,	3,	63,	725},
		{3,	6,	3,	63,	700},
		{3,	6,	3,	63,	700},
		{3,	6,	3,	63,	675},
		{3,	6,	3,	63,	675},
		{3,	6,	3,	63,	650},
		{3,	6,	3,	63,	650},
		{3,	6,	3,	63,	625},
		{3,	6,	3,	63,	625},
		{3,	6,	3,	63,	625},
		{3,	6,	3,	63,	600},
		{3,	6,	3,	63,	600},
		{3,	6,	3,	63,	600},
		{3,	6,	3,	63,	600},
		{3,	6,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{3,	10,	3,	63,	600},
		{4,	6,	3,	63,	600},
		{4,	6,	3,	63,	600},
		{4,	6,	3,	63,	600},
		{4,	6,	3,	63,	600},
		{4,	6,	3,	63,	600},
		{4,	6,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600},
		{3,	12,	3,	63,	600}
};

/******************************************************************************/
/**
 * This function initializes the parameters required to configure PLL.
 *
 * @param	PllInstancePtr is pointer to the XAVBuf_Pll instance.
 * @param	Pll is the PLL chosen to be configured.
 * @param	Pll is the PLL chosen to be configured.
 * @param	CrossDomain is the bool which is used to mention if the PLL
 *		outputs in other domain.
 * @param	ExtDividerCnt is number of external divider out of VCO.
 *
 * @return	XST_SUCCESS if PLL is configured without an error.
 *		XST_FAILURE otherwise.
 *
 * @note	In order to avoid floating point usage we have a 16bit
 *		fractional fixed point arithmetic implementation
 *
*******************************************************************************/
static void XAVBuf_PllInitialize(XAVBuf_Pll *PllInstancePtr,
				     u8 Pll, u8 CrossDomain , u8 ExtDividerCnt)
{
	/* Instantiate input frequency. */
	PllInstancePtr->InputRefClk = XAVBUF_Pss_Ref_Clk;
	PllInstancePtr->RefClkFreqhz = XAVBUF_INPUT_REF_CLK;
	/* Turn on internal Divider*/
	PllInstancePtr->Divider = 1;
	PllInstancePtr->Pll = Pll;
	PllInstancePtr->ExtDividerCnt = ExtDividerCnt;

	//Check if CrossDomain is requested
	if(CrossDomain)
		PllInstancePtr->DomainSwitchDiv = 6;
	else
		PllInstancePtr->DomainSwitchDiv = 1;
	//Check where PLL falls
	if (Pll>2){
		PllInstancePtr->Fpd = 0;
		PllInstancePtr->BaseAddress = XAVBUF_CLK_LPD_BASEADDR;
		PllInstancePtr->Offset = XAVBUF_LPD_CTRL_OFFSET;
	}
	else{
		PllInstancePtr->Fpd = 1;
		PllInstancePtr->BaseAddress = XAVBUF_CLK_FPD_BASEADDR;
		PllInstancePtr->Offset = XAVBUF_FPD_CTRL_OFFSET;
	}

}

/******************************************************************************/
/**
 * This function calculates the parameters which are required to configure PLL
 * depending upon the requested frequency.
 *
 * @param	PllInstancePtr is pointer to the XAVBuf_Pll instance
 * @param	FreqHz is the requested frequency to  DP in Hz
 *
 * @return	XST_SUCCESS if parameters are calculated
 *		XST_FAILURE otherwise.
 *
 * @note	In order to avoid floating point usage we have a 16bit
 *		fractional fixed point arithmetic implementation
 *
*******************************************************************************/
static int XAVBuf_PllCalcParameterValues(XAVBuf_Pll *PllInstancePtr,
				     u64 FreqHz)
{
	u64 ExtDivider, Vco, VcoIntFrac;

	/* Instantiate input frequency. */
	PllInstancePtr->InputRefClk =  XAVBUF_Pss_Ref_Clk;
	PllInstancePtr->RefClkFreqhz =  XAVBUF_INPUT_REF_CLK ;
	/* Turn on internal Divider*/
	PllInstancePtr->Divider = 1;
	PllInstancePtr->DomainSwitchDiv = 1;

	/* Estimate the total divider. */
	ExtDivider =  (XAVBUF_PLL_OUT_FREQ / FreqHz) /
			      PllInstancePtr->DomainSwitchDiv;
	if(ExtDivider > 63 && PllInstancePtr->ExtDividerCnt == 2){
		PllInstancePtr->ExtDivider0 = 63;
		PllInstancePtr->ExtDivider1 = ExtDivider / 63;
	}
	else if(ExtDivider < 63){
		PllInstancePtr->ExtDivider0 = ExtDivider;
		PllInstancePtr->ExtDivider1 = 1;
	}
	else
		return XST_FAILURE;

	Vco = FreqHz *(PllInstancePtr->ExtDivider1 *
		PllInstancePtr->ExtDivider0 * 2) *
		PllInstancePtr->DomainSwitchDiv;
	/* Calculate integer and fractional part. */
	VcoIntFrac = (Vco * XAVBUF_INPUT_FREQ_PRECISION *
		XAVBUF_SHIFT_DECIMAL) /
		PllInstancePtr->RefClkFreqhz  ;
	PllInstancePtr->Fractional = VcoIntFrac &  XAVBUF_DECIMAL;
	PllInstancePtr->FracIntegerFBDIV = VcoIntFrac >> XAVBUF_PRECISION;

	return XST_SUCCESS;
}

/******************************************************************************/
/**
 * This function will Read modify and write into corresponding registers.
 *
 * @param	BaseAddress is the base address to which the value has to be
 *		written.
 * @param	RegOffset is the relative offset from Base address.
 * @param	Mask is used to select the number of bits to be modified.
 * @param	Shift is the number bits to be shifted from LSB.
 * @param	Data is the Data to be written.
 *
 * @return	None.
 *
 * @note	None.
 *
*******************************************************************************/
static void XAVBuf_ReadModifyWriteReg(u32 BaseAddress, u32 RegOffset, u32 Mask,
				      u32 Shift, u32 Data)
{
	u32 RegValue;

	RegValue = XAVBuf_ReadReg(BaseAddress, RegOffset);
	RegValue = (RegValue & ~Mask) | (Data << Shift);
	XAVBuf_WriteReg(BaseAddress, RegOffset, RegValue);
}

/******************************************************************************/
/**
 * This function configures PLL.
 *
 * @param	PllInstancePtr is pointer to the XAVBuf_Pll instance.
 *
 * @return	XST_SUCCESS if PLL is configured without an error.
 *		XST_FAILURE otherwise.
 *
 * @note	None.
 *
*******************************************************************************/
static int  XAVBuf_ConfigurePll(XAVBuf_Pll *PllInstancePtr)
{
	u64 BaseAddress = PllInstancePtr->BaseAddress;
	u64 timer = 0;
	u32 RegPll = 0;
	u8 Pll = PllInstancePtr->Pll;

	RegPll |= XAVBUF_ENABLE_BIT << XAVBUF_PLL_CTRL_BYPASS_SHIFT;
	RegPll |= PllInstancePtr->FracIntegerFBDIV <<
		XAVBUF_PLL_CTRL_FBDIV_SHIFT;
	RegPll |= PllInstancePtr->Divider << XAVBUF_PLL_CTRL_DIV2_SHIFT;
	RegPll |= PllInstancePtr->InputRefClk << XAVBUF_PLL_CTRL_PRE_SRC_SHIFT;
	XAVBuf_WriteReg(BaseAddress, XAVBUF_PLL_CTRL + (MOD_3(Pll) *
		PllInstancePtr->Offset), RegPll);
	RegPll = 0;
	/* Set the values for lock dly, lock counter, capacitor and resistor. */
	RegPll |=
		PllFracDivideTable[PllInstancePtr->FracIntegerFBDIV -25].cp
		<< XAVBUF_PLL_CFG_CP_SHIFT;
	RegPll |=
		PllFracDivideTable[PllInstancePtr->FracIntegerFBDIV -25].res
		<< XAVBUF_PLL_CFG_RES_SHIFT;
	RegPll |=
		PllFracDivideTable[PllInstancePtr->FracIntegerFBDIV -25].lfhf
		<< XAVBUF_PLL_CFG_LFHF_SHIFT;
	RegPll |=
		PllFracDivideTable[PllInstancePtr->FracIntegerFBDIV -25].lock_dly
		<< XAVBUF_PLL_CFG_LOCK_DLY_SHIFT;
	RegPll |=
		PllFracDivideTable[PllInstancePtr->FracIntegerFBDIV -25].lock_cnt
		<< XAVBUF_PLL_CFG_LOCK_CNT_SHIFT;
	XAVBuf_WriteReg(BaseAddress, XAVBUF_PLL_CFG + (MOD_3(Pll) *
		PllInstancePtr->Offset), RegPll);
	/* Enable and set Fractional Data. */
	XAVBuf_WriteReg(BaseAddress, XAVBUF_PLL_FRAC_CFG + (MOD_3(Pll) *
		PllInstancePtr->Offset), (1 << XAVBUF_PLL_FRAC_CFG_ENABLED_SHIFT) |
		(PllInstancePtr->Fractional <<
		XAVBUF_PLL_FRAC_CFG_DATA_SHIFT));
	/* Assert reset to the PLL. */
	XAVBuf_ReadModifyWriteReg(BaseAddress, XAVBUF_PLL_CTRL + (MOD_3(Pll) *
		PllInstancePtr->Offset),
		XAVBUF_PLL_CTRL_RESET_MASK, XAVBUF_PLL_CTRL_RESET_SHIFT,
		XAVBUF_ENABLE_BIT);

	/* Deassert reset to the PLL. */
	XAVBuf_ReadModifyWriteReg(BaseAddress, XAVBUF_PLL_CTRL + (MOD_3(Pll) *
		PllInstancePtr->Offset),
		XAVBUF_PLL_CTRL_RESET_MASK, XAVBUF_PLL_CTRL_RESET_SHIFT,
		XAVBUF_DISABLE_BIT);

	while(!(XAVBuf_ReadReg(BaseAddress, XAVBUF_PLL_STATUS -
		((1 - PllInstancePtr->Fpd) * XAVBUF_REG_OFFSET)) &
		(1 << MOD_3(Pll))))
		if(++timer > 1000)
			return XST_FAILURE;

	/* Deassert Bypass. */
	XAVBuf_ReadModifyWriteReg(BaseAddress, XAVBUF_PLL_CTRL + (MOD_3(Pll) *
		PllInstancePtr->Offset),
		XAVBUF_PLL_CTRL_BYPASS_MASK, XAVBUF_PLL_CTRL_BYPASS_SHIFT,
		XAVBUF_DISABLE_BIT);

	if(PllInstancePtr->DomainSwitchDiv != 1)
		XAVBuf_ReadModifyWriteReg(BaseAddress, (XAVBUF_DOMAIN_SWITCH_CTRL
		+ (MOD_3(Pll) * XAVBUF_REG_OFFSET) - ((1 - PllInstancePtr->Fpd)
		* XAVBUF_REG_OFFSET)),
		XAVBUF_DOMAIN_SWITCH_DIVISOR0_MASK,
		XAVBUF_DOMAIN_SWITCH_DIVISOR0_SHIFT,
		PllInstancePtr->DomainSwitchDiv);
	usleep(1);

	return XST_SUCCESS;

}

/******************************************************************************/
/**
 * This function configures Configures external divider.
 *
 * @param	PllInstancePtr is pointer to the XAVBuf_Pll instance.
 *
 * @return	None.
 *
 * @note	None.
 *
*******************************************************************************/
static void  XAVBuf_ConfigureExtDivider(XAVBuf_Pll *PllInstancePtr,
					u64 BaseAddress, u32 Offset)
{
	XAVBuf_ReadModifyWriteReg(BaseAddress, Offset,
		XAVBUF_VIDEO_REF_CTRL_CLKACT_MASK,
		XAVBUF_VIDEO_REF_CTRL_CLKACT_SHIFT, XAVBUF_DISABLE_BIT);
	XAVBuf_ReadModifyWriteReg(BaseAddress, Offset,
		XAVBUF_VIDEO_REF_CTRL_DIVISOR1_MASK,
		XAVBUF_VIDEO_REF_CTRL_DIVISOR1_SHIFT,
		PllInstancePtr->ExtDivider1);
	XAVBuf_ReadModifyWriteReg(BaseAddress, Offset,
		XAVBUF_VIDEO_REF_CTRL_DIVISOR0_MASK,
		XAVBUF_VIDEO_REF_CTRL_DIVISOR0_SHIFT,
		PllInstancePtr->ExtDivider0);
	XAVBuf_ReadModifyWriteReg(BaseAddress, Offset,
		XAVBUF_VIDEO_REF_CTRL_CLKACT_MASK,
		XAVBUF_VIDEO_REF_CTRL_CLKACT_SHIFT, XAVBUF_ENABLE_BIT);
	XAVBuf_WriteReg(BaseAddress, Offset, 0x1011003);
}

/******************************************************************************/
/**
 * This function calls API to calculate and configure PLL with desired frequency
 * for Video.
 *
 * @param	FreqHz is the desired frequency in Hz.
 *
 * @return	XST_SUCCESS if PLL is configured without an error.
 *		    XST_FAILURE otherwise.
 *
 * @note	The Pll used is design specific.
 *
*******************************************************************************/
int XAVBuf_SetPixelClock(u64 FreqHz)
{
	u32 PllAssigned;
	XAVBuf_Pll PllInstancePtr;
	u8 Pll, CrossDomain, Flag;

	/*Verify Input Arguments*/
	Xil_AssertNonvoid(FreqHz < XDPSSU_MAX_VIDEO_FREQ);

	PllAssigned = XAVBuf_ReadReg(XAVBUF_CLK_FPD_BASEADDR,
		XAVBUF_VIDEO_REF_CTRL) & XAVBUF_VIDEO_REF_CTRL_SRCSEL_MASK;

	switch (PllAssigned) {
		case XAVBUF_VPLL_SRC_SEL:
				Pll = VPLL;
				CrossDomain = 0;
				break;
		case XAVBUF_DPLL_SRC_SEL:
				Pll = DPLL;
				CrossDomain = 0;
				break;
		case XAVBUF_RPLL_TO_FPD_SRC_SEL:
				Pll = RPLL;
				CrossDomain = 1;
				break;
		default:
				return XST_FAILURE;
	}

	/*Calculate configure PLL and External Divider*/
	XAVBuf_PllInitialize(&PllInstancePtr, Pll, CrossDomain,
		XAVBUF_EXTERNAL_DIVIDER);
	Flag = XAVBuf_PllCalcParameterValues(&PllInstancePtr, FreqHz);
	if(Flag != 0)
		return XST_FAILURE;
	Flag = XAVBuf_ConfigurePll(&PllInstancePtr);
	if(Flag != 0)
		return XST_FAILURE;
	XAVBuf_ConfigureExtDivider(&PllInstancePtr, XAVBUF_CLK_FPD_BASEADDR,
		XAVBUF_VIDEO_REF_CTRL);

	return XST_SUCCESS;
}

/******************************************************************************/
/**
 * This function calls API to calculate and configure PLL with desired
 * frequency for Audio.
 *
 * @param	FreqHz is the desired frequency in Hz.
 *
 * @return	XST_SUCCESS if PLL is configured without an error.
 *		    XST_FAILURE otherwise.
 *
 * @note	The Pll used is design specific.
 *
*******************************************************************************/
int XAVBuf_SetAudioClock(u64 FreqHz)
{
	u32 Flag, PllAssigned;
	u8 Pll, CrossDomain;
	XAVBuf_Pll XAVBuf_RPllInstancePtr;

	/*Verify Input Arguments*/
	Flag = (FreqHz == (XAVBUF_AUDIO_SAMPLE_RATE_44_1 *
		XAVBUF_AUDIO_SAMPLES)) ||
		(FreqHz == (XAVBUF_AUDIO_SAMPLE_RATE_48_0 *
		XAVBUF_AUDIO_SAMPLES));
	Xil_AssertNonvoid(Flag);

	PllAssigned = XAVBuf_ReadReg(XAVBUF_CLK_FPD_BASEADDR,
		XAVBUF_AUDIO_REF_CTRL) &
		XAVBUF_AUDIO_REF_CTRL_SRCSEL_MASK;

	switch (PllAssigned) {
		case XAVBUF_VPLL_SRC_SEL:
				Pll = VPLL;
				CrossDomain = 0;
				break;
		case XAVBUF_DPLL_SRC_SEL:
				Pll = DPLL;
				CrossDomain = 0;
				break;
		case XAVBUF_RPLL_TO_FPD_SRC_SEL:
				Pll = RPLL;
				CrossDomain = 1;
				break;
		default:
				return XST_FAILURE;
	}

	/*Calculate configure PLL and External Divider*/
	XAVBuf_PllInitialize(&XAVBuf_RPllInstancePtr, Pll, CrossDomain,
		XAVBUF_EXTERNAL_DIVIDER);
	Flag = XAVBuf_PllCalcParameterValues(&XAVBuf_RPllInstancePtr, FreqHz);
	if(Flag != 0)
		return XST_FAILURE;
	Flag = XAVBuf_ConfigurePll(&XAVBuf_RPllInstancePtr);
	if(Flag != 0)
		return XST_FAILURE;
	XAVBuf_ConfigureExtDivider(&XAVBuf_RPllInstancePtr,
		XAVBUF_CLK_FPD_BASEADDR, XAVBUF_AUDIO_REF_CTRL);

	return XST_SUCCESS;
}
