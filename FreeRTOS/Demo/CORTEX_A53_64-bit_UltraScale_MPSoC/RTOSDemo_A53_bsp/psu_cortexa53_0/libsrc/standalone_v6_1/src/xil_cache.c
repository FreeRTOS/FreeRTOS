/******************************************************************************
*
* Copyright (C) 2014 - 2016 Xilinx, Inc. All rights reserved.
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
/*****************************************************************************/
/**
*
* @file xil_cache.c
*
* Contains required functions for the ARM cache functionality. Cache APIs are
* yet to be implemented. They are left blank to avoid any compilation error
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver    Who Date     Changes
* ----- ---- -------- -----------------------------------------------
* 5.00 	pkp  05/29/14 First release
* 5.05	pkp	 04/15/16 Updated the Xil_DCacheInvalidate,
*					  Xil_DCacheInvalidateLine and Xil_DCacheInvalidateRange
*					  functions description for proper explaination
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_cache.h"
#include "xil_io.h"
#include "xpseudo_asm.h"
#include "xparameters.h"
#include "xreg_cortexa53.h"
#include "xil_exception.h"
#include "bspconfig.h"

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/
#define IRQ_FIQ_MASK 0xC0U	/* Mask IRQ and FIQ interrupts in cpsr */

/****************************************************************************
*
* Enable the Data cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/

void Xil_DCacheEnable(void)
{
	u32 CtrlReg;

	CtrlReg = mfcp(SCTLR_EL3);

	/* enable caches only if they are disabled */
	if((CtrlReg & XREG_CONTROL_DCACHE_BIT) == 0X00000000U){

		/* invalidate the Data cache */
		Xil_DCacheInvalidate();

		CtrlReg |= XREG_CONTROL_DCACHE_BIT;

		/* enable the Data cache for el3*/
		mtcp(SCTLR_EL3,CtrlReg);
	}
}

/****************************************************************************
*
* Disable the Data cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_DCacheDisable(void)
{
	u32 CtrlReg;
	/* clean and invalidate the Data cache */
	Xil_DCacheFlush();

	CtrlReg = mfcp(SCTLR_EL3);

	CtrlReg &= ~(XREG_CONTROL_DCACHE_BIT);

	/* disable the Data cache for el3*/
	mtcp(SCTLR_EL3,CtrlReg);
}

/****************************************************************************
*
* Invalidate the Data cache. The contents present in the cache are cleaned and
* invalidated.
*
* @param	None.
*
* @return	None.
*
* @note		In Cortex-A53, functionality to simply invalide the cachelines
*  			is not present. Such operations are a problem for an environment
* 			that supports virtualisation. It would allow one OS to invalidate
* 			a line belonging to another OS which could lead to that OS crashing
* 			because of the loss of essential data. Hence, such operations are
* 			promoted to clean and invalidate which avoids such corruption.
*
****************************************************************************/
void Xil_DCacheInvalidate(void)
{
	register u32 CsidReg, C7Reg;
	u32 LineSize, NumWays;
	u32 Way, WayIndex,WayAdjust, Set, SetIndex, NumSet, CacheLevel;
	u32 currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);


	/* Number of level of cache*/

	CacheLevel=0U;
	/* Select cache level 0 and D cache in CSSR */
	mtcp(CSSELR_EL1,CacheLevel);
	isb();

	CsidReg = mfcp(CCSIDR_EL1);

	/* Get the cacheline size, way size, index size from csidr */
	LineSize = (CsidReg & 0x00000007U) + 0x00000004U;

	/* Number of Ways */
	NumWays = (CsidReg & 0x00001FFFU) >> 3U;
	NumWays += 0X00000001U;

	/*Number of Set*/
	NumSet = (CsidReg >> 13U) & 0x00007FFFU;
	NumSet += 0X00000001U;

	WayAdjust = clz(NumWays) - (u32)0x0000001FU;

	Way = 0U;
	Set = 0U;

	/* Invalidate all the cachelines */
	for (WayIndex =0U; WayIndex < NumWays; WayIndex++) {
		for (SetIndex =0U; SetIndex < NumSet; SetIndex++) {
			C7Reg = Way | Set | CacheLevel;
			mtcpdc(ISW,C7Reg);
			Set += (0x00000001U << LineSize);
		}
		Set = 0U;
		Way += (0x00000001U << WayAdjust);
	}

	/* Wait for invalidate to complete */
	dsb();

	/* Select cache level 1 and D cache in CSSR */
	CacheLevel += (0x00000001U<<1U) ;
	mtcp(CSSELR_EL1,CacheLevel);
	isb();

	CsidReg = mfcp(CCSIDR_EL1);

	/* Get the cacheline size, way size, index size from csidr */
		LineSize = (CsidReg & 0x00000007U) + 0x00000004U;

	/* Number of Ways */
	NumWays = (CsidReg & 0x00001FFFU) >> 3U;
	NumWays += 0x00000001U;

	/* Number of Sets */
	NumSet = (CsidReg >> 13U) & 0x00007FFFU;
	NumSet += 0x00000001U;

	WayAdjust = clz(NumWays) - (u32)0x0000001FU;

	Way = 0U;
	Set = 0U;

	/* Invalidate all the cachelines */
	for (WayIndex = 0U; WayIndex < NumWays; WayIndex++) {
		for (SetIndex = 0U; SetIndex < NumSet; SetIndex++) {
			C7Reg = Way | Set | CacheLevel;
			mtcpdc(ISW,C7Reg);
			Set += (0x00000001U << LineSize);
		}
		Set = 0U;
		Way += (0x00000001U << WayAdjust);
	}
	/* Wait for invalidate to complete */
	dsb();

	mtcpsr(currmask);
}

/****************************************************************************
*
* Invalidate a Data cache line. The cacheline is cleaned and invalidated
*
* @param	Address to be flushed.
*
* @return	None.
*
* @note		In Cortex-A53, functionality to simply invalide the cachelines
*  			is not present. Such operations are a problem for an environment
* 			that supports virtualisation. It would allow one OS to invalidate
* 			a line belonging to another OS which could lead to that OS crashing
* 			because of the loss of essential data. Hence, such operations are
* 			promoted to clean and invalidate which avoids such corruption.
*
****************************************************************************/
void Xil_DCacheInvalidateLine(INTPTR adr)
{

	u32 currmask;
	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	/* Select cache level 0 and D cache in CSSR */
	mtcp(CSSELR_EL1,0x0);
	mtcpdc(IVAC,(adr & (~0x3F)));
	/* Wait for invalidate to complete */
	dsb();
	/* Select cache level 1 and D cache in CSSR */
	mtcp(CSSELR_EL1,0x2);
	mtcpdc(IVAC,(adr & (~0x3F)));
	/* Wait for invalidate to complete */
	dsb();
	mtcpsr(currmask);
}

/****************************************************************************
*
* Invalidate the Data cache for the given address range.
* The cachelines present in the adderss range are cleaned and invalidated
*
* @param	Start address of range to be invalidated.
* @param	Length of range to be invalidated in bytes.
*
* @return	None.
*
* @note		In Cortex-A53, functionality to simply invalide the cachelines
*  			is not present. Such operations are a problem for an environment
* 			that supports virtualisation. It would allow one OS to invalidate
* 			a line belonging to another OS which could lead to that OS crashing
* 			because of the loss of essential data. Hence, such operations are
* 			promoted to clean and invalidate which avoids such corruption.
*
****************************************************************************/
void Xil_DCacheInvalidateRange(INTPTR  adr, INTPTR len)
{
	const u32 cacheline = 64U;
	INTPTR end;
	INTPTR tempadr = adr;
	INTPTR tempend;
	u32 currmask;
	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);
	if (len != 0U) {
		end = tempadr + len;
		tempend = end;

		if ((tempadr & (cacheline-1U)) != 0U) {
			tempadr &= (~(cacheline - 1U));
			Xil_DCacheFlushLine(tempadr);
			tempadr += cacheline;
		}
		if ((tempend & (cacheline-1U)) != 0U) {
			tempend &= (~(cacheline - 1U));
			Xil_DCacheFlushLine(tempend);
		}

		while (tempadr < tempend) {
			/* Select cache level 0 and D cache in CSSR */
			mtcp(CSSELR_EL1,0x0);
			/* Invalidate Data cache line */
			mtcpdc(IVAC,(tempadr & (~0x3F)));
			/* Wait for invalidate to complete */
			dsb();
			/* Select cache level 0 and D cache in CSSR */
			mtcp(CSSELR_EL1,0x2);
			/* Invalidate Data cache line */
			mtcpdc(IVAC,(tempadr & (~0x3F)));
			/* Wait for invalidate to complete */
			dsb();
			tempadr += cacheline;
		}
	}
	mtcpsr(currmask);
}

/****************************************************************************
*
* Flush the Data cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_DCacheFlush(void)
{
	register u32 CsidReg, C7Reg;
	u32 LineSize, NumWays;
	u32 Way, WayIndex,WayAdjust, Set, SetIndex, NumSet, CacheLevel;
	u32 currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);


	/* Number of level of cache*/

	CacheLevel = 0U;
	/* Select cache level 0 and D cache in CSSR */
	mtcp(CSSELR_EL1,CacheLevel);
	isb();

	CsidReg = mfcp(CCSIDR_EL1);

	/* Get the cacheline size, way size, index size from csidr */
	LineSize = (CsidReg & 0x00000007U) + 0x00000004U;

	/* Number of Ways */
	NumWays = (CsidReg & 0x00001FFFU) >> 3U;
	NumWays += 0x00000001U;

	/*Number of Set*/
	NumSet = (CsidReg >> 13U) & 0x00007FFFU;
	NumSet += 0x00000001U;

	WayAdjust = clz(NumWays) - (u32)0x0000001FU;

	Way = 0U;
	Set = 0U;

	/* Flush all the cachelines */
	for (WayIndex = 0U; WayIndex < NumWays; WayIndex++) {
		for (SetIndex = 0U; SetIndex < NumSet; SetIndex++) {
			C7Reg = Way | Set | CacheLevel;
			mtcpdc(CISW,C7Reg);
			Set += (0x00000001U << LineSize);
		}
		Set = 0U;
		Way += (0x00000001U << WayAdjust);
	}

	/* Wait for Flush to complete */
	dsb();

	/* Select cache level 1 and D cache in CSSR */
	CacheLevel += (0x00000001U << 1U);
	mtcp(CSSELR_EL1,CacheLevel);
	isb();

	CsidReg = mfcp(CCSIDR_EL1);

	/* Get the cacheline size, way size, index size from csidr */
		LineSize = (CsidReg & 0x00000007U) + 0x00000004U;

	/* Number of Ways */
	NumWays = (CsidReg & 0x00001FFFU) >> 3U;
	NumWays += 0x00000001U;

	/* Number of Sets */
	NumSet = (CsidReg >> 13U) & 0x00007FFFU;
	NumSet += 0x00000001U;

	WayAdjust=clz(NumWays) - (u32)0x0000001FU;

	Way = 0U;
	Set = 0U;

	/* Flush all the cachelines */
	for (WayIndex =0U; WayIndex < NumWays; WayIndex++) {
		for (SetIndex =0U; SetIndex < NumSet; SetIndex++) {
			C7Reg = Way | Set | CacheLevel;
			mtcpdc(CISW,C7Reg);
			Set += (0x00000001U << LineSize);
		}
		Set=0U;
		Way += (0x00000001U<<WayAdjust);
	}
	/* Wait for Flush to complete */
	dsb();

	mtcpsr(currmask);
}

/****************************************************************************
*
* Flush a Data cache line. If the byte specified by the address (adr)
* is cached by the Data cache, the cacheline containing that byte is
* invalidated.	If the cacheline is modified (dirty), the entire
* contents of the cacheline are written to system memory before the
* line is invalidated.
*
* @param	Address to be flushed.
*
* @return	None.
*
* @note		The bottom 6 bits are set to 0, forced by architecture.
*
****************************************************************************/
void Xil_DCacheFlushLine(INTPTR  adr)
{
	u32 currmask;
	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);
	/* Select cache level 0 and D cache in CSSR */
	mtcp(CSSELR_EL1,0x0);
	mtcpdc(CIVAC,(adr & (~0x3F)));
	/* Wait for flush to complete */
	dsb();
	/* Select cache level 1 and D cache in CSSR */
	mtcp(CSSELR_EL1,0x2);
	mtcpdc(CIVAC,(adr & (~0x3F)));
	/* Wait for flush to complete */
	dsb();
	mtcpsr(currmask);
}
/****************************************************************************
* Flush the Data cache for the given address range.
* If the bytes specified by the address (adr) are cached by the Data cache,
* the cacheline containing that byte is invalidated. If the cacheline
* is modified (dirty), the written to system memory first before the
* before the line is invalidated.
*
* @param	Start address of range to be flushed.
* @param	Length of range to be flushed in bytes.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/

void Xil_DCacheFlushRange(INTPTR  adr, INTPTR len)
{
	const u32 cacheline = 64U;
	INTPTR end;
	INTPTR tempadr = adr;
	INTPTR tempend;
	u32 currmask;
	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);
	if (len != 0x00000000U) {
		end = tempadr + len;
		tempend = end;
		if ((tempadr & (0x3F)) != 0) {
			tempadr &= ~(0x3F);
			Xil_DCacheFlushLine(tempadr);
			tempadr += cacheline;
		}
		if ((tempend & (0x3F)) != 0) {
			tempend &= ~(0x3F);
			Xil_DCacheFlushLine(tempend);
		}

		while (tempadr < tempend) {
			/* Select cache level 0 and D cache in CSSR */
			mtcp(CSSELR_EL1,0x0);
			/* Flush Data cache line */
			mtcpdc(CIVAC,(tempadr & (~0x3F)));
			/* Wait for flush to complete */
			dsb();
			/* Select cache level 1 and D cache in CSSR */
			mtcp(CSSELR_EL1,0x2);
			/* Flush Data cache line */
			mtcpdc(CIVAC,(tempadr & (~0x3F)));
			/* Wait for flush to complete */
			dsb();
			tempadr += cacheline;
		}
	}

	mtcpsr(currmask);
}


/****************************************************************************
*
* Enable the instruction cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/


void Xil_ICacheEnable(void)
{
	u32 CtrlReg;

	CtrlReg = mfcp(SCTLR_EL3);

	/* enable caches only if they are disabled */
	if((CtrlReg & XREG_CONTROL_ICACHE_BIT)==0x00000000U){
		/* invalidate the instruction cache */
		Xil_ICacheInvalidate();

		CtrlReg |= XREG_CONTROL_ICACHE_BIT;

		/* enable the instruction cache for el3*/
		mtcp(SCTLR_EL3,CtrlReg);
	}
}

/****************************************************************************
*
* Disable the instruction cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_ICacheDisable(void)
{
	u32 CtrlReg;

	CtrlReg = mfcp(SCTLR_EL3);

	/* invalidate the instruction cache */
	Xil_ICacheInvalidate();
	CtrlReg &= ~(XREG_CONTROL_ICACHE_BIT);
	/* disable the instruction cache */
	mtcp(SCTLR_EL3,CtrlReg);

}

/****************************************************************************
*
* Invalidate the entire instruction cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_ICacheInvalidate(void)
{
	unsigned int currmask;
	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);
	mtcp(CSSELR_EL1,0x1);
	dsb();
	/* invalidate the instruction cache */
	mtcpicall(IALLU);
	/* Wait for invalidate to complete */
	dsb();
	mtcpsr(currmask);
}
/****************************************************************************
*
* Invalidate an instruction cache line.	If the instruction specified by the
* parameter adr is cached by the instruction cache, the cacheline containing
* that instruction is invalidated.
*
* @param	None.
*
* @return	None.
*
* @note		The bottom 6 bits are set to 0, forced by architecture.
*
****************************************************************************/

void Xil_ICacheInvalidateLine(INTPTR  adr)
{
	u32 currmask;
	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	mtcp(CSSELR_EL1,0x1);
	/*Invalidate I Cache line*/
	mtcpic(IVAU,adr & (~0x3F));
	/* Wait for invalidate to complete */
	dsb();
	mtcpsr(currmask);
}

/****************************************************************************
*
* Invalidate the instruction cache for the given address range.
* If the bytes specified by the address (adr) are cached by the Data cache,
* the cacheline containing that byte is invalidated. If the cacheline
* is modified (dirty), the modified contents are lost and are NOT
* written to system memory before the line is invalidated.
*
* @param	Start address of range to be invalidated.
* @param	Length of range to be invalidated in bytes.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_ICacheInvalidateRange(INTPTR  adr, INTPTR len)
{
	const u32 cacheline = 64U;
	INTPTR end;
	INTPTR tempadr = adr;
	INTPTR tempend;
	u32 currmask;
	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	if (len != 0x00000000U) {
		end = tempadr + len;
		tempend = end;
		tempadr &= ~(cacheline - 0x00000001U);

		/* Select cache Level 0 I-cache in CSSR */
		mtcp(CSSELR_EL1,0x1);
		while (tempadr < tempend) {
			/*Invalidate I Cache line*/
			mtcpic(IVAU,adr & (~0x3F));

			tempadr += cacheline;
		}
	}
/* Wait for invalidate to complete */
	dsb();
	mtcpsr(currmask);
}
