/******************************************************************************
*
* Copyright (C) 2014 - 2015 Xilinx, Inc. All rights reserved.
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
* Contains required functions for the ARM cache functionality.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver    Who Date     Changes
* ----- ---- -------- -----------------------------------------------
* 5.00 	pkp  02/20/14 First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_cache.h"
#include "xil_io.h"
#include "xpseudo_asm.h"
#include "xparameters.h"
#include "xreg_cortexr5.h"
#include "xil_exception.h"


/************************** Variable Definitions *****************************/

#define IRQ_FIQ_MASK 0xC0	/* Mask IRQ and FIQ interrupts in cpsr */


extern s32  _stack_end;
extern s32  __undef_stack;

/****************************************************************************/
/************************** Function Prototypes ******************************/

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
	register u32 CtrlReg;

	/* enable caches only if they are disabled */
	CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);

	if ((CtrlReg & XREG_CP15_CONTROL_C_BIT)==0x00000000U) {
		/* invalidate the Data cache */
		Xil_DCacheInvalidate();

		/* enable the Data cache */
		CtrlReg |= (XREG_CP15_CONTROL_C_BIT);

		mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
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
	register u32 CtrlReg;

	/* clean and invalidate the Data cache */
	Xil_DCacheFlush();

	/* disable the Data cache */
	CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);

	CtrlReg &= ~(XREG_CP15_CONTROL_C_BIT);

	mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
}

/****************************************************************************
*
* Invalidate the entire Data cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_DCacheInvalidate(void)
{
	u32 currmask;
	u32 stack_start,stack_end,stack_size;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);


	stack_end = (u32 )&_stack_end;
	stack_start = (u32 )&__undef_stack;
	stack_size = stack_start-stack_end;

	/* Flush stack memory to save return address */
	Xil_DCacheFlushRange(stack_end, stack_size);

	mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);

	/*invalidate all D cache*/
	mtcp(XREG_CP15_INVAL_DC_ALL, 0);

	mtcpsr(currmask);
}

/****************************************************************************
*
* Invalidate a Data cache line. If the byte specified by the address (adr)
* is cached by the Data cache, the cacheline containing that byte is
* invalidated.	If the cacheline is modified (dirty), the modified contents
* are lost and are NOT written to system memory before the line is
* invalidated.
*
* @param	Address to be flushed.
*
* @return	None.
*
* @note		The bottom 4 bits are set to 0, forced by architecture.
*
****************************************************************************/
void Xil_DCacheInvalidateLine(INTPTR adr)
{
	u32 currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);
	mtcp(XREG_CP15_INVAL_DC_LINE_MVA_POC, (adr & (~0x1F)));

		/* Wait for invalidate to complete */
	dsb();

	mtcpsr(currmask);
}

/****************************************************************************
*
* Invalidate the Data cache for the given address range.
* If the bytes specified by the address (adr) are cached by the Data cache,
* the cacheline containing that byte is invalidated.	If the cacheline
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
void Xil_DCacheInvalidateRange(INTPTR adr, u32 len)
{
	const u32 cacheline = 32U;
	u32 end;
	u32 tempadr = adr;
	u32 tempend;
	u32 currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	if (len != 0U) {
		end = tempadr + len;
		tempend = end;
		/* Select L1 Data cache in CSSR */
		mtcp(XREG_CP15_CACHE_SIZE_SEL, 0U);

		if ((tempadr & (cacheline-1U)) != 0U) {
			tempadr &= (~(cacheline - 1U));

			Xil_DCacheFlushLine(tempadr);
		}
		if ((tempend & (cacheline-1U)) != 0U) {
			tempend &= (~(cacheline - 1U));

			Xil_DCacheFlushLine(tempend);
		}

		while (tempadr < tempend) {

		/* Invalidate Data cache line */
		asm_inval_dc_line_mva_poc(tempadr);

		tempadr += cacheline;
		}
	}

	dsb();
	mtcpsr(currmask);
}

/****************************************************************************
*
* Flush the entire Data cache.
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
	u32 CacheSize, LineSize, NumWays;
	u32 Way, WayIndex, Set, SetIndex, NumSet;
	u32 currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	/* Select cache level 0 and D cache in CSSR */
	mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);

	CsidReg = mfcp(XREG_CP15_CACHE_SIZE_ID);

	/* Determine Cache Size */

	CacheSize = (CsidReg >> 13U) & 0x000001FFU;
	CacheSize += 0x00000001U;
	CacheSize *= (u32)128;    /* to get number of bytes */

	/* Number of Ways */
	NumWays = (CsidReg & 0x000003ffU) >> 3U;
	NumWays += 0x00000001U;

	/* Get the cacheline size, way size, index size from csidr */
	LineSize = (CsidReg & 0x00000007U) + 0x00000004U;

	NumSet = CacheSize/NumWays;
	NumSet /= (0x00000001U << LineSize);

	Way = 0U;
	Set = 0U;

	/* Invalidate all the cachelines */
	for (WayIndex = 0U; WayIndex < NumWays; WayIndex++) {
		for (SetIndex = 0U; SetIndex < NumSet; SetIndex++) {
			C7Reg = Way | Set;
			/* Flush by Set/Way */
			asm_clean_inval_dc_line_sw(C7Reg);

			Set += (0x00000001U << LineSize);
		}
		Set = 0U;
		Way += 0x40000000U;
	}

	/* Wait for flush to complete */
	dsb();
	mtcpsr(currmask);

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
* @note		The bottom 4 bits are set to 0, forced by architecture.
*
****************************************************************************/
void Xil_DCacheFlushLine(INTPTR adr)
{
	u32 currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);

	mtcp(XREG_CP15_CLEAN_INVAL_DC_LINE_MVA_POC, (adr & (~0x1F)));

		/* Wait for flush to complete */
	dsb();
	mtcpsr(currmask);
}

/****************************************************************************
* Flush the Data cache for the given address range.
* If the bytes specified by the address (adr) are cached by the Data cache,
* the cacheline containing that byte is invalidated.	If the cacheline
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
void Xil_DCacheFlushRange(INTPTR adr, u32 len)
{
	u32 LocalAddr = adr;
	const u32 cacheline = 32U;
	u32 end;
	u32 currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	if (len != 0x00000000U) {
		/* Back the starting address up to the start of a cache line
		 * perform cache operations until adr+len
		 */
		end = LocalAddr + len;
		LocalAddr &= ~(cacheline - 1U);

		while (LocalAddr < end) {
			/* Flush Data cache line */
			asm_clean_inval_dc_line_mva_poc(LocalAddr);

			LocalAddr += cacheline;
		}
	}
	dsb();
	mtcpsr(currmask);
}
/****************************************************************************
*
* Store a Data cache line. If the byte specified by the address (adr)
* is cached by the Data cache and the cacheline is modified (dirty),
* the entire contents of the cacheline are written to system memory.
* After the store completes, the cacheline is marked as unmodified
* (not dirty).
*
* @param	Address to be stored.
*
* @return	None.
*
* @note		The bottom 4 bits are set to 0, forced by architecture.
*
****************************************************************************/
void Xil_DCacheStoreLine(INTPTR adr)
{
	u32 currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);
	mtcp(XREG_CP15_CLEAN_DC_LINE_MVA_POC, (adr & (~0x1F)));

	/* Wait for store to complete */
	dsb();
	isb();

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
	register u32 CtrlReg;

	/* enable caches only if they are disabled */

	CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);

	if ((CtrlReg & XREG_CP15_CONTROL_I_BIT)==0x00000000U) {
		/* invalidate the instruction cache */
		mtcp(XREG_CP15_INVAL_IC_POU, 0);

		/* enable the instruction cache */
		CtrlReg |= (XREG_CP15_CONTROL_I_BIT);

		mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
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
	register u32 CtrlReg;

	dsb();

	/* invalidate the instruction cache */
	mtcp(XREG_CP15_INVAL_IC_POU, 0);

		/* disable the instruction cache */

	CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);

	CtrlReg &= ~(XREG_CP15_CONTROL_I_BIT);

	mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
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
	u32 currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	mtcp(XREG_CP15_CACHE_SIZE_SEL, 1);

	/* invalidate the instruction cache */
	mtcp(XREG_CP15_INVAL_IC_POU, 0);

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
* @note		The bottom 4 bits are set to 0, forced by architecture.
*
****************************************************************************/
void Xil_ICacheInvalidateLine(INTPTR adr)
{
	u32 currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	mtcp(XREG_CP15_CACHE_SIZE_SEL, 1);
	mtcp(XREG_CP15_INVAL_IC_LINE_MVA_POU, (adr & (~0x1F)));

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
void Xil_ICacheInvalidateRange(INTPTR adr, u32 len)
{
	u32 LocalAddr = adr;
	const u32 cacheline = 32U;
	u32 end;
	u32 currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);
	if (len != 0x00000000U) {
		/* Back the starting address up to the start of a cache line
		 * perform cache operations until adr+len
		 */
		end = LocalAddr + len;
		LocalAddr = LocalAddr & ~(cacheline - 1U);

		/* Select cache L0 I-cache in CSSR */
		mtcp(XREG_CP15_CACHE_SIZE_SEL, 1U);

		while (LocalAddr < end) {

			/* Invalidate L1 I-cache line */
			asm_inval_ic_line_mva_pou(LocalAddr);

			LocalAddr += cacheline;
		}
	}

	/* Wait for invalidate to complete */
	dsb();
	mtcpsr(currmask);
}
