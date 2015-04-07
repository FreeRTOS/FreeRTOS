/******************************************************************************
*
* (c) Copyright 2010-14  Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
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
* 1.00a  ecm 01/29/10 First release
* 1.00a  ecm 06/24/10 Moved the L1 and L2 specific function prototypes
*		      to xil_cache_mach.h to give access to sophisticated users
* 3.02a  sdm 04/07/11 Updated Flush/InvalidateRange APIs to flush/invalidate
*		      L1 and L2 caches in a single loop and used dsb, L2 sync
*		      at the end of the loop.
* 3.04a  sdm 01/02/12 Remove redundant dsb/dmb instructions in cache maintenance
*		      APIs.
* 3.07a  asa 07/16/12 Corrected the L1 and L2 cache invalidation order.
* 3.07a  sgd 09/18/12 Corrected the L2 cache enable and disable sequence.
* 3.10a  srt 04/18/13 Implemented ARM Erratas. Please refer to file
*		      'xil_errata.h' for errata description
* 3.10a  asa 05/13/13 Modified cache disable APIs. The L2 cache disable
*			  operation was being done with L1 Data cache disabled. This is
*			  fixed so that L2 cache disable operation happens independent of
*			  L1 cache disable operation. This fixes CR #706464.
*			  Changes are done to do a L2 cache sync (poll reg7_?cache_?sync).
*			  This is done to fix the CR #700542.
* 3.11a  asa 09/23/13 Modified the Xil_DCacheFlushRange and
*			 Xil_DCacheInvalidateRange to fix potential issues. Fixed other
*			 relevant cache APIs to disable and enable back the interrupts.
*			 This fixes CR #663885.
* 3.11a  asa 09/28/13 Made changes for L2 cache sync operation. It is found
*			 out that for L2 cache flush/clean/invalidation by cache lines
*			 does not need a cache sync as these are atomic nature. Similarly
*			 figured out that for complete L2 cache flush/invalidation by way
*			 we need to wait for some more time in a loop till the status
*			 shows that the cache operation is completed.
* 4.00	 pkp 24/01/14 Modified Xil_DCacheInvalidateRange to fix the bug. Few
*			 cache lines were missed to invalidate when unaligned address
*			 invalidation was accommodated. That fixes CR #766768. 
*			 Also in Xil_L1DCacheInvalidate, while invalidating all L1D cache
*			 stack memory which contains return address was invalidated. So
*			 stack memory was flushed first and then L1D cache is invalidated.
*			 This is done to fix CR #763829
* 4.01   asa 05/09/14 Made changes in cortexa9/xil_cache.c to fix CR# 798230.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_cache.h"
#include "xil_cache_l.h"
#include "xil_io.h"
#include "xpseudo_asm.h"
#include "xparameters.h"
#include "xreg_cortexa9.h"
#include "xl2cc.h"
#include "xil_errata.h"
#include "xil_exception.h"

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

#define IRQ_FIQ_MASK 0xC0	/* Mask IRQ and FIQ interrupts in cpsr */

#ifdef __GNUC__
	extern int  _stack_end;
	extern int  _stack;
#endif

/****************************************************************************
*
* Access L2 Debug Control Register.
*
* @param	Value, value to be written to Debug Control Register.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
#ifdef __GNUC__
static inline void Xil_L2WriteDebugCtrl(u32 Value)
#else
static void Xil_L2WriteDebugCtrl(u32 Value)
#endif
{
#if defined(CONFIG_PL310_ERRATA_588369) || defined(CONFIG_PL310_ERRATA_727915)
	Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_DEBUG_CTRL_OFFSET, Value);
#else
	(void)(Value);
#endif
}

/****************************************************************************
*
* Perform L2 Cache Sync Operation.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
#ifdef __GNUC__
static inline void Xil_L2CacheSync(void)
#else
static void Xil_L2CacheSync(void)
#endif
{
#ifdef CONFIG_PL310_ERRATA_753970
	Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_DUMMY_CACHE_SYNC_OFFSET, 0x0);
#else
	Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_CACHE_SYNC_OFFSET, 0x0);
#endif
}

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
	Xil_L1DCacheEnable();
	Xil_L2CacheEnable();
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
	Xil_L2CacheDisable();
	Xil_L1DCacheDisable();
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
	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	Xil_L2CacheInvalidate();
	Xil_L1DCacheInvalidate();

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
void Xil_DCacheInvalidateLine(unsigned int adr)
{
	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	Xil_L2CacheInvalidateLine(adr);
	Xil_L1DCacheInvalidateLine(adr);

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
void Xil_DCacheInvalidateRange(unsigned int adr, unsigned len)
{
	const unsigned cacheline = 32;
	unsigned int end;
	unsigned int tempadr = adr;
	unsigned int tempend;
	unsigned int currmask;
	volatile u32 *L2CCOffset = (volatile u32 *) (XPS_L2CC_BASEADDR +
				    XPS_L2CC_CACHE_INVLD_PA_OFFSET);

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	if (len != 0) {
		end = tempadr + len;
		tempend = end;
		/* Select L1 Data cache in CSSR */
		mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);

		if (tempadr & (cacheline-1)) {
			tempadr &= ~(cacheline - 1);

			Xil_L1DCacheFlushLine(tempadr);
			/* Disable Write-back and line fills */
			Xil_L2WriteDebugCtrl(0x3);
			Xil_L2CacheFlushLine(tempadr);
			/* Enable Write-back and line fills */
			Xil_L2WriteDebugCtrl(0x0);
			Xil_L2CacheSync();
			tempadr += cacheline;
		}
		if (tempend & (cacheline-1)) {
			tempend &= ~(cacheline - 1);

			Xil_L1DCacheFlushLine(tempend);
			/* Disable Write-back and line fills */
			Xil_L2WriteDebugCtrl(0x3);
			Xil_L2CacheFlushLine(tempend);
			/* Enable Write-back and line fills */
			Xil_L2WriteDebugCtrl(0x0);
			Xil_L2CacheSync();
		}

		while (tempadr < tempend) {
			/* Invalidate L2 cache line */
			*L2CCOffset = tempadr;
			dsb();
#ifdef __GNUC__
			/* Invalidate L1 Data cache line */
			__asm__ __volatile__("mcr " \
			XREG_CP15_INVAL_DC_LINE_MVA_POC :: "r" (tempadr));
#else
			{ volatile register unsigned int Reg
				__asm(XREG_CP15_INVAL_DC_LINE_MVA_POC);
			  Reg = tempadr; }
#endif
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
	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);
	Xil_L1DCacheFlush();
	Xil_L2CacheFlush();

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
void Xil_DCacheFlushLine(unsigned int adr)
{
	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);
	Xil_L1DCacheFlushLine(adr);

	/* Disable Write-back and line fills */
	Xil_L2WriteDebugCtrl(0x3);

	Xil_L2CacheFlushLine(adr);

	/* Enable Write-back and line fills */
	Xil_L2WriteDebugCtrl(0x0);
	Xil_L2CacheSync();
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
void Xil_DCacheFlushRange(unsigned int adr, unsigned len)
{
	const unsigned cacheline = 32;
	unsigned int end;
	unsigned int currmask;
	volatile u32 *L2CCOffset = (volatile u32 *) (XPS_L2CC_BASEADDR +
				    XPS_L2CC_CACHE_INV_CLN_PA_OFFSET);

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	if (len != 0) {
		/* Back the starting address up to the start of a cache line
		 * perform cache operations until adr+len
		 */
		end = adr + len;
		adr &= ~(cacheline - 1);

		while (adr < end) {
#ifdef __GNUC__
			/* Flush L1 Data cache line */
			__asm__ __volatile__("mcr " \
			XREG_CP15_CLEAN_INVAL_DC_LINE_MVA_POC :: "r" (adr));
#else
			{ volatile register unsigned int Reg
				__asm(XREG_CP15_CLEAN_INVAL_DC_LINE_MVA_POC);
			  Reg = adr; }
#endif
			/* Flush L2 cache line */
			*L2CCOffset = adr;
			dsb();
			adr += cacheline;
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
void Xil_DCacheStoreLine(unsigned int adr)
{
	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	Xil_L1DCacheStoreLine(adr);
	Xil_L2CacheStoreLine(adr);
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
	Xil_L1ICacheEnable();
	Xil_L2CacheEnable();
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
	Xil_L2CacheDisable();
	Xil_L1ICacheDisable();
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

	Xil_L2CacheInvalidate();
	Xil_L1ICacheInvalidate();

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
void Xil_ICacheInvalidateLine(unsigned int adr)
{
	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);
	Xil_L2CacheInvalidateLine(adr);
	Xil_L1ICacheInvalidateLine(adr);
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
void Xil_ICacheInvalidateRange(unsigned int adr, unsigned len)
{
	const unsigned cacheline = 32;
	unsigned int end;
	volatile u32 *L2CCOffset = (volatile u32 *) (XPS_L2CC_BASEADDR +
				    XPS_L2CC_CACHE_INVLD_PA_OFFSET);

	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);
	if (len != 0) {
		/* Back the starting address up to the start of a cache line
		 * perform cache operations until adr+len
		 */
		end = adr + len;
		adr = adr & ~(cacheline - 1);

		/* Select cache L0 I-cache in CSSR */
		mtcp(XREG_CP15_CACHE_SIZE_SEL, 1);

		while (adr < end) {
		/* Invalidate L2 cache line */
		*L2CCOffset = adr;
		dsb();
#ifdef __GNUC__
			/* Invalidate L1 I-cache line */
			__asm__ __volatile__("mcr " \
			XREG_CP15_INVAL_IC_LINE_MVA_POU :: "r" (adr));
#else
			{ volatile register unsigned int Reg
				__asm(XREG_CP15_INVAL_IC_LINE_MVA_POU);
			  Reg = adr; }
#endif

			adr += cacheline;
		}
	}

	/* Wait for L1 and L2 invalidate to complete */
	dsb();
	mtcpsr(currmask);
}

/****************************************************************************
*
* Enable the level 1 Data cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_L1DCacheEnable(void)
{
	register unsigned int CtrlReg;

	/* enable caches only if they are disabled */
#ifdef __GNUC__
	CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
#else
	{ volatile register unsigned int Reg __asm(XREG_CP15_SYS_CONTROL);
	  CtrlReg = Reg; }
#endif
	if (CtrlReg & XREG_CP15_CONTROL_C_BIT) {
		return;
	}

	/* clean and invalidate the Data cache */
	Xil_L1DCacheInvalidate();

	/* enable the Data cache */
	CtrlReg |= (XREG_CP15_CONTROL_C_BIT);

	mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
}

/****************************************************************************
*
* Disable the level 1 Data cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_L1DCacheDisable(void)
{
	register unsigned int CtrlReg;

	/* clean and invalidate the Data cache */
	Xil_L1DCacheFlush();

#ifdef __GNUC__
	/* disable the Data cache */
	CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
#else
	{ volatile register unsigned int Reg __asm(XREG_CP15_SYS_CONTROL);
	  CtrlReg = Reg; }
#endif

	CtrlReg &= ~(XREG_CP15_CONTROL_C_BIT);

	mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
}

/****************************************************************************
*
* Invalidate the level 1 Data cache.
*
* @param	None.
*
* @return	None.
*
* @note		In Cortex A9, there is no cp instruction for invalidating
*		the whole D-cache. This function invalidates each line by
*		set/way.
*
****************************************************************************/
void Xil_L1DCacheInvalidate(void)
{
	register unsigned int CsidReg, C7Reg;
	unsigned int CacheSize, LineSize, NumWays;
	unsigned int Way, WayIndex, Set, SetIndex, NumSet;
	unsigned int currmask;
	
#ifdef __GNUC__
	unsigned int stack_start,stack_end,stack_size;
#endif 
	
	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);
	
#ifdef __GNUC__
	stack_end = (unsigned int )&_stack_end;
	stack_start = (unsigned int )&_stack;
	stack_size=stack_start-stack_end;

	/*Flush stack memory to save return address*/
	Xil_DCacheFlushRange(stack_end, stack_size);
#endif
	
	/* Select cache level 0 and D cache in CSSR */
	mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);

#ifdef __GNUC__
	CsidReg = mfcp(XREG_CP15_CACHE_SIZE_ID);
#else
	{ volatile register unsigned int Reg __asm(XREG_CP15_CACHE_SIZE_ID);
	  CsidReg = Reg; }
#endif
	/* Determine Cache Size */
	CacheSize = (CsidReg >> 13) & 0x1FF;
	CacheSize +=1;
	CacheSize *=128;    /* to get number of bytes */

	/* Number of Ways */
	NumWays = (CsidReg & 0x3ff) >> 3;
	NumWays += 1;

	/* Get the cacheline size, way size, index size from csidr */
	LineSize = (CsidReg & 0x07) + 4;

	NumSet = CacheSize/NumWays;
	NumSet /= (1 << LineSize);

	Way = 0UL;
	Set = 0UL;

	/* Invalidate all the cachelines */
	for (WayIndex =0; WayIndex < NumWays; WayIndex++) {
		for (SetIndex =0; SetIndex < NumSet; SetIndex++) {
			C7Reg = Way | Set;
#ifdef __GNUC__
			/* Invalidate by Set/Way */
			__asm__ __volatile__("mcr " \
			XREG_CP15_INVAL_DC_LINE_SW :: "r" (C7Reg));
#else
			//mtcp(XREG_CP15_INVAL_DC_LINE_SW, C7Reg);
			{ volatile register unsigned int Reg
				__asm(XREG_CP15_INVAL_DC_LINE_SW);
			  Reg = C7Reg; }
#endif
			Set += (1 << LineSize);
		}
		Set=0UL;
		Way += 0x40000000;
	}

	/* Wait for L1 invalidate to complete */
	dsb();
	mtcpsr(currmask);
}

/****************************************************************************
*
* Invalidate a level 1 Data cache line. If the byte specified by the address
* (Addr) is cached by the Data cache, the cacheline containing that byte is
* invalidated.	If the cacheline is modified (dirty), the modified contents
* are lost and are NOT written to system memory before the line is
* invalidated.
*
* @param	Address to be flushed.
*
* @return	None.
*
* @note		The bottom 5 bits are set to 0, forced by architecture.
*
****************************************************************************/
void Xil_L1DCacheInvalidateLine(unsigned int adr)
{
	mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);
	mtcp(XREG_CP15_INVAL_DC_LINE_MVA_POC, (adr & (~0x1F)));

	/* Wait for L1 invalidate to complete */
	dsb();
}

/****************************************************************************
*
* Invalidate the level 1 Data cache for the given address range.
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
void Xil_L1DCacheInvalidateRange(unsigned int adr, unsigned len)
{
	const unsigned cacheline = 32;
	unsigned int end;
	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	if (len != 0) {
		/* Back the starting address up to the start of a cache line
		 * perform cache operations until adr+len
		 */
		end = adr + len;
		adr = adr & ~(cacheline - 1);

		/* Select cache L0 D-cache in CSSR */
		mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);

		while (adr < end) {
#ifdef __GNUC__
			__asm__ __volatile__("mcr " \
			XREG_CP15_INVAL_DC_LINE_MVA_POC :: "r" (adr));
#else
			{ volatile register unsigned int Reg
				__asm(XREG_CP15_INVAL_DC_LINE_MVA_POC);
			  Reg = adr; }
#endif
			adr += cacheline;
		}
	}

	/* Wait for L1 invalidate to complete */
	dsb();
	mtcpsr(currmask);
}

/****************************************************************************
*
* Flush the level 1 Data cache.
*
* @param	None.
*
* @return	None.
*
* @note		In Cortex A9, there is no cp instruction for flushing
*		the whole D-cache. Need to flush each line.
*
****************************************************************************/
void Xil_L1DCacheFlush(void)
{
	register unsigned int CsidReg, C7Reg;
	unsigned int CacheSize, LineSize, NumWays;
	unsigned int Way, WayIndex, Set, SetIndex, NumSet;
	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	/* Select cache level 0 and D cache in CSSR */
	mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);

#ifdef __GNUC__
	CsidReg = mfcp(XREG_CP15_CACHE_SIZE_ID);
#else
	{ volatile register unsigned int Reg __asm(XREG_CP15_CACHE_SIZE_ID);
	  CsidReg = Reg; }
#endif

	/* Determine Cache Size */

	CacheSize = (CsidReg >> 13) & 0x1FF;
	CacheSize +=1;
	CacheSize *=128;    /* to get number of bytes */

	/* Number of Ways */
	NumWays = (CsidReg & 0x3ff) >> 3;
	NumWays += 1;

	/* Get the cacheline size, way size, index size from csidr */
	LineSize = (CsidReg & 0x07) + 4;

	NumSet = CacheSize/NumWays;
	NumSet /= (1 << LineSize);

	Way = 0UL;
	Set = 0UL;

	/* Invalidate all the cachelines */
	for (WayIndex =0; WayIndex < NumWays; WayIndex++) {
		for (SetIndex =0; SetIndex < NumSet; SetIndex++) {
			C7Reg = Way | Set;
			/* Flush by Set/Way */
#ifdef __GNUC__
			__asm__ __volatile__("mcr " \
			XREG_CP15_CLEAN_INVAL_DC_LINE_SW :: "r" (C7Reg));
#else
			{ volatile register unsigned int Reg
				__asm(XREG_CP15_CLEAN_INVAL_DC_LINE_SW);
			  Reg = C7Reg; }
#endif
			Set += (1 << LineSize);
		}
		Set = 0UL;
		Way += 0x40000000;
	}

	/* Wait for L1 flush to complete */
	dsb();
	mtcpsr(currmask);
}

/****************************************************************************
*
* Flush a level 1 Data cache line. If the byte specified by the address (adr)
* is cached by the Data cache, the cacheline containing that byte is
* invalidated.	If the cacheline is modified (dirty), the entire
* contents of the cacheline are written to system memory before the
* line is invalidated.
*
* @param	Address to be flushed.
*
* @return	None.
*
* @note		The bottom 5 bits are set to 0, forced by architecture.
*
****************************************************************************/
void Xil_L1DCacheFlushLine(unsigned int adr)
{
	mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);
	mtcp(XREG_CP15_CLEAN_INVAL_DC_LINE_MVA_POC, (adr & (~0x1F)));

	/* Wait for L1 flush to complete */
	dsb();
}

/****************************************************************************
* Flush the level 1  Data cache for the given address range.
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
void Xil_L1DCacheFlushRange(unsigned int adr, unsigned len)
{
	const unsigned cacheline = 32;
	unsigned int end;
	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	if (len != 0) {
		/* Back the starting address up to the start of a cache line
		 * perform cache operations until adr+len
		 */
		end = adr + len;
		adr = adr & ~(cacheline - 1);

		/* Select cache L0 D-cache in CSSR */
		mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);

		while (adr < end) {
#ifdef __GNUC__
			__asm__ __volatile__("mcr " \
			XREG_CP15_CLEAN_INVAL_DC_LINE_MVA_POC :: "r" (adr));
#else
			{ volatile register unsigned int Reg
				__asm(XREG_CP15_CLEAN_INVAL_DC_LINE_MVA_POC);
			  Reg = adr; }
#endif
			adr += cacheline;
		}
	}

	/* Wait for L1 flush to complete */
	dsb();
	mtcpsr(currmask);
}

/****************************************************************************
*
* Store a level 1  Data cache line. If the byte specified by the address (adr)
* is cached by the Data cache and the cacheline is modified (dirty),
* the entire contents of the cacheline are written to system memory.
* After the store completes, the cacheline is marked as unmodified
* (not dirty).
*
* @param	Address to be stored.
*
* @return	None.
*
* @note		The bottom 5 bits are set to 0, forced by architecture.
*
****************************************************************************/
void Xil_L1DCacheStoreLine(unsigned int adr)
{
	mtcp(XREG_CP15_CACHE_SIZE_SEL, 0);
	mtcp(XREG_CP15_CLEAN_DC_LINE_MVA_POC, (adr & (~0x1F)));

	/* Wait for L1 store to complete */
	dsb();
}

/****************************************************************************
*
* Enable the level 1 instruction cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_L1ICacheEnable(void)
{
	register unsigned int CtrlReg;

	/* enable caches only if they are disabled */
#ifdef __GNUC__
	CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
#else
	{ volatile register unsigned int Reg __asm(XREG_CP15_SYS_CONTROL);
	  CtrlReg = Reg; }
#endif
	if (CtrlReg & XREG_CP15_CONTROL_I_BIT) {
		return;
	}

	/* invalidate the instruction cache */
	mtcp(XREG_CP15_INVAL_IC_POU, 0);

	/* enable the instruction cache */
	CtrlReg |= (XREG_CP15_CONTROL_I_BIT);

	mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
}

/****************************************************************************
*
* Disable level 1 the instruction cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_L1ICacheDisable(void)
{
	register unsigned int CtrlReg;

	dsb();

	/* invalidate the instruction cache */
	mtcp(XREG_CP15_INVAL_IC_POU, 0);

	/* disable the instruction cache */
#ifdef __GNUC__
	CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
#else
	{ volatile register unsigned int Reg __asm(XREG_CP15_SYS_CONTROL);
	  CtrlReg = Reg; }
#endif
	CtrlReg &= ~(XREG_CP15_CONTROL_I_BIT);

	mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
}

/****************************************************************************
*
* Invalidate the entire level 1 instruction cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_L1ICacheInvalidate(void)
{
	mtcp(XREG_CP15_CACHE_SIZE_SEL, 1);
	/* invalidate the instruction cache */
	mtcp(XREG_CP15_INVAL_IC_POU, 0);

	/* Wait for L1 invalidate to complete */
	dsb();
}

/****************************************************************************
*
* Invalidate a level 1  instruction cache line.	If the instruction specified by
* the parameter adr is cached by the instruction cache, the cacheline containing
* that instruction is invalidated.
*
* @param	None.
*
* @return	None.
*
* @note		The bottom 5 bits are set to 0, forced by architecture.
*
****************************************************************************/
void Xil_L1ICacheInvalidateLine(unsigned int adr)
{
	mtcp(XREG_CP15_CACHE_SIZE_SEL, 1);
	mtcp(XREG_CP15_INVAL_IC_LINE_MVA_POU, (adr & (~0x1F)));

	/* Wait for L1 invalidate to complete */
	dsb();
}

/****************************************************************************
*
* Invalidate the level 1 instruction cache for the given address range.
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
void Xil_L1ICacheInvalidateRange(unsigned int adr, unsigned len)
{
	const unsigned cacheline = 32;
	unsigned int end;
	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	if (len != 0) {
		/* Back the starting address up to the start of a cache line
		 * perform cache operations until adr+len
		 */
		end = adr + len;
		adr = adr & ~(cacheline - 1);

		/* Select cache L0 I-cache in CSSR */
		mtcp(XREG_CP15_CACHE_SIZE_SEL, 1);

		while (adr < end) {
#ifdef __GNUC__
			__asm__ __volatile__("mcr " \
			XREG_CP15_INVAL_IC_LINE_MVA_POU :: "r" (adr));
#else
			{ volatile register unsigned int Reg
				__asm(XREG_CP15_INVAL_IC_LINE_MVA_POU);
			  Reg = adr; }
#endif
			adr += cacheline;
		}
	}

	/* Wait for L1 invalidate to complete */
	dsb();
	mtcpsr(currmask);
}

/****************************************************************************
*
* Enable the L2 cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_L2CacheEnable(void)
{
	register unsigned int L2CCReg;

	L2CCReg = Xil_In32(XPS_L2CC_BASEADDR + XPS_L2CC_CNTRL_OFFSET);

	/* only enable if L2CC is currently disabled */
	if ((L2CCReg & 0x01) == 0) {
		/* set up the way size and latencies */
		L2CCReg = Xil_In32(XPS_L2CC_BASEADDR +
				   XPS_L2CC_AUX_CNTRL_OFFSET);
		L2CCReg &= XPS_L2CC_AUX_REG_ZERO_MASK;
		L2CCReg |= XPS_L2CC_AUX_REG_DEFAULT_MASK;
		Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_AUX_CNTRL_OFFSET,
			  L2CCReg);
		Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_TAG_RAM_CNTRL_OFFSET,
			  XPS_L2CC_TAG_RAM_DEFAULT_MASK);
		Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_DATA_RAM_CNTRL_OFFSET,
			  XPS_L2CC_DATA_RAM_DEFAULT_MASK);

		/* Clear the pending interrupts */
		L2CCReg = Xil_In32(XPS_L2CC_BASEADDR +
				   XPS_L2CC_ISR_OFFSET);
		Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_IAR_OFFSET, L2CCReg);

		Xil_L2CacheInvalidate();
		/* Enable the L2CC */
		L2CCReg = Xil_In32(XPS_L2CC_BASEADDR +
				   XPS_L2CC_CNTRL_OFFSET);
		Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_CNTRL_OFFSET,
			  (L2CCReg | (0x01)));

        Xil_L2CacheSync();
        /* synchronize the processor */
	    dsb();

    }
}

/****************************************************************************
*
* Disable the L2 cache.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_L2CacheDisable(void)
{
    register unsigned int L2CCReg;

	L2CCReg = Xil_In32(XPS_L2CC_BASEADDR + XPS_L2CC_CNTRL_OFFSET);

    if(L2CCReg & 0x1) {

        /* Clean and Invalidate L2 Cache */
        Xil_L2CacheFlush();

	    /* Disable the L2CC */
    	L2CCReg = Xil_In32(XPS_L2CC_BASEADDR + XPS_L2CC_CNTRL_OFFSET);
	    Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_CNTRL_OFFSET,
		      (L2CCReg & (~0x01)));
		/* Wait for the cache operations to complete */

		dsb();
    }
}

/****************************************************************************
*
* Invalidate the L2 cache. If the byte specified by the address (adr)
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
void Xil_L2CacheInvalidate(void)
{
	/* Invalidate the caches */
	Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_CACHE_INVLD_WAY_OFFSET,
		  0x0000FFFF);
	while((Xil_In32(XPS_L2CC_BASEADDR + XPS_L2CC_CACHE_INVLD_WAY_OFFSET))
																& 0x0000FFFF);

	/* Wait for the invalidate to complete */
	Xil_L2CacheSync();

	/* synchronize the processor */
	dsb();
}

/****************************************************************************
*
* Invalidate a level 2 cache line. If the byte specified by the address (adr)
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
void Xil_L2CacheInvalidateLine(unsigned int adr)
{
	Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_CACHE_INVLD_PA_OFFSET, adr);
	/* synchronize the processor */
	dsb();
}

/****************************************************************************
*
* Invalidate the level 2 cache for the given address range.
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
void Xil_L2CacheInvalidateRange(unsigned int adr, unsigned len)
{
	const unsigned cacheline = 32;
	unsigned int end;
	volatile u32 *L2CCOffset = (volatile u32 *) (XPS_L2CC_BASEADDR +
				    XPS_L2CC_CACHE_INVLD_PA_OFFSET);

	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);

	if (len != 0) {
		/* Back the starting address up to the start of a cache line
		 * perform cache operations until adr+len
		 */
		end = adr + len;
		adr = adr & ~(cacheline - 1);

		/* Disable Write-back and line fills */
		Xil_L2WriteDebugCtrl(0x3);

		while (adr < end) {
			*L2CCOffset = adr;
			adr += cacheline;
		}

		/* Enable Write-back and line fills */
		Xil_L2WriteDebugCtrl(0x0);
	}

	/* synchronize the processor */
	dsb();
	mtcpsr(currmask);
}

/****************************************************************************
*
* Flush the L2 cache. If the byte specified by the address (adr)
* is cached by the Data cache, the cacheline containing that byte is
* invalidated. If the cacheline is modified (dirty), the entire
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
void Xil_L2CacheFlush(void)
{

	/* Flush the caches */

	/* Disable Write-back and line fills */
	Xil_L2WriteDebugCtrl(0x3);

	Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_CACHE_INV_CLN_WAY_OFFSET,
		  0x0000FFFF);

	while((Xil_In32(XPS_L2CC_BASEADDR + XPS_L2CC_CACHE_INV_CLN_WAY_OFFSET))
															& 0x0000FFFF);

	Xil_L2CacheSync();
	/* Enable Write-back and line fills */
	Xil_L2WriteDebugCtrl(0x0);

	/* synchronize the processor */
	dsb();
}

/****************************************************************************
*
* Flush a level 2 cache line. If the byte specified by the address (adr)
* is cached by the Data cache, the cacheline containing that byte is
* invalidated. If the cacheline is modified (dirty), the entire
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
void Xil_L2CacheFlushLine(unsigned int adr)
{
#ifdef CONFIG_PL310_ERRATA_588369
	Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_CACHE_CLEAN_PA_OFFSET, adr);
	Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_CACHE_INVLD_PA_OFFSET, adr);
#else
	Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_CACHE_INV_CLN_PA_OFFSET, adr);
#endif
	/* synchronize the processor */
	dsb();
}

/****************************************************************************
* Flush the level 2 cache for the given address range.
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
void Xil_L2CacheFlushRange(unsigned int adr, unsigned len)
{
	const unsigned cacheline = 32;
	unsigned int end;
	volatile u32 *L2CCOffset = (volatile u32 *) (XPS_L2CC_BASEADDR +
				    XPS_L2CC_CACHE_INV_CLN_PA_OFFSET);

	unsigned int currmask;

	currmask = mfcpsr();
	mtcpsr(currmask | IRQ_FIQ_MASK);
	if (len != 0) {
		/* Back the starting address up to the start of a cache line
		 * perform cache operations until adr+len
		 */
		end = adr + len;
		adr = adr & ~(cacheline - 1);

		/* Disable Write-back and line fills */
		Xil_L2WriteDebugCtrl(0x3);

		while (adr < end) {
			*L2CCOffset = adr;
			Xil_L2CacheSync();
			adr += cacheline;
		}

		/* Enable Write-back and line fills */
		Xil_L2WriteDebugCtrl(0x0);
	}
	/* synchronize the processor */
	dsb();
	mtcpsr(currmask);
}

/****************************************************************************
*
* Store a level 2 cache line. If the byte specified by the address (adr)
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
void Xil_L2CacheStoreLine(unsigned int adr)
{
	Xil_Out32(XPS_L2CC_BASEADDR + XPS_L2CC_CACHE_CLEAN_PA_OFFSET, adr);
	/* synchronize the processor */
	dsb();
}
