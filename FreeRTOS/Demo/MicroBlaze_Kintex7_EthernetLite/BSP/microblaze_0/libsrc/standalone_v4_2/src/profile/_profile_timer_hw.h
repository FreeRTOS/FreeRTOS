// $Id: _profile_timer_hw.h,v 1.1.2.2 2011/05/30 06:46:18 svemula Exp $
/******************************************************************************
*
* Copyright (C) 2004 - 2014 Xilinx, Inc.  All rights reserved.
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
******************************************************************************
*
* _program_timer_hw.h:
*	Timer related functions
*
******************************************************************************/

#ifndef _PROFILE_TIMER_HW_H
#define _PROFILE_TIMER_HW_H

#include "profile.h"

#ifdef PROC_PPC
#if defined __GNUC__
#  define SYNCHRONIZE_IO __asm__ volatile ("eieio")
#elif defined __DCC__
#  define SYNCHRONIZE_IO __asm volatile(" eieio")
#else
#  define SYNCHRONIZE_IO
#endif
#endif

#ifdef PROC_PPC
#define ProfIo_In32(InputPtr) (*(volatile u32 *)(InputPtr)); SYNCHRONIZE_IO;
#define ProfIo_Out32(OutputPtr, Value) { (*(volatile u32 *)(OutputPtr) = Value); SYNCHRONIZE_IO; }
#else
#define ProfIo_In32(InputPtr) (*(volatile u32 *)(InputPtr));
#define ProfIo_Out32(OutputPtr, Value) { (*(volatile u32 *)(OutputPtr) = Value); }
#endif

#define ProfTmrCtr_mWriteReg(BaseAddress, TmrCtrNumber, RegOffset, ValueToWrite)\
	ProfIo_Out32(((BaseAddress) + XTmrCtr_Offsets[(TmrCtrNumber)] +	\
			   (RegOffset)), (ValueToWrite))

#define ProfTimerCtr_mReadReg(BaseAddress, TmrCtrNumber, RegOffset)	\
	ProfIo_In32((BaseAddress) + XTmrCtr_Offsets[(TmrCtrNumber)] + (RegOffset))

#define ProfTmrCtr_mSetControlStatusReg(BaseAddress, TmrCtrNumber, RegisterValue)\
	ProfTmrCtr_mWriteReg((BaseAddress), (TmrCtrNumber), XTC_TCSR_OFFSET,     \
					   (RegisterValue))

#define ProfTmrCtr_mGetControlStatusReg(BaseAddress, TmrCtrNumber)		\
	ProfTimerCtr_mReadReg((BaseAddress), (TmrCtrNumber), XTC_TCSR_OFFSET)



#ifdef __cplusplus
extern "C" {
#endif

#ifdef PROC_PPC
#include "xexception_l.h"
#include "xtime_l.h"
#include "xpseudo_asm.h"
#endif

#ifdef TIMER_CONNECT_INTC
#include "xintc_l.h"
#include "xintc.h"
#endif	// TIMER_CONNECT_INTC

#if (!defined PPC_PIT_INTERRUPT && !defined PROC_CORTEXA9)
#include "xtmrctr_l.h"
#endif

#ifdef PROC_CORTEXA9
#include "xscutimer_hw.h"
#include "xscugic.h"
#endif

extern unsigned int timer_clk_ticks ;

//--------------------------------------------------------------------
// PowerPC Target - Timer related functions
//--------------------------------------------------------------------
#ifdef PROC_PPC

#ifdef PPC_PIT_INTERRUPT
unsigned long timer_lo_clk_ticks ;	// Clk ticks when Timer is disabled in CG
#endif

#ifdef PROC_PPC440
#define XREG_TCR_PIT_INTERRUPT_ENABLE XREG_TCR_DEC_INTERRUPT_ENABLE
#define XREG_TSR_PIT_INTERRUPT_STATUS XREG_TSR_DEC_INTERRUPT_STATUS
#define XREG_SPR_PIT XREG_SPR_DEC
#define XEXC_ID_PIT_INT XEXC_ID_DEC_INT
#endif

//--------------------------------------------------------------------
// Disable the Timer - During Profiling
//
// For PIT Timer -
//	1. XTime_PITDisableInterrupt() ;
//	2. Store the remaining timer clk tick
//	3. Stop the PIT Timer
//--------------------------------------------------------------------

#ifdef PPC_PIT_INTERRUPT
#define disable_timer() 		\
	{				\
		unsigned long val;	\
		val=mfspr(XREG_SPR_TCR);	\
		mtspr(XREG_SPR_TCR, val & ~XREG_TCR_PIT_INTERRUPT_ENABLE);	\
		timer_lo_clk_ticks = mfspr(XREG_SPR_PIT);			\
		mtspr(XREG_SPR_PIT, 0);	\
	}
#else
#define disable_timer() 	\
   { \
      u32 addr = (PROFILE_TIMER_BASEADDR) + XTmrCtr_Offsets[(0)] + XTC_TCSR_OFFSET; \
      u32 tmp_v = ProfIo_In32(addr); \
      tmp_v = tmp_v & ~XTC_CSR_ENABLE_TMR_MASK; \
      ProfIo_Out32((PROFILE_TIMER_BASEADDR) + XTmrCtr_Offsets[(0)] + XTC_TCSR_OFFSET, tmp_v); \
   }
#endif



//--------------------------------------------------------------------
// Enable the Timer
//
// For PIT Timer -
//	1. Load the remaining timer clk ticks
//	2. XTime_PITEnableInterrupt() ;
//--------------------------------------------------------------------
#ifdef PPC_PIT_INTERRUPT
#define enable_timer()				\
	{					\
		unsigned long val;		\
		val=mfspr(XREG_SPR_TCR);	\
		mtspr(XREG_SPR_PIT, timer_lo_clk_ticks);	\
		mtspr(XREG_SPR_TCR, val | XREG_TCR_PIT_INTERRUPT_ENABLE); \
	}
#else
#define enable_timer()						\
	{							\
      u32 addr = (PROFILE_TIMER_BASEADDR) + XTmrCtr_Offsets[(0)] + XTC_TCSR_OFFSET; \
      u32 tmp_v = ProfIo_In32(addr); \
      tmp_v = tmp_v |  XTC_CSR_ENABLE_TMR_MASK; \
      ProfIo_Out32((PROFILE_TIMER_BASEADDR) + XTmrCtr_Offsets[(0)] + XTC_TCSR_OFFSET, tmp_v); \
	}
#endif



//--------------------------------------------------------------------
// Send Ack to Timer Interrupt
//
// For PIT Timer -
// 	1. Load the timer clk ticks
//	2. Enable AutoReload and Interrupt
//	3. Clear PIT Timer Status bits
//--------------------------------------------------------------------
#ifdef PPC_PIT_INTERRUPT
#define timer_ack()							\
	{								\
		unsigned long val;					\
		mtspr(XREG_SPR_PIT, timer_clk_ticks);			\
		mtspr(XREG_SPR_TSR, XREG_TSR_PIT_INTERRUPT_STATUS);	\
		val=mfspr(XREG_SPR_TCR);				\
		mtspr(XREG_SPR_TCR, val| XREG_TCR_PIT_INTERRUPT_ENABLE| XREG_TCR_AUTORELOAD_ENABLE); \
	}
#else
#define timer_ack()				\
	{						\
		unsigned int csr;			\
		csr = ProfTmrCtr_mGetControlStatusReg(PROFILE_TIMER_BASEADDR, 0);	\
		ProfTmrCtr_mSetControlStatusReg(PROFILE_TIMER_BASEADDR, 0, csr);	\
	}
#endif

//--------------------------------------------------------------------
#endif	// PROC_PPC
//--------------------------------------------------------------------




//--------------------------------------------------------------------
// MicroBlaze Target - Timer related functions
//--------------------------------------------------------------------
#ifdef PROC_MICROBLAZE

//--------------------------------------------------------------------
// Disable the Timer during Call-Graph Data collection
//
//--------------------------------------------------------------------
#define disable_timer()					\
	{						\
      u32 addr = (PROFILE_TIMER_BASEADDR) + XTmrCtr_Offsets[(0)] + XTC_TCSR_OFFSET; \
      u32 tmp_v = ProfIo_In32(addr); \
      tmp_v = tmp_v & ~XTC_CSR_ENABLE_TMR_MASK; \
      ProfIo_Out32((PROFILE_TIMER_BASEADDR) + XTmrCtr_Offsets[(0)] + XTC_TCSR_OFFSET, tmp_v); \
    }


//--------------------------------------------------------------------
// Enable the Timer after Call-Graph Data collection
//
//--------------------------------------------------------------------
#define enable_timer()					\
	{						\
      u32 addr = (PROFILE_TIMER_BASEADDR) + XTmrCtr_Offsets[(0)] + XTC_TCSR_OFFSET; \
      u32 tmp_v = ProfIo_In32(addr); \
      tmp_v = tmp_v |  XTC_CSR_ENABLE_TMR_MASK; \
      ProfIo_Out32((PROFILE_TIMER_BASEADDR) + XTmrCtr_Offsets[(0)] + XTC_TCSR_OFFSET, tmp_v); \
	}


//--------------------------------------------------------------------
// Send Ack to Timer Interrupt
//
//--------------------------------------------------------------------
#define timer_ack()				\
	{						\
		unsigned int csr;			\
		csr = ProfTmrCtr_mGetControlStatusReg(PROFILE_TIMER_BASEADDR, 0);	\
		ProfTmrCtr_mSetControlStatusReg(PROFILE_TIMER_BASEADDR, 0, csr);	\
	}

//--------------------------------------------------------------------
#endif	// PROC_MICROBLAZE
//--------------------------------------------------------------------

//--------------------------------------------------------------------
// Cortex A9 Target - Timer related functions
//--------------------------------------------------------------------
#ifdef PROC_CORTEXA9

//--------------------------------------------------------------------
// Disable the Timer during Call-Graph Data collection
//
//--------------------------------------------------------------------
#define disable_timer()							\
{								\
	u32 Reg;							\
	Reg = Xil_In32(PROFILE_TIMER_BASEADDR + XSCUTIMER_CONTROL_OFFSET); \
	Reg &= ~XSCUTIMER_CONTROL_ENABLE_MASK;\
	Xil_Out32(PROFILE_TIMER_BASEADDR + XSCUTIMER_CONTROL_OFFSET, Reg);\
}								\


//--------------------------------------------------------------------
// Enable the Timer after Call-Graph Data collection
//
//--------------------------------------------------------------------
#define enable_timer()							\
{								\
	u32 Reg;							\
	Reg = Xil_In32(PROFILE_TIMER_BASEADDR + XSCUTIMER_CONTROL_OFFSET); \
	Reg |= XSCUTIMER_CONTROL_ENABLE_MASK; \
	Xil_Out32(PROFILE_TIMER_BASEADDR + XSCUTIMER_CONTROL_OFFSET, Reg);\
}								\


//--------------------------------------------------------------------
// Send Ack to Timer Interrupt
//
//--------------------------------------------------------------------
#define timer_ack()						\
{							\
	Xil_Out32(PROFILE_TIMER_BASEADDR + XSCUTIMER_ISR_OFFSET, \
		XSCUTIMER_ISR_EVENT_FLAG_MASK);\
}

//--------------------------------------------------------------------
#endif	// PROC_CORTEXA9
//--------------------------------------------------------------------


#ifdef __cplusplus
}
#endif

#endif
