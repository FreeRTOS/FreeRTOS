/******************************************************************************
*
* Copyright (C) 2004 - 2014 Xilinx, Inc. All rights reserved.
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
*  _program_timer_hw.c:
*	Timer related functions
*
******************************************************************************/

#include "profile.h"
#include "_profile_timer_hw.h"

#include "xil_exception.h"

#ifdef PROC_PPC
#include "xtime_l.h"
#include "xpseudo_asm.h"
#endif

#ifdef TIMER_CONNECT_INTC
#include "xintc_l.h"
#include "xintc.h"
#endif	/* TIMER_CONNECT_INTC */

/* #ifndef PPC_PIT_INTERRUPT */
#if (!defined PPC_PIT_INTERRUPT && !defined PROC_CORTEXA9)
#include "xtmrctr_l.h"
#endif

/* extern u32 timer_clk_ticks, */

#ifdef PROC_PPC405
#ifdef PPC_PIT_INTERRUPT
s32 ppc_pit_init( void );
#endif
s32 powerpc405_init()
#endif	/* PROC_CORTEXA9 */

#ifdef PROC_PPC440
#ifdef PPC_PIT_INTERRUPT
s32 ppc_dec_init( void );
#endif
s32 powerpc405_init(void);
#endif	/* PROC_PPC440 */

#if (!defined PPC_PIT_INTERRUPT && !defined PROC_CORTEXA9)
s32 opb_timer_init( void );
#endif

#ifdef PROC_MICROBLAZE
s32 microblaze_init(void);
#endif	/* PROC_MICROBLAZE */

#ifdef PROC_CORTEXA9
s32 scu_timer_init( void );
s32 cortexa9_init(void);
#endif	/* PROC_CORTEXA9 */


/*--------------------------------------------------------------------
  * PowerPC Target - Timer related functions
  *-------------------------------------------------------------------- */
#ifdef PROC_PPC405


/*--------------------------------------------------------------------
* PowerPC PIT Timer Init.
*	Defined only if PIT Timer is used for Profiling
*
*-------------------------------------------------------------------- */
#ifdef PPC_PIT_INTERRUPT
int ppc_pit_init( void )
{
	/* 1. Register Profile_intr_handler as Interrupt handler */
	/* 2. Set PIT Timer Interrupt and Enable it. */
	Xil_ExceptionRegisterHandler( XIL_EXCEPTION_ID_PIT_INT,
			    (Xil_ExceptionHandler)profile_intr_handler,NULL);
	XTime_PITSetInterval( timer_clk_ticks ) ;
	XTime_PITEnableAutoReload() ;
	return 0;
}
#endif


/* --------------------------------------------------------------------
* PowerPC Timer Initialization functions.
*	For PowerPC, PIT and opb_timer can be used for Profiling. This
*	is selected by the user in standalone BSP
*
*-------------------------------------------------------------------- */
s32 powerpc405_init()
{
	Xil_ExceptionInit() ;
	Xil_ExceptionDisableMask( XIL_EXCEPTION_NON_CRITICAL ) ;

	/* Initialize the Timer.
	  * 1. If PowerPC PIT Timer has to be used, initialize PIT timer.
	  * 2. Else use opb_timer. It can be directly connected or thru intc to PowerPC */
#ifdef PPC_PIT_INTERRUPT
	ppc_pit_init();
#else
#ifdef TIMER_CONNECT_INTC
	Xil_ExceptionRegisterHandler( XIL_EXCEPTION_ID_NON_CRITICAL_INT,
			      (Xil_ExceptionHandler)XIntc_DeviceInterruptHandler,NULL);
	XIntc_RegisterHandler( INTC_BASEADDR, PROFILE_TIMER_INTR_ID,
			     (XInterruptHandler)profile_intr_handler,NULL);
#else
	Xil_ExceptionRegisterHandler( XIL_EXCEPTION_ID_NON_CRITICAL_INT,
			      (Xil_ExceptionHandler)profile_intr_handler,NULL);
#endif
	/* Initialize the timer with Timer Ticks */
	opb_timer_init() ;
#endif

	/* Enable Interrupts in the System, if Profile Timer is the only Interrupt
	  * in the System. */
#ifdef ENABLE_SYS_INTR
#ifdef PPC_PIT_INTERRUPT
	XTime_PITEnableInterrupt() ;
#elif TIMER_CONNECT_INTC
	XIntc_MasterEnable( INTC_BASEADDR );
	XIntc_SetIntrSvcOption( INTC_BASEADDR, XIN_SVC_ALL_ISRS_OPTION);
	XIntc_EnableIntr( INTC_BASEADDR, PROFILE_TIMER_INTR_MASK );
#endif
	Xil_ExceptionEnableMask( XIL_EXCEPTION_NON_CRITICAL ) ;
#endif
	return 0;
}

#endif	/* PROC_PPC */



/*--------------------------------------------------------------------
  * PowerPC440 Target - Timer related functions
  * -------------------------------------------------------------------- */
#ifdef PROC_PPC440


/*--------------------------------------------------------------------
 * PowerPC DEC Timer Init.
 *	Defined only if DEC Timer is used for Profiling
 *
 *-------------------------------------------------------------------- */
#ifdef PPC_PIT_INTERRUPT
s32 ppc_dec_init( void )
{
	/* 1. Register Profile_intr_handler as Interrupt handler */
	/* 2. Set DEC Timer Interrupt and Enable it. */
	Xil_ExceptionRegisterHandler( XIL_EXCEPTION_ID_DEC_INT,
			    (Xil_ExceptionHandler)profile_intr_handler,NULL);
	XTime_DECSetInterval( timer_clk_ticks ) ;
	XTime_DECEnableAutoReload() ;
	return 0;
}
#endif


/*--------------------------------------------------------------------
 * PowerPC Timer Initialization functions.
 *	For PowerPC, DEC and opb_timer can be used for Profiling. This
 *	is selected by the user in standalone BSP
 *
 *-------------------------------------------------------------------- */
s32 powerpc405_init(void)
{
	Xil_ExceptionInit();
	Xil_ExceptionDisableMask( XIL_EXCEPTION_NON_CRITICAL ) ;

	/* Initialize the Timer.
	 * 1. If PowerPC DEC Timer has to be used, initialize DEC timer.
	 * 2. Else use opb_timer. It can be directly connected or thru intc to PowerPC */
#ifdef PPC_PIT_INTERRUPT
	ppc_dec_init();
#else
#ifdef TIMER_CONNECT_INTC
	Xil_ExceptionRegisterHandler(XIL_EXCEPTION_ID_NON_CRITICAL_INT,
				     (Xil_ExceptionHandler)XIntc_DeviceInterruptHandler,NULL);

	XIntc_RegisterHandler( INTC_BASEADDR, PROFILE_TIMER_INTR_ID,
			     (XInterruptHandler)profile_intr_handler,NULL);
#else
	Xil_ExceptionRegisterHandler( XIL_EXCEPTION_ID_NON_CRITICAL_INT,
			      (Xil_ExceptionHandler)profile_intr_handler,NULL);
	Xil_ExceptionRegisterHandler( XIL_EXCEPTION_ID_NON_CRITICAL_INT,
			      (Xil_ExceptionHandler)profile_intr_handler,NULL);
#endif
	/* Initialize the timer with Timer Ticks */
	opb_timer_init() ;
#endif

	/* Enable Interrupts in the System, if Profile Timer is the only Interrupt
	 * in the System. */
#ifdef ENABLE_SYS_INTR
#ifdef PPC_PIT_INTERRUPT
	XTime_DECEnableInterrupt() ;
#elif TIMER_CONNECT_INTC
	XIntc_MasterEnable( INTC_BASEADDR );
	XIntc_SetIntrSvcOption( INTC_BASEADDR, XIN_SVC_ALL_ISRS_OPTION);
	XIntc_EnableIntr( INTC_BASEADDR, PROFILE_TIMER_INTR_MASK );
#endif
	Xil_ExceptionEnableMask( XEXC_NON_CRITICAL ) ;
#endif
	return 0;
}

#endif	/* PROC_PPC440 */

/* --------------------------------------------------------------------
 * opb_timer Initialization for PowerPC and MicroBlaze. This function
 * is not needed if DEC timer is used in PowerPC
 *
 *-------------------------------------------------------------------- */
/* #ifndef PPC_PIT_INTERRUPT */
#if (!defined PPC_PIT_INTERRUPT && !defined PROC_CORTEXA9)
s32 opb_timer_init( void )
{
	/* set the number of cycles the timer counts before interrupting */
	XTmrCtr_SetLoadReg((u32)PROFILE_TIMER_BASEADDR, (u16)0, (u32)timer_clk_ticks);

	/* reset the timers, and clear interrupts */
	XTmrCtr_SetControlStatusReg((u32)PROFILE_TIMER_BASEADDR, (u16)0,
				     (u32)XTC_CSR_INT_OCCURED_MASK | (u32)XTC_CSR_LOAD_MASK );

	/* start the timers */
	XTmrCtr_SetControlStatusReg((u32)PROFILE_TIMER_BASEADDR, (u16)0, (u32)XTC_CSR_ENABLE_TMR_MASK
			     | (u32)XTC_CSR_ENABLE_INT_MASK | (u32)XTC_CSR_AUTO_RELOAD_MASK | (u32)XTC_CSR_DOWN_COUNT_MASK);
	return 0;
}
#endif


/*--------------------------------------------------------------------
 * MicroBlaze Target - Timer related functions
 *-------------------------------------------------------------------- */
#ifdef PROC_MICROBLAZE

/* --------------------------------------------------------------------
 * Initialize the Profile Timer for MicroBlaze Target.
 *	For MicroBlaze, opb_timer is used. The opb_timer can be directly
 *	connected to MicroBlaze or connected through Interrupt Controller.
 *
 *-------------------------------------------------------------------- */
s32 microblaze_init(void)
{
	/* Register profile_intr_handler
	 * 1. If timer is connected to Interrupt Controller, register the handler
	 *    to Interrupt Controllers vector table.
	 * 2. If timer is directly connected to MicroBlaze, register the handler
	 *    as Interrupt handler */
	Xil_ExceptionInit();

#ifdef TIMER_CONNECT_INTC
	XIntc_RegisterHandler( INTC_BASEADDR, PROFILE_TIMER_INTR_ID,
			     (XInterruptHandler)profile_intr_handler,NULL);
#else
	Xil_ExceptionRegisterHandler(XIL_EXCEPTION_ID_INT,
				     (Xil_ExceptionHandler)profile_intr_handler,
				     NULL) ;
#endif

	/* Initialize the timer with Timer Ticks */
	(void)opb_timer_init() ;

	/* Enable Interrupts in the System, if Profile Timer is the only Interrupt
	 * in the System. */
#ifdef ENABLE_SYS_INTR
#ifdef TIMER_CONNECT_INTC
	XIntc_MasterEnable((u32)INTC_BASEADDR );
	XIntc_SetIntrSvcOption( INTC_BASEADDR, XIN_SVC_ALL_ISRS_OPTION);
	XIntc_EnableIntr( (u32)INTC_BASEADDR, PROFILE_TIMER_INTR_MASK );
	Xil_ExceptionRegisterHandler(XIL_EXCEPTION_ID_INT,
				     (Xil_ExceptionHandler)XIntc_DeviceInterruptHandler,NULL);
#endif

#endif

	Xil_ExceptionEnable();

	return 0;

}

#endif	/* PROC_MICROBLAZE */



/* --------------------------------------------------------------------
 * Cortex A9 Target - Timer related functions
 *-------------------------------------------------------------------- */
#ifdef PROC_CORTEXA9

/* --------------------------------------------------------------------
 * Initialize the Profile Timer for Cortex A9 Target.
 *	The scu private timer is connected to the Scu GIC controller.
 *
 *-------------------------------------------------------------------- */
s32 scu_timer_init( void )
{
	/* set the number of cycles the timer counts before interrupting
	 * scu timer runs at half the cpu clock */
	XScuTimer_SetLoadReg(PROFILE_TIMER_BASEADDR, timer_clk_ticks/2U);

	/* clear any pending interrupts */
	XScuTimer_SetIntrReg(PROFILE_TIMER_BASEADDR, 1U);

	/* enable interrupts, auto-reload mode and start the timer */
	XScuTimer_SetControlReg(PROFILE_TIMER_BASEADDR, XSCUTIMER_CONTROL_IRQ_ENABLE_MASK |
				XSCUTIMER_CONTROL_AUTO_RELOAD_MASK | XSCUTIMER_CONTROL_ENABLE_MASK);

	return 0;
}

s32 cortexa9_init(void)
{

	Xil_ExceptionInit();

	XScuGic_DeviceInitialize(0);

	/*
	 * Connect the interrupt controller interrupt handler to the hardware
	 * interrupt handling logic in the processor.
	 */
	Xil_ExceptionRegisterHandler(XIL_EXCEPTION_ID_IRQ_INT,
				(Xil_ExceptionHandler)XScuGic_DeviceInterruptHandler,
				NULL);

	/*
	 * Connect the device driver handler that will be called when an
	 * interrupt for the device occurs, the handler defined above performs
	 * the specific interrupt processing for the device.
	 */
	XScuGic_RegisterHandler(SCUGIC_CPU_BASEADDR,
				PROFILE_TIMER_INTR_ID,
				(Xil_ExceptionHandler)profile_intr_handler,
				NULL);

	/*
	 * Enable the interrupt for scu timer.
	 */
	XScuGic_EnableIntr(SCUGIC_DIST_BASEADDR, PROFILE_TIMER_INTR_ID);

	/*
	 * Enable interrupts in the Processor.
	 */
	Xil_ExceptionEnableMask(XIL_EXCEPTION_IRQ);

	/*
	 * Initialize the timer with Timer Ticks
	 */
	(void)scu_timer_init() ;

	Xil_ExceptionEnable();

	return 0;
}

#endif	/* PROC_CORTEXA9 */
