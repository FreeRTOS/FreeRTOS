/******************************************************************************
*
* (c) Copyright 2009-2013 Xilinx, Inc. All rights reserved.
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
* @file xil-crt0.S
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 1.00a ecm  10/20/09 Initial version
* 3.05a sdm  02/02/12 Added code for profiling
* 3.06a sgd  05/16/12 Added global constructors and cleanup code
*                     Uart initialization based on compiler flag
* 3.07a sgd  07/05/12 Updated with reset and start Global Timer
* 3.07a sgd	 10/19/12 SMC NOR and SRAM initialization with build option
* </pre>
*
* @note
*
* None.
*
******************************************************************************/

.extern XSmc_NorInit
.extern XSmc_SramInit

	.file	"xil-crt0.S"
	.section ".got2","aw"
	.align	2

	.text
.Lsbss_start:
	.long	__sbss_start

.Lsbss_end:
	.long	__sbss_end

.Lbss_start:
	.long	__bss_start

.Lbss_end:	
	.long	__bss_end

.Lstack:	
	.long	__stack

    
	.globl	_start
_start:
	bl      __cpu_init		/* Initialize the CPU first (BSP provides this) */

	mov	r0, #0
	
	/* clear sbss */
	ldr 	r1,.Lsbss_start		/* calculate beginning of the SBSS */
	ldr	r2,.Lsbss_end		/* calculate end of the SBSS */

.Lloop_sbss:
	cmp	r1,r2
	bge	.Lenclsbss		/* If no SBSS, no clearing required */
	str	r0, [r1], #4
	b	.Lloop_sbss

.Lenclsbss:  
	/* clear bss */
	ldr	r1,.Lbss_start		/* calculate beginning of the BSS */
	ldr	r2,.Lbss_end		/* calculate end of the BSS */

.Lloop_bss:	
	cmp	r1,r2
	bge	.Lenclbss		/* If no BSS, no clearing required */
	str	r0, [r1], #4
	b	.Lloop_bss

.Lenclbss:

	/* set stack pointer */
	ldr	r13,.Lstack		/* stack address */

    /* Reset and start Global Timer */
	mov	r0, #0x0
	mov	r1, #0x0
    bl XTime_SetTime
    	
#ifdef PEEP
	/* Initialize STDOUT */
	bl	Init_Uart

	/* Initialize the SMC interfaces for NOR */
	bl	XSmc_NorInit

    /* Initialize the SMC interfaces for SRAM */
	bl	XSmc_SramInit
#endif

#ifdef PROFILING			/* defined in Makefile */
	/* Setup profiling stuff */
	bl	_profile_init
#endif /* PROFILING */

   /* run global constructors */ 
   bl __libc_init_array 

	/* make sure argc and argv are valid */
	mov	r0, #0
	mov	r1, #0

	/* Let her rip */
	bl	main

   /* Cleanup global constructors */ 
   bl __libc_fini_array 

#ifdef PROFILING
	/* Cleanup profiling stuff */
	bl	_profile_clean
#endif /* PROFILING */

        /* All done */
	bl	exit

.Lexit:	/* should never get here */
	b .Lexit

.Lstart:
	.size	_start,.Lstart-_start
