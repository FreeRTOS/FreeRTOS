/******************************************************************************
*
* Copyright (C) 2010 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file smc.c
*
* This file contains APIs for configuring the PL353 Static Memory Controller
* interfaces for NAND flash, SRAM and NOR flash.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 1.00a sdm  08/02/10 Initial version
* </pre>
*
* @note
*
* None.
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "smc.h"

/***************** Macros (Inline Functions) Definitions *********************/

/**************************** Type Definitions *******************************/

/************************** Constant Definitions *****************************/

/*
 * Register values for using NOR interface of SMC Controller
 */
#define NOR_SET_CYCLES ((0x0 << 20) | /* set_t6 or we_time from sram_cycles */ \
			(0x1 << 17) | /* set_t5 or t_tr from sram_cycles */    \
			(0x2 << 14) | /* set_t4 or t_pc from sram_cycles */    \
			(0x5 << 11) | /* set_t3 or t_wp from sram_cycles */    \
			(0x2 << 8)  | /* set_t2 t_ceoe from sram_cycles */     \
			(0x7 << 4)  | /* set_t1 t_wc from sram_cycles */       \
			(0x7))	      /* set_t0 t_rc from sram_cycles */

#define NOR_SET_OPMODE ((0x1 << 13) | /* set_burst_align,set to 32 beats */    \
			(0x1 << 12) | /* set_bls,set to default */	       \
			(0x0 << 11) | /* set_adv bit, set to default */	       \
			(0x0 << 10) | /* set_baa, we don't use baa_n */	       \
			(0x0 << 7)  | /* set_wr_bl,write brust len,set to 0 */ \
			(0x0 << 6)  | /* set_wr_sync, set to 0 */	       \
			(0x0 << 3)  | /* set_rd_bl,read brust len,set to 0 */  \
			(0x0 << 2)  | /* set_rd_sync, set to 0 */	       \
			(0x0))	      /* set_mw, memory width, 16bits width*/
				      /* 0x00002000 */
#define NOR_DIRECT_CMD ((0x0 << 23) | /* Chip 0 from interface 0 */	       \
			(0x2 << 21) | /* UpdateRegs operation */	       \
			(0x0 << 20) | /* No ModeReg write */		       \
			(0x0))	      /* Addr, not used in UpdateRegs */

/* Register values for using SRAM interface of SMC Controller */
#define SRAM_SET_CYCLES (0x00125155)
#define SRAM_SET_OPMODE (0x00003000)
#define SRAM_DIRECT_CMD (0x00C00000)	/* Chip 1 */

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

/****************************************************************************
*
* Configure the SMC interface for SRAM.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void XSmc_SramInit (void)
{
	Xil_Out32(XPAR_XPARPORTPS_CTRL_BASEADDR + XSMCPSS_MC_SET_CYCLES,
		  SRAM_SET_CYCLES);
	Xil_Out32(XPAR_XPARPORTPS_CTRL_BASEADDR + XSMCPSS_MC_SET_OPMODE,
		  SRAM_SET_OPMODE);
	Xil_Out32(XPAR_XPARPORTPS_CTRL_BASEADDR + XSMCPSS_MC_DIRECT_CMD,
		  SRAM_DIRECT_CMD);
}

/****************************************************************************
*
* Configure the SMC interface for NOR flash.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void XSmc_NorInit(void)
{
	Xil_Out32(XPAR_XPARPORTPS_CTRL_BASEADDR + XSMCPSS_MC_SET_CYCLES,
		  NOR_SET_CYCLES);
	Xil_Out32(XPAR_XPARPORTPS_CTRL_BASEADDR + XSMCPSS_MC_SET_OPMODE,
		  NOR_SET_OPMODE);
	Xil_Out32(XPAR_XPARPORTPS_CTRL_BASEADDR + XSMCPSS_MC_DIRECT_CMD,
		  NOR_DIRECT_CMD);
}
