/******************************************************************************
*
* (c) Copyright 2010-13  Xilinx, Inc. All rights reserved.
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
