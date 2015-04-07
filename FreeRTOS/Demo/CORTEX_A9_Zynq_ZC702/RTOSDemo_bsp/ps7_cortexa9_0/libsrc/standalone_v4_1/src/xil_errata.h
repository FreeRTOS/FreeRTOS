/*******************************************************************************
*
* (c) Copyright 2013 Xilinx, Inc. All rights reserved.
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
*******************************************************************************/
/*****************************************************************************/
/**
*
* @file xil_errata.h
*
* This header file contains Cortex A9 and PL310 Errata definitions.
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a srt  04/18/13 First release
* </pre>
*
******************************************************************************/
#ifndef XIL_ERRATA_H
#define XIL_ERRATA_H

#define ENABLE_ARM_ERRATA 1

#ifdef ENABLE_ARM_ERRATA
/* Cortex A9 ARM Errata */

/*
 *  Errata No: 	 742230
 *  Description: DMB operation may be faulty
 */
#define CONFIG_ARM_ERRATA_742230 1

/*
 *  Errata No: 	 743622
 *  Description: Faulty hazard checking in the Store Buffer may lead
 *	         to data corruption.
 */
#define CONFIG_ARM_ERRATA_743622 1

/*
 *  Errata No: 	 775420
 *  Description: A data cache maintenance operation which aborts, 
 *		 might lead to deadlock
 */
#define CONFIG_ARM_ERRATA_775420 1

/*
 *  Errata No: 	 794073
 *  Description: Speculative instruction fetches with MMU disabled 
 *               might not comply with architectural requirements
 */
#define CONFIG_ARM_ERRATA_794073 1


/* PL310 L2 Cache Errata */

/*
 *  Errata No: 	 588369
 *  Description: Clean & Invalidate maintenance operations do not 
 *	   	 invalidate clean lines
 */
#define CONFIG_PL310_ERRATA_588369 1

/*
 *  Errata No: 	 727915
 *  Description: Background Clean and Invalidate by Way operation
 *		 can cause data corruption
 */
#define CONFIG_PL310_ERRATA_727915 1

/*
 *  Errata No: 	 753970
 *  Description: Cache sync operation may be faulty
 */
#define CONFIG_PL310_ERRATA_753970 1

#endif  /* ENABLE_ARM_ERRATA */

#endif  /* XIL_ERRATA_H */
