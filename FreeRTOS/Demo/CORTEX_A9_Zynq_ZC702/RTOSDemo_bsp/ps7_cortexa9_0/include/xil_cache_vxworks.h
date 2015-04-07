/******************************************************************************
*
* (c) Copyright 2009 Xilinx, Inc. All rights reserved.
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
* @file xil_cache_vxworks.h
*
* Contains the cache related functions for VxWorks that is wrapped by
* xil_cache. 
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date	 Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a hbm  12/11/09 Initial release
*
* </pre>
*
* @note
*
******************************************************************************/

#ifndef XIL_CACHE_VXWORKS_H
#define XIL_CACHE_VXWORKS_H

#ifdef __cplusplus
extern "C" {
#endif

#include "vxWorks.h"
#include "vxLib.h"
#include "sysLibExtra.h"
#include "cacheLib.h"

#if (CPU_FAMILY==PPC)

#define Xil_DCacheEnable()		cacheEnable(DATA_CACHE)

#define Xil_DCacheDisable()		cacheDisable(DATA_CACHE)

#define Xil_DCacheInvalidateRange(Addr, Len) \
		cacheInvalidate(DATA_CACHE, (void *)(Addr), (Len))

#define Xil_DCacheFlushRange(Addr, Len) \
		cacheFlush(DATA_CACHE, (void *)(Addr), (Len))

#define Xil_ICacheEnable()		cacheEnable(INSTRUCTION_CACHE)

#define Xil_ICacheDisable()		cacheDisable(INSTRUCTION_CACHE)

#define Xil_ICacheInvalidateRange(Addr, Len) \
		cacheInvalidate(INSTRUCTION_CACHE, (void *)(Addr), (Len))


#else
#error "Unknown processor / architecture. Must be PPC for VxWorks."
#endif

#ifdef __cplusplus
}
#endif

#endif

