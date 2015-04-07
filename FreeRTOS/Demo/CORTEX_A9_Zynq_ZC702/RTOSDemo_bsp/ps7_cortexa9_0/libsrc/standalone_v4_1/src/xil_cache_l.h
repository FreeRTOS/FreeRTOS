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
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xil_cache_l.h
*
* Contains L1 and L2 specific functions for the ARM cache functionality
* used by xcache.c. This functionality is being made available here for
* more sophisticated users.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a ecm  01/24/10 First release
* </pre>
*
******************************************************************************/
#ifndef XIL_CACHE_MACH_H
#define XIL_CACHE_MACH_H

#ifdef __cplusplus
extern "C" {
#endif

/************************** Function Prototypes ******************************/

void Xil_DCacheInvalidateLine(unsigned int adr);
void Xil_DCacheFlushLine(unsigned int adr);
void Xil_DCacheStoreLine(unsigned int adr);
void Xil_ICacheInvalidateLine(unsigned int adr);

void Xil_L1DCacheEnable(void);
void Xil_L1DCacheDisable(void);
void Xil_L1DCacheInvalidate(void);
void Xil_L1DCacheInvalidateLine(unsigned int adr);
void Xil_L1DCacheInvalidateRange(unsigned int adr, unsigned len);
void Xil_L1DCacheFlush(void);
void Xil_L1DCacheFlushLine(unsigned int adr);
void Xil_L1DCacheFlushRange(unsigned int adr, unsigned len);
void Xil_L1DCacheStoreLine(unsigned int adr);

void Xil_L1ICacheEnable(void);
void Xil_L1ICacheDisable(void);
void Xil_L1ICacheInvalidate(void);
void Xil_L1ICacheInvalidateLine(unsigned int adr);
void Xil_L1ICacheInvalidateRange(unsigned int adr, unsigned len);

void Xil_L2CacheEnable(void);
void Xil_L2CacheDisable(void);
void Xil_L2CacheInvalidate(void);
void Xil_L2CacheInvalidateLine(unsigned int adr);
void Xil_L2CacheInvalidateRange(unsigned int adr, unsigned len);
void Xil_L2CacheFlush(void);
void Xil_L2CacheFlushLine(unsigned int adr);
void Xil_L2CacheFlushRange(unsigned int adr, unsigned len);
void Xil_L2CacheStoreLine(unsigned int adr);

#ifdef __cplusplus
}
#endif

#endif
