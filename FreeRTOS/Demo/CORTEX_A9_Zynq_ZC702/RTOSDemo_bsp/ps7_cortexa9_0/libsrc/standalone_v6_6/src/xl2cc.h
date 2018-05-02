/******************************************************************************
*
* Copyright (C) 2011 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xl2cc.h
*
* This file contains the address definitions for the PL310 Level-2 Cache
* Controller.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 1.00a sdm  02/01/10 Initial version
* 3.10a srt 04/18/13 Implemented ARM Erratas. Please refer to file
*		      'xil_errata.h' for errata description
* </pre>
*
* @note
*
* None.
*
******************************************************************************/

#ifndef _XL2CC_H_
#define _XL2CC_H_

#ifdef __cplusplus
extern "C" {
#endif

/************************** Constant Definitions *****************************/
/* L2CC Register Offsets */
#define XPS_L2CC_ID_OFFSET		0x0000U
#define XPS_L2CC_TYPE_OFFSET		0x0004U
#define XPS_L2CC_CNTRL_OFFSET		0x0100U
#define XPS_L2CC_AUX_CNTRL_OFFSET	0x0104U
#define XPS_L2CC_TAG_RAM_CNTRL_OFFSET	0x0108U
#define XPS_L2CC_DATA_RAM_CNTRL_OFFSET	0x010CU

#define XPS_L2CC_EVNT_CNTRL_OFFSET	0x0200U
#define XPS_L2CC_EVNT_CNT1_CTRL_OFFSET	0x0204U
#define XPS_L2CC_EVNT_CNT0_CTRL_OFFSET	0x0208U
#define XPS_L2CC_EVNT_CNT1_VAL_OFFSET	0x020CU
#define XPS_L2CC_EVNT_CNT0_VAL_OFFSET	0x0210U

#define XPS_L2CC_IER_OFFSET		0x0214U		/* Interrupt Mask */
#define XPS_L2CC_IPR_OFFSET		0x0218U		/* Masked interrupt status */
#define XPS_L2CC_ISR_OFFSET		0x021CU		/* Raw Interrupt Status */
#define XPS_L2CC_IAR_OFFSET		0x0220U		/* Interrupt Clear */

#define XPS_L2CC_CACHE_SYNC_OFFSET		0x0730U		/* Cache Sync */
#define XPS_L2CC_DUMMY_CACHE_SYNC_OFFSET	0x0740U		/* Dummy Register for Cache Sync */
#define XPS_L2CC_CACHE_INVLD_PA_OFFSET		0x0770U		/* Cache Invalid by PA */
#define XPS_L2CC_CACHE_INVLD_WAY_OFFSET		0x077CU		/* Cache Invalid by Way */
#define XPS_L2CC_CACHE_CLEAN_PA_OFFSET		0x07B0U		/* Cache Clean by PA */
#define XPS_L2CC_CACHE_CLEAN_INDX_OFFSET	0x07B8U		/* Cache Clean by Index */
#define XPS_L2CC_CACHE_CLEAN_WAY_OFFSET		0x07BCU		/* Cache Clean by Way */
#define XPS_L2CC_CACHE_INV_CLN_PA_OFFSET	0x07F0U		/* Cache Invalidate and Clean by PA */
#define XPS_L2CC_CACHE_INV_CLN_INDX_OFFSET	0x07F8U		/* Cache Invalidate and Clean by Index */
#define XPS_L2CC_CACHE_INV_CLN_WAY_OFFSET	0x07FCU		/* Cache Invalidate and Clean by Way */

#define XPS_L2CC_CACHE_DLCKDWN_0_WAY_OFFSET	0x0900U		/* Cache Data Lockdown 0 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_0_WAY_OFFSET	0x0904U		/* Cache Instruction Lockdown 0 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_1_WAY_OFFSET	0x0908U		/* Cache Data Lockdown 1 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_1_WAY_OFFSET	0x090CU		/* Cache Instruction Lockdown 1 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_2_WAY_OFFSET	0x0910U		/* Cache Data Lockdown 2 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_2_WAY_OFFSET	0x0914U		/* Cache Instruction Lockdown 2 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_3_WAY_OFFSET	0x0918U		/* Cache Data Lockdown 3 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_3_WAY_OFFSET	0x091CU		/* Cache Instruction Lockdown 3 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_4_WAY_OFFSET	0x0920U		/* Cache Data Lockdown 4 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_4_WAY_OFFSET	0x0924U		/* Cache Instruction Lockdown 4 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_5_WAY_OFFSET	0x0928U		/* Cache Data Lockdown 5 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_5_WAY_OFFSET	0x092CU		/* Cache Instruction Lockdown 5 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_6_WAY_OFFSET	0x0930U		/* Cache Data Lockdown 6 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_6_WAY_OFFSET	0x0934U		/* Cache Instruction Lockdown 6 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_7_WAY_OFFSET	0x0938U		/* Cache Data Lockdown 7 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_7_WAY_OFFSET	0x093CU		/* Cache Instruction Lockdown 7 by Way */

#define XPS_L2CC_CACHE_LCKDWN_LINE_ENABLE_OFFSET 0x0950U		/* Cache Lockdown Line Enable */
#define XPS_L2CC_CACHE_UUNLOCK_ALL_WAY_OFFSET	0x0954U		/* Cache Unlock All Lines by Way */

#define XPS_L2CC_ADDR_FILTER_START_OFFSET	0x0C00U		/* Start of address filtering */
#define XPS_L2CC_ADDR_FILTER_END_OFFSET		0x0C04U		/* Start of address filtering */

#define XPS_L2CC_DEBUG_CTRL_OFFSET		0x0F40U		/* Debug Control Register */

/* XPS_L2CC_CNTRL_OFFSET bit masks */
#define XPS_L2CC_ENABLE_MASK		0x00000001U	/* enables the L2CC */

/* XPS_L2CC_AUX_CNTRL_OFFSET bit masks */
#define XPS_L2CC_AUX_EBRESPE_MASK	0x40000000U	/* Early BRESP Enable */
#define XPS_L2CC_AUX_IPFE_MASK		0x20000000U	/* Instruction Prefetch Enable */
#define XPS_L2CC_AUX_DPFE_MASK		0x10000000U	/* Data Prefetch Enable */
#define XPS_L2CC_AUX_NSIC_MASK		0x08000000U	/* Non-secure interrupt access control */
#define XPS_L2CC_AUX_NSLE_MASK		0x04000000U	/* Non-secure lockdown enable */
#define XPS_L2CC_AUX_CRP_MASK		0x02000000U	/* Cache replacement policy */
#define XPS_L2CC_AUX_FWE_MASK		0x01800000U	/* Force write allocate */
#define XPS_L2CC_AUX_SAOE_MASK		0x00400000U	/* Shared attribute override enable */
#define XPS_L2CC_AUX_PE_MASK		0x00200000U	/* Parity enable */
#define XPS_L2CC_AUX_EMBE_MASK		0x00100000U	/* Event monitor bus enable */
#define XPS_L2CC_AUX_WAY_SIZE_MASK	0x000E0000U	/* Way-size */
#define XPS_L2CC_AUX_ASSOC_MASK		0x00010000U	/* Associativity */
#define XPS_L2CC_AUX_SAIE_MASK		0x00002000U	/* Shared attribute invalidate enable */
#define XPS_L2CC_AUX_EXCL_CACHE_MASK	0x00001000U	/* Exclusive cache configuration */
#define XPS_L2CC_AUX_SBDLE_MASK		0x00000800U	/* Store buffer device limitation Enable */
#define XPS_L2CC_AUX_HPSODRE_MASK	0x00000400U	/* High Priority for SO and Dev Reads Enable */
#define XPS_L2CC_AUX_FLZE_MASK		0x00000001U	/* Full line of zero enable */

#define XPS_L2CC_AUX_REG_DEFAULT_MASK	0x72360000U	/* Enable all prefetching, */
                                                    /* Cache replacement policy, Parity enable, */
                                                    /* Event monitor bus enable and Way Size (64 KB) */
#define XPS_L2CC_AUX_REG_ZERO_MASK	0xFFF1FFFFU	/* */

#define XPS_L2CC_TAG_RAM_DEFAULT_MASK	0x00000111U	/* latency for TAG RAM */
#define XPS_L2CC_DATA_RAM_DEFAULT_MASK	0x00000121U	/* latency for DATA RAM */

/* Interrupt bit masks */
#define XPS_L2CC_IXR_DECERR_MASK	0x00000100U	/* DECERR from L3 */
#define XPS_L2CC_IXR_SLVERR_MASK	0x00000080U	/* SLVERR from L3 */
#define XPS_L2CC_IXR_ERRRD_MASK		0x00000040U	/* Error on L2 data RAM (Read) */
#define XPS_L2CC_IXR_ERRRT_MASK		0x00000020U	/* Error on L2 tag RAM (Read) */
#define XPS_L2CC_IXR_ERRWD_MASK		0x00000010U	/* Error on L2 data RAM (Write) */
#define XPS_L2CC_IXR_ERRWT_MASK		0x00000008U	/* Error on L2 tag RAM (Write) */
#define XPS_L2CC_IXR_PARRD_MASK		0x00000004U	/* Parity Error on L2 data RAM (Read) */
#define XPS_L2CC_IXR_PARRT_MASK		0x00000002U	/* Parity Error on L2 tag RAM (Read) */
#define XPS_L2CC_IXR_ECNTR_MASK		0x00000001U	/* Event Counter1/0 Overflow Increment */

/* Address filtering mask and enable bit */
#define XPS_L2CC_ADDR_FILTER_VALID_MASK	0xFFF00000U	/* Address filtering valid bits*/
#define XPS_L2CC_ADDR_FILTER_ENABLE_MASK 0x00000001U	/* Address filtering enable bit*/

/* Debug control bits */
#define XPS_L2CC_DEBUG_SPIDEN_MASK	0x00000004U	/* Debug SPIDEN bit */
#define XPS_L2CC_DEBUG_DWB_MASK		0x00000002U	/* Debug DWB bit, forces write through */
#define XPS_L2CC_DEBUG_DCL_MASK		0x00000002U	/* Debug DCL bit, disables cache line fill */

#ifdef __cplusplus
}
#endif

#endif /* protection macro */
