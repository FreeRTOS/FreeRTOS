/******************************************************************************
*
* Copyright (C) 2011 - 2014 Xilinx, Inc.  All rights reserved.
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
#define XPS_L2CC_ID_OFFSET		0x0000
#define XPS_L2CC_TYPE_OFFSET		0x0004
#define XPS_L2CC_CNTRL_OFFSET		0x0100
#define XPS_L2CC_AUX_CNTRL_OFFSET	0x0104
#define XPS_L2CC_TAG_RAM_CNTRL_OFFSET	0x0108
#define XPS_L2CC_DATA_RAM_CNTRL_OFFSET	0x010C

#define XPS_L2CC_EVNT_CNTRL_OFFSET	0x0200
#define XPS_L2CC_EVNT_CNT1_CTRL_OFFSET	0x0204
#define XPS_L2CC_EVNT_CNT0_CTRL_OFFSET	0x0208
#define XPS_L2CC_EVNT_CNT1_VAL_OFFSET	0x020C
#define XPS_L2CC_EVNT_CNT0_VAL_OFFSET	0x0210

#define XPS_L2CC_IER_OFFSET		0x0214		/* Interrupt Mask */
#define XPS_L2CC_IPR_OFFSET		0x0218		/* Masked interrupt status */
#define XPS_L2CC_ISR_OFFSET		0x021C		/* Raw Interrupt Status */
#define XPS_L2CC_IAR_OFFSET		0x0220		/* Interrupt Clear */

#define XPS_L2CC_CACHE_SYNC_OFFSET		0x0730		/* Cache Sync */
#define XPS_L2CC_DUMMY_CACHE_SYNC_OFFSET	0x0740		/* Dummy Register for Cache Sync */
#define XPS_L2CC_CACHE_INVLD_PA_OFFSET		0x0770		/* Cache Invalid by PA */
#define XPS_L2CC_CACHE_INVLD_WAY_OFFSET		0x077C		/* Cache Invalid by Way */
#define XPS_L2CC_CACHE_CLEAN_PA_OFFSET		0x07B0		/* Cache Clean by PA */
#define XPS_L2CC_CACHE_CLEAN_INDX_OFFSET	0x07B8		/* Cache Clean by Index */
#define XPS_L2CC_CACHE_CLEAN_WAY_OFFSET		0x07BC		/* Cache Clean by Way */
#define XPS_L2CC_CACHE_INV_CLN_PA_OFFSET	0x07F0		/* Cache Invalidate and Clean by PA */
#define XPS_L2CC_CACHE_INV_CLN_INDX_OFFSET	0x07F8		/* Cache Invalidate and Clean by Index */
#define XPS_L2CC_CACHE_INV_CLN_WAY_OFFSET	0x07FC		/* Cache Invalidate and Clean by Way */

#define XPS_L2CC_CACHE_DLCKDWN_0_WAY_OFFSET	0x0900		/* Cache Data Lockdown 0 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_0_WAY_OFFSET	0x0904		/* Cache Instruction Lockdown 0 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_1_WAY_OFFSET	0x0908		/* Cache Data Lockdown 1 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_1_WAY_OFFSET	0x090C		/* Cache Instruction Lockdown 1 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_2_WAY_OFFSET	0x0910		/* Cache Data Lockdown 2 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_2_WAY_OFFSET	0x0914		/* Cache Instruction Lockdown 2 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_3_WAY_OFFSET	0x0918		/* Cache Data Lockdown 3 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_3_WAY_OFFSET	0x091C		/* Cache Instruction Lockdown 3 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_4_WAY_OFFSET	0x0920		/* Cache Data Lockdown 4 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_4_WAY_OFFSET	0x0924		/* Cache Instruction Lockdown 4 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_5_WAY_OFFSET	0x0928		/* Cache Data Lockdown 5 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_5_WAY_OFFSET	0x092C		/* Cache Instruction Lockdown 5 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_6_WAY_OFFSET	0x0930		/* Cache Data Lockdown 6 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_6_WAY_OFFSET	0x0934		/* Cache Instruction Lockdown 6 by Way */
#define XPS_L2CC_CACHE_DLCKDWN_7_WAY_OFFSET	0x0938		/* Cache Data Lockdown 7 by Way */
#define XPS_L2CC_CACHE_ILCKDWN_7_WAY_OFFSET	0x093C		/* Cache Instruction Lockdown 7 by Way */

#define XPS_L2CC_CACHE_LCKDWN_LINE_ENABLE_OFFSET 0x0950		/* Cache Lockdown Line Enable */
#define XPS_L2CC_CACHE_UUNLOCK_ALL_WAY_OFFSET	0x0954		/* Cache Unlock All Lines by Way */

#define XPS_L2CC_ADDR_FILTER_START_OFFSET	0x0C00		/* Start of address filtering */
#define XPS_L2CC_ADDR_FILTER_END_OFFSET		0x0C04		/* Start of address filtering */

#define XPS_L2CC_DEBUG_CTRL_OFFSET		0x0F40		/* Debug Control Register */

/* XPS_L2CC_CNTRL_OFFSET bit masks */
#define XPS_L2CC_ENABLE_MASK		0x00000001	/* enables the L2CC */

/* XPS_L2CC_AUX_CNTRL_OFFSET bit masks */
#define XPS_L2CC_AUX_EBRESPE_MASK	0x40000000	/* Early BRESP Enable */
#define XPS_L2CC_AUX_IPFE_MASK		0x20000000	/* Instruction Prefetch Enable */
#define XPS_L2CC_AUX_DPFE_MASK		0x10000000	/* Data Prefetch Enable */
#define XPS_L2CC_AUX_NSIC_MASK		0x08000000	/* Non-secure interrupt access control */
#define XPS_L2CC_AUX_NSLE_MASK		0x04000000	/* Non-secure lockdown enable */
#define XPS_L2CC_AUX_CRP_MASK		0x02000000	/* Cache replacement policy */
#define XPS_L2CC_AUX_FWE_MASK		0x01800000	/* Force write allocate */
#define XPS_L2CC_AUX_SAOE_MASK		0x00400000	/* Shared attribute override enable */
#define XPS_L2CC_AUX_PE_MASK		0x00200000	/* Parity enable */
#define XPS_L2CC_AUX_EMBE_MASK		0x00100000	/* Event monitor bus enable */
#define XPS_L2CC_AUX_WAY_SIZE_MASK	0x000E0000	/* Way-size */
#define XPS_L2CC_AUX_ASSOC_MASK		0x00010000	/* Associativity */
#define XPS_L2CC_AUX_SAIE_MASK		0x00002000	/* Shared attribute invalidate enable */
#define XPS_L2CC_AUX_EXCL_CACHE_MASK	0x00001000	/* Exclusive cache configuration */
#define XPS_L2CC_AUX_SBDLE_MASK		0x00000800	/* Store buffer device limitation Enable */
#define XPS_L2CC_AUX_HPSODRE_MASK	0x00000400	/* High Priority for SO and Dev Reads Enable */
#define XPS_L2CC_AUX_FLZE_MASK		0x00000001	/* Full line of zero enable */

#define XPS_L2CC_AUX_REG_DEFAULT_MASK	0x72360000	/* Enable all prefetching, */
                                                    /* Cache replacement policy, Parity enable, */
                                                    /* Event monitor bus enable and Way Size (64 KB) */
#define XPS_L2CC_AUX_REG_ZERO_MASK	0xFFF1FFFF	/* */

#define XPS_L2CC_TAG_RAM_DEFAULT_MASK	0x00000111	/* latency for TAG RAM */
#define XPS_L2CC_DATA_RAM_DEFAULT_MASK	0x00000121	/* latency for DATA RAM */

/* Interrupt bit masks */
#define XPS_L2CC_IXR_DECERR_MASK	0x00000100	/* DECERR from L3 */
#define XPS_L2CC_IXR_SLVERR_MASK	0x00000080	/* SLVERR from L3 */
#define XPS_L2CC_IXR_ERRRD_MASK		0x00000040	/* Error on L2 data RAM (Read) */
#define XPS_L2CC_IXR_ERRRT_MASK		0x00000020	/* Error on L2 tag RAM (Read) */
#define XPS_L2CC_IXR_ERRWD_MASK		0x00000010	/* Error on L2 data RAM (Write) */
#define XPS_L2CC_IXR_ERRWT_MASK		0x00000008	/* Error on L2 tag RAM (Write) */
#define XPS_L2CC_IXR_PARRD_MASK		0x00000004	/* Parity Error on L2 data RAM (Read) */
#define XPS_L2CC_IXR_PARRT_MASK		0x00000002	/* Parity Error on L2 tag RAM (Read) */
#define XPS_L2CC_IXR_ECNTR_MASK		0x00000001	/* Event Counter1/0 Overflow Increment */

/* Address filtering mask and enable bit */
#define XPS_L2CC_ADDR_FILTER_VALID_MASK	0xFFF00000	/* Address filtering valid bits*/
#define XPS_L2CC_ADDR_FILTER_ENABLE_MASK 0x00000001	/* Address filtering enable bit*/

/* Debug control bits */
#define XPS_L2CC_DEBUG_SPIDEN_MASK	0x00000004	/* Debug SPIDEN bit */
#define XPS_L2CC_DEBUG_DWB_MASK		0x00000002	/* Debug DWB bit, forces write through */
#define XPS_L2CC_DEBUG_DCL_MASK		0x00000002	/* Debug DCL bit, disables cache line fill */

#ifdef __cplusplus
}
#endif

#endif /* protection macro */
