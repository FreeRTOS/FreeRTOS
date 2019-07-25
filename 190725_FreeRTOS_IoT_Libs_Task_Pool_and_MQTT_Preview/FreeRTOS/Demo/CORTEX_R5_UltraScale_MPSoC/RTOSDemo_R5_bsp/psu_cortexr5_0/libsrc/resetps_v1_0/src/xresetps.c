/******************************************************************************
*
* Copyright (C) 2017 Xilinx, Inc.  All rights reserved.
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
/****************************************************************************/
/**
*
* @file xresetps.c
* @addtogroup xresetps_v1_0
* @{
*
* Contains the implementation of interface functions of the XResetPs driver.
* See xresetps.h for a description of the driver.
*
* <pre>
* MODIFICATION HISTORY:
* Ver   Who    Date     Changes
* ----- ------ -------- ---------------------------------------------
* 1.00  cjp    09/05/17 First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/
#include "xresetps.h"
#include "xresetps_hw.h"
#include "xil_types.h"

/************************** Constant Definitions *****************************/
#define XRESETPS_RSTID_BASE             (1000)
#define XRESETPS_REGADDR_INVALID        (0xFFFFFFFFU)
#define XRESETPS_BM_INVALID             (0xFFFFFFFFU)

/**************************** Type Definitions *******************************/
typedef struct {
	const u32                 SlcrregAddr;
	const u32                 SlcrregBitmask;
	const u32                 PwrStateBitmask;
	const XResetPs_PulseTypes PulseType;
	const u8                  SupportedActions;
} XResetPs_Lookup;

/************************** Variable Definitions *****************************/
#if !EL1_NONSECURE
const static XResetPs_Lookup ResetMap[] = {
	/*
	 *	{Control Register, Control Bitmask,
	 *	 Power State Bitask, Pulse Type,
	 *	 Supported Actions},
	 */
	{XRESETPS_CRF_APB_RST_FPD_TOP,  PCIE_CFG_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  PCIE_BRIDGE_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  PCIE_CTRL_RESET_MASK,
	PCIE_CTRL_PSCHK_MASK,           XRESETPS_PT_DLY_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  DP_RESET_MASK,
	DP_PSCHK_MASK,                  XRESETPS_PT_DLY_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  SWDT_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  AFI_FM5_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  AFI_FM4_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  AFI_FM3_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  AFI_FM2_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  AFI_FM1_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  AFI_FM0_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  GDMA_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  GPU_PP1_RESET_MASK,
	GPU_PP1_PSCHK_MASK,             XRESETPS_PT_DLY_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  GPU_PP0_RESET_MASK,
	GPU_PP0_PSCHK_MASK,             XRESETPS_PT_DLY_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  GPU_RESET_MASK,
	GPU_PSCHK_MASK,                 XRESETPS_PT_DLY_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  GT_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_TOP,  SATA_RESET_MASK,
	SATA_PSCHK_MASK,                XRESETPS_PT_DLY_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_APU,  ACPU3_PWRON_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_APU,  ACPU2_PWRON_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_APU,  ACPU1_PWRON_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_APU,  ACPU0_PWRON_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_APU,  APU_L2_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_APU,  ACPU3_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_APU,  ACPU2_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_APU,  ACPU1_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_FPD_APU,  ACPU0_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_DDR_SS,   DDR_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_RST_DDR_SS,   DDR_APM_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RESET_CTRL,   SOFT_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU0, GEM0_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU0, GEM1_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU0, GEM2_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU0, GEM3_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, QSPI_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, UART0_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, UART1_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, SPI0_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, SPI1_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, SDIO0_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, SDIO1_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, CAN0_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, CAN1_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, I2C0_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, I2C1_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, TTC0_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, TTC1_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, TTC2_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, TTC3_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, SWDT_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, NAND_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, ADMA_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, GPIO_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, IOU_CC_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_IOU2, TIMESTAMP_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  RPU_R50_RESET_MASK,
	R50_PSCHK_MASK,                 XRESETPS_PT_DLY_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  RPU_R51_RESET_MASK,
	R51_PSCHK_MASK,                 XRESETPS_PT_DLY_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  RPU_AMBA_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  OCM_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  RPU_PGE_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  USB0_CORERESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  USB1_CORERESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  USB0_HIBERRESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  USB1_HIBERRESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  USB0_APB_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  USB1_APB_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  IPI_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  APM_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  RTC_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  SYSMON_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  AFI_FM6_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  LPD_SWDT_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_TOP,  FPD_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_DBG,  RPU_DBG1_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_DBG,  RPU_DBG0_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_DBG,  DBG_LPD_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RST_LPD_DBG,  DBG_FPD_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_APLL_CTRL,    APLL_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_DPLL_CTRL,    DPLL_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRF_APB_VPLL_CTRL,    VPLL_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_IOPLL_CTRL,   IOPLL_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_CRL_APB_RPLL_CTRL,    RPLL_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_SUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL0_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL1_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL2_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL3_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL4_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL5_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL6_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL7_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL8_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL9_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL10_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL11_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL12_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL13_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL14_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL15_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL16_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL17_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL18_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL19_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL20_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL21_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL22_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL23_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL24_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL25_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL26_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL27_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL28_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL29_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL30_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_IOM_GPO3_CTRL,    GPO3_PL31_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_GLB_RST_CTRL,     RPU_LS_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_NOSUP)},
	{XRESETPS_PMU_GLB_RST_CTRL,     PS_ONLY_RESET_MASK,
	XRESETPS_BM_INVALID,            XRESETPS_PT_NO_DLY_NO_PSCHK,
	XRESETPS_SUPPORTED_ACT(XRESETPS_SUP, XRESETPS_SUP, XRESETPS_NOSUP)},
	/* All fields invalidated for PL since not supported */
	{XRESETPS_REGADDR_INVALID,      XRESETPS_BM_INVALID,
	XRESETPS_BM_INVALID,            XRESETPS_PT_INVALID,
	XRESETPS_SUPPORTED_ACT(XRESETPS_NOSUP, XRESETPS_NOSUP, XRESETPS_NOSUP)},
};
#endif

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* Initialize a specific reset controller instance/driver. This function
* must be called before other functions of the driver are called.
*
* @param	InstancePtr is a pointer to the XResetPs instance.
* @param	ConfigPtr is the config structure.
* @param	EffectiveAddress is the base address for the device. It could be
*		a virtual address if address translation is supported in the
*		system, otherwise it is the physical address.
*
* @return
*		- XST_SUCCESS if initialization was successful.
*
* @note		None.
*
******************************************************************************/
XStatus XResetPs_CfgInitialize(XResetPs *InstancePtr,
			       XResetPs_Config *ConfigPtr, u32 EffectiveAddress)
{
	/* Arguments validation */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/* Copying instance */
	InstancePtr->Config.DeviceId = ConfigPtr->DeviceId;
	InstancePtr->Config.BaseAddress = EffectiveAddress;

	return XST_SUCCESS;
}

#if !EL1_NONSECURE
/****************************************************************************/
/**
*
* Pulse Reset RPU.
*
* @param	None.
*
* @return
*		- XST_SUCCESS if successful else error code.
*
* @note		The pulse reset sequence is referred from ug1085(v1.3)
*		chapter-38. Few changes to the sequence are adpoted from PMUFW.
*
******************************************************************************/
static XStatus XResetPs_PulseResetRpuLs(void)
{
	u32 TimeOut;
	u32 RegValue;

	/* Block Cortex-R5 master interface */
	RegValue = XResetPs_ReadReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL);
	RegValue &= (~RPU_MASTER_ISO_MASK);
	RegValue |= RPU_MASTER_ISO_MASK;
	XResetPs_WriteReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL, RegValue);

	/* Wait for acknowledgment from AIB until timeout */
	TimeOut = XRESETPS_AIB_PSPL_DELAY;
	RegValue = XResetPs_ReadReg(XRESETPS_LPD_SCR_AXIISO_ACK_CTRL);
	while ((TimeOut > 0U) &&
		((RegValue & RPU_MASTER_ISO_MASK) != RPU_MASTER_ISO_MASK)) {
		RegValue = XResetPs_ReadReg(XRESETPS_LPD_SCR_AXIISO_ACK_CTRL);
		TimeOut--;
	}

	if (TimeOut == 0U) {
		/*
		 * @NOTE:
		 * AIB ack Timed Out.
		 * As per ug1085(v1.3), nothing is to be done on timeout, hence
		 * continuing with reset sequence.
		 */
	}

	/* Block Cortex-R5 slave interface */
	RegValue = XResetPs_ReadReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL);
	RegValue &= (~RPU_SLAVE_ISO_MASK);
	RegValue |= RPU_SLAVE_ISO_MASK;
	XResetPs_WriteReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL, RegValue);

	/* Wait for acknowledgment from AIB until timeout */
	TimeOut = XRESETPS_AIB_PSPL_DELAY;
	RegValue = XResetPs_ReadReg(XRESETPS_LPD_SCR_AXIISO_ACK_CTRL);
	while ((TimeOut > 0U) &&
		((RegValue & RPU_SLAVE_ISO_MASK) != RPU_SLAVE_ISO_MASK)) {
		RegValue = XResetPs_ReadReg(XRESETPS_LPD_SCR_AXIISO_ACK_CTRL);
		TimeOut--;
	}

	if (TimeOut == 0U) {
		/*
		 * @NOTE:
		 * AIB ack Timed Out.
		 * As per ug1085(v1.3), nothing is to be done on timeout, hence
		 * continuing with reset sequence.
		 */
	}

	/* Unblock Cortex-R5 master interface */
	RegValue = XResetPs_ReadReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL);
	RegValue &= (~RPU_MASTER_ISO_MASK);
	XResetPs_WriteReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL, RegValue);

	/* Initiate Cortex-R5 LockStep reset */
	RegValue = XResetPs_ReadReg(XRESETPS_PMU_GLB_RST_CTRL);
	RegValue |= RPU_LS_RESET_MASK;
	XResetPs_WriteReg(XRESETPS_PMU_GLB_RST_CTRL, RegValue);

	/* Wait */
	TimeOut = XRESETPS_RST_PROP_DELAY;
	while (TimeOut > 0U) {
		TimeOut--;
	}

	/* Release Cortex-R5 from Reset */
	RegValue = XResetPs_ReadReg(XRESETPS_PMU_GLB_RST_CTRL);
	RegValue &= (~RPU_LS_RESET_MASK);
	XResetPs_WriteReg(XRESETPS_PMU_GLB_RST_CTRL, RegValue);

	/* Wait */
	TimeOut = XRESETPS_RST_PROP_DELAY;
	while (TimeOut > 0U) {
		TimeOut--;
	}

	/* Unblock Cortex-R5 slave interface */
	RegValue = XResetPs_ReadReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL);
	RegValue &= (~RPU_SLAVE_ISO_MASK);
	XResetPs_WriteReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL, RegValue);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* Pulse Reset PS only.
*
* @param	None.
*
* @return
*		- XST_SUCCESS if successful else error code.
*
* @note		The pulse reset sequence is referred from ug1085(v1.3)
*		chapter-38. Few changes to the sequence are adpoted from PMUFW.
*
******************************************************************************/
static XStatus XResetPs_PulseResetPsOnly(void)
{

	u32 RegValue;
	u32 TimeOut;
	u8  ReconfirmAckCnt;

	/* TODO: Set PMU Error to indicate to PL */

	/* Block FPD to PL and LPD to PL interfaces with AIB (in PS) */
	XResetPs_WriteReg(XRESETPS_PMU_GLB_AIB_CTRL, AIB_ISO_CTRL_MASK);

	/*
	 * @NOTE: Updated referring PMUFW
	 * There is a possibility of glitch in AIB ack signal to PMU, hence ack
	 * needs reconfirmation.
	 */
	/* Wait for AIB ack or Timeout */
	ReconfirmAckCnt = XRESETPS_AIB_PSPL_RECONFIRM_CNT;
	do {
		TimeOut = XRESETPS_AIB_PSPL_DELAY;
		RegValue = XResetPs_ReadReg(XRESETPS_PMU_GLB_AIB_STATUS);
		while ((TimeOut > 0U) &&
		    ((RegValue & AIB_ISO_STATUS_MASK) != AIB_ISO_STATUS_MASK)) {
			RegValue =
				  XResetPs_ReadReg(XRESETPS_PMU_GLB_AIB_STATUS);
			TimeOut--;
		}

		if (TimeOut == 0U) {
			/*
			 * @NOTE:
			 * AIB ack Timed Out.
			 * As per ug1085(v1.3), nothing is to be done on
			 * timeout, hence continuing with reset sequence.
			 */
			ReconfirmAckCnt = 0U;
		} else {
			ReconfirmAckCnt--;
		}
	}
	while (ReconfirmAckCnt > 0U);

	/*
	 * @NOTE: Updated referring PMUFW.
	 * Check if we are running Silicon version 1.0. If so,
	 * bypass the RPLL before initiating the reset. This is
	 * due to a bug in 1.0 Silicon wherein the PS hangs on a
	 * reset if the RPLL is in use.
	 */
	RegValue = XResetPs_ReadReg(XRESETPS_CSU_VERSION_REG);
	if (XRESETPS_PLATFORM_PS_VER1 == (RegValue & PS_VERSION_MASK)) {
		RegValue = XResetPs_ReadReg(XRESETPS_CRL_APB_RPLL_CTRL);
		RegValue |= RPLL_BYPASS_MASK;
		XResetPs_WriteReg(XRESETPS_CRL_APB_RPLL_CTRL, RegValue);
	}

	/* Block the propagation of the PROG signal to the PL */
	RegValue = XResetPs_ReadReg(XRESETPS_PMU_GLB_PS_CTRL);
	RegValue &= (~PROG_ENABLE_MASK);
	XResetPs_WriteReg(XRESETPS_PMU_GLB_PS_CTRL, RegValue);

	RegValue = XResetPs_ReadReg(XRESETPS_PMU_GLB_PS_CTRL);
	RegValue |= PROG_GATE_MASK;
	XResetPs_WriteReg(XRESETPS_PMU_GLB_PS_CTRL, RegValue);

	/* Initiate PS-only reset */
	RegValue = XResetPs_ReadReg(XRESETPS_PMU_GLB_RST_CTRL);
	RegValue |= PS_ONLY_RESET_MASK;
	XResetPs_WriteReg(XRESETPS_PMU_GLB_RST_CTRL, RegValue);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* Pulse Reset FPD.
*
* @param	None.
*
* @return
*		- XST_SUCCESS if successful else error code.
*
* @note		The pulse reset sequence is referred from ug1085(v1.3)
*		chapter-38. Few changes to the sequence are adpoted from PMUFW.
*
******************************************************************************/
static XStatus XResetPs_PulseResetFpd(void)
{
	u32 TimeOut;
	u32 RegValue;

	/* Enable FPD to LPD isolations */
	RegValue = XResetPs_ReadReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL);
	RegValue &= (~FPD_TO_LPD_ISO_MASK);
	RegValue |= FPD_TO_LPD_ISO_MASK;
	XResetPs_WriteReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL, RegValue);

	RegValue = XResetPs_ReadReg(XRESETPS_LPD_SLCR_APBISO_REQ_CTRL);
	RegValue |= GPU_ISO_MASK;
	XResetPs_WriteReg(XRESETPS_LPD_SLCR_APBISO_REQ_CTRL, RegValue);

	/* Enable LPD to FPD isolations */
	RegValue = XResetPs_ReadReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL);
	RegValue &= (~LPD_TO_FPD_ISO_MASK);
	RegValue |= LPD_TO_FPD_ISO_MASK;
	XResetPs_WriteReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL, RegValue);

	/*
	 * Here we need to check for AIB ack, since nothing is done incase
	 * ack is not received, we are just waiting for specified timeout
	 * and continuing
	 */
	TimeOut = XRESETPS_AIB_ISO_DELAY;
	while (TimeOut > 0U) {
		TimeOut--;
	}

	/* Initiate FPD reset */
	RegValue = XResetPs_ReadReg(XRESETPS_PMU_GLB_RST_CTRL);
	RegValue |= FPD_APU_RESET_MASK;
	XResetPs_WriteReg(XRESETPS_PMU_GLB_RST_CTRL, RegValue);

	/* Wait till reset propagates */
	TimeOut = XRESETPS_RST_PROP_DELAY;
	while (TimeOut > 0U) {
		TimeOut--;
	}

	/* Disable FPD to LPD isolations */
	RegValue = XResetPs_ReadReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL);
	RegValue &= (~FPD_TO_LPD_ISO_MASK);
	XResetPs_WriteReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL, RegValue);

	RegValue = XResetPs_ReadReg(XRESETPS_LPD_SLCR_APBISO_REQ_CTRL);
	RegValue &= (~GPU_ISO_MASK);
	XResetPs_WriteReg(XRESETPS_LPD_SLCR_APBISO_REQ_CTRL, RegValue);

	/* Release from Reset and wait till it propagates */
	RegValue = XResetPs_ReadReg(XRESETPS_PMU_GLB_RST_CTRL);
	RegValue &= (~FPD_APU_RESET_MASK);
	XResetPs_WriteReg(XRESETPS_PMU_GLB_RST_CTRL, RegValue);

	/* Wait till reset propagates */
	TimeOut = XRESETPS_RST_PROP_DELAY;
	while (TimeOut > 0U) {
		TimeOut--;
	}

	/* Disable LPD to FPD isolations */
	RegValue = XResetPs_ReadReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL);
	RegValue &= (~LPD_TO_FPD_ISO_MASK);
	XResetPs_WriteReg(XRESETPS_LPD_SCR_AXIISO_REQ_CTRL, RegValue);

	return XST_SUCCESS;
}
#endif

/****************************************************************************/
/**
*
* Assert reset for specific peripheral based on reset ID.
*
* @param	InstancePtr is a pointer to the XResetPs instance.
* @param	ResetID is the ID of the peripheral.
*
* @return
*		- XST_SUCCESS if reset assertion was successful.
*		- Error Code otherwise.
*
* @note		None.
*
******************************************************************************/
XStatus XResetPs_ResetAssert(XResetPs *InstancePtr,
						   const XResetPs_RstId ResetID)
{
	/* Arguments validation */
	Xil_AssertNonvoid(InstancePtr != NULL);
	if ((ResetID > XRESETPS_RSTID_END) ||
		(ResetID < XRESETPS_RSTID_START)) {
		return XST_INVALID_PARAM;
	}

#if EL1_NONSECURE
	/* Assert reset via PMUFW */
	u64 SmcArgs;
	XSmc_OutVar out;

	SmcArgs =  (u64)XRESETPS_RSTACT_ASSERT << 32;
	SmcArgs |= ((u64)(ResetID + XRESETPS_RSTID_BASE));

	out = Xil_Smc(PM_ASSERT_SMC_FID, SmcArgs, 0, 0, 0, 0, 0, 0);

	return ((u32)out.Arg0);
#else
	u32 RegAddr;
	u32 RegBitmask;
	u32 RegValue;

	/* Ignoring Nodes that doesnot support assert */
	if (!XRESETPS_CHK_ASSERT_SUPPORT(ResetMap[ResetID].SupportedActions)) {
			return XST_NO_FEATURE;
	}

	RegAddr = ResetMap[ResetID].SlcrregAddr;
	RegBitmask = ResetMap[ResetID].SlcrregBitmask;

	/* Enable bit to assert reset */
	RegValue = XResetPs_ReadReg(RegAddr);
	RegValue |= RegBitmask;
	XResetPs_WriteReg(RegAddr, RegValue);

	return XST_SUCCESS;
#endif
}

/****************************************************************************/
/**
*
* Deassert reset for specific peripheral based on reset ID.
*
* @param	InstancePtr is a pointer to the XResetPs instance.
* @param	ResetID is the ID of the peripheral.
*
* @return
*		- XST_SUCCESS if reset deassertion was successful.
*		- Error Code otherwise.
*
* @note		None.
*
******************************************************************************/
XStatus XResetPs_ResetDeassert(XResetPs *InstancePtr,
						   const XResetPs_RstId ResetID)
{
	/* Arguments validation */
	Xil_AssertNonvoid(InstancePtr != NULL);
	if ((ResetID > XRESETPS_RSTID_END) ||
		(ResetID < XRESETPS_RSTID_START)) {
		return XST_INVALID_PARAM;
	}

#if EL1_NONSECURE
	/* Deassert reset via PMUFW */
	u64 SmcArgs;
	XSmc_OutVar out;

	SmcArgs =  (u64)XRESETPS_RSTACT_RELEASE << 32;
	SmcArgs |= ((u64)(ResetID + XRESETPS_RSTID_BASE));

	out = Xil_Smc(PM_ASSERT_SMC_FID, SmcArgs, 0, 0, 0, 0, 0, 0);

	return ((u32)out.Arg0);
#else
	u32 RegAddr;
	u32 RegBitmask;
	u32 RegValue;

	/* Ignoring Nodes that does not support deassert */
	if (!XRESETPS_CHK_ASSERT_SUPPORT(ResetMap[ResetID].SupportedActions)) {
			return XST_NO_FEATURE;
	}

	RegAddr = ResetMap[ResetID].SlcrregAddr;
	RegBitmask = ResetMap[ResetID].SlcrregBitmask;

	/* Disable bit to deassert reset */
	RegValue = XResetPs_ReadReg(RegAddr);
	RegValue &= (~RegBitmask);
	XResetPs_WriteReg(RegAddr, RegValue);

	return XST_SUCCESS;
#endif
}

/****************************************************************************/
/**
*
* Pulse reset for specific peripheral based on reset ID.
*
* @param	InstancePtr is a pointer to the XResetPs instance.
* @param	ResetID is the ID of the peripheral.
*
* @return
*		- XST_SUCCESS if pulse reset was successful.
*		- Error Code otherwise.
*
* @note		None.
*
******************************************************************************/
XStatus XResetPs_ResetPulse(XResetPs *InstancePtr, const XResetPs_RstId ResetID)
{
	/* Arguments validation */
	Xil_AssertNonvoid(InstancePtr != NULL);
	if ((ResetID > XRESETPS_RSTID_END) ||
		(ResetID < XRESETPS_RSTID_START)) {
		return XST_INVALID_PARAM;
	}

#if EL1_NONSECURE
	/* Pulse reset via PMUFW */
	u64 SmcArgs;
	XSmc_OutVar out;

	SmcArgs =  (u64)XRESETPS_RSTACT_PULSE << 32;
	SmcArgs |= ((u64)(ResetID + XRESETPS_RSTID_BASE));

	out = Xil_Smc(PM_ASSERT_SMC_FID, SmcArgs, 0, 0, 0, 0, 0, 0);

	return ((u32)out.Arg0);
#else
	u32 RegAddr;
	u32 RegBitmask;
	u32 RegValue;
	u32 TimeOut;

	/* Ignoring Nodes that donot support pulse reset */
	if (!XRESETPS_CHK_PULSE_SUPPORT(ResetMap[ResetID].SupportedActions)) {
			return XST_NO_FEATURE;
	}

	/* Handling specific pulse resets */
	switch (ResetID) {
		case XRESETPS_RSTID_FPD:
			return XResetPs_PulseResetFpd();
		case XRESETPS_RSTID_RPU_LS:
			return XResetPs_PulseResetRpuLs();
		case XRESETPS_RSTID_PS_ONLY:
			return XResetPs_PulseResetPsOnly();
		default:
			break;
	}

	RegAddr = ResetMap[ResetID].SlcrregAddr;
	RegBitmask = ResetMap[ResetID].SlcrregBitmask;

	/* Power state mask validation */
	if ((ResetMap[ResetID].PulseType == XRESETPS_PT_DLY_PSCHK) &&
		(ResetMap[ResetID].PwrStateBitmask != XRESETPS_BM_INVALID)) {
		RegValue = XResetPs_ReadReg(XRESETPS_PMU_GLB_PWR_STATUS);
		if (ResetMap[ResetID].PwrStateBitmask !=
			(RegValue && ResetMap[ResetID].PwrStateBitmask )) {
			return XST_REGISTER_ERROR;
		}
	}

	/* Enable bit to assert reset */
	RegValue = XResetPs_ReadReg(RegAddr);
	RegValue |= RegBitmask;
	XResetPs_WriteReg(RegAddr, RegValue);

	/* Wait for assert propogation */
	if (ResetMap[ResetID].PulseType != XRESETPS_PT_NO_DLY_NO_PSCHK) {
		TimeOut = XRESETPS_PULSE_PROP_DELAY;
		while (TimeOut > 0U) {
			TimeOut--;
		}
	}

	/* Disable bit to deassert reset */
	RegValue = XResetPs_ReadReg(RegAddr);
	RegValue &= (~RegBitmask);
	XResetPs_WriteReg(RegAddr, RegValue);

	/* Wait for release propogation */
	if (ResetMap[ResetID].PulseType != XRESETPS_PT_NO_DLY_NO_PSCHK) {
		TimeOut = XRESETPS_PULSE_PROP_DELAY;
		while (TimeOut > 0U) {
			TimeOut--;
		}
	}

	return XST_SUCCESS;
#endif
}

/****************************************************************************/
/**
*
* Get reset status for specific peripheral based on reset ID.
*
* @param	InstancePtr is a pointer to the XResetPs instance.
* @param	ResetID is the ID of the peripheral.
* @param	Status is the status of reset for ResetID.
*		1 if asserted and 0 if released
*
* @return
*		- XST_SUCCESS if status fetched successful.
*		- Error Code otherwise.
*
* @note		None.
*
******************************************************************************/
XStatus XResetPs_ResetStatus(XResetPs *InstancePtr,
		       const XResetPs_RstId ResetID, XResetPs_RstStatus *Status)
{
	/* Arguments validation */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(Status != NULL);
	if ((ResetID > XRESETPS_RSTID_END) ||
		(ResetID < XRESETPS_RSTID_START)) {
		return XST_INVALID_PARAM;
	}

#if EL1_NONSECURE
	/* Get reset status via PMUFW */
	XSmc_OutVar out;

	out = Xil_Smc(PM_GETSTATUS_SMC_FID,
		      ((u64)(ResetID + XRESETPS_RSTID_BASE)), 0, 0, 0, 0, 0, 0);
	*Status = ((u32)(out.Arg0 >> 32));

	return ((u32)out.Arg0);
#else
	u32 RegAddr;
	u32 RegBitmask;
	u32 RegValue;

	/* Ignoring Nodes that donot support reset status */
	if (!XRESETPS_CHK_STATUS_SUPPORT(ResetMap[ResetID].SupportedActions)) {
			return XST_NO_FEATURE;
	}

	/*
	 * @NOTE:
	 * This will always move to else part as GPO3 are ignored because
	 * XRESETPS_PMU_LCL_READ_CTRL is not accessible.
	 */
	/* GPO3PL have status address different from control address */
	if ((ResetID >= XRESETPS_RSTID_GPO3PL0) &&
			(ResetID <= XRESETPS_RSTID_GPO3PL31)) {
		RegAddr = XRESETPS_PMU_LCL_READ_CTRL;
	} else {
		RegAddr = ResetMap[ResetID].SlcrregAddr;
	}

	RegBitmask = ResetMap[ResetID].SlcrregBitmask;

	RegValue = XResetPs_ReadReg(RegAddr);
	if ((RegValue & RegBitmask) == RegBitmask) {
		*Status = XRESETPS_RESETASSERTED;
	} else {
		*Status = XRESETPS_RESETRELEASED;
	}

	return XST_SUCCESS;
#endif
}

/** @} */
