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
* @file xresetps_hw.h
* @addtogroup xresetps_v1_0
* @{
*
* This file contains the hardware interface to the System Reset controller.
*
* <pre>
* MODIFICATION HISTORY:
* Ver   Who    Date     Changes
* ----- ------ -------- ---------------------------------------------
* 1.00  cjp    09/05/17 First release
* </pre>
*
******************************************************************************/
#ifndef XRESETPS_HW_H		/* prevent circular inclusions */
#define XRESETPS_HW_H		/* by using protection macros */

/***************************** Include Files *********************************/
#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

#ifdef __cplusplus
extern "C" {
#endif

/************************** Constant Definitions *****************************/
/* Register address defines */
/* CRF_APB defines */
#define XRESETPS_CRF_APB_BASE         (0XFD1A0000U)
/* RST_FPD_TOP Address and mask definations */
#define XRESETPS_CRF_APB_RST_FPD_TOP \
				  ((XRESETPS_CRF_APB_BASE) + ((u32)0X00000100U))
#define PCIE_CFG_RESET_MASK       ((u32)0X00080000U)
#define PCIE_BRIDGE_RESET_MASK    ((u32)0X00040000U)
#define PCIE_CTRL_RESET_MASK      ((u32)0X00020000U)
#define DP_RESET_MASK             ((u32)0X00010000U)
#define SWDT_RESET_MASK           ((u32)0X00008000U)
#define AFI_FM5_RESET_MASK        ((u32)0X00001000U)
#define AFI_FM4_RESET_MASK        ((u32)0X00000800U)
#define AFI_FM3_RESET_MASK        ((u32)0X00000400U)
#define AFI_FM2_RESET_MASK        ((u32)0X00000200U)
#define AFI_FM1_RESET_MASK        ((u32)0X00000100U)
#define AFI_FM0_RESET_MASK        ((u32)0X00000080U)
#define GDMA_RESET_MASK           ((u32)0X00000040U)
#define GPU_PP1_RESET_MASK        ((u32)0X00000020U)
#define GPU_PP0_RESET_MASK        ((u32)0X00000010U)
#define GPU_RESET_MASK            ((u32)0X00000008U)
#define GT_RESET_MASK             ((u32)0X00000004U)
#define SATA_RESET_MASK           ((u32)0X00000002U)
/* RST_FPD_APU Address and mask definations */
#define XRESETPS_CRF_APB_RST_FPD_APU \
				  ((XRESETPS_CRF_APB_BASE) + ((u32)0X00000104U))
#define ACPU3_PWRON_RESET_MASK    ((u32)0X00002000U)
#define ACPU2_PWRON_RESET_MASK    ((u32)0X00001000U)
#define ACPU1_PWRON_RESET_MASK    ((u32)0X00000800U)
#define ACPU0_PWRON_RESET_MASK    ((u32)0X00000400U)
#define APU_L2_RESET_MASK         ((u32)0X00000100U)
#define ACPU3_RESET_MASK          ((u32)0X00000008U)
#define ACPU2_RESET_MASK          ((u32)0X00000004U)
#define ACPU1_RESET_MASK          ((u32)0X00000002U)
#define ACPU0_RESET_MASK          ((u32)0X00000001U)
/* RST_DDR_SS Address and mask definations */
#define XRESETPS_CRF_APB_RST_DDR_SS \
				  ((XRESETPS_CRF_APB_BASE) + ((u32)0X00000108U))
#define DDR_RESET_MASK            ((u32)0X00000008U)
#define DDR_APM_RESET_MASK        ((u32)0X00000004U)
/* APLL_CTRL Address and mask definations */
#define XRESETPS_CRF_APB_APLL_CTRL \
				  ((XRESETPS_CRF_APB_BASE) + ((u32)0X00000020U))
#define APLL_RESET_MASK           ((u32)0X00000001U)
/* DPLL_CTRL Address and mask definations */
#define XRESETPS_CRF_APB_DPLL_CTRL \
				  ((XRESETPS_CRF_APB_BASE) + ((u32)0X0000002CU))
#define DPLL_RESET_MASK           ((u32)0X00000001U)
/* VPLL_CTRL Address and mask definations */
#define XRESETPS_CRF_APB_VPLL_CTRL \
				  ((XRESETPS_CRF_APB_BASE) + ((u32)0X00000038U))
#define VPLL_RESET_MASK           ((u32)0X00000001U)

/* CRL_APB defines */
#define XRESETPS_CRL_APB_BASE     (0XFF5E0000U)
/* RESET_CTRL Address and mask definations */
#define XRESETPS_CRL_APB_RESET_CTRL \
				  ((XRESETPS_CRL_APB_BASE) + ((u32)0X00000218U))
#define SOFT_RESET_MASK           ((u32)0X00000010U)
/* RST_LPD_IOU0 Address and mask definations */
#define XRESETPS_CRL_APB_RST_LPD_IOU0 \
				  ((XRESETPS_CRL_APB_BASE) + ((u32)0X00000230U))
#define GEM0_RESET_MASK           ((u32)0X00000001U)
#define GEM1_RESET_MASK           ((u32)0X00000002U)
#define GEM2_RESET_MASK           ((u32)0X00000004U)
#define GEM3_RESET_MASK           ((u32)0X00000008U)
/* RST_LPD_IOU2 Address and mask definations */
#define XRESETPS_CRL_APB_RST_LPD_IOU2 \
				  ((XRESETPS_CRL_APB_BASE) + ((u32)0X00000238U))
#define QSPI_RESET_MASK           ((u32)0X00000001U)
#define UART0_RESET_MASK          ((u32)0X00000002U)
#define UART1_RESET_MASK          ((u32)0X00000004U)
#define SPI0_RESET_MASK           ((u32)0X00000008U)
#define SPI1_RESET_MASK           ((u32)0X00000010U)
#define SDIO0_RESET_MASK          ((u32)0X00000020U)
#define SDIO1_RESET_MASK          ((u32)0X00000040U)
#define CAN0_RESET_MASK           ((u32)0X00000080U)
#define CAN1_RESET_MASK           ((u32)0X00000100U)
#define I2C0_RESET_MASK           ((u32)0X00000200U)
#define I2C1_RESET_MASK           ((u32)0X00000400U)
#define TTC0_RESET_MASK           ((u32)0X00000800U)
#define TTC1_RESET_MASK           ((u32)0X00001000U)
#define TTC2_RESET_MASK           ((u32)0X00002000U)
#define TTC3_RESET_MASK           ((u32)0X00004000U)
#define SWDT_RESET_MASK           ((u32)0X00008000U)
#define NAND_RESET_MASK           ((u32)0X00010000U)
#define ADMA_RESET_MASK           ((u32)0X00020000U)
#define GPIO_RESET_MASK           ((u32)0X00040000U)
#define IOU_CC_RESET_MASK         ((u32)0X00080000U)
#define TIMESTAMP_RESET_MASK      ((u32)0X00100000U)
/* RST_LPD_TOP Address and mask definations */
#define XRESETPS_CRL_APB_RST_LPD_TOP \
				  ((XRESETPS_CRL_APB_BASE) + ((u32)0X0000023CU))
#define RPU_R50_RESET_MASK        ((u32)0X00000001U)
#define RPU_R51_RESET_MASK        ((u32)0X00000002U)
#define RPU_AMBA_RESET_MASK       ((u32)0X00000004U)
#define OCM_RESET_MASK            ((u32)0X00000008U)
#define RPU_PGE_RESET_MASK        ((u32)0X00000010U)
#define USB0_CORERESET_MASK       ((u32)0X00000040U)
#define USB1_CORERESET_MASK       ((u32)0X00000080U)
#define USB0_HIBERRESET_MASK      ((u32)0X00000100U)
#define USB1_HIBERRESET_MASK      ((u32)0X00000200U)
#define USB0_APB_RESET_MASK       ((u32)0X00000400U)
#define USB1_APB_RESET_MASK       ((u32)0X00000800U)
#define IPI_RESET_MASK            ((u32)0X00004000U)
#define APM_RESET_MASK            ((u32)0X00008000U)
#define RTC_RESET_MASK            ((u32)0X00010000U)
#define SYSMON_RESET_MASK         ((u32)0X00020000U)
#define AFI_FM6_RESET_MASK        ((u32)0X00080000U)
#define LPD_SWDT_RESET_MASK       ((u32)0X00100000U)
#define FPD_RESET_MASK            ((u32)0X00800000U)
/* RST_LPD_DBG Address and mask definations */
#define XRESETPS_CRL_APB_RST_LPD_DBG \
				  ((XRESETPS_CRL_APB_BASE) + ((u32)0X00000240U))
#define RPU_DBG1_RESET_MASK       ((u32)0X00000020U)
#define RPU_DBG0_RESET_MASK       ((u32)0X00000010U)
#define DBG_LPD_RESET_MASK        ((u32)0X00000002U)
#define DBG_FPD_RESET_MASK        ((u32)0X00000001U)
/* IOPLL_CTRL Address and mask definations */
#define XRESETPS_CRL_APB_IOPLL_CTRL \
				  ((XRESETPS_CRL_APB_BASE) + ((u32)0X00000020U))
#define IOPLL_RESET_MASK          ((u32)0X00000001U)
/* RPLL_CTRL Address and mask definations */
#define XRESETPS_CRL_APB_RPLL_CTRL \
				  ((XRESETPS_CRL_APB_BASE) + ((u32)0X00000030U))
#define RPLL_RESET_MASK           ((u32)0X00000001U)
#define RPLL_BYPASS_MASK          ((u32)0X00000008U)

/* PMU_IOM defines */
#define XRESETPS_PMU_IOM_BASE     (0XFFD40000U)
/* PMU_IOM_GPO3 Address and mask definations */
#define XRESETPS_PMU_IOM_GPO3_CTRL \
				  ((XRESETPS_PMU_IOM_BASE) + ((u32)0X0000001CU))
#define GPO3_PL0_RESET_MASK       ((u32)0X00000001U)
#define GPO3_PL1_RESET_MASK       ((u32)0X00000002U)
#define GPO3_PL2_RESET_MASK       ((u32)0X00000004U)
#define GPO3_PL3_RESET_MASK       ((u32)0X00000008U)
#define GPO3_PL4_RESET_MASK       ((u32)0X00000010U)
#define GPO3_PL5_RESET_MASK       ((u32)0X00000020U)
#define GPO3_PL6_RESET_MASK       ((u32)0X00000040U)
#define GPO3_PL7_RESET_MASK       ((u32)0X00000080U)
#define GPO3_PL8_RESET_MASK       ((u32)0X00000100U)
#define GPO3_PL9_RESET_MASK       ((u32)0X00000200U)
#define GPO3_PL10_RESET_MASK      ((u32)0X00000400U)
#define GPO3_PL11_RESET_MASK      ((u32)0X00000800U)
#define GPO3_PL12_RESET_MASK      ((u32)0X00001000U)
#define GPO3_PL13_RESET_MASK      ((u32)0X00002000U)
#define GPO3_PL14_RESET_MASK      ((u32)0X00004000U)
#define GPO3_PL15_RESET_MASK      ((u32)0X00008000U)
#define GPO3_PL16_RESET_MASK      ((u32)0X00010000U)
#define GPO3_PL17_RESET_MASK      ((u32)0X00020000U)
#define GPO3_PL18_RESET_MASK      ((u32)0X00040000U)
#define GPO3_PL19_RESET_MASK      ((u32)0X00080000U)
#define GPO3_PL20_RESET_MASK      ((u32)0X00100000U)
#define GPO3_PL21_RESET_MASK      ((u32)0X00200000U)
#define GPO3_PL22_RESET_MASK      ((u32)0X00400000U)
#define GPO3_PL23_RESET_MASK      ((u32)0X00800000U)
#define GPO3_PL24_RESET_MASK      ((u32)0X01000000U)
#define GPO3_PL25_RESET_MASK      ((u32)0X02000000U)
#define GPO3_PL26_RESET_MASK      ((u32)0X04000000U)
#define GPO3_PL27_RESET_MASK      ((u32)0X08000000U)
#define GPO3_PL28_RESET_MASK      ((u32)0X10000000U)
#define GPO3_PL29_RESET_MASK      ((u32)0X20000000U)
#define GPO3_PL30_RESET_MASK      ((u32)0X40000000U)
#define GPO3_PL31_RESET_MASK      ((u32)0X80000000U)

/* PMU_LCL defines */
#define XRESETPS_PMU_LCL_BASE     (0XFFD60000U)
/* GPO Read control address */
#define XRESETPS_PMU_LCL_READ_CTRL \
				  ((XRESETPS_PMU_LCL_BASE) + ((u32)0X0000021CU))

/* PMU_GLB defines */
#define XRESETPS_PMU_GLB_BASE     (0XFFD80000U)
/* PMU_GLB_RST Address and mask definations */
#define XRESETPS_PMU_GLB_RST_CTRL ((XRESETPS_PMU_GLB_BASE) + ((u32)0X00000608U))
#define RPU_LS_RESET_MASK         ((u32)0X00000100U)
#define FPD_APU_RESET_MASK        ((u32)0X00000200U)
#define PS_ONLY_RESET_MASK        ((u32)0X00000400U)
/* PMU_GLB_PS Address and mask definations */
#define XRESETPS_PMU_GLB_PS_CTRL  ((XRESETPS_PMU_GLB_BASE) + ((u32)0X00000004U))
#define PROG_ENABLE_MASK          ((u32)0X00000002U)
#define PROG_GATE_MASK            ((u32)0X00000001U)
/* PMU_GLB_AIB Address and mask definations */
#define XRESETPS_PMU_GLB_AIB_CTRL ((XRESETPS_PMU_GLB_BASE) + ((u32)0X00000600U))
#define LPD_AFI_FM_ISO_MASK       ((u32)0X00000001U)
#define LPD_AFI_FS_ISO_MASK       ((u32)0X00000002U)
#define FPD_AFI_FM_ISO_MASK       ((u32)0X00000004U)
#define FPD_AFI_FS_ISO_MASK       ((u32)0X00000008U)
#define AIB_ISO_CTRL_MASK         (LPD_AFI_FM_ISO_MASK | LPD_AFI_FS_ISO_MASK | \
				      FPD_AFI_FM_ISO_MASK | FPD_AFI_FS_ISO_MASK)
/* PMU_GLB_AIB status Address and mask definations */
#define XRESETPS_PMU_GLB_AIB_STATUS \
				  ((XRESETPS_PMU_GLB_BASE) + ((u32)0X00000604U))
#define AIB_ISO_STATUS_MASK       (AIB_ISO_CTRL_MASK)
/* PMU_GLB_PWR status Address and mask definations */
#define XRESETPS_PMU_GLB_PWR_STATUS \
				  ((XRESETPS_PMU_GLB_BASE) + ((u32)0X00000100U))
#define FPD_PSCHK_MASK            ((u32)0x00400000U)
#define PCIE_CTRL_PSCHK_MASK      (FPD_PSCHK_MASK)
#define DP_PSCHK_MASK             (FPD_PSCHK_MASK)
#define SATA_PSCHK_MASK           (FPD_PSCHK_MASK)
#define R50_PSCHK_MASK            ((u32)0x00000400U)
#define R51_PSCHK_MASK            ((u32)0x00000800U)
#define GPU_PP0_PSCHK_MASK        (((u32)0x00000010U) | (FPD_PSCHK_MASK))
#define GPU_PP1_PSCHK_MASK        (((u32)0x00000020U) | (FPD_PSCHK_MASK))
#define GPU_PSCHK_MASK            ((GPU_PP0_PSCHK_MASK) | \
					(GPU_PP1_PSCHK_MASK) | (FPD_PSCHK_MASK))

/* LPD_SLCR defines */
#define XRESETPS_LPD_SCR_BASE     (0XFF410000U)
/* LPD_SCR_AXIISO_REQ and LPD_SCR_AXIISO_ACK Address and mask definations */
#define XRESETPS_LPD_SCR_AXIISO_REQ_CTRL \
				  ((XRESETPS_LPD_SCR_BASE) + ((u32)0X00003030U))
#define XRESETPS_LPD_SCR_AXIISO_ACK_CTRL \
				  ((XRESETPS_LPD_SCR_BASE) + ((u32)0X00003040U))
#define RPU0_MASTER_ISO_MASK      ((u32)0X00010000U)
#define RPU1_MASTER_ISO_MASK      ((u32)0X00020000U)
#define RPU_MASTER_ISO_MASK	  (RPU0_MASTER_ISO_MASK | RPU1_MASTER_ISO_MASK)
#define RPU0_SLAVE_ISO_MASK       ((u32)0X00040000U)
#define RPU1_SLAVE_ISO_MASK       ((u32)0X00080000U)
#define RPU_SLAVE_ISO_MASK	  (RPU0_SLAVE_ISO_MASK | RPU1_SLAVE_ISO_MASK)
#define FPD_OCM_ISO_MASK          ((u32)0X00000008U)
#define FPD_LPDIBS_ISO_MASK       ((u32)0X00000004U)
#define AFIFS1_ISO_MASK           ((u32)0X00000002U)
#define AFIFS0_ISO_MASK           ((u32)0X00000001U)
#define FPD_TO_LPD_ISO_MASK       (FPD_LPDIBS_ISO_MASK | FPD_OCM_ISO_MASK | \
					      AFIFS0_ISO_MASK | AFIFS1_ISO_MASK)
#define LPD_DDR_ISO_MASK          ((u32)0X08000000U)
#define FPD_MAIN_ISO_MASK         ((u32)0X01000000U)
#define LPD_TO_FPD_ISO_MASK       (LPD_DDR_ISO_MASK | FPD_MAIN_ISO_MASK)
/* LPD_SLCR_APBISO_REQ Address and mask definations */
#define XRESETPS_LPD_SLCR_APBISO_REQ_CTRL \
				  ((XRESETPS_LPD_SCR_BASE) + ((u32)0X00003048U))
#define GPU_ISO_MASK              ((u32)0X00000001U)

/* CSU defines */
#define XRESETPS_CSU_BASE         (0xFFCA0000U)
#define XRESETPS_CSU_VERSION_REG  ((XRESETPS_CSU_BASE) + ((u32)0x00000044U))
#define XRESETPS_PLATFORM_PS_VER1 ((u32)0x00000000U)
#define PS_VERSION_MASK           ((u32)0x0000000FU)

/* Timeout delay defines */
#define XRESETPS_RST_PROP_DELAY   (0xFU)
#define XRESETPS_AIB_ISO_DELAY	  (0xFU)
#define XRESETPS_AIB_PSPL_DELAY	  (0xFU)
#define XRESETPS_PULSE_PROP_DELAY (0xFU)

/* AIB ack reconfirmation count */
#define XRESETPS_AIB_PSPL_RECONFIRM_CNT \
				  (0x2U)

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/

#ifdef __cplusplus
}
#endif
#endif /* end of protection macro */
/** @} */
