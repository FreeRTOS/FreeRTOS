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
* @file smc.h
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 1.00a sdm  11/03/09 Initial release.
* </pre>
*
* @note		None.
*
******************************************************************************/

#ifndef SMC_H /* prevent circular inclusions */
#define SMC_H /* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xparameters.h"
#include "xil_io.h"

/***************** Macros (Inline Functions) Definitions *********************/

/**************************** Type Definitions *******************************/

/************************** Constant Definitions *****************************/

/* Memory controller configuration register offset */
#define XSMCPSS_MC_STATUS		0x000	/* Controller status reg, RO */
#define XSMCPSS_MC_INTERFACE_CONFIG	0x004	/* Interface config reg, RO */
#define XSMCPSS_MC_SET_CONFIG		0x008	/* Set configuration reg, WO */
#define XSMCPSS_MC_CLR_CONFIG		0x00C	/* Clear config reg, WO */
#define XSMCPSS_MC_DIRECT_CMD		0x010	/* Direct command reg, WO */
#define XSMCPSS_MC_SET_CYCLES		0x014	/* Set cycles register, WO */
#define XSMCPSS_MC_SET_OPMODE		0x018	/* Set opmode register, WO */
#define XSMCPSS_MC_REFRESH_PERIOD_0	0x020	/* Refresh period_0 reg, RW */
#define XSMCPSS_MC_REFRESH_PERIOD_1	0x024	/* Refresh period_1 reg, RW */

/* Chip select configuration register offset */
#define XSMCPSS_CS_IF0_CHIP_0_OFFSET	0x100	/* Interface 0 chip 0 config */
#define XSMCPSS_CS_IF0_CHIP_1_OFFSET	0x120	/* Interface 0 chip 1 config */
#define XSMCPSS_CS_IF0_CHIP_2_OFFSET	0x140	/* Interface 0 chip 2 config */
#define XSMCPSS_CS_IF0_CHIP_3_OFFSET	0x160	/* Interface 0 chip 3 config */
#define XSMCPSS_CS_IF1_CHIP_0_OFFSET	0x180	/* Interface 1 chip 0 config */
#define XSMCPSS_CS_IF1_CHIP_1_OFFSET	0x1A0	/* Interface 1 chip 1 config */
#define XSMCPSS_CS_IF1_CHIP_2_OFFSET	0x1C0	/* Interface 1 chip 2 config */
#define XSMCPSS_CS_IF1_CHIP_3_OFFSET	0x1E0	/* Interface 1 chip 3 config */

/* User configuration register offset */
#define XSMCPSS_UC_STATUS_OFFSET	0x200	/* User status reg, RO */
#define XSMCPSS_UC_CONFIG_OFFSET	0x204	/* User config reg, WO */

/* Integration test register offset */
#define XSMCPSS_IT_OFFSET		0xE00

/* ID configuration register offset */
#define XSMCPSS_ID_PERIP_0_OFFSET	0xFE0
#define XSMCPSS_ID_PERIP_1_OFFSET	0xFE4
#define XSMCPSS_ID_PERIP_2_OFFSET	0xFE8
#define XSMCPSS_ID_PERIP_3_OFFSET	0xFEC
#define XSMCPSS_ID_PCELL_0_OFFSET	0xFF0
#define XSMCPSS_ID_PCELL_1_OFFSET	0xFF4
#define XSMCPSS_ID_PCELL_2_OFFSET	0xFF8
#define XSMCPSS_ID_PCELL_3_OFFSET	0xFFC

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

void XSmc_SramInit (void);
void XSmc_NorInit(void);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* SMC_H */
