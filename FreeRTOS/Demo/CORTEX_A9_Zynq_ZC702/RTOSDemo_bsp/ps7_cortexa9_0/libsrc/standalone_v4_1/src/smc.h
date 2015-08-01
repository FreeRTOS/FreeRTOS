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
