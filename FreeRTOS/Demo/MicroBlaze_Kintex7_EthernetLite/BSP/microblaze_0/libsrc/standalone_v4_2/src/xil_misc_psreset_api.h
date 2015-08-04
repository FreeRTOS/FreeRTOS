/******************************************************************************
*
* Copyright (C) 2013 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xil_misc_psreset_api.h
*
* This file contains the various register defintions and function prototypes for
* implementing the reset functionality of zynq ps devices
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date   Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00b kpc   03/07/13 First release.
* </pre>
*
******************************************************************************/

#ifndef XIL_MISC_RESET_H		/* prevent circular inclusions */
#define XIL_MISC_RESET_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif


/***************************** Include Files *********************************/
#include "xil_types.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/
#define XDDRC_CTRL_BASEADDR				0xF8006000
#define XSLCR_BASEADDR					0xF8000000
/**< OCM configuration register */
#define XSLCR_OCM_CFG_ADDR				(XSLCR_BASEADDR + 0x910)
/**< SLCR unlock register */
#define XSLCR_UNLOCK_ADDR				(XSLCR_BASEADDR + 0x8)
/**< SLCR GEM0 rx clock control register */
#define XSLCR_GEM0_RCLK_CTRL_ADDR		(XSLCR_BASEADDR + 0x138)
/**< SLCR GEM1 rx clock control register */
#define XSLCR_GEM1_RCLK_CTRL_ADDR		(XSLCR_BASEADDR + 0x13C)
/**< SLCR GEM0 clock control register */
#define XSLCR_GEM0_CLK_CTRL_ADDR		(XSLCR_BASEADDR + 0x140)
/**< SLCR GEM1 clock control register */
#define XSLCR_GEM1_CLK_CTRL_ADDR		(XSLCR_BASEADDR + 0x144)
/**< SLCR SMC clock control register */
#define XSLCR_SMC_CLK_CTRL_ADDR			(XSLCR_BASEADDR + 0x148)
/**< SLCR GEM reset control register */
#define XSLCR_GEM_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x214)
/**< SLCR USB0 clock control register */
#define XSLCR_USB0_CLK_CTRL_ADDR		(XSLCR_BASEADDR + 0x130)
/**< SLCR USB1 clock control register */
#define XSLCR_USB1_CLK_CTRL_ADDR		(XSLCR_BASEADDR + 0x134)
/**< SLCR USB1 reset control register */
#define XSLCR_USB_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x210)
/**< SLCR SMC reset control register */
#define XSLCR_SMC_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x234)
/**< SLCR Level shifter enable register */
#define XSLCR_LVL_SHFTR_EN_ADDR			(XSLCR_BASEADDR + 0x900)
/**< SLCR ARM pll control register */
#define XSLCR_ARM_PLL_CTRL_ADDR			(XSLCR_BASEADDR + 0x100)
/**< SLCR DDR pll control register */
#define XSLCR_DDR_PLL_CTRL_ADDR			(XSLCR_BASEADDR + 0x104)
/**< SLCR IO pll control register */
#define XSLCR_IO_PLL_CTRL_ADDR			(XSLCR_BASEADDR + 0x108)
/**< SLCR ARM pll configuration register */
#define XSLCR_ARM_PLL_CFG_ADDR			(XSLCR_BASEADDR + 0x110)
/**< SLCR DDR pll configuration register */
#define XSLCR_DDR_PLL_CFG_ADDR			(XSLCR_BASEADDR + 0x114)
/**< SLCR IO pll configuration register */
#define XSLCR_IO_PLL_CFG_ADDR			(XSLCR_BASEADDR + 0x118)
/**< SLCR ARM clock control register */
#define XSLCR_ARM_CLK_CTRL_ADDR			(XSLCR_BASEADDR + 0x120)
/**< SLCR DDR clock control register */
#define XSLCR_DDR_CLK_CTRL_ADDR			(XSLCR_BASEADDR + 0x124)
/**< SLCR MIO pin address register */
#define XSLCR_MIO_PIN_00_ADDR			(XSLCR_BASEADDR + 0x700)
/**< SLCR DMAC reset control address register */
#define XSLCR_DMAC_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x20C)
/**< SLCR USB reset control address register */
#define XSLCR_USB_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x210)
/**< SLCR GEM reset control address register */
#define XSLCR_GEM_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x214)
/**< SLCR SDIO reset control address register */
#define XSLCR_SDIO_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x218)
/**< SLCR SPI reset control address register */
#define XSLCR_SPI_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x21C)
/**< SLCR CAN reset control address register */
#define XSLCR_CAN_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x220)
/**< SLCR I2C reset control address register */
#define XSLCR_I2C_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x224)
/**< SLCR UART reset control address register */
#define XSLCR_UART_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x228)
/**< SLCR GPIO reset control address register */
#define XSLCR_GPIO_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x22C)
/**< SLCR LQSPI reset control address register */
#define XSLCR_LQSPI_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x230)
/**< SLCR SMC reset control address register */
#define XSLCR_SMC_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x234)
/**< SLCR OCM reset control address register */
#define XSLCR_OCM_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x238)

/**< SMC mem controller clear config register */
#define XSMC_MEMC_CLR_CONFIG_OFFSET			0x0C
/**< SMC idlecount configuration register */
#define XSMC_REFRESH_PERIOD_0_OFFSET		0x20
#define XSMC_REFRESH_PERIOD_1_OFFSET		0x24
/**< SMC ECC configuration register */
#define XSMC_ECC_MEMCFG1_OFFSET				0x404
/**< SMC ECC command 1 register */
#define XSMC_ECC_MEMCMD1_OFFSET				0x404
/**< SMC ECC command 2 register */
#define XSMC_ECC_MEMCMD2_OFFSET				0x404

/**< SLCR unlock code */
#define XSLCR_UNLOCK_CODE		0x0000DF0D

/**< SMC mem clear configuration mask */
#define XSMC_MEMC_CLR_CONFIG_MASK 	0x5F
/**< SMC ECC memconfig 1 reset value */
#define XSMC_ECC_MEMCFG1_RESET_VAL 	0x43
/**< SMC ECC memcommand 1 reset value */
#define XSMC_ECC_MEMCMD1_RESET_VAL 	0x01300080
/**< SMC ECC memcommand 2 reset value */
#define XSMC_ECC_MEMCMD2_RESET_VAL 	0x01E00585

/**< DDR controller reset bit mask */
#define XDDRPS_CTRL_RESET_MASK 		0x1
/**< SLCR OCM configuration reset value*/
#define XSLCR_OCM_CFG_RESETVAL		0x8
/**< SLCR OCM bank selection mask*/
#define XSLCR_OCM_CFG_HIADDR_MASK	0xF
/**< SLCR level shifter enable mask*/
#define XSLCR_LVL_SHFTR_EN_MASK		0xF

/**< SLCR PLL register reset values */
#define XSLCR_ARM_PLL_CTRL_RESET_VAL	0x0001A008
#define XSLCR_DDR_PLL_CTRL_RESET_VAL	0x0001A008
#define XSLCR_IO_PLL_CTRL_RESET_VAL		0x0001A008
#define XSLCR_ARM_PLL_CFG_RESET_VAL		0x00177EA0
#define XSLCR_DDR_PLL_CFG_RESET_VAL		0x00177EA0
#define XSLCR_IO_PLL_CFG_RESET_VAL		0x00177EA0
#define XSLCR_ARM_CLK_CTRL_RESET_VAL	0x1F000400
#define XSLCR_DDR_CLK_CTRL_RESET_VAL	0x18400003

/**< SLCR MIO register default values */
#define XSLCR_MIO_PIN_00_RESET_VAL		0x00001601
#define XSLCR_MIO_PIN_02_RESET_VAL		0x00000601

/**< SLCR Reset control registers default values */
#define XSLCR_DMAC_RST_CTRL_VAL			0x1
#define XSLCR_GEM_RST_CTRL_VAL			0xF3
#define XSLCR_USB_RST_CTRL_VAL			0x3
#define XSLCR_I2C_RST_CTRL_VAL			0x3
#define XSLCR_SPI_RST_CTRL_VAL			0xF
#define XSLCR_UART_RST_CTRL_VAL			0xF
#define XSLCR_QSPI_RST_CTRL_VAL			0x3
#define XSLCR_GPIO_RST_CTRL_VAL			0x1
#define XSLCR_SMC_RST_CTRL_VAL			0x3
#define XSLCR_OCM_RST_CTRL_VAL			0x1
#define XSLCR_SDIO_RST_CTRL_VAL			0x33
#define XSLCR_CAN_RST_CTRL_VAL			0x3
/**************************** Type Definitions *******************************/

/* the following data type is used to hold a null terminated version string
 * consisting of the following format, "X.YYX"
 */


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/
/*
 * Performs reset operation to the ddr interface
 */
void XDdr_ResetHw();
/*
 * Map the ocm region to post bootrom state
 */
void XOcm_Remap();
/*
 * Performs the smc interface reset
 */
void XSmc_ResetHw(u32 BaseAddress);
/*
 * updates the MIO registers with reset values
 */
void XSlcr_MioWriteResetValues();
/*
 * updates the PLL and clock registers with reset values
 */
void XSlcr_PllWriteResetValues();
/*
 * Disables the level shifters
 */
void XSlcr_DisableLevelShifters();
/*
 * provides softreset to the GPIO interface
 */
void XSlcr_GpioPsReset(void);
/*
 * provides softreset to the DMA interface
 */
void XSlcr_DmaPsReset(void);
/*
 * provides softreset to the SMC interface
 */
void XSlcr_SmcPsReset(void);
/*
 * provides softreset to the CAN interface
 */
void XSlcr_CanPsReset(void);
/*
 * provides softreset to the Uart interface
 */
void XSlcr_UartPsReset(void);
/*
 * provides softreset to the I2C interface
 */
void XSlcr_I2cPsReset(void);
/*
 * provides softreset to the SPI interface
 */
void XSlcr_SpiPsReset(void);
/*
 * provides softreset to the QSPI interface
 */
void XSlcr_QspiPsReset(void);
/*
 * provides softreset to the USB interface
 */
void XSlcr_UsbPsReset(void);
/*
 * provides softreset to the GEM interface
 */
void XSlcr_EmacPsReset(void);
/*
 * provides softreset to the OCM interface
 */
void XSlcr_OcmReset(void);


#ifdef __cplusplus
}
#endif

#endif /* XIL_MISC_RESET_H */
