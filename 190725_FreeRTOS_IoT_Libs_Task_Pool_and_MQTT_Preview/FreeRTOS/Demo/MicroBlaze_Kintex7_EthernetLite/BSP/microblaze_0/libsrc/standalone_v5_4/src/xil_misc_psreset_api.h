/******************************************************************************
*
* Copyright (C) 2013 - 2014 Xilinx, Inc. All rights reserved.
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
#define XDDRC_CTRL_BASEADDR				0xF8006000U
#define XSLCR_BASEADDR					0xF8000000U
/**< OCM configuration register */
#define XSLCR_OCM_CFG_ADDR				(XSLCR_BASEADDR + 0x00000910U)
/**< SLCR unlock register */
#define XSLCR_UNLOCK_ADDR				(XSLCR_BASEADDR + 0x00000008U)
/**< SLCR GEM0 rx clock control register */
#define XSLCR_GEM0_RCLK_CTRL_ADDR		(XSLCR_BASEADDR + 0x00000138U)
/**< SLCR GEM1 rx clock control register */
#define XSLCR_GEM1_RCLK_CTRL_ADDR		(XSLCR_BASEADDR + 0x0000013CU)
/**< SLCR GEM0 clock control register */
#define XSLCR_GEM0_CLK_CTRL_ADDR		(XSLCR_BASEADDR + 0x00000140U)
/**< SLCR GEM1 clock control register */
#define XSLCR_GEM1_CLK_CTRL_ADDR		(XSLCR_BASEADDR + 0x00000144U)
/**< SLCR SMC clock control register */
#define XSLCR_SMC_CLK_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000148U)
/**< SLCR GEM reset control register */
#define XSLCR_GEM_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000214U)
/**< SLCR USB0 clock control register */
#define XSLCR_USB0_CLK_CTRL_ADDR		(XSLCR_BASEADDR + 0x00000130U)
/**< SLCR USB1 clock control register */
#define XSLCR_USB1_CLK_CTRL_ADDR		(XSLCR_BASEADDR + 0x00000134U)
/**< SLCR USB1 reset control register */
#define XSLCR_USB_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000210U)
/**< SLCR SMC reset control register */
#define XSLCR_SMC_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000234U)
/**< SLCR Level shifter enable register */
#define XSLCR_LVL_SHFTR_EN_ADDR			(XSLCR_BASEADDR + 0x00000900U)
/**< SLCR ARM pll control register */
#define XSLCR_ARM_PLL_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000100U)
/**< SLCR DDR pll control register */
#define XSLCR_DDR_PLL_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000104U)
/**< SLCR IO pll control register */
#define XSLCR_IO_PLL_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000108U)
/**< SLCR ARM pll configuration register */
#define XSLCR_ARM_PLL_CFG_ADDR			(XSLCR_BASEADDR + 0x00000110U)
/**< SLCR DDR pll configuration register */
#define XSLCR_DDR_PLL_CFG_ADDR			(XSLCR_BASEADDR + 0x00000114U)
/**< SLCR IO pll configuration register */
#define XSLCR_IO_PLL_CFG_ADDR			(XSLCR_BASEADDR + 0x00000118U)
/**< SLCR ARM clock control register */
#define XSLCR_ARM_CLK_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000120U)
/**< SLCR DDR clock control register */
#define XSLCR_DDR_CLK_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000124U)
/**< SLCR MIO pin address register */
#define XSLCR_MIO_PIN_00_ADDR			(XSLCR_BASEADDR + 0x00000700U)
/**< SLCR DMAC reset control address register */
#define XSLCR_DMAC_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x0000020CU)
/**< SLCR USB reset control address register */
/*#define XSLCR_USB_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000210U)*/
/**< SLCR GEM reset control address register */
/*#define XSLCR_GEM_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000214U)*/
/**< SLCR SDIO reset control address register */
#define XSLCR_SDIO_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000218U)
/**< SLCR SPI reset control address register */
#define XSLCR_SPI_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x0000021CU)
/**< SLCR CAN reset control address register */
#define XSLCR_CAN_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000220U)
/**< SLCR I2C reset control address register */
#define XSLCR_I2C_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000224U)
/**< SLCR UART reset control address register */
#define XSLCR_UART_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000228U)
/**< SLCR GPIO reset control address register */
#define XSLCR_GPIO_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x0000022CU)
/**< SLCR LQSPI reset control address register */
#define XSLCR_LQSPI_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000230U)
/**< SLCR SMC reset control address register */
/*#define XSLCR_SMC_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000234U)*/
/**< SLCR OCM reset control address register */
#define XSLCR_OCM_RST_CTRL_ADDR			(XSLCR_BASEADDR + 0x00000238U)

/**< SMC mem controller clear config register */
#define XSMC_MEMC_CLR_CONFIG_OFFSET			0x0000000CU
/**< SMC idlecount configuration register */
#define XSMC_REFRESH_PERIOD_0_OFFSET		0x00000020U
#define XSMC_REFRESH_PERIOD_1_OFFSET		0x00000024U
/**< SMC ECC configuration register */
#define XSMC_ECC_MEMCFG1_OFFSET				0x00000404U
/**< SMC ECC command 1 register */
#define XSMC_ECC_MEMCMD1_OFFSET				0x00000404U
/**< SMC ECC command 2 register */
#define XSMC_ECC_MEMCMD2_OFFSET				0x00000404U

/**< SLCR unlock code */
#define XSLCR_UNLOCK_CODE		0x0000DF0DU

/**< SMC mem clear configuration mask */
#define XSMC_MEMC_CLR_CONFIG_MASK 	0x0000005FU
/**< SMC ECC memconfig 1 reset value */
#define XSMC_ECC_MEMCFG1_RESET_VAL 	0x00000043U
/**< SMC ECC memcommand 1 reset value */
#define XSMC_ECC_MEMCMD1_RESET_VAL 	0x01300080U
/**< SMC ECC memcommand 2 reset value */
#define XSMC_ECC_MEMCMD2_RESET_VAL 	0x01E00585U

/**< DDR controller reset bit mask */
#define XDDRPS_CTRL_RESET_MASK 		0x00000001U
/**< SLCR OCM configuration reset value*/
#define XSLCR_OCM_CFG_RESETVAL		0x00000008U
/**< SLCR OCM bank selection mask*/
#define XSLCR_OCM_CFG_HIADDR_MASK	0x0000000FU
/**< SLCR level shifter enable mask*/
#define XSLCR_LVL_SHFTR_EN_MASK		0x0000000FU

/**< SLCR PLL register reset values */
#define XSLCR_ARM_PLL_CTRL_RESET_VAL	0x0001A008U
#define XSLCR_DDR_PLL_CTRL_RESET_VAL	0x0001A008U
#define XSLCR_IO_PLL_CTRL_RESET_VAL		0x0001A008U
#define XSLCR_ARM_PLL_CFG_RESET_VAL		0x00177EA0U
#define XSLCR_DDR_PLL_CFG_RESET_VAL		0x00177EA0U
#define XSLCR_IO_PLL_CFG_RESET_VAL		0x00177EA0U
#define XSLCR_ARM_CLK_CTRL_RESET_VAL	0x1F000400U
#define XSLCR_DDR_CLK_CTRL_RESET_VAL	0x18400003U

/**< SLCR MIO register default values */
#define XSLCR_MIO_PIN_00_RESET_VAL		0x00001601U
#define XSLCR_MIO_PIN_02_RESET_VAL		0x00000601U

/**< SLCR Reset control registers default values */
#define XSLCR_DMAC_RST_CTRL_VAL			0x00000001U
#define XSLCR_GEM_RST_CTRL_VAL			0x000000F3U
#define XSLCR_USB_RST_CTRL_VAL			0x00000003U
#define XSLCR_I2C_RST_CTRL_VAL			0x00000003U
#define XSLCR_SPI_RST_CTRL_VAL			0x0000000FU
#define XSLCR_UART_RST_CTRL_VAL			0x0000000FU
#define XSLCR_QSPI_RST_CTRL_VAL			0x00000003U
#define XSLCR_GPIO_RST_CTRL_VAL			0x00000001U
#define XSLCR_SMC_RST_CTRL_VAL			0x00000003U
#define XSLCR_OCM_RST_CTRL_VAL			0x00000001U
#define XSLCR_SDIO_RST_CTRL_VAL			0x00000033U
#define XSLCR_CAN_RST_CTRL_VAL			0x00000003U
/**************************** Type Definitions *******************************/

/* the following data type is used to hold a null terminated version string
 * consisting of the following format, "X.YYX"
 */


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/
/*
 * Performs reset operation to the ddr interface
 */
void XDdr_ResetHw(void);
/*
 * Map the ocm region to post bootrom state
 */
void XOcm_Remap(void);
/*
 * Performs the smc interface reset
 */
void XSmc_ResetHw(u32 BaseAddress);
/*
 * updates the MIO registers with reset values
 */
void XSlcr_MioWriteResetValues(void);
/*
 * updates the PLL and clock registers with reset values
 */
void XSlcr_PllWriteResetValues(void);
/*
 * Disables the level shifters
 */
void XSlcr_DisableLevelShifters(void);
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
