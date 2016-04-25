/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xparameters_ps.h
*
* This file contains the address definitions for the hard peripherals
* attached to the ARM Cortex A9 core.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------- -------- ---------------------------------------------------
* 1.00a ecm/sdm 02/01/10 Initial version
* 3.04a sdm     02/02/12 Removed some of the defines as they are being generated through
*                        driver tcl
* 5.0	pkp		01/16/15 Added interrupt ID definition of ttc for TEST APP
* </pre>
*
* @note
*
* None.
*
******************************************************************************/

#ifndef _XPARAMETERS_PS_H_
#define _XPARAMETERS_PS_H_

#ifdef __cplusplus
extern "C" {
#endif

/************************** Constant Definitions *****************************/

/*
 * This block contains constant declarations for the peripherals
 * within the hardblock
 */

/* Canonical definitions for DDR MEMORY */
#define XPAR_DDR_MEM_BASEADDR		0x00000000U
#define XPAR_DDR_MEM_HIGHADDR		0x3FFFFFFFU

/* Canonical definitions for Interrupts  */
#define XPAR_XUARTPS_0_INTR		XPS_UART0_INT_ID
#define XPAR_XUARTPS_1_INTR		XPS_UART1_INT_ID
#define XPAR_XUSBPS_0_INTR		XPS_USB0_INT_ID
#define XPAR_XUSBPS_1_INTR		XPS_USB1_INT_ID
#define XPAR_XIICPS_0_INTR		XPS_I2C0_INT_ID
#define XPAR_XIICPS_1_INTR		XPS_I2C1_INT_ID
#define XPAR_XSPIPS_0_INTR		XPS_SPI0_INT_ID
#define XPAR_XSPIPS_1_INTR		XPS_SPI1_INT_ID
#define XPAR_XCANPS_0_INTR		XPS_CAN0_INT_ID
#define XPAR_XCANPS_1_INTR		XPS_CAN1_INT_ID
#define XPAR_XGPIOPS_0_INTR		XPS_GPIO_INT_ID
#define XPAR_XEMACPS_0_INTR		XPS_GEM0_INT_ID
#define XPAR_XEMACPS_0_WAKE_INTR	XPS_GEM0_WAKE_INT_ID
#define XPAR_XEMACPS_1_INTR		XPS_GEM1_INT_ID
#define XPAR_XEMACPS_1_WAKE_INTR	XPS_GEM1_WAKE_INT_ID
#define XPAR_XSDIOPS_0_INTR		XPS_SDIO0_INT_ID
#define XPAR_XQSPIPS_0_INTR		XPS_QSPI_INT_ID
#define XPAR_XSDIOPS_1_INTR		XPS_SDIO1_INT_ID
#define XPAR_XWDTPS_0_INTR		XPS_WDT_INT_ID
#define XPAR_XDCFG_0_INTR		XPS_DVC_INT_ID
#define XPAR_SCUTIMER_INTR		XPS_SCU_TMR_INT_ID
#define XPAR_SCUWDT_INTR		XPS_SCU_WDT_INT_ID
#define XPAR_XTTCPS_0_INTR		XPS_TTC0_0_INT_ID
#define XPAR_XTTCPS_1_INTR		XPS_TTC0_1_INT_ID
#define XPAR_XTTCPS_2_INTR		XPS_TTC0_2_INT_ID
#define XPAR_XTTCPS_3_INTR		XPS_TTC1_0_INT_ID
#define XPAR_XTTCPS_4_INTR		XPS_TTC1_1_INT_ID
#define XPAR_XTTCPS_5_INTR		XPS_TTC1_2_INT_ID
#define XPAR_XDMAPS_0_FAULT_INTR	XPS_DMA0_ABORT_INT_ID
#define XPAR_XDMAPS_0_DONE_INTR_0	XPS_DMA0_INT_ID
#define XPAR_XDMAPS_0_DONE_INTR_1	XPS_DMA1_INT_ID
#define XPAR_XDMAPS_0_DONE_INTR_2	XPS_DMA2_INT_ID
#define XPAR_XDMAPS_0_DONE_INTR_3	XPS_DMA3_INT_ID
#define XPAR_XDMAPS_0_DONE_INTR_4	XPS_DMA4_INT_ID
#define XPAR_XDMAPS_0_DONE_INTR_5	XPS_DMA5_INT_ID
#define XPAR_XDMAPS_0_DONE_INTR_6	XPS_DMA6_INT_ID
#define XPAR_XDMAPS_0_DONE_INTR_7	XPS_DMA7_INT_ID


#define XPAR_XQSPIPS_0_LINEAR_BASEADDR	XPS_QSPI_LINEAR_BASEADDR
#define XPAR_XPARPORTPS_CTRL_BASEADDR	XPS_PARPORT_CRTL_BASEADDR



/* Canonical definitions for DMAC */


/* Canonical definitions for WDT */

/* Canonical definitions for SLCR */
#define XPAR_XSLCR_NUM_INSTANCES	1U
#define XPAR_XSLCR_0_DEVICE_ID		0U
#define XPAR_XSLCR_0_BASEADDR		XPS_SYS_CTRL_BASEADDR

/* Canonical definitions for SCU GIC */
#define XPAR_SCUGIC_NUM_INSTANCES	1U
#define XPAR_SCUGIC_SINGLE_DEVICE_ID	0U
#define XPAR_SCUGIC_CPU_BASEADDR	(XPS_SCU_PERIPH_BASE + 0x00000100U)
#define XPAR_SCUGIC_DIST_BASEADDR	(XPS_SCU_PERIPH_BASE + 0x00001000U)
#define XPAR_SCUGIC_ACK_BEFORE		0U

/* Canonical definitions for Global Timer */
#define XPAR_GLOBAL_TMR_NUM_INSTANCES	1U
#define XPAR_GLOBAL_TMR_DEVICE_ID	0U
#define XPAR_GLOBAL_TMR_BASEADDR	(XPS_SCU_PERIPH_BASE + 0x00000200U)
#define XPAR_GLOBAL_TMR_INTR		XPS_GLOBAL_TMR_INT_ID


/* Xilinx Parallel Flash Library (XilFlash) User Settings */
#define XPAR_AXI_EMC


#define XPAR_CPU_CORTEXA9_CORE_CLOCK_FREQ_HZ	XPAR_CPU_CORTEXA9_0_CPU_CLK_FREQ_HZ


/*
 * This block contains constant declarations for the peripherals
 * within the hardblock. These have been put for bacwards compatibilty
 */

#define XPS_PERIPHERAL_BASEADDR		0xE0000000U
#define XPS_UART0_BASEADDR		0xE0000000U
#define XPS_UART1_BASEADDR		0xE0001000U
#define XPS_USB0_BASEADDR		0xE0002000U
#define XPS_USB1_BASEADDR		0xE0003000U
#define XPS_I2C0_BASEADDR		0xE0004000U
#define XPS_I2C1_BASEADDR		0xE0005000U
#define XPS_SPI0_BASEADDR		0xE0006000U
#define XPS_SPI1_BASEADDR		0xE0007000U
#define XPS_CAN0_BASEADDR		0xE0008000U
#define XPS_CAN1_BASEADDR		0xE0009000U
#define XPS_GPIO_BASEADDR		0xE000A000U
#define XPS_GEM0_BASEADDR		0xE000B000U
#define XPS_GEM1_BASEADDR		0xE000C000U
#define XPS_QSPI_BASEADDR		0xE000D000U
#define XPS_PARPORT_CRTL_BASEADDR	0xE000E000U
#define XPS_SDIO0_BASEADDR		0xE0100000U
#define XPS_SDIO1_BASEADDR		0xE0101000U
#define XPS_IOU_BUS_CFG_BASEADDR	0xE0200000U
#define XPS_NAND_BASEADDR		0xE1000000U
#define XPS_PARPORT0_BASEADDR		0xE2000000U
#define XPS_PARPORT1_BASEADDR		0xE4000000U
#define XPS_QSPI_LINEAR_BASEADDR	0xFC000000U
#define XPS_SYS_CTRL_BASEADDR		0xF8000000U	/* AKA SLCR */
#define XPS_TTC0_BASEADDR		0xF8001000U
#define XPS_TTC1_BASEADDR		0xF8002000U
#define XPS_DMAC0_SEC_BASEADDR		0xF8003000U
#define XPS_DMAC0_NON_SEC_BASEADDR	0xF8004000U
#define XPS_WDT_BASEADDR		0xF8005000U
#define XPS_DDR_CTRL_BASEADDR		0xF8006000U
#define XPS_DEV_CFG_APB_BASEADDR	0xF8007000U
#define XPS_AFI0_BASEADDR		0xF8008000U
#define XPS_AFI1_BASEADDR		0xF8009000U
#define XPS_AFI2_BASEADDR		0xF800A000U
#define XPS_AFI3_BASEADDR		0xF800B000U
#define XPS_OCM_BASEADDR		0xF800C000U
#define XPS_EFUSE_BASEADDR		0xF800D000U
#define XPS_CORESIGHT_BASEADDR		0xF8800000U
#define XPS_TOP_BUS_CFG_BASEADDR	0xF8900000U
#define XPS_SCU_PERIPH_BASE		0xF8F00000U
#define XPS_L2CC_BASEADDR		0xF8F02000U
#define XPS_SAM_RAM_BASEADDR		0xFFFC0000U
#define XPS_FPGA_AXI_S0_BASEADDR	0x40000000U
#define XPS_FPGA_AXI_S1_BASEADDR	0x80000000U
#define XPS_IOU_S_SWITCH_BASEADDR	0xE0000000U
#define XPS_PERIPH_APB_BASEADDR		0xF8000000U

/* Shared Peripheral Interrupts (SPI) */
#define XPS_CORE_PARITY0_INT_ID		32U
#define XPS_CORE_PARITY1_INT_ID		33U
#define XPS_L2CC_INT_ID			34U
#define XPS_OCMINTR_INT_ID		35U
#define XPS_ECC_INT_ID			36U
#define XPS_PMU0_INT_ID			37U
#define XPS_PMU1_INT_ID			38U
#define XPS_SYSMON_INT_ID		39U
#define XPS_DVC_INT_ID			40U
#define XPS_WDT_INT_ID			41U
#define XPS_TTC0_0_INT_ID		42U
#define XPS_TTC0_1_INT_ID		43U
#define XPS_TTC0_2_INT_ID 		44U
#define XPS_DMA0_ABORT_INT_ID		45U
#define XPS_DMA0_INT_ID			46U
#define XPS_DMA1_INT_ID			47U
#define XPS_DMA2_INT_ID			48U
#define XPS_DMA3_INT_ID			49U
#define XPS_SMC_INT_ID			50U
#define XPS_QSPI_INT_ID			51U
#define XPS_GPIO_INT_ID			52U
#define XPS_USB0_INT_ID			53U
#define XPS_GEM0_INT_ID			54U
#define XPS_GEM0_WAKE_INT_ID		55U
#define XPS_SDIO0_INT_ID		56U
#define XPS_I2C0_INT_ID			57U
#define XPS_SPI0_INT_ID			58U
#define XPS_UART0_INT_ID		59U
#define XPS_CAN0_INT_ID			60U
#define XPS_FPGA0_INT_ID		61U
#define XPS_FPGA1_INT_ID		62U
#define XPS_FPGA2_INT_ID		63U
#define XPS_FPGA3_INT_ID		64U
#define XPS_FPGA4_INT_ID		65U
#define XPS_FPGA5_INT_ID		66U
#define XPS_FPGA6_INT_ID		67U
#define XPS_FPGA7_INT_ID		68U
#define XPS_TTC1_0_INT_ID		69U
#define XPS_TTC1_1_INT_ID		70U
#define XPS_TTC1_2_INT_ID		71U
#define XPS_DMA4_INT_ID			72U
#define XPS_DMA5_INT_ID			73U
#define XPS_DMA6_INT_ID			74U
#define XPS_DMA7_INT_ID			75U
#define XPS_USB1_INT_ID			76U
#define XPS_GEM1_INT_ID			77U
#define XPS_GEM1_WAKE_INT_ID		78U
#define XPS_SDIO1_INT_ID		79U
#define XPS_I2C1_INT_ID			80U
#define XPS_SPI1_INT_ID			81U
#define XPS_UART1_INT_ID		82U
#define XPS_CAN1_INT_ID			83U
#define XPS_FPGA8_INT_ID		84U
#define XPS_FPGA9_INT_ID		85U
#define XPS_FPGA10_INT_ID		86U
#define XPS_FPGA11_INT_ID		87U
#define XPS_FPGA12_INT_ID		88U
#define XPS_FPGA13_INT_ID		89U
#define XPS_FPGA14_INT_ID		90U
#define XPS_FPGA15_INT_ID		91U

/* Private Peripheral Interrupts (PPI) */
#define XPS_GLOBAL_TMR_INT_ID		27U	/* SCU Global Timer interrupt */
#define XPS_FIQ_INT_ID			28U	/* FIQ from FPGA fabric */
#define XPS_SCU_TMR_INT_ID		29U	/* SCU Private Timer interrupt */
#define XPS_SCU_WDT_INT_ID		30U	/* SCU Private WDT interrupt */
#define XPS_IRQ_INT_ID			31U	/* IRQ from FPGA fabric */


/* REDEFINES for TEST APP */
/* Definitions for UART */
#define XPAR_PS7_UART_0_INTR		XPS_UART0_INT_ID
#define XPAR_PS7_UART_1_INTR		XPS_UART1_INT_ID
#define XPAR_PS7_USB_0_INTR		XPS_USB0_INT_ID
#define XPAR_PS7_USB_1_INTR		XPS_USB1_INT_ID
#define XPAR_PS7_I2C_0_INTR		XPS_I2C0_INT_ID
#define XPAR_PS7_I2C_1_INTR		XPS_I2C1_INT_ID
#define XPAR_PS7_SPI_0_INTR		XPS_SPI0_INT_ID
#define XPAR_PS7_SPI_1_INTR		XPS_SPI1_INT_ID
#define XPAR_PS7_CAN_0_INTR		XPS_CAN0_INT_ID
#define XPAR_PS7_CAN_1_INTR		XPS_CAN1_INT_ID
#define XPAR_PS7_GPIO_0_INTR		XPS_GPIO_INT_ID
#define XPAR_PS7_ETHERNET_0_INTR	XPS_GEM0_INT_ID
#define XPAR_PS7_ETHERNET_0_WAKE_INTR	XPS_GEM0_WAKE_INT_ID
#define XPAR_PS7_ETHERNET_1_INTR	XPS_GEM1_INT_ID
#define XPAR_PS7_ETHERNET_1_WAKE_INTR	XPS_GEM1_WAKE_INT_ID
#define XPAR_PS7_QSPI_0_INTR		XPS_QSPI_INT_ID
#define XPAR_PS7_WDT_0_INTR		XPS_WDT_INT_ID
#define XPAR_PS7_SCUWDT_0_INTR		XPS_SCU_WDT_INT_ID
#define XPAR_PS7_SCUTIMER_0_INTR	XPS_SCU_TMR_INT_ID
#define XPAR_PS7_XADC_0_INTR		XPS_SYSMON_INT_ID
#define XPAR_PS7_TTC_0_INTR         XPS_TTC0_0_INT_ID
#define XPAR_PS7_TTC_1_INTR         XPS_TTC0_1_INT_ID
#define XPAR_PS7_TTC_2_INTR         XPS_TTC0_2_INT_ID
#define XPAR_PS7_TTC_3_INTR         XPS_TTC1_0_INT_ID
#define XPAR_PS7_TTC_4_INTR         XPS_TTC1_1_INT_ID
#define XPAR_PS7_TTC_5_INTR         XPS_TTC1_2_INT_ID

#define XPAR_XADCPS_INT_ID		XPS_SYSMON_INT_ID

/* For backwards compatibilty */
#define XPAR_XUARTPS_0_CLOCK_HZ		XPAR_XUARTPS_0_UART_CLK_FREQ_HZ
#define XPAR_XUARTPS_1_CLOCK_HZ		XPAR_XUARTPS_1_UART_CLK_FREQ_HZ
#define XPAR_XTTCPS_0_CLOCK_HZ		XPAR_XTTCPS_0_TTC_CLK_FREQ_HZ
#define XPAR_XTTCPS_1_CLOCK_HZ		XPAR_XTTCPS_1_TTC_CLK_FREQ_HZ
#define XPAR_XTTCPS_2_CLOCK_HZ		XPAR_XTTCPS_2_TTC_CLK_FREQ_HZ
#define XPAR_XTTCPS_3_CLOCK_HZ		XPAR_XTTCPS_3_TTC_CLK_FREQ_HZ
#define XPAR_XTTCPS_4_CLOCK_HZ		XPAR_XTTCPS_4_TTC_CLK_FREQ_HZ
#define XPAR_XTTCPS_5_CLOCK_HZ		XPAR_XTTCPS_5_TTC_CLK_FREQ_HZ
#define XPAR_XIICPS_0_CLOCK_HZ		XPAR_XIICPS_0_I2C_CLK_FREQ_HZ
#define XPAR_XIICPS_1_CLOCK_HZ		XPAR_XIICPS_1_I2C_CLK_FREQ_HZ

#define XPAR_XQSPIPS_0_CLOCK_HZ		XPAR_XQSPIPS_0_QSPI_CLK_FREQ_HZ

#ifdef XPAR_CPU_CORTEXA9_0_CPU_CLK_FREQ_HZ
#define XPAR_CPU_CORTEXA9_CORE_CLOCK_FREQ_HZ	XPAR_CPU_CORTEXA9_0_CPU_CLK_FREQ_HZ
#endif

#ifdef XPAR_CPU_CORTEXA9_1_CPU_CLK_FREQ_HZ
#define XPAR_CPU_CORTEXA9_CORE_CLOCK_FREQ_HZ	XPAR_CPU_CORTEXA9_1_CPU_CLK_FREQ_HZ
#endif

#define XPAR_SCUTIMER_DEVICE_ID		0U
#define XPAR_SCUWDT_DEVICE_ID		0U


#ifdef __cplusplus
}
#endif

#endif /* protection macro */
