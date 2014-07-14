/******************************************************************************
*
* (c) Copyright 2010-2013  Xilinx, Inc. All rights reserved.
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
#define XPAR_DDR_MEM_BASEADDR		0x00000000
#define XPAR_DDR_MEM_HIGHADDR		0x3FFFFFFF

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
#define XPAR_XSLCR_NUM_INSTANCES	1
#define XPAR_XSLCR_0_DEVICE_ID		0
#define XPAR_XSLCR_0_BASEADDR		XPS_SYS_CTRL_BASEADDR

/* Canonical definitions for SCU GIC */
#define XPAR_SCUGIC_NUM_INSTANCES	1
#define XPAR_SCUGIC_SINGLE_DEVICE_ID	0
#define XPAR_SCUGIC_CPU_BASEADDR	(XPS_SCU_PERIPH_BASE + 0x0100)
#define XPAR_SCUGIC_DIST_BASEADDR	(XPS_SCU_PERIPH_BASE + 0x1000)
#define XPAR_SCUGIC_ACK_BEFORE		0

/* Canonical definitions for Global Timer */
#define XPAR_GLOBAL_TMR_NUM_INSTANCES	1
#define XPAR_GLOBAL_TMR_DEVICE_ID	0
#define XPAR_GLOBAL_TMR_BASEADDR	(XPS_SCU_PERIPH_BASE + 0x200)
#define XPAR_GLOBAL_TMR_INTR		XPS_GLOBAL_TMR_INT_ID


/* Xilinx Parallel Flash Library (XilFlash) User Settings */
#define XPAR_AXI_EMC


#define XPAR_CPU_CORTEXA9_CORE_CLOCK_FREQ_HZ	XPAR_CPU_CORTEXA9_0_CPU_CLK_FREQ_HZ


/*
 * This block contains constant declarations for the peripherals
 * within the hardblock. These have been put for bacwards compatibilty
 */

#define XPS_PERIPHERAL_BASEADDR		0xE0000000
#define XPS_UART0_BASEADDR		0xE0000000
#define XPS_UART1_BASEADDR		0xE0001000
#define XPS_USB0_BASEADDR		0xE0002000
#define XPS_USB1_BASEADDR		0xE0003000
#define XPS_I2C0_BASEADDR		0xE0004000
#define XPS_I2C1_BASEADDR		0xE0005000
#define XPS_SPI0_BASEADDR		0xE0006000
#define XPS_SPI1_BASEADDR		0xE0007000
#define XPS_CAN0_BASEADDR		0xE0008000
#define XPS_CAN1_BASEADDR		0xE0009000
#define XPS_GPIO_BASEADDR		0xE000A000
#define XPS_GEM0_BASEADDR		0xE000B000
#define XPS_GEM1_BASEADDR		0xE000C000
#define XPS_QSPI_BASEADDR		0xE000D000
#define XPS_PARPORT_CRTL_BASEADDR	0xE000E000
#define XPS_SDIO0_BASEADDR		0xE0100000
#define XPS_SDIO1_BASEADDR		0xE0101000
#define XPS_IOU_BUS_CFG_BASEADDR	0xE0200000
#define XPS_NAND_BASEADDR		0xE1000000
#define XPS_PARPORT0_BASEADDR		0xE2000000
#define XPS_PARPORT1_BASEADDR		0xE4000000
#define XPS_QSPI_LINEAR_BASEADDR	0xFC000000
#define XPS_SYS_CTRL_BASEADDR		0xF8000000	/* AKA SLCR */
#define XPS_TTC0_BASEADDR		0xF8001000
#define XPS_TTC1_BASEADDR		0xF8002000
#define XPS_DMAC0_SEC_BASEADDR		0xF8003000
#define XPS_DMAC0_NON_SEC_BASEADDR	0xF8004000
#define XPS_WDT_BASEADDR		0xF8005000
#define XPS_DDR_CTRL_BASEADDR		0xF8006000
#define XPS_DEV_CFG_APB_BASEADDR	0xF8007000
#define XPS_AFI0_BASEADDR		0xF8008000
#define XPS_AFI1_BASEADDR		0xF8009000
#define XPS_AFI2_BASEADDR		0xF800A000
#define XPS_AFI3_BASEADDR		0xF800B000
#define XPS_OCM_BASEADDR		0xF800C000
#define XPS_EFUSE_BASEADDR		0xF800D000
#define XPS_CORESIGHT_BASEADDR		0xF8800000
#define XPS_TOP_BUS_CFG_BASEADDR	0xF8900000
#define XPS_SCU_PERIPH_BASE		0xF8F00000
#define XPS_L2CC_BASEADDR		0xF8F02000
#define XPS_SAM_RAM_BASEADDR		0xFFFC0000
#define XPS_FPGA_AXI_S0_BASEADDR	0x40000000
#define XPS_FPGA_AXI_S1_BASEADDR	0x80000000
#define XPS_IOU_S_SWITCH_BASEADDR	0xE0000000
#define XPS_PERIPH_APB_BASEADDR		0xF8000000

/* Shared Peripheral Interrupts (SPI) */
#define XPS_CORE_PARITY0_INT_ID		32
#define XPS_CORE_PARITY1_INT_ID		33
#define XPS_L2CC_INT_ID			34
#define XPS_OCMINTR_INT_ID		35
#define XPS_ECC_INT_ID			36
#define XPS_PMU0_INT_ID			37
#define XPS_PMU1_INT_ID			38
#define XPS_SYSMON_INT_ID		39
#define XPS_DVC_INT_ID			40
#define XPS_WDT_INT_ID			41
#define XPS_TTC0_0_INT_ID		42
#define XPS_TTC0_1_INT_ID		43
#define XPS_TTC0_2_INT_ID 		44
#define XPS_DMA0_ABORT_INT_ID		45
#define XPS_DMA0_INT_ID			46
#define XPS_DMA1_INT_ID			47
#define XPS_DMA2_INT_ID			48
#define XPS_DMA3_INT_ID			49
#define XPS_SMC_INT_ID			50
#define XPS_QSPI_INT_ID			51
#define XPS_GPIO_INT_ID			52
#define XPS_USB0_INT_ID			53
#define XPS_GEM0_INT_ID			54
#define XPS_GEM0_WAKE_INT_ID		55
#define XPS_SDIO0_INT_ID		56
#define XPS_I2C0_INT_ID			57
#define XPS_SPI0_INT_ID			58
#define XPS_UART0_INT_ID		59
#define XPS_CAN0_INT_ID			60
#define XPS_FPGA0_INT_ID		61
#define XPS_FPGA1_INT_ID		62
#define XPS_FPGA2_INT_ID		63
#define XPS_FPGA3_INT_ID		64
#define XPS_FPGA4_INT_ID		65
#define XPS_FPGA5_INT_ID		66
#define XPS_FPGA6_INT_ID		67
#define XPS_FPGA7_INT_ID		68
#define XPS_TTC1_0_INT_ID		69
#define XPS_TTC1_1_INT_ID		70
#define XPS_TTC1_2_INT_ID		71
#define XPS_DMA4_INT_ID			72
#define XPS_DMA5_INT_ID			73
#define XPS_DMA6_INT_ID			74
#define XPS_DMA7_INT_ID			75
#define XPS_USB1_INT_ID			76
#define XPS_GEM1_INT_ID			77
#define XPS_GEM1_WAKE_INT_ID		78
#define XPS_SDIO1_INT_ID		79
#define XPS_I2C1_INT_ID			80
#define XPS_SPI1_INT_ID			81
#define XPS_UART1_INT_ID		82
#define XPS_CAN1_INT_ID			83
#define XPS_FPGA8_INT_ID		84
#define XPS_FPGA9_INT_ID		85
#define XPS_FPGA10_INT_ID		86
#define XPS_FPGA11_INT_ID		87
#define XPS_FPGA12_INT_ID		88
#define XPS_FPGA13_INT_ID		89
#define XPS_FPGA14_INT_ID		90
#define XPS_FPGA15_INT_ID		91

/* Private Peripheral Interrupts (PPI) */
#define XPS_GLOBAL_TMR_INT_ID		27	/* SCU Global Timer interrupt */
#define XPS_FIQ_INT_ID			28	/* FIQ from FPGA fabric */
#define XPS_SCU_TMR_INT_ID		29	/* SCU Private Timer interrupt */
#define XPS_SCU_WDT_INT_ID		30	/* SCU Private WDT interrupt */
#define XPS_IRQ_INT_ID			31	/* IRQ from FPGA fabric */


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

#define XPAR_SCUTIMER_DEVICE_ID		0
#define XPAR_SCUWDT_DEVICE_ID		0


#ifdef __cplusplus
}
#endif

#endif /* protection macro */
