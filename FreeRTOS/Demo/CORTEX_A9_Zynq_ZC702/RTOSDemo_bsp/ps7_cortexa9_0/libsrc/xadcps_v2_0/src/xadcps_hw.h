/******************************************************************************
*
* (c) Copyright 2011-2013 Xilinx, Inc. All rights reserved.
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
/****************************************************************************/
/**
*
* @file xadcps_hw.h
*
* This header file contains identifiers and basic driver functions (or
* macros) that can be used to access the XADC device through the Device
* Config Interface of the Zynq.
*
*
* Refer to the device specification for more information about this driver.
*
* @note	 None.
*
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- -----  -------- -----------------------------------------------------
* 1.00a bss    12/22/11 First release based on the XPS/AXI xadc driver
* 1.03a bss    11/01/13 Modified macros to use correct Register offsets
*			CR#749687
*
* </pre>
*
*****************************************************************************/
#ifndef XADCPS_HW_H /* Prevent circular inclusions */
#define XADCPS_HW_H /* by using protection macros  */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions ****************************/


/**@name Register offsets of XADC in the Device Config
 *
 * The following constants provide access to each of the registers of the
 * XADC device.
 * @{
 */

#define XADCPS_CFG_OFFSET	 0x00 /**< Configuration Register */
#define XADCPS_INT_STS_OFFSET	 0x04 /**< Interrupt Status Register */
#define XADCPS_INT_MASK_OFFSET	 0x08 /**< Interrupt Mask Register */
#define XADCPS_MSTS_OFFSET	 0x0C /**< Misc status register */
#define XADCPS_CMDFIFO_OFFSET	 0x10 /**< Command FIFO Register */
#define XADCPS_RDFIFO_OFFSET	 0x14 /**< Read FIFO Register */
#define XADCPS_MCTL_OFFSET	 0x18 /**< Misc control register */

/* @} */





/** @name XADC Config Register Bit definitions
  * @{
 */
#define XADCPS_CFG_ENABLE_MASK	 0x80000000 /**< Enable access from PS mask */
#define XADCPS_CFG_CFIFOTH_MASK  0x00F00000 /**< Command FIFO Threshold mask */
#define XADCPS_CFG_DFIFOTH_MASK  0x000F0000 /**< Data FIFO Threshold mask */
#define XADCPS_CFG_WEDGE_MASK	 0x00002000 /**< Write Edge Mask */
#define XADCPS_CFG_REDGE_MASK	 0x00001000 /**< Read Edge Mask */
#define XADCPS_CFG_TCKRATE_MASK  0x00000300 /**< Clock freq control */
#define XADCPS_CFG_IGAP_MASK	 0x0000001F /**< Idle Gap between
						* successive commands */
/* @} */


/** @name XADC Interrupt Status/Mask Register Bit definitions
  *
  * The definitions are same for the Interrupt Status Register and
  * Interrupt Mask Register. They are defined only once.
  * @{
 */
#define XADCPS_INTX_ALL_MASK   	   0x000003FF /**< Alarm Signals Mask  */
#define XADCPS_INTX_CFIFO_LTH_MASK 0x00000200 /**< CMD FIFO less than threshold */
#define XADCPS_INTX_DFIFO_GTH_MASK 0x00000100 /**< Data FIFO greater than threshold */
#define XADCPS_INTX_OT_MASK	   0x00000080 /**< Over temperature Alarm Status */
#define XADCPS_INTX_ALM_ALL_MASK   0x0000007F /**< Alarm Signals Mask  */
#define XADCPS_INTX_ALM6_MASK	   0x00000040 /**< Alarm 6 Mask  */
#define XADCPS_INTX_ALM5_MASK	   0x00000020 /**< Alarm 5 Mask  */
#define XADCPS_INTX_ALM4_MASK	   0x00000010 /**< Alarm 4 Mask  */
#define XADCPS_INTX_ALM3_MASK	   0x00000008 /**< Alarm 3 Mask  */
#define XADCPS_INTX_ALM2_MASK	   0x00000004 /**< Alarm 2 Mask  */
#define XADCPS_INTX_ALM1_MASK	   0x00000002 /**< Alarm 1 Mask  */
#define XADCPS_INTX_ALM0_MASK	   0x00000001 /**< Alarm 0 Mask  */

/* @} */


/** @name XADC Miscellaneous Register Bit definitions
  * @{
 */
#define XADCPS_MSTS_CFIFO_LVL_MASK  0x000F0000 /**< Command FIFO Level mask */
#define XADCPS_MSTS_DFIFO_LVL_MASK  0x0000F000 /**< Data FIFO Level Mask  */
#define XADCPS_MSTS_CFIFOF_MASK     0x00000800 /**< Command FIFO Full Mask  */
#define XADCPS_MSTS_CFIFOE_MASK     0x00000400 /**< Command FIFO Empty Mask  */
#define XADCPS_MSTS_DFIFOF_MASK     0x00000200 /**< Data FIFO Full Mask  */
#define XADCPS_MSTS_DFIFOE_MASK     0x00000100 /**< Data FIFO Empty Mask  */
#define XADCPS_MSTS_OT_MASK	    0x00000080 /**< Over Temperature Mask */
#define XADCPS_MSTS_ALM_MASK	    0x0000007F /**< Alarms Mask  */
/* @} */


/** @name XADC Miscellaneous Control Register Bit definitions
  * @{
 */
#define XADCPS_MCTL_RESET_MASK      0x00000010 /**< Reset XADC */
#define XADCPS_MCTL_FLUSH_MASK      0x00000001 /**< Flush the FIFOs */
/* @} */


/**@name Internal Register offsets of the XADC
 *
 * The following constants provide access to each of the internal registers of
 * the XADC device.
 * @{
 */

/*
 * XADC Internal Channel Registers
 */
#define XADCPS_TEMP_OFFSET		  0x00 /**< On-chip Temperature Reg */
#define XADCPS_VCCINT_OFFSET		  0x01 /**< On-chip VCCINT Data Reg */
#define XADCPS_VCCAUX_OFFSET		  0x02 /**< On-chip VCCAUX Data Reg */
#define XADCPS_VPVN_OFFSET		  0x03 /**< ADC out of VP/VN	   */
#define XADCPS_VREFP_OFFSET		  0x04 /**< On-chip VREFP Data Reg */
#define XADCPS_VREFN_OFFSET		  0x05 /**< On-chip VREFN Data Reg */
#define XADCPS_VBRAM_OFFSET		  0x06 /**< On-chip VBRAM , 7 Series */
#define XADCPS_ADC_A_SUPPLY_CALIB_OFFSET  0x08 /**< ADC A Supply Offset Reg */
#define XADCPS_ADC_A_OFFSET_CALIB_OFFSET  0x09 /**< ADC A Offset Data Reg */
#define XADCPS_ADC_A_GAINERR_CALIB_OFFSET 0x0A /**< ADC A Gain Error Reg  */
#define XADCPS_VCCPINT_OFFSET		  0x0D /**< On-chip VCCPINT Reg, Zynq */
#define XADCPS_VCCPAUX_OFFSET		  0x0E /**< On-chip VCCPAUX Reg, Zynq */
#define XADCPS_VCCPDRO_OFFSET		  0x0F /**< On-chip VCCPDRO Reg, Zynq */

/*
 * XADC External Channel Registers
 */
#define XADCPS_AUX00_OFFSET	0x10 /**< ADC out of VAUXP0/VAUXN0 */
#define XADCPS_AUX01_OFFSET	0x11 /**< ADC out of VAUXP1/VAUXN1 */
#define XADCPS_AUX02_OFFSET	0x12 /**< ADC out of VAUXP2/VAUXN2 */
#define XADCPS_AUX03_OFFSET	0x13 /**< ADC out of VAUXP3/VAUXN3 */
#define XADCPS_AUX04_OFFSET	0x14 /**< ADC out of VAUXP4/VAUXN4 */
#define XADCPS_AUX05_OFFSET	0x15 /**< ADC out of VAUXP5/VAUXN5 */
#define XADCPS_AUX06_OFFSET	0x16 /**< ADC out of VAUXP6/VAUXN6 */
#define XADCPS_AUX07_OFFSET	0x17 /**< ADC out of VAUXP7/VAUXN7 */
#define XADCPS_AUX08_OFFSET	0x18 /**< ADC out of VAUXP8/VAUXN8 */
#define XADCPS_AUX09_OFFSET	0x19 /**< ADC out of VAUXP9/VAUXN9 */
#define XADCPS_AUX10_OFFSET	0x1A /**< ADC out of VAUXP10/VAUXN10 */
#define XADCPS_AUX11_OFFSET	0x1B /**< ADC out of VAUXP11/VAUXN11 */
#define XADCPS_AUX12_OFFSET	0x1C /**< ADC out of VAUXP12/VAUXN12 */
#define XADCPS_AUX13_OFFSET	0x1D /**< ADC out of VAUXP13/VAUXN13 */
#define XADCPS_AUX14_OFFSET	0x1E /**< ADC out of VAUXP14/VAUXN14 */
#define XADCPS_AUX15_OFFSET	0x1F /**< ADC out of VAUXP15/VAUXN15 */

/*
 * XADC Registers for Maximum/Minimum data captured for the
 * on chip Temperature/VCCINT/VCCAUX data.
 */
#define XADCPS_MAX_TEMP_OFFSET		0x20 /**< Max Temperature Reg */
#define XADCPS_MAX_VCCINT_OFFSET	0x21 /**< Max VCCINT Register */
#define XADCPS_MAX_VCCAUX_OFFSET	0x22 /**< Max VCCAUX Register */
#define XADCPS_MAX_VCCBRAM_OFFSET	0x23 /**< Max BRAM Register, 7 series */
#define XADCPS_MIN_TEMP_OFFSET		0x24 /**< Min Temperature Reg */
#define XADCPS_MIN_VCCINT_OFFSET	0x25 /**< Min VCCINT Register */
#define XADCPS_MIN_VCCAUX_OFFSET	0x26 /**< Min VCCAUX Register */
#define XADCPS_MIN_VCCBRAM_OFFSET	0x27 /**< Min BRAM Register, 7 series */
#define XADCPS_MAX_VCCPINT_OFFSET	0x28 /**< Max VCCPINT Register, Zynq */
#define XADCPS_MAX_VCCPAUX_OFFSET	0x29 /**< Max VCCPAUX Register, Zynq */
#define XADCPS_MAX_VCCPDRO_OFFSET	0x2A /**< Max VCCPDRO Register, Zynq */
#define XADCPS_MIN_VCCPINT_OFFSET	0x2C /**< Min VCCPINT Register, Zynq */
#define XADCPS_MIN_VCCPAUX_OFFSET	0x2D /**< Min VCCPAUX Register, Zynq */
#define XADCPS_MIN_VCCPDRO_OFFSET	0x2E /**< Min VCCPDRO Register,Zynq */
 /* Undefined 0x2F to 0x3E */
#define XADCPS_FLAG_OFFSET		0x3F /**< Flag Register */

/*
 * XADC Configuration Registers
 */
#define XADCPS_CFR0_OFFSET	0x40	/**< Configuration Register 0 */
#define XADCPS_CFR1_OFFSET	0x41	/**< Configuration Register 1 */
#define XADCPS_CFR2_OFFSET	0x42	/**< Configuration Register 2 */

/* Test Registers 0x43 to 0x47 */

/*
 * XADC Sequence Registers
 */
#define XADCPS_SEQ00_OFFSET	0x48 /**< Seq Reg 00 Adc Channel Selection */
#define XADCPS_SEQ01_OFFSET	0x49 /**< Seq Reg 01 Adc Channel Selection */
#define XADCPS_SEQ02_OFFSET	0x4A /**< Seq Reg 02 Adc Average Enable */
#define XADCPS_SEQ03_OFFSET	0x4B /**< Seq Reg 03 Adc Average Enable */
#define XADCPS_SEQ04_OFFSET	0x4C /**< Seq Reg 04 Adc Input Mode Select */
#define XADCPS_SEQ05_OFFSET	0x4D /**< Seq Reg 05 Adc Input Mode Select */
#define XADCPS_SEQ06_OFFSET	0x4E /**< Seq Reg 06 Adc Acquisition Select */
#define XADCPS_SEQ07_OFFSET	0x4F /**< Seq Reg 07 Adc Acquisition Select */

/*
 * XADC Alarm Threshold/Limit Registers (ATR)
 */
#define XADCPS_ATR_TEMP_UPPER_OFFSET	0x50 /**< Temp Upper Alarm Register */
#define XADCPS_ATR_VCCINT_UPPER_OFFSET	0x51 /**< VCCINT Upper Alarm Reg */
#define XADCPS_ATR_VCCAUX_UPPER_OFFSET	0x52 /**< VCCAUX Upper Alarm Reg */
#define XADCPS_ATR_OT_UPPER_OFFSET	0x53 /**< Over Temp Upper Alarm Reg */
#define XADCPS_ATR_TEMP_LOWER_OFFSET	0x54 /**< Temp Lower Alarm Register */
#define XADCPS_ATR_VCCINT_LOWER_OFFSET	0x55 /**< VCCINT Lower Alarm Reg */
#define XADCPS_ATR_VCCAUX_LOWER_OFFSET	0x56 /**< VCCAUX Lower Alarm Reg */
#define XADCPS_ATR_OT_LOWER_OFFSET	0x57 /**< Over Temp Lower Alarm Reg */
#define XADCPS_ATR_VBRAM_UPPER_OFFSET	0x58 /**< VBRAM Upper Alarm, 7 series */
#define XADCPS_ATR_VCCPINT_UPPER_OFFSET	0x59 /**< VCCPINT Upper Alarm, Zynq */
#define XADCPS_ATR_VCCPAUX_UPPER_OFFSET	0x5A /**< VCCPAUX Upper Alarm, Zynq */
#define XADCPS_ATR_VCCPDRO_UPPER_OFFSET	0x5B /**< VCCPDRO Upper Alarm, Zynq */
#define XADCPS_ATR_VBRAM_LOWER_OFFSET	0x5C /**< VRBAM Lower Alarm, 7 Series */
#define XADCPS_ATR_VCCPINT_LOWER_OFFSET	0x5D /**< VCCPINT Lower Alarm, Zynq */
#define XADCPS_ATR_VCCPAUX_LOWER_OFFSET	0x5E /**< VCCPAUX Lower Alarm, Zynq */
#define XADCPS_ATR_VCCPDRO_LOWER_OFFSET	0x5F /**< VCCPDRO Lower Alarm, Zynq */

/* Undefined 0x60 to 0x7F */

/*@}*/



/**
 * @name Configuration Register 0 (CFR0) mask(s)
 * @{
 */
#define XADCPS_CFR0_CAL_AVG_MASK	0x8000 /**< Averaging enable Mask */
#define XADCPS_CFR0_AVG_VALID_MASK	0x3000 /**< Averaging bit Mask */
#define XADCPS_CFR0_AVG1_MASK		0x0000 /**< No Averaging */
#define XADCPS_CFR0_AVG16_MASK		0x1000 /**< Average 16 samples */
#define XADCPS_CFR0_AVG64_MASK	 	0x2000 /**< Average 64 samples */
#define XADCPS_CFR0_AVG256_MASK 	0x3000 /**< Average 256 samples */
#define XADCPS_CFR0_AVG_SHIFT	 	12     /**< Averaging bits shift */
#define XADCPS_CFR0_MUX_MASK	 	0x0800 /**< External Mask Enable */
#define XADCPS_CFR0_DU_MASK	 	0x0400 /**< Bipolar/Unipolar mode */
#define XADCPS_CFR0_EC_MASK	 	0x0200 /**< Event driven/
						 *  Continuous mode selection
						 */
#define XADCPS_CFR0_ACQ_MASK	 	0x0100 /**< Add acquisition by 6 ADCCLK */
#define XADCPS_CFR0_CHANNEL_MASK	0x001F /**< Channel number bit Mask */

/*@}*/

/**
 * @name Configuration Register 1 (CFR1) mask(s)
 * @{
 */
#define XADCPS_CFR1_SEQ_VALID_MASK	  0xF000 /**< Sequence bit Mask */
#define XADCPS_CFR1_SEQ_SAFEMODE_MASK	  0x0000 /**< Default Safe Mode */
#define XADCPS_CFR1_SEQ_ONEPASS_MASK	  0x1000 /**< Onepass through Seq */
#define XADCPS_CFR1_SEQ_CONTINPASS_MASK	     0x2000 /**< Continuous Cycling Seq */
#define XADCPS_CFR1_SEQ_SINGCHAN_MASK	     0x3000 /**< Single channel - No Seq */
#define XADCPS_CFR1_SEQ_SIMUL_SAMPLING_MASK  0x4000 /**< Simulataneous Sampling Mask */
#define XADCPS_CFR1_SEQ_INDEPENDENT_MASK  0x8000 /**< Independent Mode */
#define XADCPS_CFR1_SEQ_SHIFT		  12     /**< Sequence bit shift */
#define XADCPS_CFR1_ALM_VCCPDRO_MASK	  0x0800 /**< Alm 6 - VCCPDRO, Zynq  */
#define XADCPS_CFR1_ALM_VCCPAUX_MASK	  0x0400 /**< Alm 5 - VCCPAUX, Zynq */
#define XADCPS_CFR1_ALM_VCCPINT_MASK	  0x0200 /**< Alm 4 - VCCPINT, Zynq */
#define XADCPS_CFR1_ALM_VBRAM_MASK	  0x0100 /**< Alm 3 - VBRAM, 7 series */
#define XADCPS_CFR1_CAL_VALID_MASK	  0x00F0 /**< Valid Calibration Mask */
#define XADCPS_CFR1_CAL_PS_GAIN_OFFSET_MASK  0x0080 /**< Calibration 3 -Power
							Supply Gain/Offset
							Enable */
#define XADCPS_CFR1_CAL_PS_OFFSET_MASK	  0x0040 /**< Calibration 2 -Power
							Supply Offset Enable */
#define XADCPS_CFR1_CAL_ADC_GAIN_OFFSET_MASK 0x0020 /**< Calibration 1 -ADC Gain
							Offset Enable */
#define XADCPS_CFR1_CAL_ADC_OFFSET_MASK	 0x0010 /**< Calibration 0 -ADC Offset
							Enable */
#define XADCPS_CFR1_CAL_DISABLE_MASK	0x0000 /**< No Calibration */
#define XADCPS_CFR1_ALM_ALL_MASK	0x0F0F /**< Mask for all alarms */
#define XADCPS_CFR1_ALM_VCCAUX_MASK	0x0008 /**< Alarm 2 - VCCAUX Enable */
#define XADCPS_CFR1_ALM_VCCINT_MASK	0x0004 /**< Alarm 1 - VCCINT Enable */
#define XADCPS_CFR1_ALM_TEMP_MASK	0x0002 /**< Alarm 0 - Temperature */
#define XADCPS_CFR1_OT_MASK		0x0001 /**< Over Temperature Enable */

/*@}*/

/**
 * @name Configuration Register 2 (CFR2) mask(s)
 * @{
 */
#define XADCPS_CFR2_CD_VALID_MASK	0xFF00  /**<Clock Divisor bit Mask   */
#define XADCPS_CFR2_CD_SHIFT		8	/**<Num of shift on division */
#define XADCPS_CFR2_CD_MIN		8	/**<Minimum value of divisor */
#define XADCPS_CFR2_CD_MAX		255	/**<Maximum value of divisor */

#define XADCPS_CFR2_CD_MIN		8	/**<Minimum value of divisor */
#define XADCPS_CFR2_PD_MASK		0x0030	/**<Power Down Mask */
#define XADCPS_CFR2_PD_XADC_MASK	0x0030	/**<Power Down XADC Mask */
#define XADCPS_CFR2_PD_ADC1_MASK	0x0020	/**<Power Down ADC1 Mask */
#define XADCPS_CFR2_PD_SHIFT		4	/**<Power Down Shift */
/*@}*/

/**
 * @name Sequence Register (SEQ) Bit Definitions
 * @{
 */
#define XADCPS_SEQ_CH_CALIB	0x00000001 /**< ADC Calibration Channel */
#define XADCPS_SEQ_CH_VCCPINT	0x00000020 /**< VCCPINT, Zynq Only */
#define XADCPS_SEQ_CH_VCCPAUX	0x00000040 /**< VCCPAUX, Zynq Only */
#define XADCPS_SEQ_CH_VCCPDRO	0x00000080 /**< VCCPDRO, Zynq Only */
#define XADCPS_SEQ_CH_TEMP	0x00000100 /**< On Chip Temperature Channel */
#define XADCPS_SEQ_CH_VCCINT	0x00000200 /**< VCCINT Channel */
#define XADCPS_SEQ_CH_VCCAUX	0x00000400 /**< VCCAUX Channel */
#define XADCPS_SEQ_CH_VPVN	0x00000800 /**< VP/VN analog inputs Channel */
#define XADCPS_SEQ_CH_VREFP	0x00001000 /**< VREFP Channel */
#define XADCPS_SEQ_CH_VREFN	0x00002000 /**< VREFN Channel */
#define XADCPS_SEQ_CH_VBRAM	0x00004000 /**< VBRAM Channel, 7 series */
#define XADCPS_SEQ_CH_AUX00	0x00010000 /**< 1st Aux Channel */
#define XADCPS_SEQ_CH_AUX01	0x00020000 /**< 2nd Aux Channel */
#define XADCPS_SEQ_CH_AUX02	0x00040000 /**< 3rd Aux Channel */
#define XADCPS_SEQ_CH_AUX03	0x00080000 /**< 4th Aux Channel */
#define XADCPS_SEQ_CH_AUX04	0x00100000 /**< 5th Aux Channel */
#define XADCPS_SEQ_CH_AUX05	0x00200000 /**< 6th Aux Channel */
#define XADCPS_SEQ_CH_AUX06	0x00400000 /**< 7th Aux Channel */
#define XADCPS_SEQ_CH_AUX07	0x00800000 /**< 8th Aux Channel */
#define XADCPS_SEQ_CH_AUX08	0x01000000 /**< 9th Aux Channel */
#define XADCPS_SEQ_CH_AUX09	0x02000000 /**< 10th Aux Channel */
#define XADCPS_SEQ_CH_AUX10	0x04000000 /**< 11th Aux Channel */
#define XADCPS_SEQ_CH_AUX11	0x08000000 /**< 12th Aux Channel */
#define XADCPS_SEQ_CH_AUX12	0x10000000 /**< 13th Aux Channel */
#define XADCPS_SEQ_CH_AUX13	0x20000000 /**< 14th Aux Channel */
#define XADCPS_SEQ_CH_AUX14	0x40000000 /**< 15th Aux Channel */
#define XADCPS_SEQ_CH_AUX15	0x80000000 /**< 16th Aux Channel */

#define XADCPS_SEQ00_CH_VALID_MASK  0x7FE1 /**< Mask for the valid channels */
#define XADCPS_SEQ01_CH_VALID_MASK  0xFFFF /**< Mask for the valid channels */

#define XADCPS_SEQ02_CH_VALID_MASK  0x7FE0 /**< Mask for the valid channels */
#define XADCPS_SEQ03_CH_VALID_MASK  0xFFFF /**< Mask for the valid channels */

#define XADCPS_SEQ04_CH_VALID_MASK  0x0800 /**< Mask for the valid channels */
#define XADCPS_SEQ05_CH_VALID_MASK  0xFFFF /**< Mask for the valid channels */

#define XADCPS_SEQ06_CH_VALID_MASK  0x0800 /**< Mask for the valid channels */
#define XADCPS_SEQ07_CH_VALID_MASK  0xFFFF /**< Mask for the valid channels */


#define XADCPS_SEQ_CH_AUX_SHIFT	16 /**< Shift for the Aux Channel */

/*@}*/

/**
 * @name OT Upper Alarm Threshold Register Bit Definitions
 * @{
 */

#define XADCPS_ATR_OT_UPPER_ENB_MASK	0x000F /**< Mask for OT enable */
#define XADCPS_ATR_OT_UPPER_VAL_MASK	0xFFF0 /**< Mask for OT value */
#define XADCPS_ATR_OT_UPPER_VAL_SHIFT	4      /**< Shift for OT value */
#define XADCPS_ATR_OT_UPPER_ENB_VAL	0x0003 /**< Value for OT enable */
#define XADCPS_ATR_OT_UPPER_VAL_MAX	0x0FFF /**< Max OT value */

/*@}*/


/**
 * @name JTAG DRP Bit Definitions
 * @{
 */
#define XADCPS_JTAG_DATA_MASK		0x0000FFFF /**< Mask for the Data */
#define XADCPS_JTAG_ADDR_MASK		0x03FF0000 /**< Mask for the Addr */
#define XADCPS_JTAG_ADDR_SHIFT		16	   /**< Shift for the Addr */
#define XADCPS_JTAG_CMD_MASK		0x3C000000 /**< Mask for the Cmd */
#define XADCPS_JTAG_CMD_WRITE_MASK	0x08000000 /**< Mask for CMD Write */
#define XADCPS_JTAG_CMD_READ_MASK	0x04000000 /**< Mask for CMD Read */
#define XADCPS_JTAG_CMD_SHIFT		26	   /**< Shift for the Cmd */

/*@}*/

/** @name Unlock Register Definitions
  * @{
 */
 #define XADCPS_UNLK_OFFSET	 0x034 /**< Unlock Register */
 #define XADCPS_UNLK_VALUE	 0x757BDF0D /**< Unlock Value */

 /* @} */


/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/*****************************************************************************/
/**
*
* Read a register of the XADC device. This macro provides register
* access to all registers using the register offsets defined above.
*
* @param	BaseAddress contains the base address of the device.
* @param	RegOffset is the offset of the register to read.
*
* @return	The contents of the register.
*
* @note		C-style Signature:
*		u32 XAdcPs_ReadReg(u32 BaseAddress, u32 RegOffset);
*
******************************************************************************/
#define XAdcPs_ReadReg(BaseAddress, RegOffset) \
			(Xil_In32((BaseAddress) + (RegOffset)))

/*****************************************************************************/
/**
*
* Write a register of the XADC device. This macro provides
* register access to all registers using the register offsets defined above.
*
* @param	BaseAddress contains the base address of the device.
* @param	RegOffset is the offset of the register to write.
* @param	Data is the value to write to the register.
*
* @return	None.
*
* @note 	C-style Signature:
*		void XAdcPs_WriteReg(u32 BaseAddress,
*					u32 RegOffset,u32 Data)
*
******************************************************************************/
#define XAdcPs_WriteReg(BaseAddress, RegOffset, Data) \
		(Xil_Out32((BaseAddress) + (RegOffset), (Data)))

/************************** Function Prototypes ******************************/


/*****************************************************************************/
/**
*
* Formats the data to be written to the the XADC registers.
*
* @param	RegOffset is the offset of the Register
* @param	Data is the data to be written to the Register if it is
*		a write.
* @param	ReadWrite specifies whether it is a Read or a Write.
*		Use 0 for Read, 1 for Write.
*
* @return	None.
*
* @note 	C-style Signature:
*		void XAdcPs_FormatWriteData(u32 RegOffset,
*					     u16 Data, int ReadWrite)
*
******************************************************************************/
#define XAdcPs_FormatWriteData(RegOffset, Data, ReadWrite) 	    \
    ((ReadWrite ? XADCPS_JTAG_CMD_WRITE_MASK : XADCPS_JTAG_CMD_READ_MASK ) | \
     ((RegOffset << XADCPS_JTAG_ADDR_SHIFT) & XADCPS_JTAG_ADDR_MASK) | 	     \
     (Data & XADCPS_JTAG_DATA_MASK))



#ifdef __cplusplus
}
#endif

#endif  /* End of protection macro. */
