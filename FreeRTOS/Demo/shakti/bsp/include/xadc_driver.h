/***************************************************************************
* Project           	     : shakti devt board
* Name of the file	     : xadc_driver.h
* Brief Description of file  : Header file for xadc driver.
* Name of Author    	     : Sathya Narayanan N
* Email ID                   : sathya281@gmail.com

  Copyright (C) 2020  IIT Madras. All rights reserved.

  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <https://www.gnu.org/licenses/>.
***************************************************************************/
/**
 * @file xadc_driver.h
 * @brief  Header file for xadc driver.c
 * @detail This file contains the definitions for xadc driver. The memory map
 * for the xadc registers are also defined here.
 */

#ifndef XADC_DRIVER
#define XADC_DRIVER

#include "platform.h"
#include "traps.h"

/**@name Register offsets
 *
 * The following constants provide access to each of the registers of the
 * System Monitor/ADC device.
 * @{
 */

/*
 * System Monitor/ADC Local Registers
 */
#define XADC_SRR_OFFSET		0x00  /**< Software Reset Register */
#define XADC_SR_OFFSET		0x04  /**< Status Register */
#define XADC_AOR_OFFSET		0x08  /**< Alarm Output Register */
#define XADC_CONVST_OFFSET	0x0C  /**< ADC Convert Start Register */
#define XADC_ARR_OFFSET		0x10  /**< ADC Reset Register */

/*
 * System Monitor/ADC Interrupt Registers
 */
#define XADC_GIER_OFFSET	0x5C  /**< Global Interrupt Enable */
#define XADC_ISR_OFFSET	        0x60  /**< Interrupt Status Register */
#define XADC_IER_OFFSET		0x68  /**< Interrupt Enable register */

/*
 * System Monitor/ADC Internal Channel Registers
 */
#define XADC_TEMP_OFFSET	  (0x200)   /**< On-chip Temperature Reg */
#define XADC_VCCINT_OFFSET	  (0x204)   /**< On-chip VCCINT Data Reg */
#define XADC_VCCAUX_OFFSET	  (0x208)   /**< On-chip VCCAUX Data Reg */
#define XADC_VPVN_OFFSET	  (0x20C)   /**< ADC out of VP/VN	   */
#define XADC_VREFP_OFFSET	  (0x210)   /**< On-chip VREFP Data Reg */
#define XADC_VREFN_OFFSET	  (0x214)   /**< On-chip VREFN Data Reg */
#define XADC_VBRAM_OFFSET	  (0x218)   /**< On-chip VBRAM Data */
#define XADC_SUPPLY_CALIB_OFFSET  (0x220)   /**< Supply Offset Data Reg */
#define XADC_ADC_CALIB_OFFSET	  (0x224)   /**< ADC Offset Data Reg */
#define XADC_GAINERR_CALIB_OFFSET (0x228)   /**< Gain Error Data Reg  */
#define XADC_VCCPINT_OFFSET	  (0x22C)   /**< PS VCCPINT Data Reg -  */
#define XADC_VCCPAUX_OFFSET	  (0x230)   /**< PS VCCPAUX Data Reg -  */
#define XADC_VCCPDRO_OFFSET	  (0x234)   /**< PS VCCPDRO Data Reg -  */
#define XADC_VUSR0_OFFSET	  (0x400)   /**< VUSER0 Supply   */
#define XADC_VUSR1_OFFSET	  (0x404)   /**< VUSER0 Supply   */
#define XADC_VUSR2_OFFSET	  (0x408)   /**< VUSER0 Supply   */
#define XADC_VUSR3_OFFSET	  (0x40C)   /**< VUSER0 Supply   */

/*
 * System Monitor/ADC External Channel Registers
 */
#define XADC_AUX00_OFFSET	(0x240)   /**< ADC out of VAUXP0/VAUXN0 */
#define XADC_AUX01_OFFSET	(0x244)   /**< ADC out of VAUXP1/VAUXN1 */
#define XADC_AUX02_OFFSET	(0x248)   /**< ADC out of VAUXP2/VAUXN2 */
#define XADC_AUX03_OFFSET	(0x24C)   /**< ADC out of VAUXP3/VAUXN3 */
#define XADC_AUX04_OFFSET	(0x250)   /**< ADC out of VAUXP4/VAUXN4 */
#define XADC_AUX05_OFFSET	(0x254)   /**< ADC out of VAUXP5/VAUXN5 */
#define XADC_AUX06_OFFSET	(0x258)   /**< ADC out of VAUXP6/VAUXN6 */
#define XADC_AUX07_OFFSET	(0x25C)   /**< ADC out of VAUXP7/VAUXN7 */
#define XADC_AUX08_OFFSET	(0x260)   /**< ADC out of VAUXP8/VAUXN8 */
#define XADC_AUX09_OFFSET	(0x264)   /**< ADC out of VAUXP9/VAUXN9 */
#define XADC_AUX10_OFFSET	(0x268)   /**< ADC out of VAUXP10/VAUXN10 */
#define XADC_AUX11_OFFSET	(0x26C)   /**< ADC out of VAUXP11/VAUXN11 */
#define XADC_AUX12_OFFSET	(0x270)   /**< ADC out of VAUXP12/VAUXN12 */
#define XADC_AUX13_OFFSET	(0x274)   /**< ADC out of VAUXP13/VAUXN13 */
#define XADC_AUX14_OFFSET	(0x278)   /**< ADC out of VAUXP14/VAUXN14 */
#define XADC_AUX15_OFFSET	(0x27C)   /**< ADC out of VAUXP15/VAUXN15 */

/*
 * System Monitor/ADC Registers for Maximum/Minimum data captured for the
 * on chip Temperature/VCCINT/VCCAUX data.
 */
#define XADC_MAX_TEMP_OFFSET	(0x280)   /**< Maximum Temperature Reg */
#define XADC_MAX_VCCINT_OFFSET	(0x284)   /**< Maximum VCCINT Register */
#define XADC_MAX_VCCAUX_OFFSET	(0x288)   /**< Maximum VCCAUX Register */
#define XADC_MAX_VBRAM_OFFSET	(0x28C)   /**< Maximum VBRAM Reg / */
#define XADC_MIN_TEMP_OFFSET	(0x290)   /**< Minimum Temperature Reg */
#define XADC_MIN_VCCINT_OFFSET	(0x294)   /**< Minimum VCCINT Register */
#define XADC_MIN_VCCAUX_OFFSET	(0x298)   /**< Minimum VCCAUX Register */
#define XADC_MIN_VBRAM_OFFSET	(0x29C)   /**< Maximum VBRAM Reg / */
#define XADC_MAX_VCCPINT_OFFSET	(0x2A0)   /**< Max VCCPINT Register  */
#define XADC_MAX_VCCPAUX_OFFSET	(0x2A4)   /**< Max VCCPAUX Register  */
#define XADC_MAX_VCCPDRO_OFFSET	(0x2A8)   /**< Max VCCPDRO Register  */
#define XADC_MIN_VCCPINT_OFFSET	(0x2AC)   /**< Min VCCPINT Register  */
#define XADC_MIN_VCCPAUX_OFFSET	(0x2B0)   /**< Min VCCPAUX Register  */
#define XADC_MIN_VCCPDRO_OFFSET	(0x2B4)   /**< Min VCCPDRO Register  */
#define XADC_MAX_VUSR0_OFFSET	(0x480)   /**< Maximum VUSER0 Supply Reg */
#define XADC_MAX_VUSR1_OFFSET	(0x484)   /**< Maximum VUSER1 Supply Reg */
#define XADC_MAX_VUSR2_OFFSET	(0x488)   /**< Maximum VUSER2 Supply Reg */
#define XADC_MAX_VUSR3_OFFSET	(0x48C)   /**< Maximum VUSER3 Supply Reg */
#define XADC_MIN_VUSR0_OFFSET	(0x4A0)   /**< Minimum VUSER0 Supply Reg */
#define XADC_MIN_VUSR1_OFFSET	(0x4A4)   /**< Minimum VUSER1 Supply Reg */
#define XADC_MIN_VUSR2_OFFSET	(0x4A8)   /**< Minimum VUSER2 Supply Reg */
#define XADC_MIN_VUSR3_OFFSET	(0x4AC)   /**< Minimum VUSER3 Supply Reg */


#define XADC_FLAG_REG_OFFSET	(0x2FC) /**< General Status */

/*
 * System Monitor/ADC Configuration Registers
 */
#define XADC_CFR0_OFFSET		(0x300)   /**< Configuration Register 0 */
#define XADC_CFR1_OFFSET		(0x304)   /**< Configuration Register 1 */
#define XADC_CFR2_OFFSET		(0x308)   /**< Configuration Register 2 */

/*
 * System Monitor/ADC Sequence Registers
 */
#define XADC_SEQ00_OFFSET	(0x320)   /**< Seq Reg 00 Adc Channel Selection */
#define XADC_SEQ01_OFFSET	(0x324)   /**< Seq Reg 01 Adc Channel Selection */
#define XADC_SEQ02_OFFSET	(0x328)   /**< Seq Reg 02 Adc Average Enable */
#define XADC_SEQ03_OFFSET	(0x32C)   /**< Seq Reg 03 Adc Average Enable */
#define XADC_SEQ04_OFFSET	(0x330)   /**< Seq Reg 04 Adc Input Mode Select */
#define XADC_SEQ05_OFFSET	(0x334)   /**< Seq Reg 05 Adc Input Mode Select */
#define XADC_SEQ06_OFFSET	(0x338)   /**< Seq Reg 06 Adc Acquisition Select */
#define XADC_SEQ07_OFFSET	(0x33C)   /**< Seq Reg 07 Adc Acquisition Select */
#define XADC_SEQ08_OFFSET	(0x318)   /**< Seq Reg 08 Adc Channel Selection */
#define XADC_SEQ09_OFFSET	(0x31C)   /**< Seq Reg 09 Adc Average Enable */

/*
 * System Monitor/ADC Alarm Threshold/Limit Registers (ATR)
 */
#define XADC_ATR_TEMP_UPPER_OFFSET	(0x340)   /**< Temp Upper Alarm Register */
#define XADC_ATR_VCCINT_UPPER_OFFSET	(0x344)   /**< VCCINT Upper Alarm Reg */
#define XADC_ATR_VCCAUX_UPPER_OFFSET	(0x348)   /**< VCCAUX Upper Alarm Reg */
#define XADC_ATR_OT_UPPER_OFFSET	(0x34C)   /**< Over Temp Upper Alarm Reg */
#define XADC_ATR_TEMP_LOWER_OFFSET	(0x350)   /**< Temp Lower Alarm Register */
#define XADC_ATR_VCCINT_LOWER_OFFSET	(0x354)   /**< VCCINT Lower Alarm Reg */
#define XADC_ATR_VCCAUX_LOWER_OFFSET	(0x358)   /**< VCCAUX Lower Alarm Reg */
#define XADC_ATR_OT_LOWER_OFFSET	(0x35C)   /**< Over Temp Lower Alarm Reg */
#define XADC_ATR_VBRAM_UPPER_OFFSET	(0x360)   /**< VBBAM Upper Alarm */
#define XADC_ATR_VCCPINT_UPPER_OFFSET	(0x364)   /**< VCCPINT Upper Alarm  */
#define XADC_ATR_VCCPAUX_UPPER_OFFSET	(0x368)   /**< VCCPAUX Upper Alarm  */
#define XADC_ATR_VCCPDRO_UPPER_OFFSET	(0x36C)   /**< VCCPDRO Upper Alarm  */
#define XADC_ATR_VBRAM_LOWER_OFFSET	(0x370)   /**< VRBAM Lower Alarm */
#define XADC_ATR_VCCPINT_LOWER_OFFSET	(0x374)   /**< VCCPINT Lower Alarm  */
#define XADC_ATR_VCCPAUX_LOWER_OFFSET	(0x378)   /**< VCCPAUX Lower Alarm  */
#define XADC_ATR_VCCPDRO_LOWER_OFFSET	(0x37C)   /**< VCCPDRO Lower Alarm  */
#define XADC_ATR_VUSR0_UPPER_OFFSET	(0x380)   /**< VUSER0 Upper Alarm Reg */
#define XADC_ATR_VUSR1_UPPER_OFFSET	(0x384)   /**< VUSER1 Upper Alarm Reg */
#define XADC_ATR_VUSR2_UPPER_OFFSET	(0x388)   /**< VUSER2 Upper Alarm Reg */
#define XADC_ATR_VUSR3_UPPER_OFFSET	(0x38C)   /**< VUSER3 Upper Alarm Reg */
#define XADC_ATR_VUSR0_LOWER_OFFSET	(0x3A0)   /**< VUSER0 Lower Alarm Reg */
#define XADC_ATR_VUSR1_LOWER_OFFSET	(0x3A4)   /**< VUSER1 Lower Alarm Reg */
#define XADC_ATR_VUSR2_LOWER_OFFSET	(0x3A8)   /**< VUSER2 Lower Alarm Reg */
#define XADC_ATR_VUSR3_LOWER_OFFSET	(0x3AC)   /**< VUSER3 Lower Alarm Reg */

/*@}*/

/**
 * @name System Monitor/ADC Software Reset Register (SRR) mask(s)
 * @{
 */
#define XADC_SRR_RESET_VALUE	0x0000000A   /**< Device Reset Mask */

/*@}*/

/**
 * @name System Monitor/ADC Status Register (SR) mask(s)
 * @{
 */
#define XADC_SR_JTAG_BUSY_MASK	   0x00000400 /**< JTAG is busy */
#define XADC_SR_JTAG_MODIFIED_MASK 0x00000200 /**< JTAG Write has occurred */
#define XADC_SR_JTAG_LOCKED_MASK   0x00000100 /**< JTAG is locked */
#define XADC_SR_BUSY_MASK	   0x00000080 /**< ADC is busy in conversion */
#define XADC_SR_EOS_MASK	   0x00000040 /**< End of Sequence */
#define XADC_SR_EOC_MASK	   0x00000020 /**< End of Conversion */
#define XADC_SR_CH_MASK		   0x0000001F /**< Input ADC channel */

/*@}*/

/**
 * @name System Monitor/ADC Alarm Output Register (AOR) mask(s)
 * @{
 */
#define XADC_AOR_ALARM_ALL_MASK	0x00001FFF /**< Mask for all Alarms */
#define XADC_AOR_VUSR3_MASK	0x00001000 /**< ALM11 - VUSER3 Alarm Mask */
#define XADC_AOR_VUSR2_MASK	0x00000800 /**< ALM10 - VUSER2 Alarm Mask */
#define XADC_AOR_VUSR1_MASK	0x00000400 /**< ALM9 -  VUSER1 Alarm Mask */
#define XADC_AOR_VUSR0_MASK	0x00000200 /**< ALM8 -  VUSER0 Alarm Mask */
#define XADC_AOR_ALL_MASK	0x00000100 /**< ALM7 - All Alarms 0 to 6 */
#define XADC_AOR_VCCPDRO_MASK	0x00000080 /**< ALM6 - VCCPDRO  Mask  */
#define XADC_AOR_VCCPAUX_MASK	0x00000040 /**< ALM5 - VCCPAUX  Mask  */
#define XADC_AOR_VCCPINT_MASK	0x00000020 /**< ALM4 - VCCPINT Mask  */
#define XADC_AOR_VBRAM_MASK	0x00000010 /**< ALM3 - VBRAM Output Mask */
#define XADC_AOR_VCCAUX_MASK	0x00000008 /**< ALM2 - VCCAUX Output Mask  */
#define XADC_AOR_VCCINT_MASK	0x00000004 /**< ALM1 - VCCINT Alarm Mask */
#define XADC_AOR_TEMP_MASK	0x00000002 /**< ALM0 - Temp sensor Alarm Mask */
#define XADC_AOR_OT_MASK		0x00000001 /**< Over Temp Alarm Output */

/*@}*/

/**
 * @name System Monitor/ADC CONVST Register (CONVST) mask(s)
 * @{
 */
#define XADC_CONVST_CONVST_MASK		0x00000001   /**< Conversion Start Mask */
#define XADC_CONVST_TEMPUPDT_MASK	0x00000002   /**< Temperature Update   	Enable Mask */
#define XADC_CONVST_WAITCYCLES_SHIFT	2	/**< Wait Cycles Shift */
#define XADC_CONVST_WAITCYCLES_MASK	0x0003FFFC /**< Wait Cycles Mask */
#define XADC_CONVST_WAITCYCLES_DEFAULT	0x03E8	/**< Wait Cycles   	 default value */
/*@}*/

/**
 * @name System Monitor/ADC Reset Register (ARR) mask(s)
 * @{
 */
#define XADC_ARR_RST_MASK	0x00000001 /**< ADC Reset bit mask */

/*@}*/

/**
 * @name Global Interrupt Enable Register (GIER) mask(s)
 * @{
 */
#define XADC_GIER_GIE_MASK	0x80000000 /**< Global interrupt enable */
/*@}*/

/**
 * @name System Monitor/ADC device Interrupt Status/Enable Registers
 *
 * <b> Interrupt Status Register (IPISR) </b>
 *
 * This register holds the interrupt status flags for the device.
 *
 * <b> Interrupt Enable Register (IPIER) </b>
 *
 * This register is used to enable interrupt sources for the device.
 * Writing a '1' to a bit in this register enables the corresponding Interrupt.
 * Writing a '0' to a bit in this register disables the corresponding Interrupt
 *
 * IPISR/IPIER registers have the same bit definitions and are only defined
 * once.
 * @{
 */
#define XADC_IPIXR_VBRAM_MASK	      0x00000400 /**< ALM3 - VBRAM Output Mask */
#define XADC_IPIXR_TEMP_DEACTIVE_MASK  0x00000200 /**< Alarm 0 DEACTIVE */
#define XADC_IPIXR_OT_DEACTIVE_MASK    0x00000100 /**< Over Temp DEACTIVE */
#define XADC_IPIXR_JTAG_MODIFIED_MASK  0x00000080 /**< JTAG Modified */
#define XADC_IPIXR_JTAG_LOCKED_MASK    0x00000040 /**< JTAG Locked */
#define XADC_IPIXR_EOC_MASK	      0x00000020 /**< End Of Conversion */
#define XADC_IPIXR_EOS_MASK	      0x00000010 /**< End Of Sequence */
#define XADC_IPIXR_VCCAUX_MASK	      0x00000008 /**< Alarm 2 - VCCAUX */
#define XADC_IPIXR_VCCINT_MASK	      0x00000004 /**< Alarm 1 - VCCINT */
#define XADC_IPIXR_TEMP_MASK	      0x00000002 /**< Alarm 0 - Temp ACTIVE */
#define XADC_IPIXR_OT_MASK	      0x00000001 /**< Over Temperature ACTIVE */
#define XADC_IPIXR_VUSR0_MASK	      0x00004000 /**< Alarm 8  VUSER0 */
#define XADC_IPIXR_VUSR1_MASK	      0x00008000 /**< Alarm 9  VUSER1 */
#define XADC_IPIXR_VUSR2_MASK	      0x00010000 /**< Alarm 10 VUSER2 */
#define XADC_IPIXR_VUSR3_MASK	      0x00020000 /**< Alarm 11 VUSER3 */
#define XADC_IPIXR_ALL_MASK	      0x0003C7FF /**< Mask of all interrupts */


/*@}*/

/**
 * @name Mask for all ADC converted data including Minimum/Maximum Measurements
 *	 and Threshold data.
 * @{
 */
#define XADC_ADCDATA_MAX_MASK	0x03FF

/*@}*/

/**
 * @name Configuration Register 0 (CFR0) mask(s)
 * @{
 */
#define XADC_CFR0_CAL_AVG_MASK	0x8000  /**< Averaging enable Mask */
#define XADC_CFR0_AVG_VALID_MASK	0x3000  /**< Averaging bit Mask */
#define XADC_CFR0_AVG1_MASK	0x0000  /**< No Averaging */
#define XADC_CFR0_AVG16_MASK	0x1000  /**< Average 16 samples */
#define XADC_CFR0_AVG64_MASK	0x2000  /**< Average 64 samples */
#define XADC_CFR0_AVG256_MASK	0x3000  /**< Average 256 samples */
#define XADC_CFR0_AVG_SHIFT	12	/**< Shift for the Averaging bits */
#define XADC_CFR0_MUX_MASK	0x0800  /**< External Mux Mask Enable */
#define XADC_CFR0_DU_MASK	0x0400  /**< Bipolar/Unipolar mode */
#define XADC_CFR0_EC_MASK	0x0200  /**< Event driven/Continuous mode */
#define XADC_CFR0_ACQ_MASK	0x0100  /**< Add acquisition by 6 ADCCLK  */
#define XADC_CFR0_CHANNEL_MASK	0x003F  /**< Channel number bit Mask */

/*@}*/

/**
 * @name Configuration Register 1 (CFR1) mask(s)
 * @{
 */
#define XADC_CFR1_SEQ_VALID_MASK	  0xF000 /**< Sequence bit Mask */
#define XADC_CFR1_SEQ_SAFEMODE_MASK	  0x0000 /**< Default Safe Mode */
#define XADC_CFR1_SEQ_ONEPASS_MASK	  0x1000 /**< Onepass through Seq */
#define XADC_CFR1_SEQ_CONTINPASS_MASK	  0x2000 /**< Continuous Cycling Seq */
#define XADC_CFR1_SEQ_SINGCHAN_MASK	  0x3000 /**< Single channel - No Seq */
#define XADC_CFR1_SEQ_SIMUL_SAMPLING_MASK  0x4000 /**< Simultaneous Sampling Mask */
#define XADC_CFR1_SEQ_INDEPENDENT_MASK	  0x8000 /**< Independent Mode */
#define XADC_CFR1_SEQ_SHIFT		  12     /**< Sequence bit shift */
#define XADC_CFR1_ALM_VCCPDRO_MASK	  0x0800 /**< Alarm 6 - VCCPDRO  */
#define XADC_CFR1_ALM_VCCPAUX_MASK	  0x0400 /**< Alarm 5 - VCCPAUX  */
#define XADC_CFR1_ALM_VCCPINT_MASK	  0x0200 /**< Alarm 4 - VCCPINT  */
#define XADC_CFR1_ALM_VBRAM_MASK  	  0x0100 /**< Alarm 3 - VBRAM Enable */
#define XADC_CFR1_CAL_VALID_MASK	  0x00F0 /**< Valid Calibration Mask */
#define XADC_CFR1_CAL_PS_GAIN_OFFSET_MASK  0x0080 /**< Calibration 3 -Power Supply Gain/Offset Enable */
#define XADC_CFR1_CAL_PS_OFFSET_MASK	  0x0040 /**< Calibration 2 -Power Supply Offset Enable */
#define XADC_CFR1_CAL_ADC_GAIN_OFFSET_MASK 0x0020 /**< Calibration 1 -ADC Gain Offset Enable */
#define XADC_CFR1_CAL_ADC_OFFSET_MASK	  0x0010 /**< Calibration 0 -ADC Offset	Enable */
#define XADC_CFR1_CAL_DISABLE_MASK	  0x0000 /**< No Calibration */
#define XADC_CFR1_ALM_ALL_MASK		  0x0F0F /**< Mask for all alarms */
#define XADC_CFR1_ALM_VCCAUX_MASK	  0x0008 /**< Alarm 2 - VCCAUX Enable */
#define XADC_CFR1_ALM_VCCINT_MASK	  0x0004 /**< Alarm 1 - VCCINT Enable */
#define XADC_CFR1_ALM_TEMP_MASK		  0x0002 /**< Alarm 0 - Temperature */
#define XADC_CFR1_OT_MASK		  0x0001 /**< Over Temperature Enable */

/*@}*/

/**
 * @name Configuration Register 2 (CFR2) mask(s)
 * @{
 */
#define XADC_CFR2_CD_VALID_MASK	0xFF00  /**<Clock Divisor bit Mask   */
#define XADC_CFR2_CD_SHIFT	8	/**<Num of shift on division */
#define XADC_CFR2_CD_MIN	8	/**<Minimum value of divisor */
#define XADC_CFR2_CD_MAX	255	/**<Maximum value of divisor */

#define XADC_CFR2_PD_MASK	0x0030	/**<Power Down Mask */
#define XADC_CFR2_PD_XADC_MASK	0x0030	/**<Power Down XADC Mask */
#define XADC_CFR2_PD_ADC1_MASK	0x0020	/**<Power Down XADC Mask */
#define XADC_CFR2_PD_SHIFT	4	/**<Power Down Shift */

/*@}*/

/**
 * @name Configuration Register 3 (CFR3) mask(s)
 * @{
 */

#define XADC_CFR3_ALM_ALL_MASK		  0x000F /**< Mask for all alarms */
#define XADC_CFR3_ALM_VUSR3_MASK	  0x0008 /**< VUSER 0 Supply */
#define XADC_CFR3_ALM_VUSR2_MASK	  0x0004 /**< VUSER 1 Supply */
#define XADC_CFR3_ALM_VUSR1_MASK	  0x0002 /**< VUSER 2 Supply */
#define XADC_CFR3_ALM_VUSR0_MASK	  0x0001 /**< VUSER 3 Supply */

/* Mask for all Alarms in CFR1 and CFR3 */
#define XADC_CFR_ALM_ALL_MASK		  0xF0F0F

/*@}*/

/**
 * @name Alarm masks for channels in Configuration registers 1 and 3
 * @{
 */
#define XADC_CFR_ALM_VUSR3_MASK		0x00080000 /**< VUSER 0 Supply */
#define XADC_CFR_ALM_VUSR2_MASK		0x00040000 /**< VUSER 1 Supply */
#define XADC_CFR_ALM_VUSR1_MASK		0x00020000 /**< VUSER 2 Supply */
#define XADC_CFR_ALM_VUSR0_MASK		0x00010000 /**< VUSER 3 Supply */
#define XADC_CFR_ALM_VCCPDRO_MASK	0x0800 /**< Alarm 6 - VCCPDRO  */
#define XADC_CFR_ALM_VCCPAUX_MASK	0x0400 /**< Alarm 5 - VCCPAUX  */
#define XADC_CFR_ALM_VCCPINT_MASK	0x0200 /**< Alarm 4 - VCCPINT  */
#define XADC_CFR_ALM_VBRAM_MASK		0x0100 /**< Alarm 3 - VBRAM Enable */
#define XADC_CFR_ALM_VCCAUX_MASK	0x0008 /**< Alarm 2 - VCCAUX Enable */
#define XADC_CFR_ALM_VCCINT_MASK	0x0004 /**< Alarm 1 - VCCINT Enable */
#define XADC_CFR_ALM_TEMP_MASK		0x0002 /**< Alarm 0 - Temperature */
#define XADC_CFR_OT_MASK		0x0001 /**< Over Temperature Enable */

/**
 * @name Sequence Register (SEQ) Bit Definitions
 * @{
 */
#define XADC_SEQ_CH_CALIB	0x00000001 /**< ADC Calibration Channel */
#define XADC_SEQ_CH_VCCPINT	0x00000020 /**< VCCPINT   */
#define XADC_SEQ_CH_VCCPAUX	0x00000040 /**< VCCPAUX   */
#define XADC_SEQ_CH_VCCPDRO	0x00000080 /**< VCCPDRO   */
#define XADC_SEQ_CH_TEMP	0x00000100 /**< On Chip Temperature Channel */
#define XADC_SEQ_CH_VCCINT	0x00000200 /**< VCCINT Channel */
#define XADC_SEQ_CH_VCCAUX	0x00000400 /**< VCCAUX Channel */
#define XADC_SEQ_CH_VPVN	0x00000800 /**< VP/VN analog inputs Channel */
#define XADC_SEQ_CH_VREFP	0x00001000 /**< VREFP Channel */
#define XADC_SEQ_CH_VREFN	0x00002000 /**< VREFN Channel */
#define XADC_SEQ_CH_VBRAM	0x00004000 /**< VBRAM Channel / */
#define XADC_SEQ_CH_AUX00	0x00010000 /**< 1st Aux Channel */
#define XADC_SEQ_CH_AUX01	0x00020000 /**< 2nd Aux Channel */
#define XADC_SEQ_CH_AUX02	0x00040000 /**< 3rd Aux Channel */
#define XADC_SEQ_CH_AUX03	0x00080000 /**< 4th Aux Channel */
#define XADC_SEQ_CH_AUX04	0x00100000 /**< 5th Aux Channel */
#define XADC_SEQ_CH_AUX05	0x00200000 /**< 6th Aux Channel */
#define XADC_SEQ_CH_AUX06	0x00400000 /**< 7th Aux Channel */
#define XADC_SEQ_CH_AUX07	0x00800000 /**< 8th Aux Channel */
#define XADC_SEQ_CH_AUX08	0x01000000 /**< 9th Aux Channel */
#define XADC_SEQ_CH_AUX09	0x02000000 /**< 10th Aux Channel */
#define XADC_SEQ_CH_AUX10	0x04000000 /**< 11th Aux Channel */
#define XADC_SEQ_CH_AUX11	0x08000000 /**< 12th Aux Channel */
#define XADC_SEQ_CH_AUX12	0x10000000 /**< 13th Aux Channel */
#define XADC_SEQ_CH_AUX13	0x20000000 /**< 14th Aux Channel */
#define XADC_SEQ_CH_AUX14	0x40000000 /**< 15th Aux Channel */
#define XADC_SEQ_CH_AUX15	0x80000000 /**< 16th Aux Channel */
#define XADC_SEQ_CH_VUSR0	0x100000000 /**<  VUSER0 Channel */
#define XADC_SEQ_CH_VUSR1	0x200000000 /**<  VUSER1 Channel */
#define XADC_SEQ_CH_VUSR2	0x400000000 /**<  VUSER2 Channel */
#define XADC_SEQ_CH_VUSR3	0x800000000 /**<  VUSER3 Channel */

#define XADC_SEQ00_CH_VALID_MASK	0x7FE1 /**< Mask for the valid channels */
#define XADC_SEQ01_CH_VALID_MASK	0xFFFF /**< Mask for the valid channels */

#define XADC_SEQ02_CH_VALID_MASK	0x7FE0 /**< Mask for the valid channels */
#define XADC_SEQ03_CH_VALID_MASK	0xFFFF /**< Mask for the valid channels */

#define XADC_SEQ04_CH_VALID_MASK	0x0800 /**< Mask for the valid channels */
#define XADC_SEQ05_CH_VALID_MASK	0xFFFF /**< Mask for the valid channels */

#define XADC_SEQ06_CH_VALID_MASK	0x0800 /**< Mask for the valid channels */
#define XADC_SEQ07_CH_VALID_MASK	0xFFFF /**< Mask for the valid channels */

#define XADC_SEQ08_CH_VALID_MASK 0x000F /**< Mask for the valid channels */
#define XADC_SEQ09_CH_VALID_MASK 0x000F /**< Mask for the valid channels */

#define XADC_SEQ_CH_AUX_SHIFT	16 /**< Shift for the Aux Channel */

#define XADC_SEQ_CH_VUSR_SHIFT	32 /**< Shift for the Aux Channel */

/*@}*/

/**
 * @name OT Upper Alarm Threshold Register Bit Definitions
 * @{
 */

#define XADC_ATR_OT_UPPER_ENB_MASK	0x000F /**< Mask for OT enable */
#define XADC_ATR_OT_UPPER_VAL_MASK	0xFFF0 /**< Mask for OT value */
#define XADC_ATR_OT_UPPER_VAL_SHIFT	4      /**< Shift for OT value */
#define XADC_ATR_OT_UPPER_ENB_VAL	0x0003 /**< Value for OT enable */
#define XADC_ATR_OT_UPPER_VAL_MAX	0x0FFF /**< Max OT value */

/*@}*/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/*****************************************************************************/
/**
*
* Read a register of the System Monitor/ADC device. This macro provides register
* access to all registers using the register offsets defined above.
*
* @param	BaseAddress contains the base address of the device.
* @param	RegOffset is the offset of the register to read.
*
* @return	The contents of the register.
*
* @note		C-style Signature:
*		u32 XSysMon_ReadReg(u32 BaseAddress, u32 RegOffset);
*
******************************************************************************/

/*****************************************************************************/
/**
*
* Write a register of the System Monitor/ADC device. This macro provides
* register access to all registers using the register offsets defined above.
*
* @param	BaseAddress contains the base address of the device.
* @param	RegOffset is the offset of the register to write.
* @param	Data is the value to write to the register.
*
* @return	None.
*
* @note 	C-style Signature:
*		void XSysMon_WriteReg(u32 BaseAddress,
*					u32 RegOffset,u32 Data)
*
******************************************************************************/

/************************** Function Prototypes ******************************/

void xadc_write_ctrl_reg(uint32_t *address, uint32_t data);
uint32_t xadc_read_ctrl_reg(uint32_t *address);
uint32_t xadc_read_data(uint32_t *address);
float xadc_onchip_temp(uint32_t value);
float xadc_onchip_voltage(uint32_t value);

#endif
