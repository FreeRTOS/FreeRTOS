/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file simulation.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief SGMII defines
 */

#ifndef MSS_DDR_SGMII_SIMULATION_H_
#define MSS_DDR_SGMII_SIMULATION_H_

/* todo: remove this file before customer distribution */

/***************************************************************************//**
  Simulation Test commands
 */
#define DDR_SIM                 0x01
#define FLASH_FREEZE_SIM        0x02
#define DESIGN_INF_TEST_SIM     0x04
#define MMSIO_SIM               0x08
#define SGMII_SIM               0x10
#define BUS_ERROR_UNIT          0x20
#define D_CACHE_TEST            0x40
#define EXT_CLK_CHOICE          0x80

/***************************************************************************//**
  SGMii Test commands
* List from Eugene
* 1.  Full SGMII test- both channels enabled, external loopback and rx_lock for
*     both channels. (This test is written)
*     (Will do a version of this for refclk = 125 mhz also- already supported
*     in sw)
* 2.  SGMII test, similar to 1 , except chan1 is off.
* 3.  TEST with both CHAn0 and CHAn 1 off. This is the default state for sgmii
*     anyway. The SGMII PLL will not be turned on either. This is our SGMII OFF
*     MODE test.
* 4.  RECALIB mode on (RECAL_CNTL-reg_recal_start_en =1). Both chans off. As I
*     understand this is for DDR IO recalibration. I am not sure what I check
*     for here. SO I will ask Jeff.
* 5.  PVT recalibration..as per Srikanths presentation...SCB reg_calib_start =1
*     and APB calib_start =1 (see my earlier email.) This allows us check status
*     of calib_start and calib_lock and calib_intrpt to be checked as per
*     Srikanths presentation.
*
*/
#define SGMII_ALL_ON                    0x00
#define SGMII_CH1_OFF                   0x01
#define SGMII_ALL_OFF                   0x02
#define SGMII_RECALIB                   0x03
#define SGMII_PVT_MONITOR               0x04
#define SGMII_CH0_OFF_CH1_ON            0x05
#define SGMII_MAC0_LOOPBACK_TEST        0x06
#define SGMII_TRIM_IO                   0x07
#define SGMII_RECALIB_IO                0x08
#define SGMII_MAC1_LOOPBACK_TEST        0x09
#define SGMII_ALL_OFF_INC_CLK           0x0A


#ifdef SIMULATION_TEST_FEEDBACK
#define   SIM_FEEDBACK0(x)  (SYSREG->TEMP0 = (uint32_t)x)
#define   SIM_FEEDBACK1(x)  (SYSREG->TEMP1 = (uint32_t)x)
#else
#define   SIM_FEEDBACK0(x)
#define   SIM_FEEDBACK1(x)
#endif

#endif /* MSS_DDR_SGMII_SIMULATION_H_ */
