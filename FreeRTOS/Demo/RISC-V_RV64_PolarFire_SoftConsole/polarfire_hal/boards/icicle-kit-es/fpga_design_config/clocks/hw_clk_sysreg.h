/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_clk_sysreg.h
 * @author Microchip-FPGA Embedded Systems Solutions
 *
 *
 * Note 1: This file should not be edited. If you need to modify a parameter
 * without going through regenerating using the MSS Configurator Libero flow 
 * or editing the associated xml file
 * the following method is recommended: 

 * 1. edit the following file 
 * boards/your_board/platform_config/mpfs_hal_config/mss_sw_config.h

 * 2. define the value you want to override there.
 * (Note: There is a commented example in the platform directory)

 * Note 2: The definition in mss_sw_config.h takes precedence, as
 * mss_sw_config.h is included prior to the generated header files located in
 * boards/your_board/fpga_design_config
 *
 */

#ifndef HW_CLK_SYSREG_H_
#define HW_CLK_SYSREG_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_MSS_CLOCK_CONFIG_CR)
/*Master clock config (00=/1 01=/2 10=/4 11=/8 ) */
#define LIBERO_SETTING_MSS_CLOCK_CONFIG_CR    0x00000024UL
    /* DIVIDER_CPU                       [0:2]   RW value= 0x0 */
    /* DIVIDER_AXI                       [2:2]   RW value= 0x1 */
    /* DIVIDER_APB_AHB                   [4:2]   RW value= 0x2 */
#endif
#if !defined (LIBERO_SETTING_MSS_RTC_CLOCK_CR)
/*RTC clock divider */
#define LIBERO_SETTING_MSS_RTC_CLOCK_CR    0x0000007DUL
    /* PERIOD                            [0:12]  RW value= 0x7D */
#endif
#if !defined (LIBERO_SETTING_MSS_ENVM_CR)
/*ENVM AHB Controller setup - - Clock period = (Value+1) * (1000/AHBFREQMHZ)
e.g. 7 will generate a 40ns period 25MHz clock if the AHB clock is 200MHz */
#define LIBERO_SETTING_MSS_ENVM_CR    0x40050006UL
    /* CLOCK_PERIOD                      [0:6]   RW value= 0x6 */
    /* CLOCK_CONTINUOUS                  [8:1]   RW value= 0x0 */
    /* CLOCK_SUPPRESS                    [9:1]   RW value= 0x0 */
    /* READAHEAD                         [16:1]  RW value= 0x1 */
    /* SLOWREAD                          [17:1]  RW value= 0x0 */
    /* INTERRUPT_ENABLE                  [18:1]  RW value= 0x1 */
    /* TIMER                             [24:8]  RW value= 0x40 */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_CLK_SYSREG_H_ */

