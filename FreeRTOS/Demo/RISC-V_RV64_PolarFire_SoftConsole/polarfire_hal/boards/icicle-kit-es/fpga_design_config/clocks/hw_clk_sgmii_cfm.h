/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_clk_sgmii_cfm.h
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

#ifndef HW_CLK_SGMII_CFM_H_
#define HW_CLK_SGMII_CFM_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_SGMII_REFCLKMUX)
/*Input mux selections */
#define LIBERO_SETTING_SGMII_REFCLKMUX    0x00000005UL
    /* PLL0_RFCLK0_SEL                   [0:2]   RW value= 0x1 */
    /* PLL0_RFCLK1_SEL                   [2:2]   RW value= 0x1 */
    /* RESERVED                          [4:28]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SGMII_SGMII_CLKMUX)
/*sgmii clk mux */
#define LIBERO_SETTING_SGMII_SGMII_CLKMUX    0x00000005UL
    /* SGMII_CLKMUX                      [0:32]  RW value= 0x5 */
#endif
#if !defined (LIBERO_SETTING_SGMII_SPARE0)
/*spare logic */
#define LIBERO_SETTING_SGMII_SPARE0    0x00000000UL
    /* RESERVED                          [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SGMII_CLK_XCVR)
/*Clock_Receiver */
#define LIBERO_SETTING_SGMII_CLK_XCVR    0x00002C30UL
    /* EN_UDRIVE_P                       [0:1]   RW value= 0x0 */
    /* EN_INS_HYST_P                     [1:1]   RW value= 0x0 */
    /* EN_TERM_P                         [2:2]   RW value= 0x0 */
    /* EN_RXMODE_P                       [4:2]   RW value= 0x3 */
    /* EN_UDRIVE_N                       [6:1]   RW value= 0x0 */
    /* EN_INS_HYST_N                     [7:1]   RW value= 0x0 */
    /* EN_TERM_N                         [8:2]   RW value= 0x0 */
    /* EN_RXMODE_N                       [10:2]  RW value= 0x3 */
    /* CLKBUF_EN_PULLUP                  [12:1]  RW value= 0x0 */
    /* EN_RDIFF                          [13:1]  RW value= 0x1 */
    /* RESERVED                          [14:18] RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SGMII_TEST_CTRL)
/*Test MUX Controls */
#define LIBERO_SETTING_SGMII_TEST_CTRL    0x00000000UL
    /* OSC_ENABLE                        [0:4]   RW value= 0x0 */
    /* ATEST_EN                          [4:1]   RW value= 0x0 */
    /* ATEST_SEL                         [5:5]   RW value= 0x0 */
    /* DTEST_EN                          [10:1]  RW value= 0x0 */
    /* DTEST_SEL                         [11:5]  RW value= 0x0 */
    /* RESERVE22                         [16:16] RSVD */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_CLK_SGMII_CFM_H_ */

