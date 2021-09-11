/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_clk_mss_cfm.h
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

#ifndef HW_CLK_MSS_CFM_H_
#define HW_CLK_MSS_CFM_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_MSS_BCLKMUX)
/*Input mux selections */
#define LIBERO_SETTING_MSS_BCLKMUX    0x00000208UL
    /* BCLK0_SEL                         [0:5]   RW value= 0x8 */
    /* BCLK1_SEL                         [5:5]   RW value= 0x10 */
    /* BCLK2_SEL                         [10:5]  RW value= 0x0 */
    /* BCLK3_SEL                         [15:5]  RW value= 0x0 */
    /* BCLK4_SEL                         [20:5]  RW value= 0x0 */
    /* BCLK5_SEL                         [25:5]  RW value= 0x0 */
    /* RESERVED                          [30:2]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_MSS_PLL_CKMUX)
/*Input mux selections */
#define LIBERO_SETTING_MSS_PLL_CKMUX    0x00000155UL
    /* CLK_IN_MAC_TSU_SEL                [0:2]   RW value= 0x1 */
    /* PLL0_RFCLK0_SEL                   [2:2]   RW value= 0x1 */
    /* PLL0_RFCLK1_SEL                   [4:2]   RW value= 0x1 */
    /* PLL1_RFCLK0_SEL                   [6:2]   RW value= 0x1 */
    /* PLL1_RFCLK1_SEL                   [8:2]   RW value= 0x1 */
    /* PLL1_FDR_SEL                      [10:5]  RW value= 0x0 */
    /* RESERVED                          [15:17] RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_MSS_MSSCLKMUX)
/*MSS Clock mux selections */
#define LIBERO_SETTING_MSS_MSSCLKMUX    0x00000003UL
    /* MSSCLK_MUX_SEL                    [0:2]   RW value= 0x3 */
    /* MSSCLK_MUX_MD                     [2:2]   RW value= 0x0 */
    /* CLK_STANDBY_SEL                   [4:1]   RW value= 0x0 */
    /* RESERVED                          [5:27]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_MSS_SPARE0)
/*spare logic */
#define LIBERO_SETTING_MSS_SPARE0    0x00000000UL
    /* SPARE0                            [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_MSS_FMETER_ADDR)
/*Frequency_meter_address_selections */
#define LIBERO_SETTING_MSS_FMETER_ADDR    0x00000000UL
    /* ADDR10                            [0:2]   RSVD */
    /* ADDR                              [2:4]   RW value= 0x0 */
    /* RESERVE18                         [6:26]  RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_FMETER_DATAW)
/*Frequency_meter_data_write */
#define LIBERO_SETTING_MSS_FMETER_DATAW    0x00000000UL
    /* DATA                              [0:24]  RW value= 0x0 */
    /* STROBE                            [24:1]  W1P */
    /* RESERVE19                         [25:7]  RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_FMETER_DATAR)
/*Frequency_meter_data_read */
#define LIBERO_SETTING_MSS_FMETER_DATAR    0x00000000UL
    /* DATA                              [0:24]  RO */
    /* RESERVE20                         [24:8]  RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_IMIRROR_TRIM)
/*Imirror TRIM Bits */
#define LIBERO_SETTING_MSS_IMIRROR_TRIM    0x00000000UL
    /* BG_CODE                           [0:3]   RW value= 0x0 */
    /* CC_CODE                           [3:8]   RW value= 0x0 */
    /* RESERVE21                         [11:21] RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_TEST_CTRL)
/*Test MUX Controls */
#define LIBERO_SETTING_MSS_TEST_CTRL    0x00000000UL
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


#endif /* #ifdef HW_CLK_MSS_CFM_H_ */

