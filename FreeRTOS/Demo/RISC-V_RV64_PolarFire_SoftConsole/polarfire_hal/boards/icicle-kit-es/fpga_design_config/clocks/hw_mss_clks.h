/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_mss_clks.h
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

#ifndef HW_MSS_CLKS_H_
#define HW_MSS_CLKS_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_MSS_EXT_SGMII_REF_CLK)
/*Ref Clock rate in MHz */
#define LIBERO_SETTING_MSS_EXT_SGMII_REF_CLK    125000000
    /* MSS_EXT_SGMII_REF_CLK             [0:32]  RW value= 125000000 */
#endif
#if !defined (LIBERO_SETTING_MSS_COREPLEX_CPU_CLK)
/*CPU Clock rate in MHz */
#define LIBERO_SETTING_MSS_COREPLEX_CPU_CLK    600000000
    /* MSS_COREPLEX_CPU_CLK              [0:32]  RW value= 600000000 */
#endif
#if !defined (LIBERO_SETTING_MSS_SYSTEM_CLK)
/*System Clock rate in MHz static power. */
#define LIBERO_SETTING_MSS_SYSTEM_CLK    600000000
    /* MSS_SYSTEM_CLK                    [0:32]  RW value= 600000000 */
#endif
#if !defined (LIBERO_SETTING_MSS_RTC_TOGGLE_CLK)
/*RTC toggle Clock rate in MHz static power. */
#define LIBERO_SETTING_MSS_RTC_TOGGLE_CLK    1000000
    /* MSS_RTC_TOGGLE_CLK                [0:32]  RW value= 1000000 */
#endif
#if !defined (LIBERO_SETTING_MSS_AXI_CLK)
/*AXI Clock rate in MHz static power. */
#define LIBERO_SETTING_MSS_AXI_CLK    300000000
    /* MSS_AXI_CLK                       [0:32]  RW value= 300000000 */
#endif
#if !defined (LIBERO_SETTING_MSS_APB_AHB_CLK)
/*AXI Clock rate in MHz static power. */
#define LIBERO_SETTING_MSS_APB_AHB_CLK    150000000
    /* MSS_APB_AHB_CLK                   [0:32]  RW value= 150000000 */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_MSS_CLKS_H_ */

