/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_sgmii_tip.h
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

#ifndef HW_SGMII_TIP_H_
#define HW_SGMII_TIP_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_SGMII_MODE)
/*SGMII mode control (SEU) */
#define LIBERO_SETTING_SGMII_MODE    0x08C0E6FFUL
    /* REG_PLL_EN                        [0:1]   RW value= 0x1 */
    /* REG_DLL_EN                        [1:1]   RW value= 0x1 */
    /* REG_PVT_EN                        [2:1]   RW value= 0x1 */
    /* REG_BC_VRGEN_EN                   [3:1]   RW value= 0x1 */
    /* REG_TX0_EN                        [4:1]   RW value= 0x1 */
    /* REG_RX0_EN                        [5:1]   RW value= 0x1 */
    /* REG_TX1_EN                        [6:1]   RW value= 0x1 */
    /* REG_RX1_EN                        [7:1]   RW value= 0x1 */
    /* REG_DLL_LOCK_FLT                  [8:2]   RW value= 0x2 */
    /* REG_DLL_ADJ_CODE                  [10:4]  RW value= 0x9 */
    /* REG_CH0_CDR_RESET_B               [14:1]  RW value= 0x1 */
    /* REG_CH1_CDR_RESET_B               [15:1]  RW value= 0x1 */
    /* REG_BC_VRGEN                      [16:6]  RW value= 0x00 */
    /* REG_CDR_MOVE_STEP                 [22:1]  RW value= 0x1 */
    /* REG_REFCLK_EN_RDIFF               [23:1]  RW value= 0x1 */
    /* REG_BC_VS                         [24:4]  RW value= 0x8 */
    /* REG_REFCLK_EN_UDRIVE_P            [28:1]  RW value= 0x0 */
    /* REG_REFCLK_EN_INS_HYST_P          [29:1]  RW value= 0x0 */
    /* REG_REFCLK_EN_UDRIVE_N            [30:1]  RW value= 0x0 */
    /* REG_REFCLK_EN_INS_HYST_N          [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_PLL_CNTL)
/*PLL control register (SEU) */
#define LIBERO_SETTING_PLL_CNTL    0x80140101UL
    /* REG_PLL_POSTDIV                   [0:7]   RW value= 0x1 */
    /* ARO_PLL0_LOCK                     [7:1]   RO */
    /* REG_PLL_RFDIV                     [8:6]   RW value= 0x1 */
    /* REG_PLL_REG_RFCLK_SEL             [14:1]  RW value= 0x0 */
    /* REG_PLL_LP_REQUIRES_LOCK          [15:1]  RW value= 0x0 */
    /* REG_PLL_INTIN                     [16:12] RW value= 0x14 */
    /* REG_PLL_BWI                       [28:2]  RW value= 0x0 */
    /* REG_PLL_BWP                       [30:2]  RW value= 0x2 */
#endif
#if !defined (LIBERO_SETTING_CH0_CNTL)
/*Channel0 control register */
#define LIBERO_SETTING_CH0_CNTL    0x37F07770UL
    /* REG_TX0_WPU_P                     [0:1]   RW value= 0x0 */
    /* REG_TX0_WPD_P                     [1:1]   RW value= 0x0 */
    /* REG_TX0_SLEW_P                    [2:2]   RW value= 0x0 */
    /* REG_TX0_DRV_P                     [4:4]   RW value= 0x7 */
    /* REG_TX0_ODT_P                     [8:4]   RW value= 0x7 */
    /* REG_TX0_ODT_STATIC_P              [12:3]  RW value= 0x7 */
    /* REG_RX0_TIM_LONG                  [15:1]  RW value= 0x0 */
    /* REG_RX0_WPU_P                     [16:1]  RW value= 0x0 */
    /* REG_RX0_WPD_P                     [17:1]  RW value= 0x0 */
    /* REG_RX0_IBUFMD_P                  [18:3]  RW value= 0x4 */
    /* REG_RX0_EYEWIDTH_P                [21:3]  RW value= 0x7 */
    /* REG_RX0_ODT_P                     [24:4]  RW value= 0x7 */
    /* REG_RX0_ODT_STATIC_P              [28:3]  RW value= 0x3 */
    /* REG_RX0_EN_FLAG_N                 [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CH1_CNTL)
/*Channel1 control register */
#define LIBERO_SETTING_CH1_CNTL    0x37F07770UL
    /* REG_TX1_WPU_P                     [0:1]   RW value= 0x0 */
    /* REG_TX1_WPD_P                     [1:1]   RW value= 0x0 */
    /* REG_TX1_SLEW_P                    [2:2]   RW value= 0x0 */
    /* REG_TX1_DRV_P                     [4:4]   RW value= 0x7 */
    /* REG_TX1_ODT_P                     [8:4]   RW value= 0x7 */
    /* REG_TX1_ODT_STATIC_P              [12:3]  RW value= 0x7 */
    /* REG_RX1_TIM_LONG                  [15:1]  RW value= 0x0 */
    /* REG_RX1_WPU_P                     [16:1]  RW value= 0x0 */
    /* REG_RX1_WPD_P                     [17:1]  RW value= 0x0 */
    /* REG_RX1_IBUFMD_P                  [18:3]  RW value= 0x4 */
    /* REG_RX1_EYEWIDTH_P                [21:3]  RW value= 0x7 */
    /* REG_RX1_ODT_P                     [24:4]  RW value= 0x7 */
    /* REG_RX1_ODT_STATIC_P              [28:3]  RW value= 0x3 */
    /* REG_RX1_EN_FLAG_N                 [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RECAL_CNTL)
/*Recalibration control register */
#define LIBERO_SETTING_RECAL_CNTL    0x000020C8UL
    /* REG_RECAL_DIFF_RANGE              [0:5]   RW value= 0x8 */
    /* REG_RECAL_START_EN                [5:1]   RW value= 0x0 */
    /* REG_PVT_CALIB_START               [6:1]   RW value= 0x1 */
    /* REG_PVT_CALIB_LOCK                [7:1]   RW value= 0x1 */
    /* REG_RECAL_UPD                     [8:1]   RW value= 0x0 */
    /* BC_VRGEN_DIRECTION                [9:1]   RW value= 0x0 */
    /* BC_VRGEN_LOAD                     [10:1]  RW value= 0x0 */
    /* BC_VRGEN_MOVE                     [11:1]  RW value= 0x0 */
    /* REG_PVT_REG_CALIB_CLKDIV          [12:2]  RW value= 0x2 */
    /* REG_PVT_REG_CALIB_DIFFR_VSEL      [14:2]  RW value= 0x0 */
    /* SRO_DLL_90_CODE                   [16:7]  RO */
    /* SRO_DLL_LOCK                      [23:1]  RO */
    /* SRO_DLL_ST_CODE                   [24:7]  RO */
    /* SRO_RECAL_START                   [31:1]  RO */
#endif
#if !defined (LIBERO_SETTING_CLK_CNTL)
/*Clock input and routing control registers */
#define LIBERO_SETTING_CLK_CNTL    0xF00050CCUL
    /* REG_REFCLK_EN_TERM_P              [0:2]   RW value= 0x0 */
    /* REG_REFCLK_EN_RXMODE_P            [2:2]   RW value= 0x3 */
    /* REG_REFCLK_EN_TERM_N              [4:2]   RW value= 0x0 */
    /* REG_REFCLK_EN_RXMODE_N            [6:2]   RW value= 0x3 */
    /* REG_REFCLK_CLKBUF_EN_PULLUP       [8:1]   RW value= 0x0 */
    /* REG_CLKMUX_FCLK_SEL               [9:3]   RW value= 0x0 */
    /* REG_CLKMUX_PLL0_RFCLK0_SEL        [12:2]  RW value= 0x1 */
    /* REG_CLKMUX_PLL0_RFCLK1_SEL        [14:2]  RW value= 0x1 */
    /* REG_CLKMUX_SPARE0                 [16:16] RW value= 0xf000 */
#endif
#if !defined (LIBERO_SETTING_DYN_CNTL)
/*Dynamic control registers */
#define LIBERO_SETTING_DYN_CNTL    0x00000000UL
    /* REG_PLL_DYNEN                     [0:1]   RW value= 0x0 */
    /* REG_DLL_DYNEN                     [1:1]   RW value= 0x0 */
    /* REG_PVT_DYNEN                     [2:1]   RW value= 0x0 */
    /* REG_BC_DYNEN                      [3:1]   RW value= 0x0 */
    /* REG_CLKMUX_DYNEN                  [4:1]   RW value= 0x0 */
    /* REG_LANE0_DYNEN                   [5:1]   RW value= 0x0 */
    /* REG_LANE1_DYNEN                   [6:1]   RW value= 0x0 */
    /* BC_VRGEN_OOR                      [7:1]   RO */
    /* REG_PLL_SOFT_RESET_PERIPH         [8:1]   RW value= 0x0 */
    /* REG_DLL_SOFT_RESET_PERIPH         [9:1]   RW value= 0x0 */
    /* REG_PVT_SOFT_RESET_PERIPH         [10:1]  RW value= 0x0 */
    /* REG_BC_SOFT_RESET_PERIPH          [11:1]  RW value= 0x0 */
    /* REG_CLKMUX_SOFT_RESET_PERIPH      [12:1]  RW value= 0x0 */
    /* REG_LANE0_SOFT_RESET_PERIPH       [13:1]  RW value= 0x0 */
    /* REG_LANE1_SOFT_RESET_PERIPH       [14:1]  RW value= 0x0 */
    /* PVT_CALIB_STATUS                  [15:1]  RO */
    /* ARO_PLL0_VCO0PH_SEL               [16:3]  RO */
    /* ARO_PLL0_VCO1PH_SEL               [19:3]  RO */
    /* ARO_PLL0_VCO2PH_SEL               [22:3]  RO */
    /* ARO_PLL0_VCO3PH_SEL               [25:3]  RO */
    /* ARO_REF_DIFFR                     [28:4]  RO */
#endif
#if !defined (LIBERO_SETTING_PVT_STAT)
/*PVT calibrator status registers */
#define LIBERO_SETTING_PVT_STAT    0x00000000UL
    /* ARO_REF_PCODE                     [0:6]   RO */
    /* ARO_IOEN_BNK                      [6:1]   RO */
    /* ARO_IOEN_BNK_B                    [7:1]   RO */
    /* ARO_REF_NCODE                     [8:6]   RO */
    /* ARO_CALIB_STATUS                  [14:1]  RO */
    /* ARO_CALIB_STATUS_B                [15:1]  RO */
    /* ARO_PCODE                         [16:6]  RO */
    /* ARO_CALIB_INTRPT                  [22:1]  RO */
    /* PVT_CALIB_INTRPT                  [23:1]  RO */
    /* ARO_NCODE                         [24:6]  RO */
    /* PVT_CALIB_LOCK                    [30:1]  RW value= 0x0 */
    /* PVT_CALIB_START                   [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SPARE_CNTL)
/*Spare control register */
#define LIBERO_SETTING_SPARE_CNTL    0xFF000000UL
    /* REG_SPARE                         [0:32]  RW value= 0xFF000000 */
#endif
#if !defined (LIBERO_SETTING_SPARE_STAT)
/*Spare status register */
#define LIBERO_SETTING_SPARE_STAT    0x00000000UL
    /* SRO_SPARE                         [0:32]  RO */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_SGMII_TIP_H_ */

