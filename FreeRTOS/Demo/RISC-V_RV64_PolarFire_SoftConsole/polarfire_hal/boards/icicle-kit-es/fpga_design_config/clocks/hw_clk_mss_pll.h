/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_clk_mss_pll.h
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

#ifndef HW_CLK_MSS_PLL_H_
#define HW_CLK_MSS_PLL_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_MSS_PLL_CTRL)
/*PLL control register */
#define LIBERO_SETTING_MSS_PLL_CTRL    0x01000037UL
    /* REG_POWERDOWN_B                   [0:1]   RW value= 0x1 */
    /* REG_RFDIV_EN                      [1:1]   RW value= 0x1 */
    /* REG_DIVQ0_EN                      [2:1]   RW value= 0x1 */
    /* REG_DIVQ1_EN                      [3:1]   RW value= 0x0 */
    /* REG_DIVQ2_EN                      [4:1]   RW value= 0x1 */
    /* REG_DIVQ3_EN                      [5:1]   RW value= 0x1 */
    /* REG_RFCLK_SEL                     [6:1]   RW value= 0x0 */
    /* RESETONLOCK                       [7:1]   RW value= 0x0 */
    /* BYPCK_SEL                         [8:4]   RW value= 0x0 */
    /* REG_BYPASS_GO_B                   [12:1]  RW value= 0x0 */
    /* RESERVE10                         [13:3]  RSVD */
    /* REG_BYPASSPRE                     [16:4]  RW value= 0x0 */
    /* REG_BYPASSPOST                    [20:4]  RW value= 0x0 */
    /* LP_REQUIRES_LOCK                  [24:1]  RW value= 0x1 */
    /* LOCK                              [25:1]  RO */
    /* LOCK_INT_EN                       [26:1]  RW value= 0x0 */
    /* UNLOCK_INT_EN                     [27:1]  RW value= 0x0 */
    /* LOCK_INT                          [28:1]  SW1C */
    /* UNLOCK_INT                        [29:1]  SW1C */
    /* RESERVE11                         [30:1]  RSVD */
    /* LOCK_B                            [31:1]  RO */
#endif
#if !defined (LIBERO_SETTING_MSS_PLL_REF_FB)
/*PLL reference and feedback registers */
#define LIBERO_SETTING_MSS_PLL_REF_FB    0x00000500UL
    /* FSE_B                             [0:1]   RW value= 0x0 */
    /* FBCK_SEL                          [1:2]   RW value= 0x0 */
    /* FOUTFB_SELMUX_EN                  [3:1]   RW value= 0x0 */
    /* RESERVE12                         [4:4]   RSVD */
    /* RFDIV                             [8:6]   RW value= 0x5 */
    /* RESERVE13                         [14:2]  RSVD */
    /* RESERVE14                         [16:12] RSVD */
    /* RESERVE15                         [28:4]  RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_PLL_FRACN)
/*PLL fractional register */
#define LIBERO_SETTING_MSS_PLL_FRACN    0x00000000UL
    /* FRACN_EN                          [0:1]   RW value= 0x0 */
    /* FRACN_DAC_EN                      [1:1]   RW value= 0x0 */
    /* RESERVE16                         [2:6]   RSVD */
    /* RESERVE17                         [8:24]  RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_PLL_DIV_0_1)
/*PLL 0/1 division registers */
#define LIBERO_SETTING_MSS_PLL_DIV_0_1    0x01000200UL
    /* VCO0PH_SEL                        [0:3]   RO */
    /* DIV0_START                        [3:3]   RW value= 0x0 */
    /* RESERVE18                         [6:2]   RSVD */
    /* POST0DIV                          [8:7]   RW value= 0x2 */
    /* RESERVE19                         [15:1]  RSVD */
    /* VCO1PH_SEL                        [16:3]  RO */
    /* DIV1_START                        [19:3]  RW value= 0x0 */
    /* RESERVE20                         [22:2]  RSVD */
    /* POST1DIV                          [24:7]  RW value= 0x1 */
    /* RESERVE21                         [31:1]  RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_PLL_DIV_2_3)
/*PLL 2/3 division registers */
#define LIBERO_SETTING_MSS_PLL_DIV_2_3    0x0F000600UL
    /* VCO2PH_SEL                        [0:3]   RO */
    /* DIV2_START                        [3:3]   RW value= 0x0 */
    /* RESERVE22                         [6:2]   RSVD */
    /* POST2DIV                          [8:7]   RW value= 0x6 */
    /* RESERVE23                         [15:1]  RSVD */
    /* VCO3PH_SEL                        [16:3]  RO */
    /* DIV3_START                        [19:3]  RW value= 0x0 */
    /* RESERVE24                         [22:2]  RSVD */
    /* POST3DIV                          [24:7]  RW value= 0xF */
    /* CKPOST3_SEL                       [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_MSS_PLL_CTRL2)
/*PLL control register */
#define LIBERO_SETTING_MSS_PLL_CTRL2    0x00001020UL
    /* BWI                               [0:2]   RW value= 0x0 */
    /* BWP                               [2:2]   RW value= 0x0 */
    /* IREF_EN                           [4:1]   RW value= 0x0 */
    /* IREF_TOGGLE                       [5:1]   RW value= 0x1 */
    /* RESERVE25                         [6:3]   RSVD */
    /* LOCKCNT                           [9:4]   RW value= 0x8 */
    /* RESERVE26                         [13:4]  RSVD */
    /* ATEST_EN                          [17:1]  RW value= 0x0 */
    /* ATEST_SEL                         [18:3]  RW value= 0x0 */
    /* RESERVE27                         [21:11] RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_PLL_CAL)
/*PLL calibration register */
#define LIBERO_SETTING_MSS_PLL_CAL    0x00000D06UL
    /* DSKEWCALCNT                       [0:3]   RW value= 0x6 */
    /* DSKEWCAL_EN                       [3:1]   RW value= 0x0 */
    /* DSKEWCALBYP                       [4:1]   RW value= 0x0 */
    /* RESERVE28                         [5:3]   RSVD */
    /* DSKEWCALIN                        [8:7]   RW value= 0xd */
    /* RESERVE29                         [15:1]  RSVD */
    /* DSKEWCALOUT                       [16:7]  RO */
    /* RESERVE30                         [23:9]  RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_PLL_PHADJ)
/*PLL phase registers */
#define LIBERO_SETTING_MSS_PLL_PHADJ    0x00004003UL
    /* PLL_REG_SYNCREFDIV_EN             [0:1]   RW value= 0x1 */
    /* PLL_REG_ENABLE_SYNCREFDIV         [1:1]   RW value= 0x1 */
    /* REG_OUT0_PHSINIT                  [2:3]   RW value= 0x0 */
    /* REG_OUT1_PHSINIT                  [5:3]   RW value= 0x0 */
    /* REG_OUT2_PHSINIT                  [8:3]   RW value= 0x0 */
    /* REG_OUT3_PHSINIT                  [11:3]  RW value= 0x8 */
    /* REG_LOADPHS_B                     [14:1]  RW value= 0x0 */
    /* RESERVE31                         [15:17] RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_SSCG_REG_0)
/*SSCG registers 0 */
#define LIBERO_SETTING_MSS_SSCG_REG_0    0x00000000UL
    /* DIVVAL                            [0:6]   RW value= 0x0 */
    /* FRACIN                            [6:24]  RW value= 0x0 */
    /* RESERVE00                         [30:2]  RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_SSCG_REG_1)
/*SSCG registers 1 */
#define LIBERO_SETTING_MSS_SSCG_REG_1    0x00000000UL
    /* DOWNSPREAD                        [0:1]   RW value= 0x0 */
    /* SSMD                              [1:5]   RW value= 0x0 */
    /* FRACMOD                           [6:24]  RO */
    /* RESERVE01                         [30:2]  RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_SSCG_REG_2)
/*SSCG registers 2 */
#define LIBERO_SETTING_MSS_SSCG_REG_2    0x000000C0UL
    /* INTIN                             [0:12]  RW value= 0xC0 */
    /* INTMOD                            [12:12] RO */
    /* RESERVE02                         [24:8]  RSVD */
#endif
#if !defined (LIBERO_SETTING_MSS_SSCG_REG_3)
/*SSCG registers 3 */
#define LIBERO_SETTING_MSS_SSCG_REG_3    0x00000001UL
    /* SSE_B                             [0:1]   RW value= 0x1 */
    /* SEL_EXTWAVE                       [1:2]   RW value= 0x0 */
    /* EXT_MAXADDR                       [3:8]   RW value= 0x0 */
    /* TBLADDR                           [11:8]  RO */
    /* RANDOM_FILTER                     [19:1]  RW value= 0x0 */
    /* RANDOM_SEL                        [20:2]  RW value= 0x0 */
    /* RESERVE03                         [22:1]  RSVD */
    /* RESERVE04                         [23:9]  RSVD */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_CLK_MSS_PLL_H_ */

