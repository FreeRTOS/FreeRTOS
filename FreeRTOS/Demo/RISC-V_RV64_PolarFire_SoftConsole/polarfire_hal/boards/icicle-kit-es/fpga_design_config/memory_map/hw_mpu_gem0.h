/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_mpu_gem0.h
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

#ifndef HW_MPU_GEM0_H_
#define HW_MPU_GEM0_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_GEM0_MPU_CFG_PMP0)
/*mpu setup register, 64 bits */
#define LIBERO_SETTING_GEM0_MPU_CFG_PMP0    0x1F00000FFFFFFFFFULL
    /* PMP                               [0:38]  RW value= 0xFFFFFFFFF */
    /* RESERVED                          [38:18] RW value= 0x0 */
    /* MODE                              [56:8]  RW value= 0x1F */
#endif
#if !defined (LIBERO_SETTING_GEM0_MPU_CFG_PMP1)
/*mpu setup register, 64 bits */
#define LIBERO_SETTING_GEM0_MPU_CFG_PMP1    0x1F00000FFFFFFFFFULL
    /* PMP                               [0:38]  RW value= 0xFFFFFFFFF */
    /* RESERVED                          [38:18] RW value= 0x0 */
    /* MODE                              [56:8]  RW value= 0x1F */
#endif
#if !defined (LIBERO_SETTING_GEM0_MPU_CFG_PMP2)
/*pmp setup register, 64 bits */
#define LIBERO_SETTING_GEM0_MPU_CFG_PMP2    0x1F00000FFFFFFFFFULL
    /* PMP                               [0:38]  RW value= 0xFFFFFFFFF */
    /* RESERVED                          [38:18] RW value= 0x0 */
    /* MODE                              [56:8]  RW value= 0x1F */
#endif
#if !defined (LIBERO_SETTING_GEM0_MPU_CFG_PMP3)
/*pmp setup register, 64 bits */
#define LIBERO_SETTING_GEM0_MPU_CFG_PMP3    0x1F00000FFFFFFFFFULL
    /* PMP                               [0:38]  RW value= 0xFFFFFFFFF */
    /* RESERVED                          [38:18] RW value= 0x0 */
    /* MODE                              [56:8]  RW value= 0x1F */
#endif
#if !defined (LIBERO_SETTING_GEM0_MPU_CFG_PMP4)
/*pmp setup register, 64 bits */
#define LIBERO_SETTING_GEM0_MPU_CFG_PMP4    0x1F00000FFFFFFFFFULL
    /* PMP                               [0:38]  RW value= 0xFFFFFFFFF */
    /* RESERVED                          [38:18] RW value= 0x0 */
    /* MODE                              [56:8]  RW value= 0x1F */
#endif
#if !defined (LIBERO_SETTING_GEM0_MPU_CFG_PMP5)
/*pmp setup register, 64 bits */
#define LIBERO_SETTING_GEM0_MPU_CFG_PMP5    0x1F00000FFFFFFFFFULL
    /* PMP                               [0:38]  RW value= 0xFFFFFFFFF */
    /* RESERVED                          [38:18] RW value= 0x0 */
    /* MODE                              [56:8]  RW value= 0x1F */
#endif
#if !defined (LIBERO_SETTING_GEM0_MPU_CFG_PMP6)
/*pmp setup register, 64 bits */
#define LIBERO_SETTING_GEM0_MPU_CFG_PMP6    0x1F00000FFFFFFFFFULL
    /* PMP                               [0:38]  RW value= 0xFFFFFFFFF */
    /* RESERVED                          [38:18] RW value= 0x0 */
    /* MODE                              [56:8]  RW value= 0x1F */
#endif
#if !defined (LIBERO_SETTING_GEM0_MPU_CFG_PMP7)
/*pmp setup register, 64 bits */
#define LIBERO_SETTING_GEM0_MPU_CFG_PMP7    0x1F00000FFFFFFFFFULL
    /* PMP                               [0:38]  RW value= 0xFFFFFFFFF */
    /* RESERVED                          [38:18] RW value= 0x0 */
    /* MODE                              [56:8]  RW value= 0x1F */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_MPU_GEM0_H_ */

