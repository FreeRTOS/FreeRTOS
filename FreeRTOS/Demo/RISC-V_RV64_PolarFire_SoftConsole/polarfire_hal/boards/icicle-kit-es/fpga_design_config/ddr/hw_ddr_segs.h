/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_ddr_segs.h
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

#ifndef HW_DDR_SEGS_H_
#define HW_DDR_SEGS_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_SEG0_0)
/*Cached access at 0x00_8000_0000 (-0x80+0x00) */
#define LIBERO_SETTING_SEG0_0    0x80007F80UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x7F80 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_SEG0_1)
/*Cached access at 0x10_0000_000 */
#define LIBERO_SETTING_SEG0_1    0x80007030UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x7030 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_SEG0_2)
/*not used */
#define LIBERO_SETTING_SEG0_2    0x00000000UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x0 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SEG0_3)
/*not used */
#define LIBERO_SETTING_SEG0_3    0x00000000UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x0 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SEG0_4)
/*not used */
#define LIBERO_SETTING_SEG0_4    0x00000000UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x0 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SEG0_5)
/*not used */
#define LIBERO_SETTING_SEG0_5    0x00000000UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x0 */
    /* RESERVED                          [15:6]  RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SEG0_6)
/*not used */
#define LIBERO_SETTING_SEG0_6    0x00000000UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x0 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SEG0_7)
/*not used */
#define LIBERO_SETTING_SEG0_7    0x00000000UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x0 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SEG1_0)
/*not used */
#define LIBERO_SETTING_SEG1_0    0x00000000UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x0 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SEG1_1)
/*not used */
#define LIBERO_SETTING_SEG1_1    0x00000000UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x0 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SEG1_2)
/*Non-Cached access at 0x00_c000_0000 */
#define LIBERO_SETTING_SEG1_2    0x80007FB0UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x7FB0 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_SEG1_3)
/*Non-Cached access at 0x14_0000_0000 */
#define LIBERO_SETTING_SEG1_3    0x80000000UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x0 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_SEG1_4)
/*Non-Cached WCB access at 0x00_d000_0000 */
#define LIBERO_SETTING_SEG1_4    0x80007FA0UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x7FA0 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_SEG1_5)
/*Non-Cached WCB 0x18_0000_0000 */
#define LIBERO_SETTING_SEG1_5    0x80000000UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x0 */
    /* RESERVED                          [15:6]  RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_SEG1_6)
/*Trace - Trace not in use here so can be left as 0 */
#define LIBERO_SETTING_SEG1_6    0x00000000UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x0 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SEG1_7)
/*not used */
#define LIBERO_SETTING_SEG1_7    0x00000000UL
    /* ADDRESS_OFFSET                    [0:15]  RW value= 0x0 */
    /* RESERVED                          [15:16] RW value= 0x0 */
    /* LOCKED                            [31:1]  RW value= 0x0 */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_DDR_SEGS_H_ */

