/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_apb_split.h
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

#ifndef HW_APB_SPLIT_H_
#define HW_APB_SPLIT_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_APB_SPLIT_VERSION)
/*This version incrments when change to format of this file */
#define LIBERO_SETTING_APB_SPLIT_VERSION    0x00000001UL
    /* VERSION                           [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_MEM_CONFIGS_ENABLED)
/*Enabled in configurator when bit set to 1 */
#define LIBERO_SETTING_MEM_CONFIGS_ENABLED    0x00000000UL
    /* PMP                               [0:0]   RW value= 0x0 */
    /* MPU                               [1:0]   RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_APBBUS_CR)
/*AMP Mode peripheral mapping register. When the register bit is '0' the
peripheral is mapped into the 0x2000000 address range using AXI bus 5 from the
Coreplex. When the register bit is '1' the peripheral is mapped into the
0x28000000 address range using AXI bus 6 from the Coreplex. */
#define LIBERO_SETTING_APBBUS_CR    0x00000000UL
    /* MMUART0                           [0:1]   RW value= 0x0 */
    /* MMUART1                           [1:1]   RW value= 0x0 */
    /* MMUART2                           [2:1]   RW value= 0x0 */
    /* MMUART3                           [3:1]   RW value= 0x0 */
    /* MMUART4                           [4:1]   RW value= 0x0 */
    /* WDOG0                             [5:1]   RW value= 0x0 */
    /* WDOG1                             [6:1]   RW value= 0x0 */
    /* WDOG2                             [7:1]   RW value= 0x0 */
    /* WDOG3                             [8:1]   RW value= 0x0 */
    /* WDOG4                             [9:1]   RW value= 0x0 */
    /* SPI0                              [10:1]  RW value= 0x0 */
    /* SPI1                              [11:1]  RW value= 0x0 */
    /* I2C0                              [12:1]  RW value= 0x0 */
    /* I2C1                              [13:1]  RW value= 0x0 */
    /* CAN0                              [14:1]  RW value= 0x0 */
    /* CAN1                              [15:1]  RW value= 0x0 */
    /* GEM0                              [16:1]  RW value= 0x0 */
    /* GEM1                              [17:1]  RW value= 0x0 */
    /* TIMER                             [18:1]  RW value= 0x0 */
    /* GPIO0                             [19:1]  RW value= 0x0 */
    /* GPIO1                             [20:1]  RW value= 0x0 */
    /* GPIO2                             [21:1]  RW value= 0x0 */
    /* RTC                               [22:1]  RW value= 0x0 */
    /* H2FINT                            [23:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CONTEXT_A_EN)
/*AMP context A. When the register bit is '0' the peripheral is not allowed
access from context A. */
#define LIBERO_SETTING_CONTEXT_A_EN    0x00000000UL
    /* MMUART0                           [0:1]   RW value= 0x0 */
    /* MMUART1                           [1:1]   RW value= 0x0 */
    /* MMUART2                           [2:1]   RW value= 0x0 */
    /* MMUART3                           [3:1]   RW value= 0x0 */
    /* MMUART4                           [4:1]   RW value= 0x0 */
    /* WDOG0                             [5:1]   RW value= 0x0 */
    /* WDOG1                             [6:1]   RW value= 0x0 */
    /* WDOG2                             [7:1]   RW value= 0x0 */
    /* WDOG3                             [8:1]   RW value= 0x0 */
    /* WDOG4                             [9:1]   RW value= 0x0 */
    /* SPI0                              [10:1]  RW value= 0x0 */
    /* SPI1                              [11:1]  RW value= 0x0 */
    /* I2C0                              [12:1]  RW value= 0x0 */
    /* I2C1                              [13:1]  RW value= 0x0 */
    /* CAN0                              [14:1]  RW value= 0x0 */
    /* CAN1                              [15:1]  RW value= 0x0 */
    /* GEM0                              [16:1]  RW value= 0x0 */
    /* GEM1                              [17:1]  RW value= 0x0 */
    /* TIMER                             [18:1]  RW value= 0x0 */
    /* GPIO0                             [19:1]  RW value= 0x0 */
    /* GPIO1                             [20:1]  RW value= 0x0 */
    /* GPIO2                             [21:1]  RW value= 0x0 */
    /* RTC                               [22:1]  RW value= 0x0 */
    /* H2FINT                            [23:1]  RW value= 0x0 */
    /* CRYPTO                            [24:1]  RW value= 0x0 */
    /* USB                               [25:1]  RW value= 0x0 */
    /* QSPIXIP                           [26:1]  RW value= 0x0 */
    /* ATHENA                            [27:1]  RW value= 0x0 */
    /* TRACE                             [28:1]  RW value= 0x0 */
    /* MAILBOX_SC                        [29:1]  RW value= 0x0 */
    /* EMMC                              [30:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CONTEXT_B_EN)
/*AMP context B. When the register bit is '0' the peripheral is not allowed
access from context B. */
#define LIBERO_SETTING_CONTEXT_B_EN    0x00000000UL
    /* MMUART0                           [0:1]   RW value= 0x0 */
    /* MMUART1                           [1:1]   RW value= 0x0 */
    /* MMUART2                           [2:1]   RW value= 0x0 */
    /* MMUART3                           [3:1]   RW value= 0x0 */
    /* MMUART4                           [4:1]   RW value= 0x0 */
    /* WDOG0                             [5:1]   RW value= 0x0 */
    /* WDOG1                             [6:1]   RW value= 0x0 */
    /* WDOG2                             [7:1]   RW value= 0x0 */
    /* WDOG3                             [8:1]   RW value= 0x0 */
    /* WDOG4                             [9:1]   RW value= 0x0 */
    /* SPI0                              [10:1]  RW value= 0x0 */
    /* SPI1                              [11:1]  RW value= 0x0 */
    /* I2C0                              [12:1]  RW value= 0x0 */
    /* I2C1                              [13:1]  RW value= 0x0 */
    /* CAN0                              [14:1]  RW value= 0x0 */
    /* CAN1                              [15:1]  RW value= 0x0 */
    /* GEM0                              [16:1]  RW value= 0x0 */
    /* GEM1                              [17:1]  RW value= 0x0 */
    /* TIMER                             [18:1]  RW value= 0x0 */
    /* GPIO0                             [19:1]  RW value= 0x0 */
    /* GPIO1                             [20:1]  RW value= 0x0 */
    /* GPIO2                             [21:1]  RW value= 0x0 */
    /* RTC                               [22:1]  RW value= 0x0 */
    /* H2FINT                            [23:1]  RW value= 0x0 */
    /* CRYPTO                            [24:1]  RW value= 0x0 */
    /* USB                               [25:1]  RW value= 0x0 */
    /* QSPIXIP                           [26:1]  RW value= 0x0 */
    /* ATHENA                            [27:1]  RW value= 0x0 */
    /* TRACE                             [28:1]  RW value= 0x0 */
    /* MAILBOX_SC                        [29:1]  RW value= 0x0 */
    /* EMMC                              [30:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CONTEXT_A_HART_EN)
/*When the register bit is '0' hart is not associated with context A. */
#define LIBERO_SETTING_CONTEXT_A_HART_EN    0x00000000UL
    /* HART0                             [0:1]   RW value= 0x0 */
    /* HART1                             [1:1]   RW value= 0x0 */
    /* HART2                             [2:1]   RW value= 0x0 */
    /* HART3                             [3:1]   RW value= 0x0 */
    /* HART4                             [4:1]   RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CONTEXT_B_HART_EN)
/*When the register bit is '0' hart is not associated with context B. */
#define LIBERO_SETTING_CONTEXT_B_HART_EN    0x00000000UL
    /* HART0                             [0:1]   RW value= 0x0 */
    /* HART1                             [1:1]   RW value= 0x0 */
    /* HART2                             [2:1]   RW value= 0x0 */
    /* HART3                             [3:1]   RW value= 0x0 */
    /* HART4                             [4:1]   RW value= 0x0 */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_APB_SPLIT_H_ */

