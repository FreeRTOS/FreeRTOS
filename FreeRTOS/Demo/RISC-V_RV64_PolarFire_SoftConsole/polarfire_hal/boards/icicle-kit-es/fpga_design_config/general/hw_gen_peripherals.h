/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_gen_peripherals.h
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

#ifndef HW_GEN_PERIPHERALS_H_
#define HW_GEN_PERIPHERALS_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_GPIO_CR)
/*GPIO Blocks reset control- (soft_reset options chossen in Libero confgurator)
*/
#define LIBERO_SETTING_GPIO_CR    0x000F0703UL
    /* GPIO0_SOFT_RESET_SELECT           [0:2]   RW value= 0x3 */
    /* GPIO0_DEFAULT                     [4:2]   RW value= 0x0 */
    /* GPIO1_SOFT_RESET_SELECT           [8:3]   RW value= 0x7 */
    /* GPIO1_DEFAULT                     [12:3]  RW value= 0x0 */
    /* GPIO2_SOFT_RESET_SELECT           [16:4]  RW value= 0xF */
    /* GPIO2_DEFAULT                     [20:4]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CRYPTO_CR_INFO)
/*Information on how Crypto setup on this MPFS */
#define LIBERO_SETTING_CRYPTO_CR_INFO    0x00000000UL
    /* MSS_MODE                          [0:2]   RO */
    /* RESERVED                          [2:1]   RO */
    /* STREAM_ENABLE                     [3:1]   RO */
    /* RESERVED1                         [4:28]  RO */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_GEN_PERIPHERALS_H_ */

