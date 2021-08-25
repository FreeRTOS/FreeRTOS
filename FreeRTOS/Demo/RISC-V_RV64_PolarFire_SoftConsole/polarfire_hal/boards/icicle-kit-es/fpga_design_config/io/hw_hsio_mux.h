/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_hsio_mux.h
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

#ifndef HW_HSIO_MUX_H_
#define HW_HSIO_MUX_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_TRIM_OPTIONS)
/*User trim options- set option to 1 to use */
#define LIBERO_SETTING_TRIM_OPTIONS    0x00000000UL
    /* TRIM_DDR_OPTION                   [0:1]    */
    /* TRIM_SGMII_OPTION                 [1:1]    */
#endif
#if !defined (LIBERO_SETTING_DDR_IOC_REG0)
/*Manual trim values */
#define LIBERO_SETTING_DDR_IOC_REG0    0x00000000UL
    /* BANK_PCODE                        [0:6]   RW value= 0x0 */
    /* BANK_NCODE                        [6:6]   RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_SGMII_IOC_REG0)
/*Manual trim values */
#define LIBERO_SETTING_SGMII_IOC_REG0    0x00000000UL
    /* BANK_PCODE                        [0:6]   RW value= 0x0 */
    /* BANK_NCODE                        [6:6]   RW value= 0x0 */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_HSIO_MUX_H_ */

