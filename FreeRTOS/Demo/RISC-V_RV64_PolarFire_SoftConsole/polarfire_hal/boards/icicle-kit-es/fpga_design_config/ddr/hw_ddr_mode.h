/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_ddr_mode.h
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

#ifndef HW_DDR_MODE_H_
#define HW_DDR_MODE_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_DDRPHY_MODE)
/*DDRPHY MODE (binary)- 000 ddr3, 001 ddr33L, 010 ddr4, 011 LPDDR3, 100 LPDDR4,
111 OFF_MODE */
#define LIBERO_SETTING_DDRPHY_MODE    0x00014B24UL
    /* DDRMODE                           [0:3]   RW value= 0x4 */
    /* ECC                               [3:1]   RW value= 0x0 */
    /* CRC                               [4:1]   RW value= 0x0 */
    /* BUS_WIDTH                         [5:3]   RW value= 0x1 */
    /* DMI_DBI                           [8:1]   RW value= 0x1 */
    /* DQ_DRIVE                          [9:2]   RW value= 0x1 */
    /* DQS_DRIVE                         [11:2]  RW value= 0x1 */
    /* ADD_CMD_DRIVE                     [13:2]  RW value= 0x2 */
    /* CLOCK_OUT_DRIVE                   [15:2]  RW value= 0x2 */
    /* DQ_TERMINATION                    [17:2]  RW value= 0x0 */
    /* DQS_TERMINATION                   [19:2]  RW value= 0x0 */
    /* ADD_CMD_INPUT_PIN_TERMINATION     [21:2]  RW value= 0x0 */
    /* PRESET_ODT_CLK                    [23:2]  RW value= 0x0 */
    /* POWER_DOWN                        [25:1]  RW value= 0x0 */
    /* RANK                              [26:1]  RW value= 0x0 */
    /* RESERVED                          [27:5]  RSVD */
#endif
#if !defined (LIBERO_SETTING_DATA_LANES_USED)
/*number of lanes used for data- does not include ECC, infer from mode register
*/
#define LIBERO_SETTING_DATA_LANES_USED    0x00000004UL
    /* DATA_LANES                        [0:3]   RW value= 0x4 */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_DDR_MODE_H_ */

