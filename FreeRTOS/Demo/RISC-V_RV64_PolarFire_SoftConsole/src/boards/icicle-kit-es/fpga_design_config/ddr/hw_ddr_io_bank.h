/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_ddr_io_bank.h
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

#ifndef HW_DDR_IO_BANK_H_
#define HW_DDR_IO_BANK_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_DPC_BITS)
/*DPC Bits Register */
#define LIBERO_SETTING_DPC_BITS    0x0004C422UL
    /* DPC_VS                            [0:4]   RW value= 0x2 */
    /* DPC_VRGEN_H                       [4:6]   RW value= 0x2 */
    /* DPC_VRGEN_EN_H                    [10:1]  RW value= 0x1 */
    /* DPC_MOVE_EN_H                     [11:1]  RW value= 0x0 */
    /* DPC_VRGEN_V                       [12:6]  RW value= 0xC */
    /* DPC_VRGEN_EN_V                    [18:1]  RW value= 0x1 */
    /* DPC_MOVE_EN_V                     [19:1]  RW value= 0x0 */
    /* RESERVE01                         [20:12] RSVD */
#endif
#if !defined (LIBERO_SETTING_RPC_ODT_DQ)
/*Need to be set by software in all modes but OFF mode. Decoding options should
follow ODT_STR table, depends on drive STR setting */
#define LIBERO_SETTING_RPC_ODT_DQ    0x00000006UL
    /* RPC_ODT_DQ                        [0:32]  RW value= 0x6 */
#endif
#if !defined (LIBERO_SETTING_RPC_ODT_DQS)
/*Need to be set by software in all modes but OFF mode. Decoding options should
follow ODT_STR table, depends on drive STR setting */
#define LIBERO_SETTING_RPC_ODT_DQS    0x00000006UL
    /* RPC_ODT_DQS                       [0:32]  RW value= 0x6 */
#endif
#if !defined (LIBERO_SETTING_RPC_ODT_ADDCMD)
/*Need to be set by software in all modes but OFF mode. Decoding options should
follow ODT_STR table, depends on drive STR setting */
#define LIBERO_SETTING_RPC_ODT_ADDCMD    0x00000002UL
    /* RPC_ODT_ADDCMD                    [0:32]  RW value= 0x2 */
#endif
#if !defined (LIBERO_SETTING_RPC_ODT_CLK)
/*Need to be set by software in all modes but OFF mode. Decoding options should
follow ODT_STR table, depends on drive STR setting */
#define LIBERO_SETTING_RPC_ODT_CLK    0x00000002UL
    /* RPC_ODT_CLK                       [0:32]  RW value= 0x2 */
#endif
#if !defined (LIBERO_SETTING_RPC_ODT_STATIC_DQ)
/*0x2000 73A8 (rpc10_ODT) */
#define LIBERO_SETTING_RPC_ODT_STATIC_DQ    0x00000005UL
    /* RPC_ODT_STATIC_DQ                 [0:32]  RW value= 0x5 */
#endif
#if !defined (LIBERO_SETTING_RPC_ODT_STATIC_DQS)
/*0x2000 73AC (rpc11_ODT) */
#define LIBERO_SETTING_RPC_ODT_STATIC_DQS    0x00000005UL
    /* RPC_ODT_STATIC_DQS                [0:32]  RW value= 0x5 */
#endif
#if !defined (LIBERO_SETTING_RPC_ODT_STATIC_ADDCMD)
/*0x2000 739C (rpc7_ODT) */
#define LIBERO_SETTING_RPC_ODT_STATIC_ADDCMD    0x00000007UL
    /* RPC_ODT_STATIC_ADDCMD             [0:32]  RW value= 0x7 */
#endif
#if !defined (LIBERO_SETTING_RPC_ODT_STATIC_CLKP)
/*0x2000 73A4 (rpc9_ODT) */
#define LIBERO_SETTING_RPC_ODT_STATIC_CLKP    0x00000007UL
    /* RPC_ODT_STATIC_CLKP               [0:32]  RW value= 0x7 */
#endif
#if !defined (LIBERO_SETTING_RPC_ODT_STATIC_CLKN)
/*0x2000 73A0 (rpc8_ODT) */
#define LIBERO_SETTING_RPC_ODT_STATIC_CLKN    0x00000007UL
    /* RPC_ODT_STATIC_CLKN               [0:32]  RW value= 0x7 */
#endif
#if !defined (LIBERO_SETTING_RPC_IBUFMD_ADDCMD)
/*0x2000 757C (rpc95) */
#define LIBERO_SETTING_RPC_IBUFMD_ADDCMD    0x00000003UL
    /* RPC_IBUFMD_ADDCMD                 [0:32]  RW value= 0x3 */
#endif
#if !defined (LIBERO_SETTING_RPC_IBUFMD_CLK)
/*0x2000 7580 (rpc96) */
#define LIBERO_SETTING_RPC_IBUFMD_CLK    0x00000004UL
    /* RPC_IBUFMD_CLK                    [0:32]  RW value= 0x4 */
#endif
#if !defined (LIBERO_SETTING_RPC_IBUFMD_DQ)
/*0x2000 7584 (rpc97) */
#define LIBERO_SETTING_RPC_IBUFMD_DQ    0x00000003UL
    /* RPC_IBUFMD_DQ                     [0:32]  RW value= 0x3 */
#endif
#if !defined (LIBERO_SETTING_RPC_IBUFMD_DQS)
/*0x2000 7588 (rpc98) */
#define LIBERO_SETTING_RPC_IBUFMD_DQS    0x00000004UL
    /* RPC_IBUFMD_DQS                    [0:32]  RW value= 0x4 */
#endif
#if !defined (LIBERO_SETTING_RPC_SPARE0_DQ)
/*bits 15:14 connect to pc_ibufmx DQ/DQS/DM bits 13:12 connect to pc_ibufmx
CA/CK Check at ioa pc bit */
#define LIBERO_SETTING_RPC_SPARE0_DQ    0x00008000UL
    /* RPC_SPARE0_DQ                     [0:32]  RW value= 0x8000 */
#endif
#if !defined (LIBERO_SETTING_RPC_EN_ADDCMD0_OVRT9)
/*Overrides the I/O, used to disable specific DDR I/0. Each bit corresponding
to an IO in corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC_EN_ADDCMD0_OVRT9    0x00000F00UL
    /* MSS_DDR_CK0                       [0:1]   RW value= 0x0 */
    /* MSS_DDR_CK_N0                     [1:1]   RW value= 0x0 */
    /* MSS_DDR_A0                        [2:1]   RW value= 0x0 */
    /* MSS_DDR_A1                        [3:1]   RW value= 0x0 */
    /* MSS_DDR_A2                        [4:1]   RW value= 0x0 */
    /* MSS_DDR_A3                        [5:1]   RW value= 0x0 */
    /* MSS_DDR_A4                        [6:1]   RW value= 0x0 */
    /* MSS_DDR_A5                        [7:1]   RW value= 0x0 */
    /* MSS_DDR_A6                        [8:1]   RW value= 0x1 */
    /* MSS_DDR_A7                        [9:1]   RW value= 0x1 */
    /* MSS_DDR_A8                        [10:1]  RW value= 0x1 */
    /* MSS_DDR_A9                        [11:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_RPC_EN_ADDCMD1_OVRT10)
/*Overrides the I/O, used to disable specific DDR I/0. Each bit corresponding
to an IO in corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC_EN_ADDCMD1_OVRT10    0x00000FFFUL
    /* MSS_DDR_CK1                       [0:1]   RW value= 0x1 */
    /* MSS_DDR_CK_N1                     [1:1]   RW value= 0x1 */
    /* MSS_DDR_A10                       [2:1]   RW value= 0x1 */
    /* MSS_DDR_A11                       [3:1]   RW value= 0x1 */
    /* MSS_DDR_A12                       [4:1]   RW value= 0x1 */
    /* MSS_DDR_A13                       [5:1]   RW value= 0x1 */
    /* MSS_DDR_A14                       [6:1]   RW value= 0x1 */
    /* MSS_DDR_A15                       [7:1]   RW value= 0x1 */
    /* MSS_DDR_A16                       [8:1]   RW value= 0x1 */
    /* MSS_DDR3_WE_N                     [9:1]   RW value= 0x1 */
    /* MSS_DDR_BA0                       [10:1]  RW value= 0x1 */
    /* MSS_DDR_BA1                       [11:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_RPC_EN_ADDCMD2_OVRT11)
/*Overrides the I/O, used to disable specific DDR I/0. Each bit corresponding
to an IO in corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC_EN_ADDCMD2_OVRT11    0x00000FE6UL
    /* MSS_DDR_RAM_RST_N                 [0:1]   RW value= 0x0 */
    /* MSS_DDR_BG0                       [1:1]   RW value= 0x1 */
    /* MSS_DDR_BG1                       [2:1]   RW value= 0x1 */
    /* MSS_DDR_CS0                       [3:1]   RW value= 0x0 */
    /* MSS_DDR_CKE0                      [4:1]   RW value= 0x0 */
    /* MSS_DDR_ODT0                      [5:1]   RW value= 0x1 */
    /* MSS_DDR_CS1                       [6:1]   RW value= 0x1 */
    /* MSS_DDR_CKE1                      [7:1]   RW value= 0x1 */
    /* MSS_DDR_ODT1                      [8:1]   RW value= 0x1 */
    /* MSS_DDR_ACT_N                     [9:1]   RW value= 0x1 */
    /* MSS_DDR_PARITY                    [10:1]  RW value= 0x1 */
    /* MSS_DDR_ALERT_N                   [11:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_RPC_EN_DATA0_OVRT12)
/*Overrides the I/O, used to disable specific DDR I/0. Each bit corresponding
to an IO in corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC_EN_DATA0_OVRT12    0x00000000UL
    /* MSS_DDR_DQ0                       [0:1]   RW value= 0x0 */
    /* MSS_DDR_DQ1                       [1:1]   RW value= 0x0 */
    /* MSS_DDR_DQ2                       [2:1]   RW value= 0x0 */
    /* MSS_DDR_DQ3                       [3:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_P0                    [4:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_N0                    [5:1]   RW value= 0x0 */
    /* MSS_DDR_DQ4                       [6:1]   RW value= 0x0 */
    /* MSS_DDR_DQ5                       [7:1]   RW value= 0x0 */
    /* MSS_DDR_DQ6                       [8:1]   RW value= 0x0 */
    /* MSS_DDR_DQ7                       [9:1]   RW value= 0x0 */
    /* MSS_DDR_DM0                       [10:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RPC_EN_DATA1_OVRT13)
/*Overrides the I/O, used to disable specific DDR I/0. Each bit corresponding
to an IO in corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC_EN_DATA1_OVRT13    0x00000000UL
    /* MSS_DDR_DQ8                       [0:1]   RW value= 0x0 */
    /* MSS_DDR_DQ9                       [1:1]   RW value= 0x0 */
    /* MSS_DDR_DQ10                      [2:1]   RW value= 0x0 */
    /* MSS_DDR_DQ11                      [3:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_P1                    [4:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_N1                    [5:1]   RW value= 0x0 */
    /* MSS_DDR_DQ12                      [6:1]   RW value= 0x0 */
    /* MSS_DDR_DQ13                      [7:1]   RW value= 0x0 */
    /* MSS_DDR_DQ14                      [8:1]   RW value= 0x0 */
    /* MSS_DDR_DQ15                      [9:1]   RW value= 0x0 */
    /* MSS_DDR_DM1                       [10:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RPC_EN_DATA2_OVRT14)
/*Overrides the I/O, used to disable specific DDR I/0. Each bit corresponding
to an IO in corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC_EN_DATA2_OVRT14    0x00000000UL
    /* MSS_DDR_DQ16                      [0:1]   RW value= 0x0 */
    /* MSS_DDR_DQ17                      [1:1]   RW value= 0x0 */
    /* MSS_DDR_DQ18                      [2:1]   RW value= 0x0 */
    /* MSS_DDR_DQ19                      [3:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_P2                    [4:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_N2                    [5:1]   RW value= 0x0 */
    /* MSS_DDR_DQ20                      [6:1]   RW value= 0x0 */
    /* MSS_DDR_DQ21                      [7:1]   RW value= 0x0 */
    /* MSS_DDR_DQ22                      [8:1]   RW value= 0x0 */
    /* MSS_DDR_DQ23                      [9:1]   RW value= 0x0 */
    /* MSS_DDR_DM2                       [10:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RPC_EN_DATA3_OVRT15)
/*Overrides the I/O, used to disable specific DDR I/0. Each bit corresponding
to an IO in corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC_EN_DATA3_OVRT15    0x00000000UL
    /* MSS_DDR_DQ24                      [0:1]   RW value= 0x0 */
    /* MSS_DDR_DQ25                      [1:1]   RW value= 0x0 */
    /* MSS_DDR_DQ26                      [2:1]   RW value= 0x0 */
    /* MSS_DDR_DQ27                      [3:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_P3                    [4:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_N3                    [5:1]   RW value= 0x0 */
    /* MSS_DDR_DQ28                      [6:1]   RW value= 0x0 */
    /* MSS_DDR_DQ29                      [7:1]   RW value= 0x0 */
    /* MSS_DDR_DQ30                      [8:1]   RW value= 0x0 */
    /* MSS_DDR_DQ31                      [9:1]   RW value= 0x0 */
    /* MSS_DDR_DM3                       [10:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RPC_EN_ECC_OVRT16)
/*Overrides the I/O, used to disable specific DDR I/0. Each bit corresponding
to an IO in corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC_EN_ECC_OVRT16    0x0000007FUL
    /* MSS_DDR_DQ32                      [0:1]   RW value= 0x1 */
    /* MSS_DDR_DQ33                      [1:1]   RW value= 0x1 */
    /* MSS_DDR_DQ34                      [2:1]   RW value= 0x1 */
    /* MSS_DDR_DQ35                      [3:1]   RW value= 0x1 */
    /* MSS_DDR_DQS_P4                    [4:1]   RW value= 0x1 */
    /* MSS_DDR_DQS_N4                    [5:1]   RW value= 0x1 */
    /* MSS_DDR_DM4                       [6:1]   RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_RPC235_WPD_ADD_CMD0)
/*Sets pull-downs when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC235_WPD_ADD_CMD0    0x00000000UL
    /* MSS_DDR_CK0                       [0:1]   RW value= 0x0 */
    /* MSS_DDR_CK_N0                     [1:1]   RW value= 0x0 */
    /* MSS_DDR_A0                        [2:1]   RW value= 0x0 */
    /* MSS_DDR_A1                        [3:1]   RW value= 0x0 */
    /* MSS_DDR_A2                        [4:1]   RW value= 0x0 */
    /* MSS_DDR_A3                        [5:1]   RW value= 0x0 */
    /* MSS_DDR_A4                        [6:1]   RW value= 0x0 */
    /* MSS_DDR_A5                        [7:1]   RW value= 0x0 */
    /* MSS_DDR_A6                        [8:1]   RW value= 0x0 */
    /* MSS_DDR_A7                        [9:1]   RW value= 0x0 */
    /* MSS_DDR_A8                        [10:1]  RW value= 0x0 */
    /* MSS_DDR_A9                        [11:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RPC236_WPD_ADD_CMD1)
/*Sets pull-downs when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC236_WPD_ADD_CMD1    0x00000000UL
    /* MSS_DDR_CK1                       [0:1]   RW value= 0x0 */
    /* MSS_DDR_CK_N1                     [1:1]   RW value= 0x0 */
    /* MSS_DDR_A10                       [2:1]   RW value= 0x0 */
    /* MSS_DDR_A11                       [3:1]   RW value= 0x0 */
    /* MSS_DDR_A12                       [4:1]   RW value= 0x0 */
    /* MSS_DDR_A13                       [5:1]   RW value= 0x0 */
    /* MSS_DDR_A14                       [6:1]   RW value= 0x0 */
    /* MSS_DDR_A15                       [7:1]   RW value= 0x0 */
    /* MSS_DDR_A16                       [8:1]   RW value= 0x0 */
    /* MSS_DDR3_WE_N                     [9:1]   RW value= 0x0 */
    /* MSS_DDR_BA0                       [10:1]  RW value= 0x0 */
    /* MSS_DDR_BA1                       [11:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RPC237_WPD_ADD_CMD2)
/*Sets pull-downs when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. Note: For LPDDR4 need
to over-ride MSS_DDR_ODT0 and MSS_DDR_ODT1 and eanble PU i.e. (set OVR_EN ==1 ,
wpu == 0 , wpd == 1 ) */
#define LIBERO_SETTING_RPC237_WPD_ADD_CMD2    0x00000120UL
    /* MSS_DDR_RAM_RST_N                 [0:1]   RW value= 0x0 */
    /* MSS_DDR_BG0                       [1:1]   RW value= 0x0 */
    /* MSS_DDR_BG1                       [2:1]   RW value= 0x0 */
    /* MSS_DDR_CS0                       [3:1]   RW value= 0x0 */
    /* MSS_DDR_CKE0                      [4:1]   RW value= 0x0 */
    /* MSS_DDR_ODT0                      [5:1]   RW value= 0x1 */
    /* MSS_DDR_CS1                       [6:1]   RW value= 0x0 */
    /* MSS_DDR_CKE1                      [7:1]   RW value= 0x0 */
    /* MSS_DDR_ODT1                      [8:1]   RW value= 0x1 */
    /* MSS_DDR_ACT_N                     [9:1]   RW value= 0x0 */
    /* MSS_DDR_PARITY                    [10:1]  RW value= 0x0 */
    /* MSS_DDR_ALERT_N                   [11:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RPC238_WPD_DATA0)
/*Sets pull-downs when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC238_WPD_DATA0    0x00000000UL
    /* MSS_DDR_DQ0                       [0:1]   RW value= 0x0 */
    /* MSS_DDR_DQ1                       [1:1]   RW value= 0x0 */
    /* MSS_DDR_DQ2                       [2:1]   RW value= 0x0 */
    /* MSS_DDR_DQ3                       [3:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_P0                    [4:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_N0                    [5:1]   RW value= 0x0 */
    /* MSS_DDR_DQ4                       [6:1]   RW value= 0x0 */
    /* MSS_DDR_DQ5                       [7:1]   RW value= 0x0 */
    /* MSS_DDR_DQ6                       [8:1]   RW value= 0x0 */
    /* MSS_DDR_DQ7                       [9:1]   RW value= 0x0 */
    /* MSS_DDR_DM0                       [10:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RPC239_WPD_DATA1)
/*Sets pull-downs when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC239_WPD_DATA1    0x00000000UL
    /* MSS_DDR_DQ8                       [0:1]   RW value= 0x0 */
    /* MSS_DDR_DQ9                       [1:1]   RW value= 0x0 */
    /* MSS_DDR_DQ10                      [2:1]   RW value= 0x0 */
    /* MSS_DDR_DQ11                      [3:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_P1                    [4:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_N1                    [5:1]   RW value= 0x0 */
    /* MSS_DDR_DQ12                      [6:1]   RW value= 0x0 */
    /* MSS_DDR_DQ13                      [7:1]   RW value= 0x0 */
    /* MSS_DDR_DQ14                      [8:1]   RW value= 0x0 */
    /* MSS_DDR_DQ15                      [9:1]   RW value= 0x0 */
    /* MSS_DDR_DM1                       [10:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RPC240_WPD_DATA2)
/*Sets pull-downs when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC240_WPD_DATA2    0x00000000UL
    /* MSS_DDR_DQ16                      [0:1]   RW value= 0x0 */
    /* MSS_DDR_DQ17                      [1:1]   RW value= 0x0 */
    /* MSS_DDR_DQ18                      [2:1]   RW value= 0x0 */
    /* MSS_DDR_DQ19                      [3:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_P2                    [4:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_N2                    [5:1]   RW value= 0x0 */
    /* MSS_DDR_DQ20                      [6:1]   RW value= 0x0 */
    /* MSS_DDR_DQ21                      [7:1]   RW value= 0x0 */
    /* MSS_DDR_DQ22                      [8:1]   RW value= 0x0 */
    /* MSS_DDR_DQ23                      [9:1]   RW value= 0x0 */
    /* MSS_DDR_DM2                       [10:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RPC241_WPD_DATA3)
/*Sets pull-downs when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC241_WPD_DATA3    0x00000000UL
    /* MSS_DDR_DQ24                      [0:1]   RW value= 0x0 */
    /* MSS_DDR_DQ25                      [1:1]   RW value= 0x0 */
    /* MSS_DDR_DQ26                      [2:1]   RW value= 0x0 */
    /* MSS_DDR_DQ27                      [3:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_P3                    [4:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_N3                    [5:1]   RW value= 0x0 */
    /* MSS_DDR_DQ28                      [6:1]   RW value= 0x0 */
    /* MSS_DDR_DQ29                      [7:1]   RW value= 0x0 */
    /* MSS_DDR_DQ30                      [8:1]   RW value= 0x0 */
    /* MSS_DDR_DQ31                      [9:1]   RW value= 0x0 */
    /* MSS_DDR_DM3                       [10:1]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RPC242_WPD_ECC)
/*Sets pull-downs when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC242_WPD_ECC    0x00000000UL
    /* MSS_DDR_DQ32                      [0:1]   RW value= 0x0 */
    /* MSS_DDR_DQ33                      [1:1]   RW value= 0x0 */
    /* MSS_DDR_DQ34                      [2:1]   RW value= 0x0 */
    /* MSS_DDR_DQ35                      [3:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_P4                    [4:1]   RW value= 0x0 */
    /* MSS_DDR_DQS_N4                    [5:1]   RW value= 0x0 */
    /* MSS_DDR_DM4                       [6:1]   RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_RPC243_WPU_ADD_CMD0)
/*Sets pull-ups when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC243_WPU_ADD_CMD0    0x00000FFFUL
    /* MSS_DDR_CK0                       [0:1]   RW value= 0x1 */
    /* MSS_DDR_CK_N0                     [1:1]   RW value= 0x1 */
    /* MSS_DDR_A0                        [2:1]   RW value= 0x1 */
    /* MSS_DDR_A1                        [3:1]   RW value= 0x1 */
    /* MSS_DDR_A2                        [4:1]   RW value= 0x1 */
    /* MSS_DDR_A3                        [5:1]   RW value= 0x1 */
    /* MSS_DDR_A4                        [6:1]   RW value= 0x1 */
    /* MSS_DDR_A5                        [7:1]   RW value= 0x1 */
    /* MSS_DDR_A6                        [8:1]   RW value= 0x1 */
    /* MSS_DDR_A7                        [9:1]   RW value= 0x1 */
    /* MSS_DDR_A8                        [10:1]  RW value= 0x1 */
    /* MSS_DDR_A9                        [11:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_RPC244_WPU_ADD_CMD1)
/*Sets pull-ups when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC244_WPU_ADD_CMD1    0x00000FFFUL
    /* MSS_DDR_CK1                       [0:1]   RW value= 0x1 */
    /* MSS_DDR_CK_N1                     [1:1]   RW value= 0x1 */
    /* MSS_DDR_A10                       [2:1]   RW value= 0x1 */
    /* MSS_DDR_A11                       [3:1]   RW value= 0x1 */
    /* MSS_DDR_A12                       [4:1]   RW value= 0x1 */
    /* MSS_DDR_A13                       [5:1]   RW value= 0x1 */
    /* MSS_DDR_A14                       [6:1]   RW value= 0x1 */
    /* MSS_DDR_A15                       [7:1]   RW value= 0x1 */
    /* MSS_DDR_A16                       [8:1]   RW value= 0x1 */
    /* MSS_DDR3_WE_N                     [9:1]   RW value= 0x1 */
    /* MSS_DDR_BA0                       [10:1]  RW value= 0x1 */
    /* MSS_DDR_BA1                       [11:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_RPC245_WPU_ADD_CMD2)
/*Sets pull-ups when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC245_WPU_ADD_CMD2    0x00000EDFUL
    /* MSS_DDR_RAM_RST_N                 [0:1]   RW value= 0x1 */
    /* MSS_DDR_BG0                       [1:1]   RW value= 0x1 */
    /* MSS_DDR_BG1                       [2:1]   RW value= 0x1 */
    /* MSS_DDR_CS0                       [3:1]   RW value= 0x1 */
    /* MSS_DDR_CKE0                      [4:1]   RW value= 0x1 */
    /* MSS_DDR_ODT0                      [5:1]   RW value= 0x0 */
    /* MSS_DDR_CS1                       [6:1]   RW value= 0x1 */
    /* MSS_DDR_CKE1                      [7:1]   RW value= 0x1 */
    /* MSS_DDR_ODT1                      [8:1]   RW value= 0x0 */
    /* MSS_DDR_ACT_N                     [9:1]   RW value= 0x1 */
    /* MSS_DDR_PARITY                    [10:1]  RW value= 0x1 */
    /* MSS_DDR_ALERT_N                   [11:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_RPC246_WPU_DATA0)
/*Sets pull-ups when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC246_WPU_DATA0    0x000007FFUL
    /* MSS_DDR_DQ0                       [0:1]   RW value= 0x1 */
    /* MSS_DDR_DQ1                       [1:1]   RW value= 0x1 */
    /* MSS_DDR_DQ2                       [2:1]   RW value= 0x1 */
    /* MSS_DDR_DQ3                       [3:1]   RW value= 0x1 */
    /* MSS_DDR_DQS_P0                    [4:1]   RW value= 0x1 */
    /* MSS_DDR_DQS_N0                    [5:1]   RW value= 0x1 */
    /* MSS_DDR_DQ4                       [6:1]   RW value= 0x1 */
    /* MSS_DDR_DQ5                       [7:1]   RW value= 0x1 */
    /* MSS_DDR_DQ6                       [8:1]   RW value= 0x1 */
    /* MSS_DDR_DQ7                       [9:1]   RW value= 0x1 */
    /* MSS_DDR_DM0                       [10:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_RPC247_WPU_DATA1)
/*Sets pull-ups when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC247_WPU_DATA1    0x000007FFUL
    /* MSS_DDR_DQ8                       [0:1]   RW value= 0x1 */
    /* MSS_DDR_DQ9                       [1:1]   RW value= 0x1 */
    /* MSS_DDR_DQ10                      [2:1]   RW value= 0x1 */
    /* MSS_DDR_DQ11                      [3:1]   RW value= 0x1 */
    /* MSS_DDR_DQS_P1                    [4:1]   RW value= 0x1 */
    /* MSS_DDR_DQS_N1                    [5:1]   RW value= 0x1 */
    /* MSS_DDR_DQ12                      [6:1]   RW value= 0x1 */
    /* MSS_DDR_DQ13                      [7:1]   RW value= 0x1 */
    /* MSS_DDR_DQ14                      [8:1]   RW value= 0x1 */
    /* MSS_DDR_DQ15                      [9:1]   RW value= 0x1 */
    /* MSS_DDR_DM1                       [10:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_RPC248_WPU_DATA2)
/*Sets pull-ups when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC248_WPU_DATA2    0x000007FFUL
    /* MSS_DDR_DQ16                      [0:1]   RW value= 0x1 */
    /* MSS_DDR_DQ17                      [1:1]   RW value= 0x1 */
    /* MSS_DDR_DQ18                      [2:1]   RW value= 0x1 */
    /* MSS_DDR_DQ19                      [3:1]   RW value= 0x1 */
    /* MSS_DDR_DQS_P2                    [4:1]   RW value= 0x1 */
    /* MSS_DDR_DQS_N2                    [5:1]   RW value= 0x1 */
    /* MSS_DDR_DQ20                      [6:1]   RW value= 0x1 */
    /* MSS_DDR_DQ21                      [7:1]   RW value= 0x1 */
    /* MSS_DDR_DQ22                      [8:1]   RW value= 0x1 */
    /* MSS_DDR_DQ23                      [9:1]   RW value= 0x1 */
    /* MSS_DDR_DM2                       [10:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_RPC249_WPU_DATA3)
/*Sets pull-ups when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC249_WPU_DATA3    0x000007FFUL
    /* MSS_DDR_DQ24                      [0:1]   RW value= 0x1 */
    /* MSS_DDR_DQ25                      [1:1]   RW value= 0x1 */
    /* MSS_DDR_DQ26                      [2:1]   RW value= 0x1 */
    /* MSS_DDR_DQ27                      [3:1]   RW value= 0x1 */
    /* MSS_DDR_DQS_P3                    [4:1]   RW value= 0x1 */
    /* MSS_DDR_DQS_N3                    [5:1]   RW value= 0x1 */
    /* MSS_DDR_DQ28                      [6:1]   RW value= 0x1 */
    /* MSS_DDR_DQ29                      [7:1]   RW value= 0x1 */
    /* MSS_DDR_DQ30                      [8:1]   RW value= 0x1 */
    /* MSS_DDR_DQ31                      [9:1]   RW value= 0x1 */
    /* MSS_DDR_DM3                       [10:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_RPC250_WPU_ECC)
/*Sets pull-ups when override enabled. Each bit corresponding to an IO in
corresponding IOG lane, starting from p_pair0 to n_pair5. */
#define LIBERO_SETTING_RPC250_WPU_ECC    0x0000007FUL
    /* MSS_DDR_DQ32                      [0:1]   RW value= 0x1 */
    /* MSS_DDR_DQ33                      [1:1]   RW value= 0x1 */
    /* MSS_DDR_DQ34                      [2:1]   RW value= 0x1 */
    /* MSS_DDR_DQ35                      [3:1]   RW value= 0x1 */
    /* MSS_DDR_DQS_P4                    [4:1]   RW value= 0x1 */
    /* MSS_DDR_DQS_N4                    [5:1]   RW value= 0x1 */
    /* MSS_DDR_DM4                       [6:1]   RW value= 0x1 */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_DDR_IO_BANK_H_ */

