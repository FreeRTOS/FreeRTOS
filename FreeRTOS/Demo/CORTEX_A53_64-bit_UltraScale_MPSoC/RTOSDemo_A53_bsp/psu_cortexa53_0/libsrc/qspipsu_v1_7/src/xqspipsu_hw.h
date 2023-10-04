/******************************************************************************
*
* Copyright (C) 2014 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/*****************************************************************************/

/**
 *
 * @file xqspipsu_hw.h
 * @addtogroup qspipsu_v1_7
 * @{
 *
 * This file contains low level access funcitons using the base address
 * directly without an instance.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who Date     Changes
 * ----- --- -------- -----------------------------------------------.
 * 1.0   hk  08/21/14 First release
 *       hk  03/18/15 Add DMA status register masks required.
 *       sk  04/24/15 Modified the code according to MISRAC-2012.
 * 1.2	nsk 07/01/16 Added LQSPI supported Masks
 *       rk  07/15/16 Added support for TapDelays at different frequencies.
 * 1.7	tjs	03/14/18 Added support in EL1 NS mode.
 *
 * </pre>
 *
 ******************************************************************************/
#ifndef _XQSPIPSU_HW_H_     /* prevent circular inclusions */
    #define _XQSPIPSU_HW_H_ /* by using protection macros */

    #ifdef __cplusplus
    extern "C" {
    #endif

/***************************** Include Files *********************************/

    #include "xil_types.h"
    #include "xil_assert.h"
    #include "xil_io.h"
    #include "xparameters.h"

/************************** Constant Definitions *****************************/

/**
 * QSPI Base Address
 */
    #define XQSPIPS_BASEADDR                                          0XFF0F0000U

/**
 * GQSPI Base Address
 */
    #define XQSPIPSU_BASEADDR                                         0xFF0F0100U
    #define XQSPIPSU_OFFSET                                           0x100U

/**
 * Register: XQSPIPS_EN_REG
 */
    #define XQSPIPS_EN_REG                                            ( ( XQSPIPS_BASEADDR ) +0X00000014U )

    #define XQSPIPS_EN_SHIFT                                          0
    #define XQSPIPS_EN_WIDTH                                          1
    #define XQSPIPS_EN_MASK                                           0X00000001U

/**
 * Register: XQSPIPSU_CFG
 */
    #define XQSPIPSU_CFG_OFFSET                                       0X00000000U
    #define XQSPIPSU_LQSPI_CR_OFFSET                                  0X000000A0U

    #define XQSPIPSU_CFG_MODE_EN_SHIFT                                30
    #define XQSPIPSU_CFG_MODE_EN_WIDTH                                2
    #define XQSPIPSU_CFG_MODE_EN_MASK                                 0XC0000000U
    #define XQSPIPSU_CFG_MODE_EN_DMA_MASK                             0X80000000U

    #define XQSPIPSU_CFG_GEN_FIFO_START_MODE_SHIFT                    29
    #define XQSPIPSU_CFG_GEN_FIFO_START_MODE_WIDTH                    1
    #define XQSPIPSU_CFG_GEN_FIFO_START_MODE_MASK                     0X20000000U

    #define XQSPIPSU_CFG_START_GEN_FIFO_SHIFT                         28
    #define XQSPIPSU_CFG_START_GEN_FIFO_WIDTH                         1
    #define XQSPIPSU_CFG_START_GEN_FIFO_MASK                          0X10000000U

    #define XQSPIPSU_CFG_ENDIAN_SHIFT                                 26
    #define XQSPIPSU_CFG_ENDIAN_WIDTH                                 1
    #define XQSPIPSU_CFG_ENDIAN_MASK                                  0X04000000U

    #define XQSPIPSU_CFG_EN_POLL_TO_SHIFT                             20
    #define XQSPIPSU_CFG_EN_POLL_TO_WIDTH                             1
    #define XQSPIPSU_CFG_EN_POLL_TO_MASK                              0X00100000U

    #define XQSPIPSU_CFG_WP_HOLD_SHIFT                                19
    #define XQSPIPSU_CFG_WP_HOLD_WIDTH                                1
    #define XQSPIPSU_CFG_WP_HOLD_MASK                                 0X00080000U

    #define XQSPIPSU_CFG_BAUD_RATE_DIV_SHIFT                          3
    #define XQSPIPSU_CFG_BAUD_RATE_DIV_WIDTH                          3
    #define XQSPIPSU_CFG_BAUD_RATE_DIV_MASK                           0X00000038U

    #define XQSPIPSU_CFG_CLK_PHA_SHIFT                                2
    #define XQSPIPSU_CFG_CLK_PHA_WIDTH                                1
    #define XQSPIPSU_CFG_CLK_PHA_MASK                                 0X00000004U

    #define XQSPIPSU_CFG_CLK_POL_SHIFT                                1
    #define XQSPIPSU_CFG_CLK_POL_WIDTH                                1
    #define XQSPIPSU_CFG_CLK_POL_MASK                                 0X00000002U

/**
 * Register: XQSPIPSU_CFG
 */
    #define XQSPIPSU_LQSPI_CR_OFFSET                                  0X000000A0U
    #define XQSPIPSU_LQSPI_CR_LINEAR_MASK                             0x80000000 /**< LQSPI mode enable */
    #define XQSPIPSU_LQSPI_CR_TWO_MEM_MASK                            0x40000000 /**< Both memories or one */
    #define XQSPIPSU_LQSPI_CR_SEP_BUS_MASK                            0x20000000 /**< Seperate memory bus */
    #define XQSPIPSU_LQSPI_CR_U_PAGE_MASK                             0x10000000 /**< Upper memory page */
    #define XQSPIPSU_LQSPI_CR_ADDR_32BIT_MASK                         0x01000000 /**< Upper memory page */
    #define XQSPIPSU_LQSPI_CR_MODE_EN_MASK                            0x02000000 /**< Enable mode bits */
    #define XQSPIPSU_LQSPI_CR_MODE_ON_MASK                            0x01000000 /**< Mode on */
    #define XQSPIPSU_LQSPI_CR_MODE_BITS_MASK                          0x00FF0000 /**< Mode value for dual I/O
                                                                                  *  or quad I/O */
    #define XQSPIPS_LQSPI_CR_INST_MASK                                0x000000FF /**< Read instr code */
    #define XQSPIPS_LQSPI_CR_RST_STATE                                0x80000003 /**< Default LQSPI CR value */
    #define XQSPIPS_LQSPI_CR_4_BYTE_STATE                             0x88000013 /**< Default 4 Byte LQSPI CR value */
    #define XQSPIPS_LQSPI_CFG_RST_STATE                               0x800238C1 /**< Default LQSPI CFG value */

/**
 * Register: XQSPIPSU_ISR
 */
    #define XQSPIPSU_ISR_OFFSET                                       0X00000004U

    #define XQSPIPSU_ISR_RXEMPTY_SHIFT                                11
    #define XQSPIPSU_ISR_RXEMPTY_WIDTH                                1
    #define XQSPIPSU_ISR_RXEMPTY_MASK                                 0X00000800U

    #define XQSPIPSU_ISR_GENFIFOFULL_SHIFT                            10
    #define XQSPIPSU_ISR_GENFIFOFULL_WIDTH                            1
    #define XQSPIPSU_ISR_GENFIFOFULL_MASK                             0X00000400U

    #define XQSPIPSU_ISR_GENFIFONOT_FULL_SHIFT                        9
    #define XQSPIPSU_ISR_GENFIFONOT_FULL_WIDTH                        1
    #define XQSPIPSU_ISR_GENFIFONOT_FULL_MASK                         0X00000200U

    #define XQSPIPSU_ISR_TXEMPTY_SHIFT                                8
    #define XQSPIPSU_ISR_TXEMPTY_WIDTH                                1
    #define XQSPIPSU_ISR_TXEMPTY_MASK                                 0X00000100U

    #define XQSPIPSU_ISR_GENFIFOEMPTY_SHIFT                           7
    #define XQSPIPSU_ISR_GENFIFOEMPTY_WIDTH                           1
    #define XQSPIPSU_ISR_GENFIFOEMPTY_MASK                            0X00000080U

    #define XQSPIPSU_ISR_RXFULL_SHIFT                                 5
    #define XQSPIPSU_ISR_RXFULL_WIDTH                                 1
    #define XQSPIPSU_ISR_RXFULL_MASK                                  0X00000020U

    #define XQSPIPSU_ISR_RXNEMPTY_SHIFT                               4
    #define XQSPIPSU_ISR_RXNEMPTY_WIDTH                               1
    #define XQSPIPSU_ISR_RXNEMPTY_MASK                                0X00000010U

    #define XQSPIPSU_ISR_TXFULL_SHIFT                                 3
    #define XQSPIPSU_ISR_TXFULL_WIDTH                                 1
    #define XQSPIPSU_ISR_TXFULL_MASK                                  0X00000008U

    #define XQSPIPSU_ISR_TXNOT_FULL_SHIFT                             2
    #define XQSPIPSU_ISR_TXNOT_FULL_WIDTH                             1
    #define XQSPIPSU_ISR_TXNOT_FULL_MASK                              0X00000004U

    #define XQSPIPSU_ISR_POLL_TIME_EXPIRE_SHIFT                       1
    #define XQSPIPSU_ISR_POLL_TIME_EXPIRE_WIDTH                       1
    #define XQSPIPSU_ISR_POLL_TIME_EXPIRE_MASK                        0X00000002U

    #define XQSPIPSU_ISR_WR_TO_CLR_MASK                               0X00000002U

/**
 * Register: XQSPIPSU_IER
 */
    #define XQSPIPSU_IER_OFFSET                                       0X00000008U

    #define XQSPIPSU_IER_RXEMPTY_SHIFT                                11
    #define XQSPIPSU_IER_RXEMPTY_WIDTH                                1
    #define XQSPIPSU_IER_RXEMPTY_MASK                                 0X00000800U

    #define XQSPIPSU_IER_GENFIFOFULL_SHIFT                            10
    #define XQSPIPSU_IER_GENFIFOFULL_WIDTH                            1
    #define XQSPIPSU_IER_GENFIFOFULL_MASK                             0X00000400U

    #define XQSPIPSU_IER_GENFIFONOT_FULL_SHIFT                        9
    #define XQSPIPSU_IER_GENFIFONOT_FULL_WIDTH                        1
    #define XQSPIPSU_IER_GENFIFONOT_FULL_MASK                         0X00000200U

    #define XQSPIPSU_IER_TXEMPTY_SHIFT                                8
    #define XQSPIPSU_IER_TXEMPTY_WIDTH                                1
    #define XQSPIPSU_IER_TXEMPTY_MASK                                 0X00000100U

    #define XQSPIPSU_IER_GENFIFOEMPTY_SHIFT                           7
    #define XQSPIPSU_IER_GENFIFOEMPTY_WIDTH                           1
    #define XQSPIPSU_IER_GENFIFOEMPTY_MASK                            0X00000080U

    #define XQSPIPSU_IER_RXFULL_SHIFT                                 5
    #define XQSPIPSU_IER_RXFULL_WIDTH                                 1
    #define XQSPIPSU_IER_RXFULL_MASK                                  0X00000020U

    #define XQSPIPSU_IER_RXNEMPTY_SHIFT                               4
    #define XQSPIPSU_IER_RXNEMPTY_WIDTH                               1
    #define XQSPIPSU_IER_RXNEMPTY_MASK                                0X00000010U

    #define XQSPIPSU_IER_TXFULL_SHIFT                                 3
    #define XQSPIPSU_IER_TXFULL_WIDTH                                 1
    #define XQSPIPSU_IER_TXFULL_MASK                                  0X00000008U

    #define XQSPIPSU_IER_TXNOT_FULL_SHIFT                             2
    #define XQSPIPSU_IER_TXNOT_FULL_WIDTH                             1
    #define XQSPIPSU_IER_TXNOT_FULL_MASK                              0X00000004U

    #define XQSPIPSU_IER_POLL_TIME_EXPIRE_SHIFT                       1
    #define XQSPIPSU_IER_POLL_TIME_EXPIRE_WIDTH                       1
    #define XQSPIPSU_IER_POLL_TIME_EXPIRE_MASK                        0X00000002U

/**
 * Register: XQSPIPSU_IDR
 */
    #define XQSPIPSU_IDR_OFFSET                                       0X0000000CU

    #define XQSPIPSU_IDR_RXEMPTY_SHIFT                                11
    #define XQSPIPSU_IDR_RXEMPTY_WIDTH                                1
    #define XQSPIPSU_IDR_RXEMPTY_MASK                                 0X00000800U

    #define XQSPIPSU_IDR_GENFIFOFULL_SHIFT                            10
    #define XQSPIPSU_IDR_GENFIFOFULL_WIDTH                            1
    #define XQSPIPSU_IDR_GENFIFOFULL_MASK                             0X00000400U

    #define XQSPIPSU_IDR_GENFIFONOT_FULL_SHIFT                        9
    #define XQSPIPSU_IDR_GENFIFONOT_FULL_WIDTH                        1
    #define XQSPIPSU_IDR_GENFIFONOT_FULL_MASK                         0X00000200U

    #define XQSPIPSU_IDR_TXEMPTY_SHIFT                                8
    #define XQSPIPSU_IDR_TXEMPTY_WIDTH                                1
    #define XQSPIPSU_IDR_TXEMPTY_MASK                                 0X00000100U

    #define XQSPIPSU_IDR_GENFIFOEMPTY_SHIFT                           7
    #define XQSPIPSU_IDR_GENFIFOEMPTY_WIDTH                           1
    #define XQSPIPSU_IDR_GENFIFOEMPTY_MASK                            0X00000080U

    #define XQSPIPSU_IDR_RXFULL_SHIFT                                 5
    #define XQSPIPSU_IDR_RXFULL_WIDTH                                 1
    #define XQSPIPSU_IDR_RXFULL_MASK                                  0X00000020U

    #define XQSPIPSU_IDR_RXNEMPTY_SHIFT                               4
    #define XQSPIPSU_IDR_RXNEMPTY_WIDTH                               1
    #define XQSPIPSU_IDR_RXNEMPTY_MASK                                0X00000010U

    #define XQSPIPSU_IDR_TXFULL_SHIFT                                 3
    #define XQSPIPSU_IDR_TXFULL_WIDTH                                 1
    #define XQSPIPSU_IDR_TXFULL_MASK                                  0X00000008U

    #define XQSPIPSU_IDR_TXNOT_FULL_SHIFT                             2
    #define XQSPIPSU_IDR_TXNOT_FULL_WIDTH                             1
    #define XQSPIPSU_IDR_TXNOT_FULL_MASK                              0X00000004U

    #define XQSPIPSU_IDR_POLL_TIME_EXPIRE_SHIFT                       1
    #define XQSPIPSU_IDR_POLL_TIME_EXPIRE_WIDTH                       1
    #define XQSPIPSU_IDR_POLL_TIME_EXPIRE_MASK                        0X00000002U

    #define XQSPIPSU_IDR_ALL_MASK                                     0X0FBEU

/**
 * Register: XQSPIPSU_IMR
 */
    #define XQSPIPSU_IMR_OFFSET                                       0X00000010U

    #define XQSPIPSU_IMR_RXEMPTY_SHIFT                                11
    #define XQSPIPSU_IMR_RXEMPTY_WIDTH                                1
    #define XQSPIPSU_IMR_RXEMPTY_MASK                                 0X00000800U

    #define XQSPIPSU_IMR_GENFIFOFULL_SHIFT                            10
    #define XQSPIPSU_IMR_GENFIFOFULL_WIDTH                            1
    #define XQSPIPSU_IMR_GENFIFOFULL_MASK                             0X00000400U

    #define XQSPIPSU_IMR_GENFIFONOT_FULL_SHIFT                        9
    #define XQSPIPSU_IMR_GENFIFONOT_FULL_WIDTH                        1
    #define XQSPIPSU_IMR_GENFIFONOT_FULL_MASK                         0X00000200U

    #define XQSPIPSU_IMR_TXEMPTY_SHIFT                                8
    #define XQSPIPSU_IMR_TXEMPTY_WIDTH                                1
    #define XQSPIPSU_IMR_TXEMPTY_MASK                                 0X00000100U

    #define XQSPIPSU_IMR_GENFIFOEMPTY_SHIFT                           7
    #define XQSPIPSU_IMR_GENFIFOEMPTY_WIDTH                           1
    #define XQSPIPSU_IMR_GENFIFOEMPTY_MASK                            0X00000080U

    #define XQSPIPSU_IMR_RXFULL_SHIFT                                 5
    #define XQSPIPSU_IMR_RXFULL_WIDTH                                 1
    #define XQSPIPSU_IMR_RXFULL_MASK                                  0X00000020U

    #define XQSPIPSU_IMR_RXNEMPTY_SHIFT                               4
    #define XQSPIPSU_IMR_RXNEMPTY_WIDTH                               1
    #define XQSPIPSU_IMR_RXNEMPTY_MASK                                0X00000010U

    #define XQSPIPSU_IMR_TXFULL_SHIFT                                 3
    #define XQSPIPSU_IMR_TXFULL_WIDTH                                 1
    #define XQSPIPSU_IMR_TXFULL_MASK                                  0X00000008U

    #define XQSPIPSU_IMR_TXNOT_FULL_SHIFT                             2
    #define XQSPIPSU_IMR_TXNOT_FULL_WIDTH                             1
    #define XQSPIPSU_IMR_TXNOT_FULL_MASK                              0X00000004U

    #define XQSPIPSU_IMR_POLL_TIME_EXPIRE_SHIFT                       1
    #define XQSPIPSU_IMR_POLL_TIME_EXPIRE_WIDTH                       1
    #define XQSPIPSU_IMR_POLL_TIME_EXPIRE_MASK                        0X00000002U

/**
 * Register: XQSPIPSU_EN_REG
 */
    #define XQSPIPSU_EN_OFFSET                                        0X00000014U

    #define XQSPIPSU_EN_SHIFT                                         0
    #define XQSPIPSU_EN_WIDTH                                         1
    #define XQSPIPSU_EN_MASK                                          0X00000001U

/**
 * Register: XQSPIPSU_TXD
 */
    #define XQSPIPSU_TXD_OFFSET                                       0X0000001CU

    #define XQSPIPSU_TXD_SHIFT                                        0
    #define XQSPIPSU_TXD_WIDTH                                        32
    #define XQSPIPSU_TXD_MASK                                         0XFFFFFFFFU

    #define XQSPIPSU_TXD_DEPTH                                        64

/**
 * Register: XQSPIPSU_RXD
 */
    #define XQSPIPSU_RXD_OFFSET                                       0X00000020U

    #define XQSPIPSU_RXD_SHIFT                                        0
    #define XQSPIPSU_RXD_WIDTH                                        32
    #define XQSPIPSU_RXD_MASK                                         0XFFFFFFFFU

/**
 * Register: XQSPIPSU_TX_THRESHOLD
 */
    #define XQSPIPSU_TX_THRESHOLD_OFFSET                              0X00000028U

    #define XQSPIPSU_TX_FIFO_THRESHOLD_SHIFT                          0
    #define XQSPIPSU_TX_FIFO_THRESHOLD_WIDTH                          6
    #define XQSPIPSU_TX_FIFO_THRESHOLD_MASK                           0X0000003FU
    #define XQSPIPSU_TX_FIFO_THRESHOLD_RESET_VAL                      0X01U

/**
 * Register: XQSPIPSU_RX_THRESHOLD
 */
    #define XQSPIPSU_RX_THRESHOLD_OFFSET                              0X0000002CU

    #define XQSPIPSU_RX_FIFO_THRESHOLD_SHIFT                          0
    #define XQSPIPSU_RX_FIFO_THRESHOLD_WIDTH                          6
    #define XQSPIPSU_RX_FIFO_THRESHOLD_MASK                           0X0000003FU
    #define XQSPIPSU_RX_FIFO_THRESHOLD_RESET_VAL                      0X01U

    #define XQSPIPSU_RXFIFO_THRESHOLD_OPT                             32U

/**
 * Register: XQSPIPSU_GPIO
 */
    #define XQSPIPSU_GPIO_OFFSET                                      0X00000030U

    #define XQSPIPSU_GPIO_WP_N_SHIFT                                  0
    #define XQSPIPSU_GPIO_WP_N_WIDTH                                  1
    #define XQSPIPSU_GPIO_WP_N_MASK                                   0X00000001U

/**
 * Register: XQSPIPSU_LPBK_DLY_ADJ
 */
    #define XQSPIPSU_LPBK_DLY_ADJ_OFFSET                              0X00000038U

    #define XQSPIPSU_LPBK_DLY_ADJ_USE_LPBK_SHIFT                      5
    #define XQSPIPSU_LPBK_DLY_ADJ_USE_LPBK_WIDTH                      1
    #define XQSPIPSU_LPBK_DLY_ADJ_USE_LPBK_MASK                       0X00000020U

    #define XQSPIPSU_LPBK_DLY_ADJ_DLY1_SHIFT                          3
    #define XQSPIPSU_LPBK_DLY_ADJ_DLY1_WIDTH                          2
    #define XQSPIPSU_LPBK_DLY_ADJ_DLY1_MASK                           0X00000018U

    #define XQSPIPSU_LPBK_DLY_ADJ_DLY0_SHIFT                          0
    #define XQSPIPSU_LPBK_DLY_ADJ_DLY0_WIDTH                          3
    #define XQSPIPSU_LPBK_DLY_ADJ_DLY0_MASK                           0X00000007U

/**
 * Register: XQSPIPSU_GEN_FIFO
 */
    #define XQSPIPSU_GEN_FIFO_OFFSET                                  0X00000040U

    #define XQSPIPSU_GEN_FIFO_DATA_SHIFT                              0
    #define XQSPIPSU_GEN_FIFO_DATA_WIDTH                              20
    #define XQSPIPSU_GEN_FIFO_DATA_MASK                               0X000FFFFFU

/**
 * Register: XQSPIPSU_SEL
 */
    #define XQSPIPSU_SEL_OFFSET                                       0X00000044U

    #define XQSPIPSU_SEL_SHIFT                                        0
    #define XQSPIPSU_SEL_WIDTH                                        1
    #define XQSPIPSU_SEL_LQSPI_MASK                                   0X0U
    #define XQSPIPSU_SEL_GQSPI_MASK                                   0X00000001U

/**
 * Register: XQSPIPSU_FIFO_CTRL
 */
    #define XQSPIPSU_FIFO_CTRL_OFFSET                                 0X0000004CU

    #define XQSPIPSU_FIFO_CTRL_RST_RX_FIFO_SHIFT                      2
    #define XQSPIPSU_FIFO_CTRL_RST_RX_FIFO_WIDTH                      1
    #define XQSPIPSU_FIFO_CTRL_RST_RX_FIFO_MASK                       0X00000004U

    #define XQSPIPSU_FIFO_CTRL_RST_TX_FIFO_SHIFT                      1
    #define XQSPIPSU_FIFO_CTRL_RST_TX_FIFO_WIDTH                      1
    #define XQSPIPSU_FIFO_CTRL_RST_TX_FIFO_MASK                       0X00000002U

    #define XQSPIPSU_FIFO_CTRL_RST_GEN_FIFO_SHIFT                     0
    #define XQSPIPSU_FIFO_CTRL_RST_GEN_FIFO_WIDTH                     1
    #define XQSPIPSU_FIFO_CTRL_RST_GEN_FIFO_MASK                      0X00000001U

/**
 * Register: XQSPIPSU_GF_THRESHOLD
 */
    #define XQSPIPSU_GF_THRESHOLD_OFFSET                              0X00000050U

    #define XQSPIPSU_GEN_FIFO_THRESHOLD_SHIFT                         0
    #define XQSPIPSU_GEN_FIFO_THRESHOLD_WIDTH                         5
    #define XQSPIPSU_GEN_FIFO_THRESHOLD_MASK                          0X0000001F
    #define XQSPIPSU_GEN_FIFO_THRESHOLD_RESET_VAL                     0X10U

/**
 * Register: XQSPIPSU_POLL_CFG
 */
    #define XQSPIPSU_POLL_CFG_OFFSET                                  0X00000054U

    #define XQSPIPSU_POLL_CFG_EN_MASK_UPPER_SHIFT                     31
    #define XQSPIPSU_POLL_CFG_EN_MASK_UPPER_WIDTH                     1
    #define XQSPIPSU_POLL_CFG_EN_MASK_UPPER_MASK                      0X80000000U

    #define XQSPIPSU_POLL_CFG_EN_MASK_LOWER_SHIFT                     30
    #define XQSPIPSU_POLL_CFG_EN_MASK_LOWER_WIDTH                     1
    #define XQSPIPSU_POLL_CFG_EN_MASK_LOWER_MASK                      0X40000000U

    #define XQSPIPSU_POLL_CFG_MASK_EN_SHIFT                           8
    #define XQSPIPSU_POLL_CFG_MASK_EN_WIDTH                           8
    #define XQSPIPSU_POLL_CFG_MASK_EN_MASK                            0X0000FF00U

    #define XQSPIPSU_POLL_CFG_DATA_VALUE_SHIFT                        0
    #define XQSPIPSU_POLL_CFG_DATA_VALUE_WIDTH                        8
    #define XQSPIPSU_POLL_CFG_DATA_VALUE_MASK                         0X000000FFU

/**
 * Register: XQSPIPSU_P_TIMEOUT
 */
    #define XQSPIPSU_P_TO_OFFSET                                      0X00000058U

    #define XQSPIPSU_P_TO_VALUE_SHIFT                                 0
    #define XQSPIPSU_P_TO_VALUE_WIDTH                                 32
    #define XQSPIPSU_P_TO_VALUE_MASK                                  0XFFFFFFFFU

/**
 * Register: XQSPIPSU_XFER_STS
 */
    #define XQSPIPSU_XFER_STS_OFFSET                                  0X0000005CU

    #define XQSPIPSU_XFER_STS_PEND_BYTES_SHIFT                        0
    #define XQSPIPSU_XFER_STS_PEND_BYTES_WIDTH                        32
    #define XQSPIPSU_XFER_STS_PEND_BYTES_MASK                         0XFFFFFFFFU

/**
 * Register: XQSPIPSU_GF_SNAPSHOT
 */
    #define XQSPIPSU_GF_SNAPSHOT_OFFSET                               0X00000060U

    #define XQSPIPSU_GF_SNAPSHOT_SHIFT                                0
    #define XQSPIPSU_GF_SNAPSHOT_WIDTH                                20
    #define XQSPIPSU_GF_SNAPSHOT_MASK                                 0X000FFFFFU

/**
 * Register: XQSPIPSU_RX_COPY
 */
    #define XQSPIPSU_RX_COPY_OFFSET                                   0X00000064U

    #define XQSPIPSU_RX_COPY_UPPER_SHIFT                              8
    #define XQSPIPSU_RX_COPY_UPPER_WIDTH                              8
    #define XQSPIPSU_RX_COPY_UPPER_MASK                               0X0000FF00U

    #define XQSPIPSU_RX_COPY_LOWER_SHIFT                              0
    #define XQSPIPSU_RX_COPY_LOWER_WIDTH                              8
    #define XQSPIPSU_RX_COPY_LOWER_MASK                               0X000000FFU

/**
 * Register: XQSPIPSU_MOD_ID
 */
    #define XQSPIPSU_MOD_ID_OFFSET                                    0X000000FCU

    #define XQSPIPSU_MOD_ID_SHIFT                                     0
    #define XQSPIPSU_MOD_ID_WIDTH                                     32
    #define XQSPIPSU_MOD_ID_MASK                                      0XFFFFFFFFU

/**
 * Register: XQSPIPSU_QSPIDMA_DST_ADDR
 */
    #define XQSPIPSU_QSPIDMA_DST_ADDR_OFFSET                          0X00000700U

    #define XQSPIPSU_QSPIDMA_DST_ADDR_SHIFT                           2
    #define XQSPIPSU_QSPIDMA_DST_ADDR_WIDTH                           30
    #define XQSPIPSU_QSPIDMA_DST_ADDR_MASK                            0XFFFFFFFCU

/**
 * Register: XQSPIPSU_QSPIDMA_DST_SIZE
 */
    #define XQSPIPSU_QSPIDMA_DST_SIZE_OFFSET                          0X00000704U

    #define XQSPIPSU_QSPIDMA_DST_SIZE_SHIFT                           2
    #define XQSPIPSU_QSPIDMA_DST_SIZE_WIDTH                           27
    #define XQSPIPSU_QSPIDMA_DST_SIZE_MASK                            0X1FFFFFFCU

/**
 * Register: XQSPIPSU_QSPIDMA_DST_STS
 */
    #define XQSPIPSU_QSPIDMA_DST_STS_OFFSET                           0X00000708U

    #define XQSPIPSU_QSPIDMA_DST_STS_DONE_CNT_SHIFT                   13
    #define XQSPIPSU_QSPIDMA_DST_STS_DONE_CNT_WIDTH                   3
    #define XQSPIPSU_QSPIDMA_DST_STS_DONE_CNT_MASK                    0X0000E000U

    #define XQSPIPSU_QSPIDMA_DST_STS_DST_FIFO_LEVEL_SHIFT             5
    #define XQSPIPSU_QSPIDMA_DST_STS_DST_FIFO_LEVEL_WIDTH             8
    #define XQSPIPSU_QSPIDMA_DST_STS_DST_FIFO_LEVEL_MASK              0X00001FE0U

    #define XQSPIPSU_QSPIDMA_DST_STS_WR_OUTSTANDING_SHIFT             1
    #define XQSPIPSU_QSPIDMA_DST_STS_WR_OUTSTANDING_WIDTH             4
    #define XQSPIPSU_QSPIDMA_DST_STS_WR_OUTSTANDING_MASK              0X0000001EU

    #define XQSPIPSU_QSPIDMA_DST_STS_BUSY_SHIFT                       0
    #define XQSPIPSU_QSPIDMA_DST_STS_BUSY_WIDTH                       1
    #define XQSPIPSU_QSPIDMA_DST_STS_BUSY_MASK                        0X00000001U

    #define XQSPIPSU_QSPIDMA_DST_STS_WTC                              0xE000U

/**
 * Register: XQSPIPSU_QSPIDMA_DST_CTRL
 */
    #define XQSPIPSU_QSPIDMA_DST_CTRL_OFFSET                          0X0000070CU

    #define XQSPIPSU_QSPIDMA_DST_CTRL_FIFO_LVL_HIT_THRESHOLD_SHIFT    25
    #define XQSPIPSU_QSPIDMA_DST_CTRL_FIFO_LVL_HIT_THRESHOLD_WIDTH    7
    #define XQSPIPSU_QSPIDMA_DST_CTRL_FIFO_LVL_HIT_THRESHOLD_MASK     0XFE000000U

    #define XQSPIPSU_QSPIDMA_DST_CTRL_APB_ERR_RESP_SHIFT              24
    #define XQSPIPSU_QSPIDMA_DST_CTRL_APB_ERR_RESP_WIDTH              1
    #define XQSPIPSU_QSPIDMA_DST_CTRL_APB_ERR_RESP_MASK               0X01000000U

    #define XQSPIPSU_QSPIDMA_DST_CTRL_ENDIAN_SHIFT                    23
    #define XQSPIPSU_QSPIDMA_DST_CTRL_ENDIAN_WIDTH                    1
    #define XQSPIPSU_QSPIDMA_DST_CTRL_ENDIAN_MASK                     0X00800000U

    #define XQSPIPSU_QSPIDMA_DST_CTRL_AXI_BRST_TYPE_SHIFT             22
    #define XQSPIPSU_QSPIDMA_DST_CTRL_AXI_BRST_TYPE_WIDTH             1
    #define XQSPIPSU_QSPIDMA_DST_CTRL_AXI_BRST_TYPE_MASK              0X00400000U

    #define XQSPIPSU_QSPIDMA_DST_CTRL_TO_VAL_SHIFT                    10
    #define XQSPIPSU_QSPIDMA_DST_CTRL_TO_VAL_WIDTH                    12
    #define XQSPIPSU_QSPIDMA_DST_CTRL_TO_VAL_MASK                     0X003FFC00U

    #define XQSPIPSU_QSPIDMA_DST_CTRL_FIFO_THRESHOLD_SHIFT            2
    #define XQSPIPSU_QSPIDMA_DST_CTRL_FIFO_THRESHOLD_WIDTH            8
    #define XQSPIPSU_QSPIDMA_DST_CTRL_FIFO_THRESHOLD_MASK             0X000003FCU

    #define XQSPIPSU_QSPIDMA_DST_CTRL_PAUSE_STRM_SHIFT                1
    #define XQSPIPSU_QSPIDMA_DST_CTRL_PAUSE_STRM_WIDTH                1
    #define XQSPIPSU_QSPIDMA_DST_CTRL_PAUSE_STRM_MASK                 0X00000002U

    #define XQSPIPSU_QSPIDMA_DST_CTRL_PAUSE_MEM_SHIFT                 0
    #define XQSPIPSU_QSPIDMA_DST_CTRL_PAUSE_MEM_WIDTH                 1
    #define XQSPIPSU_QSPIDMA_DST_CTRL_PAUSE_MEM_MASK                  0X00000001U

    #define XQSPIPSU_QSPIDMA_DST_CTRL_RESET_VAL                       0x403FFA00U

/**
 * Register: XQSPIPSU_QSPIDMA_DST_I_STS
 */
    #define XQSPIPSU_QSPIDMA_DST_I_STS_OFFSET                         0X00000714U

    #define XQSPIPSU_QSPIDMA_DST_I_STS_FIFO_OF_SHIFT                  7
    #define XQSPIPSU_QSPIDMA_DST_I_STS_FIFO_OF_WIDTH                  1
    #define XQSPIPSU_QSPIDMA_DST_I_STS_FIFO_OF_MASK                   0X00000080U

    #define XQSPIPSU_QSPIDMA_DST_I_STS_INVALID_APB_SHIFT              6
    #define XQSPIPSU_QSPIDMA_DST_I_STS_INVALID_APB_WIDTH              1
    #define XQSPIPSU_QSPIDMA_DST_I_STS_INVALID_APB_MASK               0X00000040U

    #define XQSPIPSU_QSPIDMA_DST_I_STS_THRESHOLD_HIT_SHIFT            5
    #define XQSPIPSU_QSPIDMA_DST_I_STS_THRESHOLD_HIT_WIDTH            1
    #define XQSPIPSU_QSPIDMA_DST_I_STS_THRESHOLD_HIT_MASK             0X00000020U

    #define XQSPIPSU_QSPIDMA_DST_I_STS_TO_MEM_SHIFT                   4
    #define XQSPIPSU_QSPIDMA_DST_I_STS_TO_MEM_WIDTH                   1
    #define XQSPIPSU_QSPIDMA_DST_I_STS_TO_MEM_MASK                    0X00000010U

    #define XQSPIPSU_QSPIDMA_DST_I_STS_TO_STRM_SHIFT                  3
    #define XQSPIPSU_QSPIDMA_DST_I_STS_TO_STRM_WIDTH                  1
    #define XQSPIPSU_QSPIDMA_DST_I_STS_TO_STRM_MASK                   0X00000008U

    #define XQSPIPSU_QSPIDMA_DST_I_STS_AXI_BRESP_ERR_SHIFT            2
    #define XQSPIPSU_QSPIDMA_DST_I_STS_AXI_BRESP_ERR_WIDTH            1
    #define XQSPIPSU_QSPIDMA_DST_I_STS_AXI_BRESP_ERR_MASK             0X00000004U

    #define XQSPIPSU_QSPIDMA_DST_I_STS_DONE_SHIFT                     1
    #define XQSPIPSU_QSPIDMA_DST_I_STS_DONE_WIDTH                     1
    #define XQSPIPSU_QSPIDMA_DST_I_STS_DONE_MASK                      0X00000002U

    #define XQSPIPSU_QSPIDMA_DST_INTR_ERR_MASK                        0X000000FCU
    #define XQSPIPSU_QSPIDMA_DST_INTR_ALL_MASK                        0X000000FEU

/**
 * Register: XQSPIPSU_QSPIDMA_DST_I_EN
 */
    #define XQSPIPSU_QSPIDMA_DST_I_EN_OFFSET                          0X00000718U

    #define XQSPIPSU_QSPIDMA_DST_I_EN_FIFO_OF_SHIFT                   7
    #define XQSPIPSU_QSPIDMA_DST_I_EN_FIFO_OF_WIDTH                   1
    #define XQSPIPSU_QSPIDMA_DST_I_EN_FIFO_OF_MASK                    0X00000080U

    #define XQSPIPSU_QSPIDMA_DST_I_EN_INVALID_APB_SHIFT               6
    #define XQSPIPSU_QSPIDMA_DST_I_EN_INVALID_APB_WIDTH               1
    #define XQSPIPSU_QSPIDMA_DST_I_EN_INVALID_APB_MASK                0X00000040U

    #define XQSPIPSU_QSPIDMA_DST_I_EN_THRESHOLD_HIT_SHIFT             5
    #define XQSPIPSU_QSPIDMA_DST_I_EN_THRESHOLD_HIT_WIDTH             1
    #define XQSPIPSU_QSPIDMA_DST_I_EN_THRESHOLD_HIT_MASK              0X00000020U

    #define XQSPIPSU_QSPIDMA_DST_I_EN_TO_MEM_SHIFT                    4
    #define XQSPIPSU_QSPIDMA_DST_I_EN_TO_MEM_WIDTH                    1
    #define XQSPIPSU_QSPIDMA_DST_I_EN_TO_MEM_MASK                     0X00000010U

    #define XQSPIPSU_QSPIDMA_DST_I_EN_TO_STRM_SHIFT                   3
    #define XQSPIPSU_QSPIDMA_DST_I_EN_TO_STRM_WIDTH                   1
    #define XQSPIPSU_QSPIDMA_DST_I_EN_TO_STRM_MASK                    0X00000008U

    #define XQSPIPSU_QSPIDMA_DST_I_EN_AXI_BRESP_ERR_SHIFT             2
    #define XQSPIPSU_QSPIDMA_DST_I_EN_AXI_BRESP_ERR_WIDTH             1
    #define XQSPIPSU_QSPIDMA_DST_I_EN_AXI_BRESP_ERR_MASK              0X00000004U

    #define XQSPIPSU_QSPIDMA_DST_I_EN_DONE_SHIFT                      1
    #define XQSPIPSU_QSPIDMA_DST_I_EN_DONE_WIDTH                      1
    #define XQSPIPSU_QSPIDMA_DST_I_EN_DONE_MASK                       0X00000002U

/**
 * Register: XQSPIPSU_QSPIDMA_DST_I_DIS
 */
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_OFFSET                         0X0000071CU

    #define XQSPIPSU_QSPIDMA_DST_I_DIS_FIFO_OF_SHIFT                  7
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_FIFO_OF_WIDTH                  1
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_FIFO_OF_MASK                   0X00000080U

    #define XQSPIPSU_QSPIDMA_DST_I_DIS_INVALID_APB_SHIFT              6
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_INVALID_APB_WIDTH              1
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_INVALID_APB_MASK               0X00000040U

    #define XQSPIPSU_QSPIDMA_DST_I_DIS_THRESHOLD_HIT_SHIFT            5
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_THRESHOLD_HIT_WIDTH            1
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_THRESHOLD_HIT_MASK             0X00000020U

    #define XQSPIPSU_QSPIDMA_DST_I_DIS_TO_MEM_SHIFT                   4
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_TO_MEM_WIDTH                   1
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_TO_MEM_MASK                    0X00000010U

    #define XQSPIPSU_QSPIDMA_DST_I_DIS_TO_STRM_SHIFT                  3
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_TO_STRM_WIDTH                  1
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_TO_STRM_MASK                   0X00000008U

    #define XQSPIPSU_QSPIDMA_DST_I_DIS_AXI_BRESP_ERR_SHIFT            2
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_AXI_BRESP_ERR_WIDTH            1
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_AXI_BRESP_ERR_MASK             0X00000004U

    #define XQSPIPSU_QSPIDMA_DST_I_DIS_DONE_SHIFT                     1
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_DONE_WIDTH                     1
    #define XQSPIPSU_QSPIDMA_DST_I_DIS_DONE_MASK                      0X00000002U

/**
 * Register: XQSPIPSU_QSPIDMA_DST_IMR
 */
    #define XQSPIPSU_QSPIDMA_DST_IMR_OFFSET                           0X00000720U

    #define XQSPIPSU_QSPIDMA_DST_IMR_FIFO_OF_SHIFT                    7
    #define XQSPIPSU_QSPIDMA_DST_IMR_FIFO_OF_WIDTH                    1
    #define XQSPIPSU_QSPIDMA_DST_IMR_FIFO_OF_MASK                     0X00000080U

    #define XQSPIPSU_QSPIDMA_DST_IMR_INVALID_APB_SHIFT                6
    #define XQSPIPSU_QSPIDMA_DST_IMR_INVALID_APB_WIDTH                1
    #define XQSPIPSU_QSPIDMA_DST_IMR_INVALID_APB_MASK                 0X00000040U

    #define XQSPIPSU_QSPIDMA_DST_IMR_THRESHOLD_HIT_SHIFT              5
    #define XQSPIPSU_QSPIDMA_DST_IMR_THRESHOLD_HIT_WIDTH              1
    #define XQSPIPSU_QSPIDMA_DST_IMR_THRESHOLD_HIT_MASK               0X00000020U

    #define XQSPIPSU_QSPIDMA_DST_IMR_TO_MEM_SHIFT                     4
    #define XQSPIPSU_QSPIDMA_DST_IMR_TO_MEM_WIDTH                     1
    #define XQSPIPSU_QSPIDMA_DST_IMR_TO_MEM_MASK                      0X00000010U

    #define XQSPIPSU_QSPIDMA_DST_IMR_TO_STRM_SHIFT                    3
    #define XQSPIPSU_QSPIDMA_DST_IMR_TO_STRM_WIDTH                    1
    #define XQSPIPSU_QSPIDMA_DST_IMR_TO_STRM_MASK                     0X00000008U

    #define XQSPIPSU_QSPIDMA_DST_IMR_AXI_BRESP_ERR_SHIFT              2
    #define XQSPIPSU_QSPIDMA_DST_IMR_AXI_BRESP_ERR_WIDTH              1
    #define XQSPIPSU_QSPIDMA_DST_IMR_AXI_BRESP_ERR_MASK               0X00000004U

    #define XQSPIPSU_QSPIDMA_DST_IMR_DONE_SHIFT                       1
    #define XQSPIPSU_QSPIDMA_DST_IMR_DONE_WIDTH                       1
    #define XQSPIPSU_QSPIDMA_DST_IMR_DONE_MASK                        0X00000002U

/**
 * Register: XQSPIPSU_QSPIDMA_DST_CTRL2
 */
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_OFFSET                         0X00000724U

    #define XQSPIPSU_QSPIDMA_DST_CTRL2_RAM_EMASA_SHIFT                27
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_RAM_EMASA_WIDTH                1
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_RAM_EMASA_MASK                 0X08000000U

    #define XQSPIPSU_QSPIDMA_DST_CTRL2_AWCACHE_SHIFT                  24
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_AWCACHE_WIDTH                  3
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_AWCACHE_MASK                   0X07000000U

    #define XQSPIPSU_QSPIDMA_DST_CTRL2_TO_EN_SHIFT                    22
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_TO_EN_WIDTH                    1
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_TO_EN_MASK                     0X00400000U

    #define XQSPIPSU_QSPIDMA_DST_CTRL2_RAM_EMAB_SHIFT                 19
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_RAM_EMAB_WIDTH                 3
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_RAM_EMAB_MASK                  0X00380000U

    #define XQSPIPSU_QSPIDMA_DST_CTRL2_RAM_EMAA_SHIFT                 16
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_RAM_EMAA_WIDTH                 3
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_RAM_EMAA_MASK                  0X00070000U

    #define XQSPIPSU_QSPIDMA_DST_CTRL2_TO_PRE_SHIFT                   4
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_TO_PRE_WIDTH                   12
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_TO_PRE_MASK                    0X0000FFF0U

    #define XQSPIPSU_QSPIDMA_DST_CTRL2_MAX_OUTS_CMDS_SHIFT            0
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_MAX_OUTS_CMDS_WIDTH            4
    #define XQSPIPSU_QSPIDMA_DST_CTRL2_MAX_OUTS_CMDS_MASK             0X0000000FU

/**
 * Register: XQSPIPSU_QSPIDMA_DST_ADDR_MSB
 */
    #define XQSPIPSU_QSPIDMA_DST_ADDR_MSB_OFFSET                      0X00000728U

    #define XQSPIPSU_QSPIDMA_DST_ADDR_MSB_SHIFT                       0
    #define XQSPIPSU_QSPIDMA_DST_ADDR_MSB_WIDTH                       12
    #define XQSPIPSU_QSPIDMA_DST_ADDR_MSB_MASK                        0X00000FFFU

/**
 * Register: XQSPIPSU_QSPIDMA_FUTURE_ECO
 */
    #define XQSPIPSU_QSPIDMA_FUTURE_ECO_OFFSET                        0X00000EFCU

    #define XQSPIPSU_QSPIDMA_FUTURE_ECO_VAL_SHIFT                     0
    #define XQSPIPSU_QSPIDMA_FUTURE_ECO_VAL_WIDTH                     32
    #define XQSPIPSU_QSPIDMA_FUTURE_ECO_VAL_MASK                      0XFFFFFFFFU

/*
 * Generic FIFO masks
 */
    #define XQSPIPSU_GENFIFO_IMM_DATA_MASK                            0xFFU
    #define XQSPIPSU_GENFIFO_DATA_XFER                                0x100U
    #define XQSPIPSU_GENFIFO_EXP                                      0x200U
    #define XQSPIPSU_GENFIFO_MODE_SPI                                 0x400U
    #define XQSPIPSU_GENFIFO_MODE_DUALSPI                             0x800U
    #define XQSPIPSU_GENFIFO_MODE_QUADSPI                             0xC00U
    #define XQSPIPSU_GENFIFO_MODE_MASK                                0xC00U /* And with ~MASK first */
    #define XQSPIPSU_GENFIFO_CS_LOWER                                 0x1000U
    #define XQSPIPSU_GENFIFO_CS_UPPER                                 0x2000U
    #define XQSPIPSU_GENFIFO_BUS_LOWER                                0x4000U
    #define XQSPIPSU_GENFIFO_BUS_UPPER                                0x8000U
    #define XQSPIPSU_GENFIFO_BUS_BOTH                                 0xC000U  /* inverse is no bus */
    #define XQSPIPSU_GENFIFO_BUS_MASK                                 0xC000U  /* And with ~MASK first */
    #define XQSPIPSU_GENFIFO_TX                                       0x10000U /* inverse is zero pump */
    #define XQSPIPSU_GENFIFO_RX                                       0x20000U /* inverse is RX discard */
    #define XQSPIPSU_GENFIFO_STRIPE                                   0x40000U
    #define XQSPIPSU_GENFIFO_POLL                                     0x80000U

/*QSPI Data delay register*/
    #define XQSPIPSU_DATA_DLY_ADJ_OFFSET                              0X000000F8U

    #define XQSPIPSU_DATA_DLY_ADJ_USE_DATA_DLY_SHIFT                  31
    #define XQSPIPSU_DATA_DLY_ADJ_USE_DATA_DLY_WIDTH                  1
    #define XQSPIPSU_DATA_DLY_ADJ_USE_DATA_DLY_MASK                   0X80000000U

    #define XQSPIPSU_DATA_DLY_ADJ_DLY_SHIFT                           28
    #define XQSPIPSU_DATA_DLY_ADJ_DLY_WIDTH                           3
    #define XQSPIPSU_DATA_DLY_ADJ_DLY_MASK                            0X70000000U

/* Tapdelay Bypass register*/
    #define IOU_TAPDLY_BYPASS_OFFSET                                  0X00000390
    #define IOU_TAPDLY_BYPASS_LQSPI_RX_SHIFT                          0X02
    #define IOU_TAPDLY_BYPASS_LQSPI_RX_WIDTH                          0X01
    #define IOU_TAPDLY_BYPASS_LQSPI_RX_MASK                           0x00000004
    #define IOU_TAPDLY_RESET_STATE                                    0x7

/***************** Macros (Inline Functions) Definitions *********************/

    #define XQspiPsu_In32     Xil_In32
    #define XQspiPsu_Out32    Xil_Out32

/****************************************************************************/

/**
 * Read a register.
 *
 * @param	BaseAddress contains the base address of the device.
 * @param	RegOffset contains the offset from the 1st register of the
 *		device to the target register.
 *
 * @return	The value read from the register.
 *
 * @note		C-Style signature:
 *		u32 XQspiPsu_ReadReg(u32 BaseAddress. s32 RegOffset)
 *
 ******************************************************************************/
    #define XQspiPsu_ReadReg( BaseAddress, RegOffset )    XQspiPsu_In32( ( BaseAddress ) + ( RegOffset ) )

/***************************************************************************/

/**
 * Write to a register.
 *
 * @param	BaseAddress contains the base address of the device.
 * @param	RegOffset contains the offset from the 1st register of the
 *		device to target register.
 * @param	RegisterValue is the value to be written to the register.
 *
 * @return	None.
 *
 * @note		C-Style signature:
 *		void XQspiPsu_WriteReg(u32 BaseAddress, s32 RegOffset,
 *		u32 RegisterValue)
 *
 ******************************************************************************/
    #define XQspiPsu_WriteReg( BaseAddress, RegOffset, RegisterValue )    XQspiPsu_Out32( ( BaseAddress ) + ( RegOffset ), ( RegisterValue ) )


    #ifdef __cplusplus
}
    #endif


#endif /* _XQSPIPSU_H_ */
/** @} */
