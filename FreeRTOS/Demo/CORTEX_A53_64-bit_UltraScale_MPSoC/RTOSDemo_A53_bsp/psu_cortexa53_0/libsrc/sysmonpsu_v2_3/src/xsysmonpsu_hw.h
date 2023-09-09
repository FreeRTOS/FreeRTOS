/******************************************************************************
*
* Copyright (C) 2016 Xilinx, Inc.  All rights reserved.
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
* XILINX BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
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
 * @file xsysmonpsu_hw.h
 *
 * This header file contains the identifiers and basic driver functions (or
 * macros) that can be used to access the device. Other driver functions
 * are defined in xsysmonpsu.h.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who    Date	Changes
 * ----- -----  -------- -----------------------------------------------
 * 1.0   kvn	  12/15/15 First release
 * 2.0   vns    08/14/16  Added CFG_REG3, SEQ_INPUT_MODE2, SEQ_ACQ2,
 *                        SEQ_CH2 and SEQ_AVG2 offsets and bit masks
 * 2.1   sk     03/03/16 Check for PL reset before doing PL Sysmon reset.
 *
 * </pre>
 *
 ******************************************************************************/

#ifndef XSYSMONPSU_HW_H__
    #define XSYSMONPSU_HW_H__


    #ifdef __cplusplus
    extern "C" {
    #endif

/***************************** Include Files ********************************/

    #include "xil_types.h"
    #include "xil_assert.h"
    #include "xil_io.h"
    #include "xparameters.h"

/**
 * XSysmonPsu Base Address
 */
    #define XSYSMONPSU_BASEADDR                              0xFFA50000U

/**
 * Register: XSysmonPsuMisc
 */
    #define XSYSMONPSU_MISC_OFFSET                           0x00000000U
    #define XSYSMONPSU_MISC_RSTVAL                           0x00000000U

    #define XSYSMONPSU_MISC_SLVERR_EN_DRP_SHIFT              1U
    #define XSYSMONPSU_MISC_SLVERR_EN_DRP_WIDTH              1U
    #define XSYSMONPSU_MISC_SLVERR_EN_DRP_MASK               0x00000002U

    #define XSYSMONPSU_MISC_SLVERR_EN_SHIFT                  0U
    #define XSYSMONPSU_MISC_SLVERR_EN_WIDTH                  1U
    #define XSYSMONPSU_MISC_SLVERR_EN_MASK                   0x00000001U

/**
 * Register: XSysmonPsuIsr0
 */
    #define XSYSMONPSU_ISR_0_OFFSET                          0x00000010U
    #define XSYSMONPSU_ISR_0_MASK                            0xffffffffU
    #define XSYSMONPSU_ISR_0_RSTVAL                          0x00000000U

    #define XSYSMONPSU_ISR_0_PL_ALM_15_SHIFT                 31U
    #define XSYSMONPSU_ISR_0_PL_ALM_15_WIDTH                 1U
    #define XSYSMONPSU_ISR_0_PL_ALM_15_MASK                  0x80000000U

    #define XSYSMONPSU_ISR_0_PL_ALM_14_SHIFT                 30U
    #define XSYSMONPSU_ISR_0_PL_ALM_14_WIDTH                 1U
    #define XSYSMONPSU_ISR_0_PL_ALM_14_MASK                  0x40000000U

    #define XSYSMONPSU_ISR_0_PL_ALM_13_SHIFT                 29U
    #define XSYSMONPSU_ISR_0_PL_ALM_13_WIDTH                 1U
    #define XSYSMONPSU_ISR_0_PL_ALM_13_MASK                  0x20000000U

    #define XSYSMONPSU_ISR_0_PL_ALM_12_SHIFT                 28U
    #define XSYSMONPSU_ISR_0_PL_ALM_12_WIDTH                 1U
    #define XSYSMONPSU_ISR_0_PL_ALM_12_MASK                  0x10000000U

    #define XSYSMONPSU_ISR_0_PL_ALM_11_SHIFT                 27U
    #define XSYSMONPSU_ISR_0_PL_ALM_11_WIDTH                 1U
    #define XSYSMONPSU_ISR_0_PL_ALM_11_MASK                  0x08000000U

    #define XSYSMONPSU_ISR_0_PL_ALM_10_SHIFT                 26U
    #define XSYSMONPSU_ISR_0_PL_ALM_10_WIDTH                 1U
    #define XSYSMONPSU_ISR_0_PL_ALM_10_MASK                  0x04000000U

    #define XSYSMONPSU_ISR_0_PL_ALM_9_SHIFT                  25U
    #define XSYSMONPSU_ISR_0_PL_ALM_9_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PL_ALM_9_MASK                   0x02000000U

    #define XSYSMONPSU_ISR_0_PL_ALM_8_SHIFT                  24U
    #define XSYSMONPSU_ISR_0_PL_ALM_8_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PL_ALM_8_MASK                   0x01000000U

    #define XSYSMONPSU_ISR_0_PL_ALM_7_SHIFT                  23U
    #define XSYSMONPSU_ISR_0_PL_ALM_7_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PL_ALM_7_MASK                   0x00800000U

    #define XSYSMONPSU_ISR_0_PL_ALM_6_SHIFT                  22U
    #define XSYSMONPSU_ISR_0_PL_ALM_6_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PL_ALM_6_MASK                   0x00400000U

    #define XSYSMONPSU_ISR_0_PL_ALM_5_SHIFT                  21U
    #define XSYSMONPSU_ISR_0_PL_ALM_5_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PL_ALM_5_MASK                   0x00200000U

    #define XSYSMONPSU_ISR_0_PL_ALM_4_SHIFT                  20U
    #define XSYSMONPSU_ISR_0_PL_ALM_4_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PL_ALM_4_MASK                   0x00100000U

    #define XSYSMONPSU_ISR_0_PL_ALM_3_SHIFT                  19U
    #define XSYSMONPSU_ISR_0_PL_ALM_3_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PL_ALM_3_MASK                   0x00080000U

    #define XSYSMONPSU_ISR_0_PL_ALM_2_SHIFT                  18U
    #define XSYSMONPSU_ISR_0_PL_ALM_2_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PL_ALM_2_MASK                   0x00040000U

    #define XSYSMONPSU_ISR_0_PL_ALM_1_SHIFT                  17U
    #define XSYSMONPSU_ISR_0_PL_ALM_1_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PL_ALM_1_MASK                   0x00020000U

    #define XSYSMONPSU_ISR_0_PL_ALM_0_SHIFT                  16U
    #define XSYSMONPSU_ISR_0_PL_ALM_0_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PL_ALM_0_MASK                   0x00010000U

    #define XSYSMONPSU_ISR_0_PS_ALM_15_SHIFT                 15U
    #define XSYSMONPSU_ISR_0_PS_ALM_15_WIDTH                 1U
    #define XSYSMONPSU_ISR_0_PS_ALM_15_MASK                  0x00008000U

    #define XSYSMONPSU_ISR_0_PS_ALM_14_SHIFT                 14U
    #define XSYSMONPSU_ISR_0_PS_ALM_14_WIDTH                 1U
    #define XSYSMONPSU_ISR_0_PS_ALM_14_MASK                  0x00004000U

    #define XSYSMONPSU_ISR_0_PS_ALM_13_SHIFT                 13U
    #define XSYSMONPSU_ISR_0_PS_ALM_13_WIDTH                 1U
    #define XSYSMONPSU_ISR_0_PS_ALM_13_MASK                  0x00002000U

    #define XSYSMONPSU_ISR_0_PS_ALM_12_SHIFT                 12U
    #define XSYSMONPSU_ISR_0_PS_ALM_12_WIDTH                 1U
    #define XSYSMONPSU_ISR_0_PS_ALM_12_MASK                  0x00001000U

    #define XSYSMONPSU_ISR_0_PS_ALM_11_SHIFT                 11U
    #define XSYSMONPSU_ISR_0_PS_ALM_11_WIDTH                 1U
    #define XSYSMONPSU_ISR_0_PS_ALM_11_MASK                  0x00000800U

    #define XSYSMONPSU_ISR_0_PS_ALM_10_SHIFT                 10U
    #define XSYSMONPSU_ISR_0_PS_ALM_10_WIDTH                 1U
    #define XSYSMONPSU_ISR_0_PS_ALM_10_MASK                  0x00000400U

    #define XSYSMONPSU_ISR_0_PS_ALM_9_SHIFT                  9U
    #define XSYSMONPSU_ISR_0_PS_ALM_9_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PS_ALM_9_MASK                   0x00000200U

    #define XSYSMONPSU_ISR_0_PS_ALM_8_SHIFT                  8U
    #define XSYSMONPSU_ISR_0_PS_ALM_8_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PS_ALM_8_MASK                   0x00000100U

    #define XSYSMONPSU_ISR_0_PS_ALM_7_SHIFT                  7U
    #define XSYSMONPSU_ISR_0_PS_ALM_7_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PS_ALM_7_MASK                   0x00000080U

    #define XSYSMONPSU_ISR_0_PS_ALM_6_SHIFT                  6U
    #define XSYSMONPSU_ISR_0_PS_ALM_6_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PS_ALM_6_MASK                   0x00000040U

    #define XSYSMONPSU_ISR_0_PS_ALM_5_SHIFT                  5U
    #define XSYSMONPSU_ISR_0_PS_ALM_5_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PS_ALM_5_MASK                   0x00000020U

    #define XSYSMONPSU_ISR_0_PS_ALM_4_SHIFT                  4U
    #define XSYSMONPSU_ISR_0_PS_ALM_4_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PS_ALM_4_MASK                   0x00000010U

    #define XSYSMONPSU_ISR_0_PS_ALM_3_SHIFT                  3U
    #define XSYSMONPSU_ISR_0_PS_ALM_3_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PS_ALM_3_MASK                   0x00000008U

    #define XSYSMONPSU_ISR_0_PS_ALM_2_SHIFT                  2U
    #define XSYSMONPSU_ISR_0_PS_ALM_2_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PS_ALM_2_MASK                   0x00000004U

    #define XSYSMONPSU_ISR_0_PS_ALM_1_SHIFT                  1U
    #define XSYSMONPSU_ISR_0_PS_ALM_1_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PS_ALM_1_MASK                   0x00000002U

    #define XSYSMONPSU_ISR_0_PS_ALM_0_SHIFT                  0U
    #define XSYSMONPSU_ISR_0_PS_ALM_0_WIDTH                  1U
    #define XSYSMONPSU_ISR_0_PS_ALM_0_MASK                   0x00000001U

/**
 * Register: XSysmonPsuIsr1
 */
    #define XSYSMONPSU_ISR_1_OFFSET                          0x00000014U
    #define XSYSMONPSU_ISR_1_MASK                            0xe000001fU
    #define XSYSMONPSU_ISR_1_RSTVAL                          0x00000000U

    #define XSYSMONPSU_ISR_1_ADD_DECD_ERR_SHIFT              31U
    #define XSYSMONPSU_ISR_1_ADD_DECD_ERR_WIDTH              1U
    #define XSYSMONPSU_ISR_1_ADD_DECD_ERR_MASK               0x80000000U

    #define XSYSMONPSU_ISR_1_ADD_DECD_ERR_PL_SYSMON_SHIFT    30U
    #define XSYSMONPSU_ISR_1_ADD_DECD_ERR_PL_SYSMON_WIDTH    1U
    #define XSYSMONPSU_ISR_1_ADD_DECD_ERR_PL_SYSMON_MASK     0x40000000U

    #define XSYSMONPSU_ISR_1_ADD_DECD_ERR_PS_SYSMON_SHIFT    29U
    #define XSYSMONPSU_ISR_1_ADD_DECD_ERR_PS_SYSMON_WIDTH    1U
    #define XSYSMONPSU_ISR_1_ADD_DECD_ERR_PS_SYSMON_MASK     0x20000000U

    #define XSYSMONPSU_ISR_1_EOS_SHIFT                       4U
    #define XSYSMONPSU_ISR_1_EOS_WIDTH                       1U
    #define XSYSMONPSU_ISR_1_EOS_MASK                        0x00000010U

    #define XSYSMONPSU_ISR_1_EOC_SHIFT                       3U
    #define XSYSMONPSU_ISR_1_EOC_WIDTH                       1U
    #define XSYSMONPSU_ISR_1_EOC_MASK                        0x00000008U

    #define XSYSMONPSU_ISR_1_PL_OT_SHIFT                     2U
    #define XSYSMONPSU_ISR_1_PL_OT_WIDTH                     1U
    #define XSYSMONPSU_ISR_1_PL_OT_MASK                      0x00000004U

    #define XSYSMONPSU_ISR_1_PS_LPD_OT_SHIFT                 1U
    #define XSYSMONPSU_ISR_1_PS_LPD_OT_WIDTH                 1U
    #define XSYSMONPSU_ISR_1_PS_LPD_OT_MASK                  0x00000002U

    #define XSYSMONPSU_ISR_1_PS_FPD_OT_SHIFT                 0U
    #define XSYSMONPSU_ISR_1_PS_FPD_OT_WIDTH                 1U
    #define XSYSMONPSU_ISR_1_PS_FPD_OT_MASK                  0x00000001U

/**
 * Register: XSysmonPsuImr0
 */
    #define XSYSMONPSU_IMR_0_OFFSET                          0x00000018U
    #define XSYSMONPSU_IMR_0_RSTVAL                          0xffffffffU

    #define XSYSMONPSU_IMR_0_PL_ALM_15_SHIFT                 31U
    #define XSYSMONPSU_IMR_0_PL_ALM_15_WIDTH                 1U
    #define XSYSMONPSU_IMR_0_PL_ALM_15_MASK                  0x80000000U

    #define XSYSMONPSU_IMR_0_PL_ALM_14_SHIFT                 30U
    #define XSYSMONPSU_IMR_0_PL_ALM_14_WIDTH                 1U
    #define XSYSMONPSU_IMR_0_PL_ALM_14_MASK                  0x40000000U

    #define XSYSMONPSU_IMR_0_PL_ALM_13_SHIFT                 29U
    #define XSYSMONPSU_IMR_0_PL_ALM_13_WIDTH                 1U
    #define XSYSMONPSU_IMR_0_PL_ALM_13_MASK                  0x20000000U

    #define XSYSMONPSU_IMR_0_PL_ALM_12_SHIFT                 28U
    #define XSYSMONPSU_IMR_0_PL_ALM_12_WIDTH                 1U
    #define XSYSMONPSU_IMR_0_PL_ALM_12_MASK                  0x10000000U

    #define XSYSMONPSU_IMR_0_PL_ALM_11_SHIFT                 27U
    #define XSYSMONPSU_IMR_0_PL_ALM_11_WIDTH                 1U
    #define XSYSMONPSU_IMR_0_PL_ALM_11_MASK                  0x08000000U

    #define XSYSMONPSU_IMR_0_PL_ALM_10_SHIFT                 26U
    #define XSYSMONPSU_IMR_0_PL_ALM_10_WIDTH                 1U
    #define XSYSMONPSU_IMR_0_PL_ALM_10_MASK                  0x04000000U

    #define XSYSMONPSU_IMR_0_PL_ALM_9_SHIFT                  25U
    #define XSYSMONPSU_IMR_0_PL_ALM_9_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PL_ALM_9_MASK                   0x02000000U

    #define XSYSMONPSU_IMR_0_PL_ALM_8_SHIFT                  24U
    #define XSYSMONPSU_IMR_0_PL_ALM_8_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PL_ALM_8_MASK                   0x01000000U

    #define XSYSMONPSU_IMR_0_PL_ALM_7_SHIFT                  23U
    #define XSYSMONPSU_IMR_0_PL_ALM_7_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PL_ALM_7_MASK                   0x00800000U

    #define XSYSMONPSU_IMR_0_PL_ALM_6_SHIFT                  22U
    #define XSYSMONPSU_IMR_0_PL_ALM_6_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PL_ALM_6_MASK                   0x00400000U

    #define XSYSMONPSU_IMR_0_PL_ALM_5_SHIFT                  21U
    #define XSYSMONPSU_IMR_0_PL_ALM_5_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PL_ALM_5_MASK                   0x00200000U

    #define XSYSMONPSU_IMR_0_PL_ALM_4_SHIFT                  20U
    #define XSYSMONPSU_IMR_0_PL_ALM_4_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PL_ALM_4_MASK                   0x00100000U

    #define XSYSMONPSU_IMR_0_PL_ALM_3_SHIFT                  19U
    #define XSYSMONPSU_IMR_0_PL_ALM_3_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PL_ALM_3_MASK                   0x00080000U

    #define XSYSMONPSU_IMR_0_PL_ALM_2_SHIFT                  18U
    #define XSYSMONPSU_IMR_0_PL_ALM_2_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PL_ALM_2_MASK                   0x00040000U

    #define XSYSMONPSU_IMR_0_PL_ALM_1_SHIFT                  17U
    #define XSYSMONPSU_IMR_0_PL_ALM_1_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PL_ALM_1_MASK                   0x00020000U

    #define XSYSMONPSU_IMR_0_PL_ALM_0_SHIFT                  16U
    #define XSYSMONPSU_IMR_0_PL_ALM_0_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PL_ALM_0_MASK                   0x00010000U

    #define XSYSMONPSU_IMR_0_PS_ALM_15_SHIFT                 15U
    #define XSYSMONPSU_IMR_0_PS_ALM_15_WIDTH                 1U
    #define XSYSMONPSU_IMR_0_PS_ALM_15_MASK                  0x00008000U

    #define XSYSMONPSU_IMR_0_PS_ALM_14_SHIFT                 14U
    #define XSYSMONPSU_IMR_0_PS_ALM_14_WIDTH                 1U
    #define XSYSMONPSU_IMR_0_PS_ALM_14_MASK                  0x00004000U

    #define XSYSMONPSU_IMR_0_PS_ALM_13_SHIFT                 13U
    #define XSYSMONPSU_IMR_0_PS_ALM_13_WIDTH                 1U
    #define XSYSMONPSU_IMR_0_PS_ALM_13_MASK                  0x00002000U

    #define XSYSMONPSU_IMR_0_PS_ALM_12_SHIFT                 12U
    #define XSYSMONPSU_IMR_0_PS_ALM_12_WIDTH                 1U
    #define XSYSMONPSU_IMR_0_PS_ALM_12_MASK                  0x00001000U

    #define XSYSMONPSU_IMR_0_PS_ALM_11_SHIFT                 11U
    #define XSYSMONPSU_IMR_0_PS_ALM_11_WIDTH                 1U
    #define XSYSMONPSU_IMR_0_PS_ALM_11_MASK                  0x00000800U

    #define XSYSMONPSU_IMR_0_PS_ALM_10_SHIFT                 10U
    #define XSYSMONPSU_IMR_0_PS_ALM_10_WIDTH                 1U
    #define XSYSMONPSU_IMR_0_PS_ALM_10_MASK                  0x00000400U

    #define XSYSMONPSU_IMR_0_PS_ALM_9_SHIFT                  9U
    #define XSYSMONPSU_IMR_0_PS_ALM_9_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PS_ALM_9_MASK                   0x00000200U

    #define XSYSMONPSU_IMR_0_PS_ALM_8_SHIFT                  8U
    #define XSYSMONPSU_IMR_0_PS_ALM_8_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PS_ALM_8_MASK                   0x00000100U

    #define XSYSMONPSU_IMR_0_PS_ALM_7_SHIFT                  7U
    #define XSYSMONPSU_IMR_0_PS_ALM_7_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PS_ALM_7_MASK                   0x00000080U

    #define XSYSMONPSU_IMR_0_PS_ALM_6_SHIFT                  6U
    #define XSYSMONPSU_IMR_0_PS_ALM_6_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PS_ALM_6_MASK                   0x00000040U

    #define XSYSMONPSU_IMR_0_PS_ALM_5_SHIFT                  5U
    #define XSYSMONPSU_IMR_0_PS_ALM_5_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PS_ALM_5_MASK                   0x00000020U

    #define XSYSMONPSU_IMR_0_PS_ALM_4_SHIFT                  4U
    #define XSYSMONPSU_IMR_0_PS_ALM_4_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PS_ALM_4_MASK                   0x00000010U

    #define XSYSMONPSU_IMR_0_PS_ALM_3_SHIFT                  3U
    #define XSYSMONPSU_IMR_0_PS_ALM_3_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PS_ALM_3_MASK                   0x00000008U

    #define XSYSMONPSU_IMR_0_PS_ALM_2_SHIFT                  2U
    #define XSYSMONPSU_IMR_0_PS_ALM_2_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PS_ALM_2_MASK                   0x00000004U

    #define XSYSMONPSU_IMR_0_PS_ALM_1_SHIFT                  1U
    #define XSYSMONPSU_IMR_0_PS_ALM_1_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PS_ALM_1_MASK                   0x00000002U

    #define XSYSMONPSU_IMR_0_PS_ALM_0_SHIFT                  0U
    #define XSYSMONPSU_IMR_0_PS_ALM_0_WIDTH                  1U
    #define XSYSMONPSU_IMR_0_PS_ALM_0_MASK                   0x00000001U

/**
 * Register: XSysmonPsuImr1
 */
    #define XSYSMONPSU_IMR_1_OFFSET                          0x0000001CU
    #define XSYSMONPSU_IMR_1_RSTVAL                          0xe000001fU

    #define XSYSMONPSU_IMR_1_ADD_DECD_ERR_SHIFT              31U
    #define XSYSMONPSU_IMR_1_ADD_DECD_ERR_WIDTH              1U
    #define XSYSMONPSU_IMR_1_ADD_DECD_ERR_MASK               0x80000000U

    #define XSYSMONPSU_IMR_1_ADD_DECD_ERR_PL_SYSMON_SHIFT    30U
    #define XSYSMONPSU_IMR_1_ADD_DECD_ERR_PL_SYSMON_WIDTH    1U
    #define XSYSMONPSU_IMR_1_ADD_DECD_ERR_PL_SYSMON_MASK     0x40000000U

    #define XSYSMONPSU_IMR_1_ADD_DECD_ERR_PS_SYSMON_SHIFT    29U
    #define XSYSMONPSU_IMR_1_ADD_DECD_ERR_PS_SYSMON_WIDTH    1U
    #define XSYSMONPSU_IMR_1_ADD_DECD_ERR_PS_SYSMON_MASK     0x20000000U

    #define XSYSMONPSU_IMR_1_EOS_SHIFT                       4U
    #define XSYSMONPSU_IMR_1_EOS_WIDTH                       1U
    #define XSYSMONPSU_IMR_1_EOS_MASK                        0x00000010U

    #define XSYSMONPSU_IMR_1_EOC_SHIFT                       3U
    #define XSYSMONPSU_IMR_1_EOC_WIDTH                       1U
    #define XSYSMONPSU_IMR_1_EOC_MASK                        0x00000008U

    #define XSYSMONPSU_IMR_1_PL_OT_SHIFT                     2U
    #define XSYSMONPSU_IMR_1_PL_OT_WIDTH                     1U
    #define XSYSMONPSU_IMR_1_PL_OT_MASK                      0x00000004U

    #define XSYSMONPSU_IMR_1_PS_LPD_OT_SHIFT                 1U
    #define XSYSMONPSU_IMR_1_PS_LPD_OT_WIDTH                 1U
    #define XSYSMONPSU_IMR_1_PS_LPD_OT_MASK                  0x00000002U

    #define XSYSMONPSU_IMR_1_PS_FPD_OT_SHIFT                 0U
    #define XSYSMONPSU_IMR_1_PS_FPD_OT_WIDTH                 1U
    #define XSYSMONPSU_IMR_1_PS_FPD_OT_MASK                  0x00000001U

/**
 * Register: XSysmonPsuIer0
 */
    #define XSYSMONPSU_IER_0_OFFSET                          0x00000020U
    #define XSYSMONPSU_IXR_0_MASK                            0xFFFFFFFFU
    #define XSYSMONPSU_IER_0_RSTVAL                          0x00000000U

    #define XSYSMONPSU_IER_0_PL_ALM_15_SHIFT                 31U
    #define XSYSMONPSU_IER_0_PL_ALM_15_WIDTH                 1U
    #define XSYSMONPSU_IER_0_PL_ALM_15_MASK                  0x80000000U

    #define XSYSMONPSU_IER_0_PL_ALM_14_SHIFT                 30U
    #define XSYSMONPSU_IER_0_PL_ALM_14_WIDTH                 1U
    #define XSYSMONPSU_IER_0_PL_ALM_14_MASK                  0x40000000U

    #define XSYSMONPSU_IER_0_PL_ALM_13_SHIFT                 29U
    #define XSYSMONPSU_IER_0_PL_ALM_13_WIDTH                 1U
    #define XSYSMONPSU_IER_0_PL_ALM_13_MASK                  0x20000000U

    #define XSYSMONPSU_IER_0_PL_ALM_12_SHIFT                 28U
    #define XSYSMONPSU_IER_0_PL_ALM_12_WIDTH                 1U
    #define XSYSMONPSU_IER_0_PL_ALM_12_MASK                  0x10000000U

    #define XSYSMONPSU_IER_0_PL_ALM_11_SHIFT                 27U
    #define XSYSMONPSU_IER_0_PL_ALM_11_WIDTH                 1U
    #define XSYSMONPSU_IER_0_PL_ALM_11_MASK                  0x08000000U

    #define XSYSMONPSU_IER_0_PL_ALM_10_SHIFT                 26U
    #define XSYSMONPSU_IER_0_PL_ALM_10_WIDTH                 1U
    #define XSYSMONPSU_IER_0_PL_ALM_10_MASK                  0x04000000U

    #define XSYSMONPSU_IER_0_PL_ALM_9_SHIFT                  25U
    #define XSYSMONPSU_IER_0_PL_ALM_9_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PL_ALM_9_MASK                   0x02000000U

    #define XSYSMONPSU_IER_0_PL_ALM_8_SHIFT                  24U
    #define XSYSMONPSU_IER_0_PL_ALM_8_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PL_ALM_8_MASK                   0x01000000U

    #define XSYSMONPSU_IER_0_PL_ALM_7_SHIFT                  23U
    #define XSYSMONPSU_IER_0_PL_ALM_7_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PL_ALM_7_MASK                   0x00800000U

    #define XSYSMONPSU_IER_0_PL_ALM_6_SHIFT                  22U
    #define XSYSMONPSU_IER_0_PL_ALM_6_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PL_ALM_6_MASK                   0x00400000U

    #define XSYSMONPSU_IER_0_PL_ALM_5_SHIFT                  21U
    #define XSYSMONPSU_IER_0_PL_ALM_5_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PL_ALM_5_MASK                   0x00200000U

    #define XSYSMONPSU_IER_0_PL_ALM_4_SHIFT                  20U
    #define XSYSMONPSU_IER_0_PL_ALM_4_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PL_ALM_4_MASK                   0x00100000U

    #define XSYSMONPSU_IER_0_PL_ALM_3_SHIFT                  19U
    #define XSYSMONPSU_IER_0_PL_ALM_3_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PL_ALM_3_MASK                   0x00080000U

    #define XSYSMONPSU_IER_0_PL_ALM_2_SHIFT                  18U
    #define XSYSMONPSU_IER_0_PL_ALM_2_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PL_ALM_2_MASK                   0x00040000U

    #define XSYSMONPSU_IER_0_PL_ALM_1_SHIFT                  17U
    #define XSYSMONPSU_IER_0_PL_ALM_1_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PL_ALM_1_MASK                   0x00020000U

    #define XSYSMONPSU_IER_0_PL_ALM_0_SHIFT                  16U
    #define XSYSMONPSU_IER_0_PL_ALM_0_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PL_ALM_0_MASK                   0x00010000U

    #define XSYSMONPSU_IER_0_PS_ALM_15_SHIFT                 15U
    #define XSYSMONPSU_IER_0_PS_ALM_15_WIDTH                 1U
    #define XSYSMONPSU_IER_0_PS_ALM_15_MASK                  0x00008000U

    #define XSYSMONPSU_IER_0_PS_ALM_14_SHIFT                 14U
    #define XSYSMONPSU_IER_0_PS_ALM_14_WIDTH                 1U
    #define XSYSMONPSU_IER_0_PS_ALM_14_MASK                  0x00004000U

    #define XSYSMONPSU_IER_0_PS_ALM_13_SHIFT                 13U
    #define XSYSMONPSU_IER_0_PS_ALM_13_WIDTH                 1U
    #define XSYSMONPSU_IER_0_PS_ALM_13_MASK                  0x00002000U

    #define XSYSMONPSU_IER_0_PS_ALM_12_SHIFT                 12U
    #define XSYSMONPSU_IER_0_PS_ALM_12_WIDTH                 1U
    #define XSYSMONPSU_IER_0_PS_ALM_12_MASK                  0x00001000U

    #define XSYSMONPSU_IER_0_PS_ALM_11_SHIFT                 11U
    #define XSYSMONPSU_IER_0_PS_ALM_11_WIDTH                 1U
    #define XSYSMONPSU_IER_0_PS_ALM_11_MASK                  0x00000800U

    #define XSYSMONPSU_IER_0_PS_ALM_10_SHIFT                 10U
    #define XSYSMONPSU_IER_0_PS_ALM_10_WIDTH                 1U
    #define XSYSMONPSU_IER_0_PS_ALM_10_MASK                  0x00000400U

    #define XSYSMONPSU_IER_0_PS_ALM_9_SHIFT                  9U
    #define XSYSMONPSU_IER_0_PS_ALM_9_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PS_ALM_9_MASK                   0x00000200U

    #define XSYSMONPSU_IER_0_PS_ALM_8_SHIFT                  8U
    #define XSYSMONPSU_IER_0_PS_ALM_8_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PS_ALM_8_MASK                   0x00000100U

    #define XSYSMONPSU_IER_0_PS_ALM_7_SHIFT                  7U
    #define XSYSMONPSU_IER_0_PS_ALM_7_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PS_ALM_7_MASK                   0x00000080U

    #define XSYSMONPSU_IER_0_PS_ALM_6_SHIFT                  6U
    #define XSYSMONPSU_IER_0_PS_ALM_6_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PS_ALM_6_MASK                   0x00000040U

    #define XSYSMONPSU_IER_0_PS_ALM_5_SHIFT                  5U
    #define XSYSMONPSU_IER_0_PS_ALM_5_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PS_ALM_5_MASK                   0x00000020U

    #define XSYSMONPSU_IER_0_PS_ALM_4_SHIFT                  4U
    #define XSYSMONPSU_IER_0_PS_ALM_4_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PS_ALM_4_MASK                   0x00000010U

    #define XSYSMONPSU_IER_0_PS_ALM_3_SHIFT                  3U
    #define XSYSMONPSU_IER_0_PS_ALM_3_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PS_ALM_3_MASK                   0x00000008U

    #define XSYSMONPSU_IER_0_PS_ALM_2_SHIFT                  2U
    #define XSYSMONPSU_IER_0_PS_ALM_2_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PS_ALM_2_MASK                   0x00000004U

    #define XSYSMONPSU_IER_0_PS_ALM_1_SHIFT                  1U
    #define XSYSMONPSU_IER_0_PS_ALM_1_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PS_ALM_1_MASK                   0x00000002U

    #define XSYSMONPSU_IER_0_PS_ALM_0_SHIFT                  0U
    #define XSYSMONPSU_IER_0_PS_ALM_0_WIDTH                  1U
    #define XSYSMONPSU_IER_0_PS_ALM_0_MASK                   0x00000001U

/**
 * Register: XSysmonPsuIer1
 */
    #define XSYSMONPSU_IER_1_OFFSET                          0x00000024U
    #define XSYSMONPSU_IXR_1_MASK                            0xE000001FU
    #define XSYSMONPSU_IER_1_RSTVAL                          0x00000000U

    #define XSYSMONPSU_IER_1_ADD_DECD_ERR_SHIFT              31U
    #define XSYSMONPSU_IER_1_ADD_DECD_ERR_WIDTH              1U
    #define XSYSMONPSU_IER_1_ADD_DECD_ERR_MASK               0x80000000U

    #define XSYSMONPSU_IER_1_ADD_DECD_ERR_PL_SYSMON_SHIFT    30U
    #define XSYSMONPSU_IER_1_ADD_DECD_ERR_PL_SYSMON_WIDTH    1U
    #define XSYSMONPSU_IER_1_ADD_DECD_ERR_PL_SYSMON_MASK     0x40000000U

    #define XSYSMONPSU_IER_1_ADD_DECD_ERR_PS_SYSMON_SHIFT    29U
    #define XSYSMONPSU_IER_1_ADD_DECD_ERR_PS_SYSMON_WIDTH    1U
    #define XSYSMONPSU_IER_1_ADD_DECD_ERR_PS_SYSMON_MASK     0x20000000U

    #define XSYSMONPSU_IER_1_EOS_SHIFT                       4U
    #define XSYSMONPSU_IER_1_EOS_WIDTH                       1U
    #define XSYSMONPSU_IER_1_EOS_MASK                        0x00000010U

    #define XSYSMONPSU_IER_1_EOC_SHIFT                       3U
    #define XSYSMONPSU_IER_1_EOC_WIDTH                       1U
    #define XSYSMONPSU_IER_1_EOC_MASK                        0x00000008U

    #define XSYSMONPSU_IER_1_PL_OT_SHIFT                     2U
    #define XSYSMONPSU_IER_1_PL_OT_WIDTH                     1U
    #define XSYSMONPSU_IER_1_PL_OT_MASK                      0x00000004U

    #define XSYSMONPSU_IER_1_PS_LPD_OT_SHIFT                 1U
    #define XSYSMONPSU_IER_1_PS_LPD_OT_WIDTH                 1U
    #define XSYSMONPSU_IER_1_PS_LPD_OT_MASK                  0x00000002U

    #define XSYSMONPSU_IER_1_PS_FPD_OT_SHIFT                 0U
    #define XSYSMONPSU_IER_1_PS_FPD_OT_WIDTH                 1U
    #define XSYSMONPSU_IER_1_PS_FPD_OT_MASK                  0x00000001U

    #define XSYSMONPSU_IXR_1_SHIFT                           32U

/**
 * Register: XSysmonPsuIdr0
 */
    #define XSYSMONPSU_IDR_0_OFFSET                          0x00000028U
    #define XSYSMONPSU_IDR_0_RSTVAL                          0x00000000U

    #define XSYSMONPSU_IDR_0_PL_ALM_15_SHIFT                 31U
    #define XSYSMONPSU_IDR_0_PL_ALM_15_WIDTH                 1U
    #define XSYSMONPSU_IDR_0_PL_ALM_15_MASK                  0x80000000U

    #define XSYSMONPSU_IDR_0_PL_ALM_14_SHIFT                 30U
    #define XSYSMONPSU_IDR_0_PL_ALM_14_WIDTH                 1U
    #define XSYSMONPSU_IDR_0_PL_ALM_14_MASK                  0x40000000U

    #define XSYSMONPSU_IDR_0_PL_ALM_13_SHIFT                 29U
    #define XSYSMONPSU_IDR_0_PL_ALM_13_WIDTH                 1U
    #define XSYSMONPSU_IDR_0_PL_ALM_13_MASK                  0x20000000U

    #define XSYSMONPSU_IDR_0_PL_ALM_12_SHIFT                 28U
    #define XSYSMONPSU_IDR_0_PL_ALM_12_WIDTH                 1U
    #define XSYSMONPSU_IDR_0_PL_ALM_12_MASK                  0x10000000U

    #define XSYSMONPSU_IDR_0_PL_ALM_11_SHIFT                 27U
    #define XSYSMONPSU_IDR_0_PL_ALM_11_WIDTH                 1U
    #define XSYSMONPSU_IDR_0_PL_ALM_11_MASK                  0x08000000U

    #define XSYSMONPSU_IDR_0_PL_ALM_10_SHIFT                 26U
    #define XSYSMONPSU_IDR_0_PL_ALM_10_WIDTH                 1U
    #define XSYSMONPSU_IDR_0_PL_ALM_10_MASK                  0x04000000U

    #define XSYSMONPSU_IDR_0_PL_ALM_9_SHIFT                  25U
    #define XSYSMONPSU_IDR_0_PL_ALM_9_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PL_ALM_9_MASK                   0x02000000U

    #define XSYSMONPSU_IDR_0_PL_ALM_8_SHIFT                  24U
    #define XSYSMONPSU_IDR_0_PL_ALM_8_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PL_ALM_8_MASK                   0x01000000U

    #define XSYSMONPSU_IDR_0_PL_ALM_7_SHIFT                  23U
    #define XSYSMONPSU_IDR_0_PL_ALM_7_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PL_ALM_7_MASK                   0x00800000U

    #define XSYSMONPSU_IDR_0_PL_ALM_6_SHIFT                  22U
    #define XSYSMONPSU_IDR_0_PL_ALM_6_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PL_ALM_6_MASK                   0x00400000U

    #define XSYSMONPSU_IDR_0_PL_ALM_5_SHIFT                  21U
    #define XSYSMONPSU_IDR_0_PL_ALM_5_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PL_ALM_5_MASK                   0x00200000U

    #define XSYSMONPSU_IDR_0_PL_ALM_4_SHIFT                  20U
    #define XSYSMONPSU_IDR_0_PL_ALM_4_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PL_ALM_4_MASK                   0x00100000U

    #define XSYSMONPSU_IDR_0_PL_ALM_3_SHIFT                  19U
    #define XSYSMONPSU_IDR_0_PL_ALM_3_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PL_ALM_3_MASK                   0x00080000U

    #define XSYSMONPSU_IDR_0_PL_ALM_2_SHIFT                  18U
    #define XSYSMONPSU_IDR_0_PL_ALM_2_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PL_ALM_2_MASK                   0x00040000U

    #define XSYSMONPSU_IDR_0_PL_ALM_1_SHIFT                  17U
    #define XSYSMONPSU_IDR_0_PL_ALM_1_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PL_ALM_1_MASK                   0x00020000U

    #define XSYSMONPSU_IDR_0_PL_ALM_0_SHIFT                  16U
    #define XSYSMONPSU_IDR_0_PL_ALM_0_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PL_ALM_0_MASK                   0x00010000U

    #define XSYSMONPSU_IDR_0_PS_ALM_15_SHIFT                 15U
    #define XSYSMONPSU_IDR_0_PS_ALM_15_WIDTH                 1U
    #define XSYSMONPSU_IDR_0_PS_ALM_15_MASK                  0x00008000U

    #define XSYSMONPSU_IDR_0_PS_ALM_14_SHIFT                 14U
    #define XSYSMONPSU_IDR_0_PS_ALM_14_WIDTH                 1U
    #define XSYSMONPSU_IDR_0_PS_ALM_14_MASK                  0x00004000U

    #define XSYSMONPSU_IDR_0_PS_ALM_13_SHIFT                 13U
    #define XSYSMONPSU_IDR_0_PS_ALM_13_WIDTH                 1U
    #define XSYSMONPSU_IDR_0_PS_ALM_13_MASK                  0x00002000U

    #define XSYSMONPSU_IDR_0_PS_ALM_12_SHIFT                 12U
    #define XSYSMONPSU_IDR_0_PS_ALM_12_WIDTH                 1U
    #define XSYSMONPSU_IDR_0_PS_ALM_12_MASK                  0x00001000U

    #define XSYSMONPSU_IDR_0_PS_ALM_11_SHIFT                 11U
    #define XSYSMONPSU_IDR_0_PS_ALM_11_WIDTH                 1U
    #define XSYSMONPSU_IDR_0_PS_ALM_11_MASK                  0x00000800U

    #define XSYSMONPSU_IDR_0_PS_ALM_10_SHIFT                 10U
    #define XSYSMONPSU_IDR_0_PS_ALM_10_WIDTH                 1U
    #define XSYSMONPSU_IDR_0_PS_ALM_10_MASK                  0x00000400U

    #define XSYSMONPSU_IDR_0_PS_ALM_9_SHIFT                  9U
    #define XSYSMONPSU_IDR_0_PS_ALM_9_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PS_ALM_9_MASK                   0x00000200U

    #define XSYSMONPSU_IDR_0_PS_ALM_8_SHIFT                  8U
    #define XSYSMONPSU_IDR_0_PS_ALM_8_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PS_ALM_8_MASK                   0x00000100U

    #define XSYSMONPSU_IDR_0_PS_ALM_7_SHIFT                  7U
    #define XSYSMONPSU_IDR_0_PS_ALM_7_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PS_ALM_7_MASK                   0x00000080U

    #define XSYSMONPSU_IDR_0_PS_ALM_6_SHIFT                  6U
    #define XSYSMONPSU_IDR_0_PS_ALM_6_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PS_ALM_6_MASK                   0x00000040U

    #define XSYSMONPSU_IDR_0_PS_ALM_5_SHIFT                  5U
    #define XSYSMONPSU_IDR_0_PS_ALM_5_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PS_ALM_5_MASK                   0x00000020U

    #define XSYSMONPSU_IDR_0_PS_ALM_4_SHIFT                  4U
    #define XSYSMONPSU_IDR_0_PS_ALM_4_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PS_ALM_4_MASK                   0x00000010U

    #define XSYSMONPSU_IDR_0_PS_ALM_3_SHIFT                  3U
    #define XSYSMONPSU_IDR_0_PS_ALM_3_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PS_ALM_3_MASK                   0x00000008U

    #define XSYSMONPSU_IDR_0_PS_ALM_2_SHIFT                  2U
    #define XSYSMONPSU_IDR_0_PS_ALM_2_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PS_ALM_2_MASK                   0x00000004U

    #define XSYSMONPSU_IDR_0_PS_ALM_1_SHIFT                  1U
    #define XSYSMONPSU_IDR_0_PS_ALM_1_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PS_ALM_1_MASK                   0x00000002U

    #define XSYSMONPSU_IDR_0_PS_ALM_0_SHIFT                  0U
    #define XSYSMONPSU_IDR_0_PS_ALM_0_WIDTH                  1U
    #define XSYSMONPSU_IDR_0_PS_ALM_0_MASK                   0x00000001U

/**
 * Register: XSysmonPsuIdr1
 */
    #define XSYSMONPSU_IDR_1_OFFSET                          0x0000002CU
    #define XSYSMONPSU_IDR_1_RSTVAL                          0x00000000U

    #define XSYSMONPSU_IDR_1_ADD_DECD_ERR_SHIFT              31U
    #define XSYSMONPSU_IDR_1_ADD_DECD_ERR_WIDTH              1U
    #define XSYSMONPSU_IDR_1_ADD_DECD_ERR_MASK               0x80000000U

    #define XSYSMONPSU_IDR_1_ADD_DECD_ERR_PL_SYSMON_SHIFT    30U
    #define XSYSMONPSU_IDR_1_ADD_DECD_ERR_PL_SYSMON_WIDTH    1U
    #define XSYSMONPSU_IDR_1_ADD_DECD_ERR_PL_SYSMON_MASK     0x40000000U

    #define XSYSMONPSU_IDR_1_ADD_DECD_ERR_PS_SYSMON_SHIFT    29U
    #define XSYSMONPSU_IDR_1_ADD_DECD_ERR_PS_SYSMON_WIDTH    1U
    #define XSYSMONPSU_IDR_1_ADD_DECD_ERR_PS_SYSMON_MASK     0x20000000U

    #define XSYSMONPSU_IDR_1_EOS_SHIFT                       4U
    #define XSYSMONPSU_IDR_1_EOS_WIDTH                       1U
    #define XSYSMONPSU_IDR_1_EOS_MASK                        0x00000010U

    #define XSYSMONPSU_IDR_1_EOC_SHIFT                       3U
    #define XSYSMONPSU_IDR_1_EOC_WIDTH                       1U
    #define XSYSMONPSU_IDR_1_EOC_MASK                        0x00000008U

    #define XSYSMONPSU_IDR_1_PL_OT_SHIFT                     2U
    #define XSYSMONPSU_IDR_1_PL_OT_WIDTH                     1U
    #define XSYSMONPSU_IDR_1_PL_OT_MASK                      0x00000004U

    #define XSYSMONPSU_IDR_1_PS_LPD_OT_SHIFT                 1U
    #define XSYSMONPSU_IDR_1_PS_LPD_OT_WIDTH                 1U
    #define XSYSMONPSU_IDR_1_PS_LPD_OT_MASK                  0x00000002U

    #define XSYSMONPSU_IDR_1_PS_FPD_OT_SHIFT                 0U
    #define XSYSMONPSU_IDR_1_PS_FPD_OT_WIDTH                 1U
    #define XSYSMONPSU_IDR_1_PS_FPD_OT_MASK                  0x00000001U

/**
 * Register: XSysmonPsuPsSysmonSts
 */
    #define XSYSMONPSU_PS_SYSMON_CSTS_OFFSET                 0x00000040U
    #define XSYSMONPSU_PS_SYSMON_CSTS_RSTVAL                 0x00000000U

    #define XSYSMONPSU_PS_SYSMON_CSTS_STRTUP_STE_SHIFT       24U
    #define XSYSMONPSU_PS_SYSMON_CSTS_STRTUP_STE_WIDTH       4U
    #define XSYSMONPSU_PS_SYSMON_CSTS_STRTUP_STE_MASK        0x0f000000U

    #define XSYSMONPSU_PS_SYSMON_CSTS_STRTUP_DNE_SHIFT       16U
    #define XSYSMONPSU_PS_SYSMON_CSTS_STRTUP_DNE_WIDTH       1U
    #define XSYSMONPSU_PS_SYSMON_CSTS_STRTUP_DNE_MASK        0x00010000U

    #define XSYSMONPSU_PS_SYSMON_CSTS_AUTO_CONVST_SHIFT      3U
    #define XSYSMONPSU_PS_SYSMON_CSTS_AUTO_CONVST_WIDTH      1U
    #define XSYSMONPSU_PS_SYSMON_CSTS_AUTO_CONVST_MASK       0x00000008U

    #define XSYSMONPSU_PS_SYSMON_CSTS_CONVST_SHIFT           2U
    #define XSYSMONPSU_PS_SYSMON_CSTS_CONVST_WIDTH           1U
    #define XSYSMONPSU_PS_SYSMON_CSTS_CONVST_MASK            0x00000004U

    #define XSYSMONPSU_PS_SYSMON_CSTS_RST_USR_SHIFT          1U
    #define XSYSMONPSU_PS_SYSMON_CSTS_RST_USR_WIDTH          1U
    #define XSYSMONPSU_PS_SYSMON_CSTS_RST_USR_MASK           0x00000002U

    #define XSYSMONPSU_PS_SYSMON_CSTS_STRTUP_TRIG_SHIFT      0U
    #define XSYSMONPSU_PS_SYSMON_CSTS_STRTUP_TRIG_WIDTH      1U
    #define XSYSMONPSU_PS_SYSMON_CSTS_STRTUP_TRIG_MASK       0x00000001U

    #define XSYSMONPSU_PS_SYSMON_READY                       0x08010000U

/**
 * Register: XSysmonPsuPlSysmonSts
 */
    #define XSYSMONPSU_PL_SYSMON_CSTS_OFFSET                 0x00000044U
    #define XSYSMONPSU_PL_SYSMON_CSTS_RSTVAL                 0x00000000U

    #define XSYSMONPSU_PL_SYSMON_CSTS_ACESBLE_SHIFT          0U
    #define XSYSMONPSU_PL_SYSMON_CSTS_ACESBLE_WIDTH          1U
    #define XSYSMONPSU_PL_SYSMON_CSTS_ACESBLE_MASK           0x00000001U

/**
 * Register: XSysmonPsuMonSts
 */
    #define XSYSMONPSU_MON_STS_OFFSET                        0x00000050U
    #define XSYSMONPSU_MON_STS_RSTVAL                        0x00000000U

    #define XSYSMONPSU_MON_STS_JTAG_LCKD_SHIFT               23U
    #define XSYSMONPSU_MON_STS_JTAG_LCKD_WIDTH               1U
    #define XSYSMONPSU_MON_STS_JTAG_LCKD_MASK                0x00800000U

    #define XSYSMONPSU_MON_STS_BSY_SHIFT                     22U
    #define XSYSMONPSU_MON_STS_BSY_WIDTH                     1U
    #define XSYSMONPSU_MON_STS_BSY_MASK                      0x00400000U

    #define XSYSMONPSU_MON_STS_CH_SHIFT                      16U
    #define XSYSMONPSU_MON_STS_CH_WIDTH                      6U
    #define XSYSMONPSU_MON_STS_CH_MASK                       0x003f0000U

    #define XSYSMONPSU_MON_STS_DATA_SHIFT                    0U
    #define XSYSMONPSU_MON_STS_DATA_WIDTH                    16U
    #define XSYSMONPSU_MON_STS_DATA_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuVccPspll0
 */
    #define XSYSMONPSU_VCC_PSPLL0_OFFSET                     0x00000060U
    #define XSYSMONPSU_VCC_PSPLL0_RSTVAL                     0x00000000U

    #define XSYSMONPSU_VCC_PSPLL0_VAL_SHIFT                  0U
    #define XSYSMONPSU_VCC_PSPLL0_VAL_WIDTH                  16U
    #define XSYSMONPSU_VCC_PSPLL0_VAL_MASK                   0x0000ffffU

/**
 * Register: XSysmonPsuVccPspll1
 */
    #define XSYSMONPSU_VCC_PSPLL1_OFFSET                     0x00000064U
    #define XSYSMONPSU_VCC_PSPLL1_RSTVAL                     0x00000000U

    #define XSYSMONPSU_VCC_PSPLL1_VAL_SHIFT                  0U
    #define XSYSMONPSU_VCC_PSPLL1_VAL_WIDTH                  16U
    #define XSYSMONPSU_VCC_PSPLL1_VAL_MASK                   0x0000ffffU

/**
 * Register: XSysmonPsuVccPspll2
 */
    #define XSYSMONPSU_VCC_PSPLL2_OFFSET                     0x00000068U
    #define XSYSMONPSU_VCC_PSPLL2_RSTVAL                     0x00000000U

    #define XSYSMONPSU_VCC_PSPLL2_VAL_SHIFT                  0U
    #define XSYSMONPSU_VCC_PSPLL2_VAL_WIDTH                  16U
    #define XSYSMONPSU_VCC_PSPLL2_VAL_MASK                   0x0000ffffU

/**
 * Register: XSysmonPsuVccPspll3
 */
    #define XSYSMONPSU_VCC_PSPLL3_OFFSET                     0x0000006CU
    #define XSYSMONPSU_VCC_PSPLL3_RSTVAL                     0x00000000U

    #define XSYSMONPSU_VCC_PSPLL3_VAL_SHIFT                  0U
    #define XSYSMONPSU_VCC_PSPLL3_VAL_WIDTH                  16U
    #define XSYSMONPSU_VCC_PSPLL3_VAL_MASK                   0x0000ffffU

/**
 * Register: XSysmonPsuVccPspll4
 */
    #define XSYSMONPSU_VCC_PSPLL4_OFFSET                     0x00000070U
    #define XSYSMONPSU_VCC_PSPLL4_RSTVAL                     0x00000000U

    #define XSYSMONPSU_VCC_PSPLL4_VAL_SHIFT                  0U
    #define XSYSMONPSU_VCC_PSPLL4_VAL_WIDTH                  16U
    #define XSYSMONPSU_VCC_PSPLL4_VAL_MASK                   0x0000ffffU

/**
 * Register: XSysmonPsuVccPsbatt
 */
    #define XSYSMONPSU_VCC_PSBATT_OFFSET                     0x00000074U
    #define XSYSMONPSU_VCC_PSBATT_RSTVAL                     0x00000000U

    #define XSYSMONPSU_VCC_PSBATT_VAL_SHIFT                  0U
    #define XSYSMONPSU_VCC_PSBATT_VAL_WIDTH                  16U
    #define XSYSMONPSU_VCC_PSBATT_VAL_MASK                   0x0000ffffU

/**
 * Register: XSysmonPsuVccint
 */
    #define XSYSMONPSU_VCCINT_OFFSET                         0x00000078U
    #define XSYSMONPSU_VCCINT_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VCCINT_VAL_SHIFT                      0U
    #define XSYSMONPSU_VCCINT_VAL_WIDTH                      16U
    #define XSYSMONPSU_VCCINT_VAL_MASK                       0x0000ffffU

/**
 * Register: XSysmonPsuVccbram
 */
    #define XSYSMONPSU_VCCBRAM_OFFSET                        0x0000007CU
    #define XSYSMONPSU_VCCBRAM_RSTVAL                        0x00000000U

    #define XSYSMONPSU_VCCBRAM_VAL_SHIFT                     0U
    #define XSYSMONPSU_VCCBRAM_VAL_WIDTH                     16U
    #define XSYSMONPSU_VCCBRAM_VAL_MASK                      0x0000ffffU

/**
 * Register: XSysmonPsuVccaux
 */
    #define XSYSMONPSU_VCCAUX_OFFSET                         0x00000080U
    #define XSYSMONPSU_VCCAUX_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VCCAUX_VAL_SHIFT                      0U
    #define XSYSMONPSU_VCCAUX_VAL_WIDTH                      16U
    #define XSYSMONPSU_VCCAUX_VAL_MASK                       0x0000ffffU

/**
 * Register: XSysmonPsuVccPsddrpll
 */
    #define XSYSMONPSU_VCC_PSDDRPLL_OFFSET                   0x00000084U
    #define XSYSMONPSU_VCC_PSDDRPLL_RSTVAL                   0x00000000U

    #define XSYSMONPSU_VCC_PSDDRPLL_VAL_SHIFT                0U
    #define XSYSMONPSU_VCC_PSDDRPLL_VAL_WIDTH                16U
    #define XSYSMONPSU_VCC_PSDDRPLL_VAL_MASK                 0x0000ffffU

/**
 * Register: XSysmonPsuDdrphyVref
 */
    #define XSYSMONPSU_DDRPHY_VREF_OFFSET                    0x00000088U
    #define XSYSMONPSU_DDRPHY_VREF_RSTVAL                    0x00000000U

    #define XSYSMONPSU_DDRPHY_VREF_VAL_SHIFT                 0U
    #define XSYSMONPSU_DDRPHY_VREF_VAL_WIDTH                 16U
    #define XSYSMONPSU_DDRPHY_VREF_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuDdrphyAto
 */
    #define XSYSMONPSU_DDRPHY_ATO_OFFSET                     0x0000008CU
    #define XSYSMONPSU_DDRPHY_ATO_RSTVAL                     0x00000000U

    #define XSYSMONPSU_DDRPHY_ATO_VAL_SHIFT                  0U
    #define XSYSMONPSU_DDRPHY_ATO_VAL_WIDTH                  16U
    #define XSYSMONPSU_DDRPHY_ATO_VAL_MASK                   0x0000ffffU

/**
 * Register: XSysmonPsuPsgtAt0
 */
    #define XSYSMONPSU_PSGT_AT0_OFFSET                       0x00000090U
    #define XSYSMONPSU_PSGT_AT0_RSTVAL                       0x00000000U

    #define XSYSMONPSU_PSGT_AT0_VAL_SHIFT                    0U
    #define XSYSMONPSU_PSGT_AT0_VAL_WIDTH                    16U
    #define XSYSMONPSU_PSGT_AT0_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuPsgtAt1
 */
    #define XSYSMONPSU_PSGT_AT1_OFFSET                       0x00000094U
    #define XSYSMONPSU_PSGT_AT1_RSTVAL                       0x00000000U

    #define XSYSMONPSU_PSGT_AT1_VAL_SHIFT                    0U
    #define XSYSMONPSU_PSGT_AT1_VAL_WIDTH                    16U
    #define XSYSMONPSU_PSGT_AT1_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuReserve0
 */
    #define XSYSMONPSU_RESERVE0_OFFSET                       0x00000098U
    #define XSYSMONPSU_RESERVE0_RSTVAL                       0x00000000U

    #define XSYSMONPSU_RESERVE0_VAL_SHIFT                    0U
    #define XSYSMONPSU_RESERVE0_VAL_WIDTH                    16U
    #define XSYSMONPSU_RESERVE0_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuReserve1
 */
    #define XSYSMONPSU_RESERVE1_OFFSET                       0x0000009CU
    #define XSYSMONPSU_RESERVE1_RSTVAL                       0x00000000U

    #define XSYSMONPSU_RESERVE1_VAL_SHIFT                    0U
    #define XSYSMONPSU_RESERVE1_VAL_WIDTH                    16U
    #define XSYSMONPSU_RESERVE1_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuTemp
 */
    #define XSYSMONPSU_TEMP_OFFSET                           0x00000000U
    #define XSYSMONPSU_TEMP_RSTVAL                           0x00000000U

    #define XSYSMONPSU_TEMP_SHIFT                            0U
    #define XSYSMONPSU_TEMP_WIDTH                            16U
    #define XSYSMONPSU_TEMP_MASK                             0x0000ffffU

/**
 * Register: XSysmonPsuSup1
 */
    #define XSYSMONPSU_SUP1_OFFSET                           0x00000004U
    #define XSYSMONPSU_SUP1_RSTVAL                           0x00000000U

    #define XSYSMONPSU_SUP1_SUP_VAL_SHIFT                    0U
    #define XSYSMONPSU_SUP1_SUP_VAL_WIDTH                    16U
    #define XSYSMONPSU_SUP1_SUP_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuSup2
 */
    #define XSYSMONPSU_SUP2_OFFSET                           0x00000008U
    #define XSYSMONPSU_SUP2_RSTVAL                           0x00000000U

    #define XSYSMONPSU_SUP2_SUP_VAL_SHIFT                    0U
    #define XSYSMONPSU_SUP2_SUP_VAL_WIDTH                    16U
    #define XSYSMONPSU_SUP2_SUP_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuVpVn
 */
    #define XSYSMONPSU_VP_VN_OFFSET                          0x0000000CU
    #define XSYSMONPSU_VP_VN_RSTVAL                          0x00000000U

    #define XSYSMONPSU_VP_VN_SHIFT                           0U
    #define XSYSMONPSU_VP_VN_WIDTH                           16U
    #define XSYSMONPSU_VP_VN_MASK                            0x0000ffffU

/**
 * Register: XSysmonPsuVrefp
 */
    #define XSYSMONPSU_VREFP_OFFSET                          0x00000010U
    #define XSYSMONPSU_VREFP_RSTVAL                          0x00000000U

    #define XSYSMONPSU_VREFP_SUP_VAL_SHIFT                   0U
    #define XSYSMONPSU_VREFP_SUP_VAL_WIDTH                   16U
    #define XSYSMONPSU_VREFP_SUP_VAL_MASK                    0x0000ffffU

/**
 * Register: XSysmonPsuVrefn
 */
    #define XSYSMONPSU_VREFN_OFFSET                          0x00000014U
    #define XSYSMONPSU_VREFN_RSTVAL                          0x00000000U

    #define XSYSMONPSU_VREFN_SUP_VAL_SHIFT                   0U
    #define XSYSMONPSU_VREFN_SUP_VAL_WIDTH                   16U
    #define XSYSMONPSU_VREFN_SUP_VAL_MASK                    0x0000ffffU

/**
 * Register: XSysmonPsuSup3
 */
    #define XSYSMONPSU_SUP3_OFFSET                           0x00000018U
    #define XSYSMONPSU_SUP3_RSTVAL                           0x00000000U

    #define XSYSMONPSU_SUP3_SUP_VAL_SHIFT                    0U
    #define XSYSMONPSU_SUP3_SUP_VAL_WIDTH                    16U
    #define XSYSMONPSU_SUP3_SUP_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuCalSupOff
 */
    #define XSYSMONPSU_CAL_SUP_OFF_OFFSET                    0x00000020U
    #define XSYSMONPSU_CAL_SUP_OFF_RSTVAL                    0x00000000U

    #define XSYSMONPSU_CAL_SUP_OFF_VAL_SHIFT                 0U
    #define XSYSMONPSU_CAL_SUP_OFF_VAL_WIDTH                 16U
    #define XSYSMONPSU_CAL_SUP_OFF_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuCalAdcBiplrOff
 */
    #define XSYSMONPSU_CAL_ADC_BIPLR_OFF_OFFSET              0x00000024U
    #define XSYSMONPSU_CAL_ADC_BIPLR_OFF_RSTVAL              0x00000000U

    #define XSYSMONPSU_CAL_ADC_BIPLR_OFF_VAL_SHIFT           0U
    #define XSYSMONPSU_CAL_ADC_BIPLR_OFF_VAL_WIDTH           16U
    #define XSYSMONPSU_CAL_ADC_BIPLR_OFF_VAL_MASK            0x0000ffffU

/**
 * Register: XSysmonPsuCalGainErr
 */
    #define XSYSMONPSU_CAL_GAIN_ERR_OFFSET                   0x00000028U
    #define XSYSMONPSU_CAL_GAIN_ERR_RSTVAL                   0x00000000U

    #define XSYSMONPSU_CAL_GAIN_ERR_VAL_SHIFT                0U
    #define XSYSMONPSU_CAL_GAIN_ERR_VAL_WIDTH                16U
    #define XSYSMONPSU_CAL_GAIN_ERR_VAL_MASK                 0x0000ffffU

/**
 * Register: XSysmonPsuSup4
 */
    #define XSYSMONPSU_SUP4_OFFSET                           0x00000034U
    #define XSYSMONPSU_SUP4_RSTVAL                           0x00000000U

    #define XSYSMONPSU_SUP4_SUP_VAL_SHIFT                    0U
    #define XSYSMONPSU_SUP4_SUP_VAL_WIDTH                    16U
    #define XSYSMONPSU_SUP4_SUP_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuSup5
 */
    #define XSYSMONPSU_SUP5_OFFSET                           0x00000038U
    #define XSYSMONPSU_SUP5_RSTVAL                           0x00000000U

    #define XSYSMONPSU_SUP5_SUP_VAL_SHIFT                    0U
    #define XSYSMONPSU_SUP5_SUP_VAL_WIDTH                    16U
    #define XSYSMONPSU_SUP5_SUP_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuSup6
 */
    #define XSYSMONPSU_SUP6_OFFSET                           0x0000003CU
    #define XSYSMONPSU_SUP6_RSTVAL                           0x00000000U

    #define XSYSMONPSU_SUP6_SUP_VAL_SHIFT                    0U
    #define XSYSMONPSU_SUP6_SUP_VAL_WIDTH                    16U
    #define XSYSMONPSU_SUP6_SUP_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuVaux00
 */
    #define XSYSMONPSU_VAUX00_OFFSET                         0x00000040U
    #define XSYSMONPSU_VAUX00_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX00_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX00_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX00_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux01
 */
    #define XSYSMONPSU_VAUX01_OFFSET                         0x00000044U
    #define XSYSMONPSU_VAUX01_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX01_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX01_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX01_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux02
 */
    #define XSYSMONPSU_VAUX02_OFFSET                         0x00000048U
    #define XSYSMONPSU_VAUX02_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX02_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX02_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX02_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux03
 */
    #define XSYSMONPSU_VAUX03_OFFSET                         0x0000004CU
    #define XSYSMONPSU_VAUX03_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX03_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX03_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX03_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux04
 */
    #define XSYSMONPSU_VAUX04_OFFSET                         0x00000050U
    #define XSYSMONPSU_VAUX04_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX04_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX04_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX04_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux05
 */
    #define XSYSMONPSU_VAUX05_OFFSET                         0x00000054U
    #define XSYSMONPSU_VAUX05_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX05_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX05_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX05_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux06
 */
    #define XSYSMONPSU_VAUX06_OFFSET                         0x00000058U
    #define XSYSMONPSU_VAUX06_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX06_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX06_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX06_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux07
 */
    #define XSYSMONPSU_VAUX07_OFFSET                         0x0000005CU
    #define XSYSMONPSU_VAUX07_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX07_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX07_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX07_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux08
 */
    #define XSYSMONPSU_VAUX08_OFFSET                         0x00000060U
    #define XSYSMONPSU_VAUX08_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX08_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX08_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX08_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux09
 */
    #define XSYSMONPSU_VAUX09_OFFSET                         0x00000064U
    #define XSYSMONPSU_VAUX09_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX09_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX09_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX09_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux0a
 */
    #define XSYSMONPSU_VAUX0A_OFFSET                         0x00000068U
    #define XSYSMONPSU_VAUX0A_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX0A_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX0A_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX0A_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux0b
 */
    #define XSYSMONPSU_VAUX0B_OFFSET                         0x0000006CU
    #define XSYSMONPSU_VAUX0B_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX0B_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX0B_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX0B_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux0c
 */
    #define XSYSMONPSU_VAUX0C_OFFSET                         0x00000070U
    #define XSYSMONPSU_VAUX0C_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX0C_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX0C_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX0C_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux0d
 */
    #define XSYSMONPSU_VAUX0D_OFFSET                         0x00000074U
    #define XSYSMONPSU_VAUX0D_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX0D_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX0D_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX0D_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux0e
 */
    #define XSYSMONPSU_VAUX0E_OFFSET                         0x00000078U
    #define XSYSMONPSU_VAUX0E_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX0E_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX0E_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX0E_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuVaux0f
 */
    #define XSYSMONPSU_VAUX0F_OFFSET                         0x0000007CU
    #define XSYSMONPSU_VAUX0F_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VAUX0F_VAUX_VAL_SHIFT                 0U
    #define XSYSMONPSU_VAUX0F_VAUX_VAL_WIDTH                 16U
    #define XSYSMONPSU_VAUX0F_VAUX_VAL_MASK                  0x0000ffffU

/**
 * Register: XSysmonPsuMaxTemp
 */
    #define XSYSMONPSU_MAX_TEMP_OFFSET                       0x00000080U
    #define XSYSMONPSU_MAX_TEMP_RSTVAL                       0x00000000U

    #define XSYSMONPSU_MAX_TEMP_SHIFT                        0U
    #define XSYSMONPSU_MAX_TEMP_WIDTH                        16U
    #define XSYSMONPSU_MAX_TEMP_MASK                         0x0000ffffU

/**
 * Register: XSysmonPsuMaxSup1
 */
    #define XSYSMONPSU_MAX_SUP1_OFFSET                       0x00000084U
    #define XSYSMONPSU_MAX_SUP1_RSTVAL                       0x00000000U

    #define XSYSMONPSU_MAX_SUP1_VAL_SHIFT                    0U
    #define XSYSMONPSU_MAX_SUP1_VAL_WIDTH                    16U
    #define XSYSMONPSU_MAX_SUP1_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuMaxSup2
 */
    #define XSYSMONPSU_MAX_SUP2_OFFSET                       0x00000088U
    #define XSYSMONPSU_MAX_SUP2_RSTVAL                       0x00000000U

    #define XSYSMONPSU_MAX_SUP2_VAL_SHIFT                    0U
    #define XSYSMONPSU_MAX_SUP2_VAL_WIDTH                    16U
    #define XSYSMONPSU_MAX_SUP2_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuMaxSup3
 */
    #define XSYSMONPSU_MAX_SUP3_OFFSET                       0x0000008CU
    #define XSYSMONPSU_MAX_SUP3_RSTVAL                       0x00000000U

    #define XSYSMONPSU_MAX_SUP3_VAL_SHIFT                    0U
    #define XSYSMONPSU_MAX_SUP3_VAL_WIDTH                    16U
    #define XSYSMONPSU_MAX_SUP3_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuMinTemp
 */
    #define XSYSMONPSU_MIN_TEMP_OFFSET                       0x00000090U
    #define XSYSMONPSU_MIN_TEMP_RSTVAL                       0x0000ffffU

    #define XSYSMONPSU_MIN_TEMP_SHIFT                        0U
    #define XSYSMONPSU_MIN_TEMP_WIDTH                        16U
    #define XSYSMONPSU_MIN_TEMP_MASK                         0x0000ffffU

/**
 * Register: XSysmonPsuMinSup1
 */
    #define XSYSMONPSU_MIN_SUP1_OFFSET                       0x00000094U
    #define XSYSMONPSU_MIN_SUP1_RSTVAL                       0x0000ffffU

    #define XSYSMONPSU_MIN_SUP1_VAL_SHIFT                    0U
    #define XSYSMONPSU_MIN_SUP1_VAL_WIDTH                    16U
    #define XSYSMONPSU_MIN_SUP1_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuMinSup2
 */
    #define XSYSMONPSU_MIN_SUP2_OFFSET                       0x00000098U
    #define XSYSMONPSU_MIN_SUP2_RSTVAL                       0x0000ffffU

    #define XSYSMONPSU_MIN_SUP2_VAL_SHIFT                    0U
    #define XSYSMONPSU_MIN_SUP2_VAL_WIDTH                    16U
    #define XSYSMONPSU_MIN_SUP2_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuMinSup3
 */
    #define XSYSMONPSU_MIN_SUP3_OFFSET                       0x0000009CU
    #define XSYSMONPSU_MIN_SUP3_RSTVAL                       0x0000ffffU

    #define XSYSMONPSU_MIN_SUP3_VAL_SHIFT                    0U
    #define XSYSMONPSU_MIN_SUP3_VAL_WIDTH                    16U
    #define XSYSMONPSU_MIN_SUP3_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuMaxSup4
 */
    #define XSYSMONPSU_MAX_SUP4_OFFSET                       0x000000A0U
    #define XSYSMONPSU_MAX_SUP4_RSTVAL                       0x00000000U

    #define XSYSMONPSU_MAX_SUP4_VAL_SHIFT                    0U
    #define XSYSMONPSU_MAX_SUP4_VAL_WIDTH                    16U
    #define XSYSMONPSU_MAX_SUP4_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuMaxSup5
 */
    #define XSYSMONPSU_MAX_SUP5_OFFSET                       0x000000A4U
    #define XSYSMONPSU_MAX_SUP5_RSTVAL                       0x00000000U

    #define XSYSMONPSU_MAX_SUP5_VAL_SHIFT                    0U
    #define XSYSMONPSU_MAX_SUP5_VAL_WIDTH                    16U
    #define XSYSMONPSU_MAX_SUP5_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuMaxSup6
 */
    #define XSYSMONPSU_MAX_SUP6_OFFSET                       0x000000A8U
    #define XSYSMONPSU_MAX_SUP6_RSTVAL                       0x00000000U

    #define XSYSMONPSU_MAX_SUP6_VAL_SHIFT                    0U
    #define XSYSMONPSU_MAX_SUP6_VAL_WIDTH                    16U
    #define XSYSMONPSU_MAX_SUP6_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuMinSup4
 */
    #define XSYSMONPSU_MIN_SUP4_OFFSET                       0x000000B0U
    #define XSYSMONPSU_MIN_SUP4_RSTVAL                       0x0000ffffU

    #define XSYSMONPSU_MIN_SUP4_VAL_SHIFT                    0U
    #define XSYSMONPSU_MIN_SUP4_VAL_WIDTH                    16U
    #define XSYSMONPSU_MIN_SUP4_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuMinSup5
 */
    #define XSYSMONPSU_MIN_SUP5_OFFSET                       0x000000B4U
    #define XSYSMONPSU_MIN_SUP5_RSTVAL                       0x0000ffffU

    #define XSYSMONPSU_MIN_SUP5_VAL_SHIFT                    0U
    #define XSYSMONPSU_MIN_SUP5_VAL_WIDTH                    16U
    #define XSYSMONPSU_MIN_SUP5_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuMinSup6
 */
    #define XSYSMONPSU_MIN_SUP6_OFFSET                       0x000000B8U
    #define XSYSMONPSU_MIN_SUP6_RSTVAL                       0x0000ffffU

    #define XSYSMONPSU_MIN_SUP6_VAL_SHIFT                    0U
    #define XSYSMONPSU_MIN_SUP6_VAL_WIDTH                    16U
    #define XSYSMONPSU_MIN_SUP6_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuStsFlag
 */
    #define XSYSMONPSU_STS_FLAG_OFFSET                       0x000000FCU
    #define XSYSMONPSU_STS_FLAG_RSTVAL                       0x00000000U

    #define XSYSMONPSU_STS_FLAG_CLK_OSC_USED_SHIFT           15U
    #define XSYSMONPSU_STS_FLAG_CLK_OSC_USED_WIDTH           1U
    #define XSYSMONPSU_STS_FLAG_CLK_OSC_USED_MASK            0x00008000U

    #define XSYSMONPSU_STS_FLAG_BLK_IN_RST_SHIFT             14U
    #define XSYSMONPSU_STS_FLAG_BLK_IN_RST_WIDTH             1U
    #define XSYSMONPSU_STS_FLAG_BLK_IN_RST_MASK              0x00004000U

    #define XSYSMONPSU_STS_FLAG_JTAG_DISD_SHIFT              11U
    #define XSYSMONPSU_STS_FLAG_JTAG_DISD_WIDTH              1U
    #define XSYSMONPSU_STS_FLAG_JTAG_DISD_MASK               0x00000800U

    #define XSYSMONPSU_STS_FLAG_JTAG_RD_ONLY_SHIFT           10U
    #define XSYSMONPSU_STS_FLAG_JTAG_RD_ONLY_WIDTH           1U
    #define XSYSMONPSU_STS_FLAG_JTAG_RD_ONLY_MASK            0x00000400U

    #define XSYSMONPSU_STS_FLAG_INTRNL_REF_SHIFT             9U
    #define XSYSMONPSU_STS_FLAG_INTRNL_REF_WIDTH             1U
    #define XSYSMONPSU_STS_FLAG_INTRNL_REF_MASK              0x00000200U

    #define XSYSMONPSU_STS_FLAG_DISD_SHIFT                   8U
    #define XSYSMONPSU_STS_FLAG_DISD_WIDTH                   1U
    #define XSYSMONPSU_STS_FLAG_DISD_MASK                    0x00000100U

    #define XSYSMONPSU_STS_FLAG_ALM_6_3_SHIFT                4U
    #define XSYSMONPSU_STS_FLAG_ALM_6_3_WIDTH                4U
    #define XSYSMONPSU_STS_FLAG_ALM_6_3_MASK                 0x000000f0U

    #define XSYSMONPSU_STS_FLAG_OT_SHIFT                     3U
    #define XSYSMONPSU_STS_FLAG_OT_WIDTH                     1U
    #define XSYSMONPSU_STS_FLAG_OT_MASK                      0x00000008U

    #define XSYSMONPSU_STS_FLAG_ALM_2_0_SHIFT                0U
    #define XSYSMONPSU_STS_FLAG_ALM_2_0_WIDTH                3U
    #define XSYSMONPSU_STS_FLAG_ALM_2_0_MASK                 0x00000007U

/**
 * Register: XSysmonPsuCfgReg0
 */
    #define XSYSMONPSU_CFG_REG0_OFFSET                       0x00000100U
    #define XSYSMONPSU_CFG_REG0_RSTVAL                       0x00000000U

    #define XSYSMONPSU_CFG_REG0_AVRGNG_SHIFT                 12U
    #define XSYSMONPSU_CFG_REG0_AVRGNG_WIDTH                 2U
    #define XSYSMONPSU_CFG_REG0_AVRGNG_MASK                  0x00003000U

    #define XSYSMONPSU_CFG_REG0_XTRNL_MUX_SHIFT              11U
    #define XSYSMONPSU_CFG_REG0_XTRNL_MUX_WIDTH              1U
    #define XSYSMONPSU_CFG_REG0_XTRNL_MUX_MASK               0x00000800U

    #define XSYSMONPSU_CFG_REG0_BU_SHIFT                     10U
    #define XSYSMONPSU_CFG_REG0_BU_WIDTH                     1U
    #define XSYSMONPSU_CFG_REG0_BU_MASK                      0x00000400U

    #define XSYSMONPSU_CFG_REG0_EC_SHIFT                     9U
    #define XSYSMONPSU_CFG_REG0_EC_WIDTH                     1U
    #define XSYSMONPSU_CFG_REG0_EC_MASK                      0x00000200U

    #define XSYSMONPSU_EVENT_MODE                            1
    #define XSYSMONPSU_CONTINUOUS_MODE                       2

    #define XSYSMONPSU_CFG_REG0_ACQ_SHIFT                    8U
    #define XSYSMONPSU_CFG_REG0_ACQ_WIDTH                    1U
    #define XSYSMONPSU_CFG_REG0_ACQ_MASK                     0x00000100U

    #define XSYSMONPSU_CFG_REG0_MUX_CH_SHIFT                 0U
    #define XSYSMONPSU_CFG_REG0_MUX_CH_WIDTH                 6U
    #define XSYSMONPSU_CFG_REG0_MUX_CH_MASK                  0x0000003fU

/**
 * Register: XSysmonPsuCfgReg1
 */
    #define XSYSMONPSU_CFG_REG1_OFFSET                       0x00000104U
    #define XSYSMONPSU_CFG_REG1_RSTVAL                       0x00000000U

    #define XSYSMONPSU_CFG_REG1_SEQ_MDE_SHIFT                12U
    #define XSYSMONPSU_CFG_REG1_SEQ_MDE_WIDTH                4U
    #define XSYSMONPSU_CFG_REG1_SEQ_MDE_MASK                 0x0000f000U

    #define XSYSMONPSU_CFG_REG1_ALRM_DIS6TO3_SHIFT           8U
    #define XSYSMONPSU_CFG_REG1_ALRM_DIS6TO3_WIDTH           4U
    #define XSYSMONPSU_CFG_REG1_ALRM_DIS6TO3_MASK            0x00000f00U

    #define XSYSMONPSU_CFG_REG1_ALRM_DIS2TO0_SHIFT           1U
    #define XSYSMONPSU_CFG_REG1_ALRM_DIS2TO0_WIDTH           3U
    #define XSYSMONPSU_CFG_REG1_ALRM_DIS2TO0_MASK            0x0000000eU

    #define XSYSMONPSU_CFG_REG1_OVR_TEMP_DIS_SHIFT           0U
    #define XSYSMONPSU_CFG_REG1_OVR_TEMP_DIS_WIDTH           1U
    #define XSYSMONPSU_CFG_REG1_OVR_TEMP_DIS_MASK            0x00000001U

    #define XSYSMONPSU_CFG_REG1_ALRM_ALL_MASK                0x00000f0fU
    #define XSYSMONPSU_CFR_REG1_ALRM_SUP6_MASK               0x0800U
    #define XSYSMONPSU_CFR_REG1_ALRM_SUP5_MASK               0x0400U
    #define XSYSMONPSU_CFR_REG1_ALRM_SUP4_MASK               0x0200U
    #define XSYSMONPSU_CFR_REG1_ALRM_SUP3_MASK               0x0100U
    #define XSYSMONPSU_CFR_REG1_ALRM_SUP2_MASK               0x0008U
    #define XSYSMONPSU_CFR_REG1_ALRM_SUP1_MASK               0x0004U
    #define XSYSMONPSU_CFR_REG1_ALRM_TEMP_MASK               0x0002U
    #define XSYSMONPSU_CFR_REG1_ALRM_OT_MASK                 0x0001U

/**
 * Register: XSysmonPsuCfgReg2
 */
    #define XSYSMONPSU_CFG_REG2_OFFSET                       0x00000108U
    #define XSYSMONPSU_CFG_REG2_RSTVAL                       0x00000000U

    #define XSYSMONPSU_CFG_REG2_CLK_DVDR_SHIFT               8U
    #define XSYSMONPSU_CFG_REG2_CLK_DVDR_WIDTH               8U
    #define XSYSMONPSU_CFG_REG2_CLK_DVDR_MASK                0x0000ff00U

    #define XSYSMONPSU_CLK_DVDR_MIN_VAL                      0U
    #define XSYSMONPSU_CLK_DVDR_MAX_VAL                      255U

    #define XSYSMONPSU_CFG_REG2_PWR_DOWN_SHIFT               4U
    #define XSYSMONPSU_CFG_REG2_PWR_DOWN_WIDTH               4U
    #define XSYSMONPSU_CFG_REG2_PWR_DOWN_MASK                0x000000f0U

    #define XSYSMONPSU_CFG_REG2_TST_CH_EN_SHIFT              2U
    #define XSYSMONPSU_CFG_REG2_TST_CH_EN_WIDTH              1U
    #define XSYSMONPSU_CFG_REG2_TST_CH_EN_MASK               0x00000004U

    #define XSYSMONPSU_CFG_REG2_TST_MDE_SHIFT                0U
    #define XSYSMONPSU_CFG_REG2_TST_MDE_WIDTH                2U
    #define XSYSMONPSU_CFG_REG2_TST_MDE_MASK                 0x00000003U

/* Register: XSysmonPsuCfgReg3 */
    #define XSYSMONPSU_CFG_REG3_OFFSET                       0x0000010CU
    #define XSYSMONPSU_CFG_REG3_ALRM_ALL_MASK                0x0000003FU

    #define XSM_CFG_ALARM_SHIFT                              16U

/* Register: XSysmonPsuSeqCh2 */
    #define XSYSMONPSU_SEQ_CH2_OFFSET                        0x00000118U

    #define XSYSMONPSU_SEQ_CH2_TEMP_RMT_SHIFT                5U
    #define XSYSMONPSU_SEQ_CH2_TEMP_RMT_MASK                 0x00000020U

    #define XSYSMONPSU_SEQ_CH2_VCCAMS_SHIFT                  4U
    #define XSYSMONPSU_SEQ_CH2_VCCAMS_MASK                   0x00000010U

    #define XSYSMONPSU_SEQ_CH2_SUP10_SHIFT                   3U
    #define XSYSMONPSU_SEQ_CH2_SUP10_MASK                    0x00000008U

    #define XSYSMONPSU_SEQ_CH2_SUP9_SHIFT                    2U
    #define XSYSMONPSU_SEQ_CH2_SUP9_MASK                     0x00000004U

    #define XSYSMONPSU_SEQ_CH2_SUP8_SHIFT                    1U
    #define XSYSMONPSU_SEQ_CH2_SUP8_MASK                     0x00000002U

    #define XSYSMONPSU_SEQ_CH2_SUP7_SHIFT                    0U
    #define XSYSMONPSU_SEQ_CH2_SUP7_MASK                     0x00000001U

    #define XSYSMONPSU_SEQ_CH2_VALID_MASK                    0x0000003FU

/* Register: XSysmonPsuSeqAverage0 */
    #define XSYSMONPSU_SEQ_AVERAGE2_OFFSET                   0x0000011CU
    #define XSYSMONPSU_SEQ_AVERAGE1_RSTVAL                   0x00000000U
    #define XSYSMONPSU_SEQ_AVERAGE2_MASK                     0x0000003FU

/**
 * Register: XSysmonPsuSeqCh0
 */
    #define XSYSMONPSU_SEQ_CH0_OFFSET                        0x00000120U
    #define XSYSMONPSU_SEQ_CH0_RSTVAL                        0x00000000U

    #define XSYSMONPSU_SEQ_CH0_CUR_MON_SHIFT                 15U
    #define XSYSMONPSU_SEQ_CH0_CUR_MON_WIDTH                 1U
    #define XSYSMONPSU_SEQ_CH0_CUR_MON_MASK                  0x00008000U

    #define XSYSMONPSU_SEQ_CH0_SUP3_SHIFT                    14U
    #define XSYSMONPSU_SEQ_CH0_SUP3_WIDTH                    1U
    #define XSYSMONPSU_SEQ_CH0_SUP3_MASK                     0x00004000U

    #define XSYSMONPSU_SEQ_CH0_VREFN_SHIFT                   13U
    #define XSYSMONPSU_SEQ_CH0_VREFN_WIDTH                   1U
    #define XSYSMONPSU_SEQ_CH0_VREFN_MASK                    0x00002000U

    #define XSYSMONPSU_SEQ_CH0_VREFP_SHIFT                   12U
    #define XSYSMONPSU_SEQ_CH0_VREFP_WIDTH                   1U
    #define XSYSMONPSU_SEQ_CH0_VREFP_MASK                    0x00001000U

    #define XSYSMONPSU_SEQ_CH0_VP_VN_SHIFT                   11U
    #define XSYSMONPSU_SEQ_CH0_VP_VN_WIDTH                   1U
    #define XSYSMONPSU_SEQ_CH0_VP_VN_MASK                    0x00000800U

    #define XSYSMONPSU_SEQ_CH0_SUP2_SHIFT                    10U
    #define XSYSMONPSU_SEQ_CH0_SUP2_WIDTH                    1U
    #define XSYSMONPSU_SEQ_CH0_SUP2_MASK                     0x00000400U

    #define XSYSMONPSU_SEQ_CH0_SUP1_SHIFT                    9U
    #define XSYSMONPSU_SEQ_CH0_SUP1_WIDTH                    1U
    #define XSYSMONPSU_SEQ_CH0_SUP1_MASK                     0x00000200U

    #define XSYSMONPSU_SEQ_CH0_TEMP_SHIFT                    8U
    #define XSYSMONPSU_SEQ_CH0_TEMP_WIDTH                    1U
    #define XSYSMONPSU_SEQ_CH0_TEMP_MASK                     0x00000100U

    #define XSYSMONPSU_SEQ_CH0_SUP6_SHIFT                    7U
    #define XSYSMONPSU_SEQ_CH0_SUP6_WIDTH                    1U
    #define XSYSMONPSU_SEQ_CH0_SUP6_MASK                     0x00000080U

    #define XSYSMONPSU_SEQ_CH0_SUP5_SHIFT                    6U
    #define XSYSMONPSU_SEQ_CH0_SUP5_WIDTH                    1U
    #define XSYSMONPSU_SEQ_CH0_SUP5_MASK                     0x00000040U

    #define XSYSMONPSU_SEQ_CH0_SUP4_SHIFT                    5U
    #define XSYSMONPSU_SEQ_CH0_SUP4_WIDTH                    1U
    #define XSYSMONPSU_SEQ_CH0_SUP4_MASK                     0x00000020U

    #define XSYSMONPSU_SEQ_CH0_TST_CH_SHIFT                  3U
    #define XSYSMONPSU_SEQ_CH0_TST_CH_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH0_TST_CH_MASK                   0x00000008U

    #define XSYSMONPSU_SEQ_CH0_CALIBRTN_SHIFT                0U
    #define XSYSMONPSU_SEQ_CH0_CALIBRTN_WIDTH                1U
    #define XSYSMONPSU_SEQ_CH0_CALIBRTN_MASK                 0x00000001U

    #define XSYSMONPSU_SEQ_CH0_VALID_MASK                    0x0000FFE9U

/**
 * Register: XSysmonPsuSeqCh1
 */
    #define XSYSMONPSU_SEQ_CH1_OFFSET                        0x00000124U
    #define XSYSMONPSU_SEQ_CH1_VALID_MASK                    0x0000FFFFU
    #define XSYSMONPSU_SEQ_CH1_RSTVAL                        0x00000000U

    #define XSYSMONPSU_SEQ_CH1_VAUX0F_SHIFT                  15U
    #define XSYSMONPSU_SEQ_CH1_VAUX0F_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX0F_MASK                   0x00008000U

    #define XSYSMONPSU_SEQ_CH1_VAUX0E_SHIFT                  14U
    #define XSYSMONPSU_SEQ_CH1_VAUX0E_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX0E_MASK                   0x00004000U

    #define XSYSMONPSU_SEQ_CH1_VAUX0D_SHIFT                  13U
    #define XSYSMONPSU_SEQ_CH1_VAUX0D_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX0D_MASK                   0x00002000U

    #define XSYSMONPSU_SEQ_CH1_VAUX0C_SHIFT                  12U
    #define XSYSMONPSU_SEQ_CH1_VAUX0C_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX0C_MASK                   0x00001000U

    #define XSYSMONPSU_SEQ_CH1_VAUX0B_SHIFT                  11U
    #define XSYSMONPSU_SEQ_CH1_VAUX0B_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX0B_MASK                   0x00000800U

    #define XSYSMONPSU_SEQ_CH1_VAUX0A_SHIFT                  10U
    #define XSYSMONPSU_SEQ_CH1_VAUX0A_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX0A_MASK                   0x00000400U

    #define XSYSMONPSU_SEQ_CH1_VAUX09_SHIFT                  9U
    #define XSYSMONPSU_SEQ_CH1_VAUX09_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX09_MASK                   0x00000200U

    #define XSYSMONPSU_SEQ_CH1_VAUX08_SHIFT                  8U
    #define XSYSMONPSU_SEQ_CH1_VAUX08_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX08_MASK                   0x00000100U

    #define XSYSMONPSU_SEQ_CH1_VAUX07_SHIFT                  7U
    #define XSYSMONPSU_SEQ_CH1_VAUX07_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX07_MASK                   0x00000080U

    #define XSYSMONPSU_SEQ_CH1_VAUX06_SHIFT                  6U
    #define XSYSMONPSU_SEQ_CH1_VAUX06_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX06_MASK                   0x00000040U

    #define XSYSMONPSU_SEQ_CH1_VAUX05_SHIFT                  5U
    #define XSYSMONPSU_SEQ_CH1_VAUX05_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX05_MASK                   0x00000020U

    #define XSYSMONPSU_SEQ_CH1_VAUX04_SHIFT                  4U
    #define XSYSMONPSU_SEQ_CH1_VAUX04_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX04_MASK                   0x00000010U

    #define XSYSMONPSU_SEQ_CH1_VAUX03_SHIFT                  3U
    #define XSYSMONPSU_SEQ_CH1_VAUX03_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX03_MASK                   0x00000008U

    #define XSYSMONPSU_SEQ_CH1_VAUX02_SHIFT                  2U
    #define XSYSMONPSU_SEQ_CH1_VAUX02_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX02_MASK                   0x00000004U

    #define XSYSMONPSU_SEQ_CH1_VAUX01_SHIFT                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX01_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX01_MASK                   0x00000002U

    #define XSYSMONPSU_SEQ_CH1_VAUX00_SHIFT                  0U
    #define XSYSMONPSU_SEQ_CH1_VAUX00_WIDTH                  1U
    #define XSYSMONPSU_SEQ_CH1_VAUX00_MASK                   0x00000001U

    #define XSM_SEQ_CH_SHIFT                                 16U
    #define XSM_SEQ_CH2_SHIFT                                32U

/**
 * Register: XSysmonPsuSeqAverage0
 */
    #define XSYSMONPSU_SEQ_AVERAGE0_OFFSET                   0x00000128U
    #define XSYSMONPSU_SEQ_AVERAGE0_RSTVAL                   0x00000000U

    #define XSYSMONPSU_SEQ_AVERAGE0_SHIFT                    0U
    #define XSYSMONPSU_SEQ_AVERAGE0_WIDTH                    16U
    #define XSYSMONPSU_SEQ_AVERAGE0_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuSeqAverage1
 */
    #define XSYSMONPSU_SEQ_AVERAGE1_OFFSET                   0x0000012CU
    #define XSYSMONPSU_SEQ_AVERAGE1_RSTVAL                   0x00000000U

    #define XSYSMONPSU_SEQ_AVERAGE1_SHIFT                    0U
    #define XSYSMONPSU_SEQ_AVERAGE1_WIDTH                    16U
    #define XSYSMONPSU_SEQ_AVERAGE1_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuSeqInputMde0
 */
    #define XSYSMONPSU_SEQ_INPUT_MDE0_OFFSET                 0x00000130U
    #define XSYSMONPSU_SEQ_INPUT_MDE0_RSTVAL                 0x00000000U

    #define XSYSMONPSU_SEQ_INPUT_MDE0_SHIFT                  0U
    #define XSYSMONPSU_SEQ_INPUT_MDE0_WIDTH                  16U
    #define XSYSMONPSU_SEQ_INPUT_MDE0_MASK                   0x0000ffffU

/**
 * Register: XSysmonPsuSeqInputMde1
 */
    #define XSYSMONPSU_SEQ_INPUT_MDE1_OFFSET                 0x00000134U
    #define XSYSMONPSU_SEQ_INPUT_MDE1_RSTVAL                 0x00000000U

    #define XSYSMONPSU_SEQ_INPUT_MDE1_SHIFT                  0U
    #define XSYSMONPSU_SEQ_INPUT_MDE1_WIDTH                  16U
    #define XSYSMONPSU_SEQ_INPUT_MDE1_MASK                   0x0000ffffU

/**
 * Register: XSysmonPsuSeqAcq0
 */
    #define XSYSMONPSU_SEQ_ACQ0_OFFSET                       0x00000138U
    #define XSYSMONPSU_SEQ_ACQ0_RSTVAL                       0x00000000U

    #define XSYSMONPSU_SEQ_ACQ0_SHIFT                        0U
    #define XSYSMONPSU_SEQ_ACQ0_WIDTH                        16U
    #define XSYSMONPSU_SEQ_ACQ0_MASK                         0x0000ffffU

/**
 * Register: XSysmonPsuSeqAcq1
 */
    #define XSYSMONPSU_SEQ_ACQ1_OFFSET                       0x0000013CU
    #define XSYSMONPSU_SEQ_ACQ1_RSTVAL                       0x00000000U

    #define XSYSMONPSU_SEQ_ACQ1_SHIFT                        0U
    #define XSYSMONPSU_SEQ_ACQ1_WIDTH                        16U
    #define XSYSMONPSU_SEQ_ACQ1_MASK                         0x0000ffffU

/**
 * Register: XSysmonPsuAlrmTempUpr
 */
    #define XSYSMONPSU_ALRM_TEMP_UPR_OFFSET                  0x00000140U
    #define XSYSMONPSU_ALRM_TEMP_UPR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_TEMP_UPR_SHIFT                   0U
    #define XSYSMONPSU_ALRM_TEMP_UPR_WIDTH                   16U
    #define XSYSMONPSU_ALRM_TEMP_UPR_MASK                    0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup1Upr
 */
    #define XSYSMONPSU_ALRM_SUP1_UPR_OFFSET                  0x00000144U
    #define XSYSMONPSU_ALRM_SUP1_UPR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP1_UPR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP1_UPR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP1_UPR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup2Upr
 */
    #define XSYSMONPSU_ALRM_SUP2_UPR_OFFSET                  0x00000148U
    #define XSYSMONPSU_ALRM_SUP2_UPR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP2_UPR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP2_UPR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP2_UPR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmOtUpr
 */
    #define XSYSMONPSU_ALRM_OT_UPR_OFFSET                    0x0000014CU
    #define XSYSMONPSU_ALRM_OT_UPR_RSTVAL                    0x00000000U

    #define XSYSMONPSU_ALRM_OT_UPR_TEMP_SHIFT                0U
    #define XSYSMONPSU_ALRM_OT_UPR_TEMP_WIDTH                16U
    #define XSYSMONPSU_ALRM_OT_UPR_TEMP_MASK                 0x0000ffffU

/**
 * Register: XSysmonPsuAlrmTempLwr
 */
    #define XSYSMONPSU_ALRM_TEMP_LWR_OFFSET                  0x00000150U
    #define XSYSMONPSU_ALRM_TEMP_LWR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_TEMP_LWR_SHIFT                   1U
    #define XSYSMONPSU_ALRM_TEMP_LWR_WIDTH                   15U
    #define XSYSMONPSU_ALRM_TEMP_LWR_MASK                    0x0000fffeU

    #define XSYSMONPSU_ALRM_TEMP_LWR_TSHLD_MDE_SHIFT         0U
    #define XSYSMONPSU_ALRM_TEMP_LWR_TSHLD_MDE_WIDTH         1U
    #define XSYSMONPSU_ALRM_TEMP_LWR_TSHLD_MDE_MASK          0x00000001U

/**
 * Register: XSysmonPsuAlrmSup1Lwr
 */
    #define XSYSMONPSU_ALRM_SUP1_LWR_OFFSET                  0x00000154U
    #define XSYSMONPSU_ALRM_SUP1_LWR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP1_LWR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP1_LWR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP1_LWR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup2Lwr
 */
    #define XSYSMONPSU_ALRM_SUP2_LWR_OFFSET                  0x00000158U
    #define XSYSMONPSU_ALRM_SUP2_LWR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP2_LWR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP2_LWR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP2_LWR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmOtLwr
 */
    #define XSYSMONPSU_ALRM_OT_LWR_OFFSET                    0x0000015CU
    #define XSYSMONPSU_ALRM_OT_LWR_RSTVAL                    0x00000000U

    #define XSYSMONPSU_ALRM_OT_LWR_TEMP_SHIFT                1U
    #define XSYSMONPSU_ALRM_OT_LWR_TEMP_WIDTH                15U
    #define XSYSMONPSU_ALRM_OT_LWR_TEMP_MASK                 0x0000fffeU

    #define XSYSMONPSU_ALRM_OT_LWR_TSHLD_MDE_SHIFT           0U
    #define XSYSMONPSU_ALRM_OT_LWR_TSHLD_MDE_WIDTH           1U
    #define XSYSMONPSU_ALRM_OT_LWR_TSHLD_MDE_MASK            0x00000001U

/**
 * Register: XSysmonPsuAlrmSup3Upr
 */
    #define XSYSMONPSU_ALRM_SUP3_UPR_OFFSET                  0x00000160U
    #define XSYSMONPSU_ALRM_SUP3_UPR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP3_UPR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP3_UPR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP3_UPR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup4Upr
 */
    #define XSYSMONPSU_ALRM_SUP4_UPR_OFFSET                  0x00000164U
    #define XSYSMONPSU_ALRM_SUP4_UPR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP4_UPR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP4_UPR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP4_UPR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup5Upr
 */
    #define XSYSMONPSU_ALRM_SUP5_UPR_OFFSET                  0x00000168U
    #define XSYSMONPSU_ALRM_SUP5_UPR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP5_UPR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP5_UPR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP5_UPR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup6Upr
 */
    #define XSYSMONPSU_ALRM_SUP6_UPR_OFFSET                  0x0000016CU
    #define XSYSMONPSU_ALRM_SUP6_UPR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP6_UPR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP6_UPR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP6_UPR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup3Lwr
 */
    #define XSYSMONPSU_ALRM_SUP3_LWR_OFFSET                  0x00000170U
    #define XSYSMONPSU_ALRM_SUP3_LWR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP3_LWR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP3_LWR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP3_LWR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup4Lwr
 */
    #define XSYSMONPSU_ALRM_SUP4_LWR_OFFSET                  0x00000174U
    #define XSYSMONPSU_ALRM_SUP4_LWR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP4_LWR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP4_LWR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP4_LWR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup5Lwr
 */
    #define XSYSMONPSU_ALRM_SUP5_LWR_OFFSET                  0x00000178U
    #define XSYSMONPSU_ALRM_SUP5_LWR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP5_LWR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP5_LWR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP5_LWR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup6Lwr
 */
    #define XSYSMONPSU_ALRM_SUP6_LWR_OFFSET                  0x0000017CU
    #define XSYSMONPSU_ALRM_SUP6_LWR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP6_LWR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP6_LWR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP6_LWR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup7Upr
 */
    #define XSYSMONPSU_ALRM_SUP7_UPR_OFFSET                  0x00000180U
    #define XSYSMONPSU_ALRM_SUP7_UPR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP7_UPR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP7_UPR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP7_UPR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup8Upr
 */
    #define XSYSMONPSU_ALRM_SUP8_UPR_OFFSET                  0x00000184U
    #define XSYSMONPSU_ALRM_SUP8_UPR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP8_UPR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP8_UPR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP8_UPR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup9Upr
 */
    #define XSYSMONPSU_ALRM_SUP9_UPR_OFFSET                  0x00000188U
    #define XSYSMONPSU_ALRM_SUP9_UPR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP9_UPR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP9_UPR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP9_UPR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup10Upr
 */
    #define XSYSMONPSU_ALRM_SUP10_UPR_OFFSET                 0x0000018CU
    #define XSYSMONPSU_ALRM_SUP10_UPR_RSTVAL                 0x00000000U

    #define XSYSMONPSU_ALRM_SUP10_UPR_SUP_SHIFT              0U
    #define XSYSMONPSU_ALRM_SUP10_UPR_SUP_WIDTH              16U
    #define XSYSMONPSU_ALRM_SUP10_UPR_SUP_MASK               0x0000ffffU

/**
 * Register: XSysmonPsuAlrmVccamsUpr
 */
    #define XSYSMONPSU_ALRM_VCCAMS_UPR_OFFSET                0x00000190U
    #define XSYSMONPSU_ALRM_VCCAMS_UPR_RSTVAL                0x00000000U

    #define XSYSMONPSU_ALRM_VCCAMS_UPR_SUP_SHIFT             0U
    #define XSYSMONPSU_ALRM_VCCAMS_UPR_SUP_WIDTH             16U
    #define XSYSMONPSU_ALRM_VCCAMS_UPR_SUP_MASK              0x0000ffffU

/**
 * Register: XSysmonPsuAlrmTremoteUpr
 */
    #define XSYSMONPSU_ALRM_TREMOTE_UPR_OFFSET               0x00000194U
    #define XSYSMONPSU_ALRM_TREMOTE_UPR_RSTVAL               0x00000000U

    #define XSYSMONPSU_ALRM_TREMOTE_UPR_TEMP_SHIFT           0U
    #define XSYSMONPSU_ALRM_TREMOTE_UPR_TEMP_WIDTH           16U
    #define XSYSMONPSU_ALRM_TREMOTE_UPR_TEMP_MASK            0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup7Lwr
 */
    #define XSYSMONPSU_ALRM_SUP7_LWR_OFFSET                  0x000001A0U
    #define XSYSMONPSU_ALRM_SUP7_LWR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP7_LWR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP7_LWR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP7_LWR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup8Lwr
 */
    #define XSYSMONPSU_ALRM_SUP8_LWR_OFFSET                  0x000001A4U
    #define XSYSMONPSU_ALRM_SUP8_LWR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP8_LWR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP8_LWR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP8_LWR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup9Lwr
 */
    #define XSYSMONPSU_ALRM_SUP9_LWR_OFFSET                  0x000001A8U
    #define XSYSMONPSU_ALRM_SUP9_LWR_RSTVAL                  0x00000000U

    #define XSYSMONPSU_ALRM_SUP9_LWR_SUP_SHIFT               0U
    #define XSYSMONPSU_ALRM_SUP9_LWR_SUP_WIDTH               16U
    #define XSYSMONPSU_ALRM_SUP9_LWR_SUP_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuAlrmSup10Lwr
 */
    #define XSYSMONPSU_ALRM_SUP10_LWR_OFFSET                 0x000001ACU
    #define XSYSMONPSU_ALRM_SUP10_LWR_RSTVAL                 0x00000000U

    #define XSYSMONPSU_ALRM_SUP10_LWR_SUP_SHIFT              0U
    #define XSYSMONPSU_ALRM_SUP10_LWR_SUP_WIDTH              16U
    #define XSYSMONPSU_ALRM_SUP10_LWR_SUP_MASK               0x0000ffffU

/**
 * Register: XSysmonPsuAlrmVccamsLwr
 */
    #define XSYSMONPSU_ALRM_VCCAMS_LWR_OFFSET                0x000001B0U
    #define XSYSMONPSU_ALRM_VCCAMS_LWR_RSTVAL                0x00000000U

    #define XSYSMONPSU_ALRM_VCCAMS_LWR_SUP_SHIFT             0U
    #define XSYSMONPSU_ALRM_VCCAMS_LWR_SUP_WIDTH             16U
    #define XSYSMONPSU_ALRM_VCCAMS_LWR_SUP_MASK              0x0000ffffU

/**
 * Register: XSysmonPsuAlrmTremoteLwr
 */
    #define XSYSMONPSU_ALRM_TREMOTE_LWR_OFFSET               0x000001B4U
    #define XSYSMONPSU_ALRM_TREMOTE_LWR_RSTVAL               0x00000000U

    #define XSYSMONPSU_ALRM_TREMOTE_LWR_TEMP_SHIFT           1U
    #define XSYSMONPSU_ALRM_TREMOTE_LWR_TEMP_WIDTH           15U
    #define XSYSMONPSU_ALRM_TREMOTE_LWR_TEMP_MASK            0x0000fffeU

    #define XSYSMONPSU_ALRM_TREMOTE_LWR_TSHLD_MDE_SHIFT      0U
    #define XSYSMONPSU_ALRM_TREMOTE_LWR_TSHLD_MDE_WIDTH      1U
    #define XSYSMONPSU_ALRM_TREMOTE_LWR_TSHLD_MDE_MASK       0x00000001U

/* Register: XSysmonPsuSeqInputMde2 */
    #define XSYSMONPSU_SEQ_INPUT_MDE2_OFFSET                 0x000001E0U
    #define XSYSMONPSU_SEQ_INPUT_MDE2_RSTVAL                 0x00000000U

    #define XSYSMONPSU_SEQ_INPUT_MDE2_SHIFT                  0U
    #define XSYSMONPSU_SEQ_INPUT_MDE2_MASK                   0x0000003FU

/**
 * Register: XSysmonPsuSeqAcq2
 */
    #define XSYSMONPSU_SEQ_ACQ2_OFFSET                       0x000001E4U
    #define XSYSMONPSU_SEQ_ACQ2_RSTVAL                       0x00000000U

    #define XSYSMONPSU_SEQ_ACQ2_SHIFT                        0U
    #define XSYSMONPSU_SEQ_ACQ2_MASK                         0x0000003FU

/**
 * Register: XSysmonPsuSup7
 */
    #define XSYSMONPSU_SUP7_OFFSET                           0x00000200U
    #define XSYSMONPSU_SUP7_RSTVAL                           0x00000000U

    #define XSYSMONPSU_SUP7_SUP_VAL_SHIFT                    0U
    #define XSYSMONPSU_SUP7_SUP_VAL_WIDTH                    16U
    #define XSYSMONPSU_SUP7_SUP_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuSup8
 */
    #define XSYSMONPSU_SUP8_OFFSET                           0x00000204U
    #define XSYSMONPSU_SUP8_RSTVAL                           0x00000000U

    #define XSYSMONPSU_SUP8_SUP_VAL_SHIFT                    0U
    #define XSYSMONPSU_SUP8_SUP_VAL_WIDTH                    16U
    #define XSYSMONPSU_SUP8_SUP_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuSup9
 */
    #define XSYSMONPSU_SUP9_OFFSET                           0x00000208U
    #define XSYSMONPSU_SUP9_RSTVAL                           0x00000000U

    #define XSYSMONPSU_SUP9_SUP_VAL_SHIFT                    0U
    #define XSYSMONPSU_SUP9_SUP_VAL_WIDTH                    16U
    #define XSYSMONPSU_SUP9_SUP_VAL_MASK                     0x0000ffffU

/**
 * Register: XSysmonPsuSup10
 */
    #define XSYSMONPSU_SUP10_OFFSET                          0x0000020CU
    #define XSYSMONPSU_SUP10_RSTVAL                          0x00000000U

    #define XSYSMONPSU_SUP10_SUP_VAL_SHIFT                   0U
    #define XSYSMONPSU_SUP10_SUP_VAL_WIDTH                   16U
    #define XSYSMONPSU_SUP10_SUP_VAL_MASK                    0x0000ffffU

/**
 * Register: XSysmonPsuVccams
 */
    #define XSYSMONPSU_VCCAMS_OFFSET                         0x00000210U
    #define XSYSMONPSU_VCCAMS_RSTVAL                         0x00000000U

    #define XSYSMONPSU_VCCAMS_SUP_VAL_SHIFT                  0U
    #define XSYSMONPSU_VCCAMS_SUP_VAL_WIDTH                  16U
    #define XSYSMONPSU_VCCAMS_SUP_VAL_MASK                   0x0000ffffU

/**
 * Register: XSysmonPsuTempRemte
 */
    #define XSYSMONPSU_TEMP_REMTE_OFFSET                     0x00000214U
    #define XSYSMONPSU_TEMP_REMTE_RSTVAL                     0x00000000U

    #define XSYSMONPSU_TEMP_REMTE_SHIFT                      0U
    #define XSYSMONPSU_TEMP_REMTE_WIDTH                      16U
    #define XSYSMONPSU_TEMP_REMTE_MASK                       0x0000ffffU

/**
 * Register: XSysmonPsuMaxSup7
 */
    #define XSYSMONPSU_MAX_SUP7_OFFSET                       0x00000280U
    #define XSYSMONPSU_MAX_SUP7_RSTVAL                       0x00000000U

    #define XSYSMONPSU_MAX_SUP7_SUP_VAL_SHIFT                0U
    #define XSYSMONPSU_MAX_SUP7_SUP_VAL_WIDTH                16U
    #define XSYSMONPSU_MAX_SUP7_SUP_VAL_MASK                 0x0000ffffU

/**
 * Register: XSysmonPsuMaxSup8
 */
    #define XSYSMONPSU_MAX_SUP8_OFFSET                       0x00000284U
    #define XSYSMONPSU_MAX_SUP8_RSTVAL                       0x00000000U

    #define XSYSMONPSU_MAX_SUP8_SUP_VAL_SHIFT                0U
    #define XSYSMONPSU_MAX_SUP8_SUP_VAL_WIDTH                16U
    #define XSYSMONPSU_MAX_SUP8_SUP_VAL_MASK                 0x0000ffffU

/**
 * Register: XSysmonPsuMaxSup9
 */
    #define XSYSMONPSU_MAX_SUP9_OFFSET                       0x00000288U
    #define XSYSMONPSU_MAX_SUP9_RSTVAL                       0x00000000U

    #define XSYSMONPSU_MAX_SUP9_SUP_VAL_SHIFT                0U
    #define XSYSMONPSU_MAX_SUP9_SUP_VAL_WIDTH                16U
    #define XSYSMONPSU_MAX_SUP9_SUP_VAL_MASK                 0x0000ffffU

/**
 * Register: XSysmonPsuMaxSup10
 */
    #define XSYSMONPSU_MAX_SUP10_OFFSET                      0x0000028CU
    #define XSYSMONPSU_MAX_SUP10_RSTVAL                      0x00000000U

    #define XSYSMONPSU_MAX_SUP10_SUP_VAL_SHIFT               0U
    #define XSYSMONPSU_MAX_SUP10_SUP_VAL_WIDTH               16U
    #define XSYSMONPSU_MAX_SUP10_SUP_VAL_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuMaxVccams
 */
    #define XSYSMONPSU_MAX_VCCAMS_OFFSET                     0x00000290U
    #define XSYSMONPSU_MAX_VCCAMS_RSTVAL                     0x00000000U

    #define XSYSMONPSU_MAX_VCCAMS_SUP_VAL_SHIFT              0U
    #define XSYSMONPSU_MAX_VCCAMS_SUP_VAL_WIDTH              16U
    #define XSYSMONPSU_MAX_VCCAMS_SUP_VAL_MASK               0x0000ffffU

/**
 * Register: XSysmonPsuMaxTempRemte
 */
    #define XSYSMONPSU_MAX_TEMP_REMTE_OFFSET                 0x00000294U
    #define XSYSMONPSU_MAX_TEMP_REMTE_RSTVAL                 0x00000000U

    #define XSYSMONPSU_MAX_TEMP_REMTE_SHIFT                  0U
    #define XSYSMONPSU_MAX_TEMP_REMTE_WIDTH                  16U
    #define XSYSMONPSU_MAX_TEMP_REMTE_MASK                   0x0000ffffU

/**
 * Register: XSysmonPsuMinSup7
 */
    #define XSYSMONPSU_MIN_SUP7_OFFSET                       0x000002A0U
    #define XSYSMONPSU_MIN_SUP7_RSTVAL                       0x0000ffffU

    #define XSYSMONPSU_MIN_SUP7_SUP_VAL_SHIFT                0U
    #define XSYSMONPSU_MIN_SUP7_SUP_VAL_WIDTH                16U
    #define XSYSMONPSU_MIN_SUP7_SUP_VAL_MASK                 0x0000ffffU

/**
 * Register: XSysmonPsuMinSup8
 */
    #define XSYSMONPSU_MIN_SUP8_OFFSET                       0x000002A4U
    #define XSYSMONPSU_MIN_SUP8_RSTVAL                       0x0000ffffU

    #define XSYSMONPSU_MIN_SUP8_SUP_VAL_SHIFT                0U
    #define XSYSMONPSU_MIN_SUP8_SUP_VAL_WIDTH                16U
    #define XSYSMONPSU_MIN_SUP8_SUP_VAL_MASK                 0x0000ffffU

/**
 * Register: XSysmonPsuMinSup9
 */
    #define XSYSMONPSU_MIN_SUP9_OFFSET                       0x000002A8U
    #define XSYSMONPSU_MIN_SUP9_RSTVAL                       0x0000ffffU

    #define XSYSMONPSU_MIN_SUP9_SUP_VAL_SHIFT                0U
    #define XSYSMONPSU_MIN_SUP9_SUP_VAL_WIDTH                16U
    #define XSYSMONPSU_MIN_SUP9_SUP_VAL_MASK                 0x0000ffffU

/**
 * Register: XSysmonPsuMinSup10
 */
    #define XSYSMONPSU_MIN_SUP10_OFFSET                      0x000002ACU
    #define XSYSMONPSU_MIN_SUP10_RSTVAL                      0x0000ffffU

    #define XSYSMONPSU_MIN_SUP10_SUP_VAL_SHIFT               0U
    #define XSYSMONPSU_MIN_SUP10_SUP_VAL_WIDTH               16U
    #define XSYSMONPSU_MIN_SUP10_SUP_VAL_MASK                0x0000ffffU

/**
 * Register: XSysmonPsuMinVccams
 */
    #define XSYSMONPSU_MIN_VCCAMS_OFFSET                     0x000002B0U
    #define XSYSMONPSU_MIN_VCCAMS_RSTVAL                     0x0000ffffU

    #define XSYSMONPSU_MIN_VCCAMS_SUP_VAL_SHIFT              0U
    #define XSYSMONPSU_MIN_VCCAMS_SUP_VAL_WIDTH              16U
    #define XSYSMONPSU_MIN_VCCAMS_SUP_VAL_MASK               0x0000ffffU

/**
 * Register: XSysmonPsuMinTempRemte
 */
    #define XSYSMONPSU_MIN_TEMP_REMTE_OFFSET                 0x000002B4U
    #define XSYSMONPSU_MIN_TEMP_REMTE_RSTVAL                 0x0000ffffU

    #define XSYSMONPSU_MIN_TEMP_REMTE_SHIFT                  0U
    #define XSYSMONPSU_MIN_TEMP_REMTE_WIDTH                  16U
    #define XSYSMONPSU_MIN_TEMP_REMTE_MASK                   0x0000ffffU

    #define CSU_BASEADDR                                     0xFFCA0000U
    #define PCAP_STATUS_OFFSET                               0x00003010U
    #define PL_CFG_RESET_MASK                                0x00000040U
    #define PL_CFG_RESET_SHIFT                               6U

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/

/**
 *
 * This macro reads the given register.
 *
 * @param	RegisterAddr is the register address in the address
 *          space of the SYSMONPSU device.
 *
 * @return	The 32-bit value of the register
 *
 * @note		None.
 *
 *****************************************************************************/
    #define XSysmonPsu_ReadReg( RegisterAddr )    Xil_In32( RegisterAddr )

/****************************************************************************/

/**
 *
 * This macro writes the given register.
 *
 * @param	RegisterAddr is the register address in the address
 *          space of the SYSMONPSU device.
 * @param	Data is the 32-bit value to write to the register.
 *
 * @return	None.
 *
 * @note		None.
 *
 *****************************************************************************/
    #define XSysmonPsu_WriteReg( RegisterAddr, Data )    Xil_Out32( RegisterAddr, ( u32 ) ( Data ) )

    #ifdef __cplusplus
}
    #endif

#endif /* XSYSMONPSU_HW_H__ */
