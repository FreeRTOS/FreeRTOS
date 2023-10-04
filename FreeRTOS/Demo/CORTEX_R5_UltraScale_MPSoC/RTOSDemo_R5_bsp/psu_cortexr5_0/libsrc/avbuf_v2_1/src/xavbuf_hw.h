/*******************************************************************************
*
* Copyright C 2014 Xilinx, Inc.  All rights reserved.
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
*******************************************************************************/
/******************************************************************************/

/**
 *
 * @file xavbuf_hw.h
 *
 * This header file contains macros that can be used to access the device
 *
 * @note	None.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- -----------------------------------------------
 * 1.0	 aad 02/24/17	Initial Release
 * 1.0   mh  06/24/17	Added Clock related register information
 * 2.0   aad 10/07/17   Removed Macros related to Video and Audio Src
 * </pre>
 *
 *******************************************************************************/
#ifndef XAVBUF_HW_H_
/* Prevent circular inclusions by using protection macros. */
    #define XAVBUF_HW_H_

    #ifdef __cplusplus
    extern "C" {
    #endif
/***************************** Include Files **********************************/

    #include "xil_io.h"
    #include "xil_types.h"

/************************** Constant Definitions ******************************/

/******************************************************************************/

/**
 * Address mapping for the DisplayPort TX core.
 *
 *******************************************************************************/

    #define XAVBUF_BASEADDR                                                        0xFD4A0000

/**
 *  * Register: XAVBUF_V_BLEND_BG_CLR_0
 *   */
    #define XAVBUF_V_BLEND_BG_CLR_0                                                0X0000A000

    #define XAVBUF_V_BLEND_BG_CLR_0_CLR0_SHIFT                                     0
    #define XAVBUF_V_BLEND_BG_CLR_0_CLR0_WIDTH                                     12
    #define XAVBUF_V_BLEND_BG_CLR_0_CLR0_MASK                                      0X00000FFF

/**
 *  * Register: XAVBUF_V_BLEND_BG_CLR_1
 *   */
    #define XAVBUF_V_BLEND_BG_CLR_1                                                0X0000A004

    #define XAVBUF_V_BLEND_BG_CLR_1_CLR1_SHIFT                                     0
    #define XAVBUF_V_BLEND_BG_CLR_1_CLR1_WIDTH                                     12
    #define XAVBUF_V_BLEND_BG_CLR_1_CLR1_MASK                                      0X00000FFF

/**
 *  * Register: XAVBUF_V_BLEND_BG_CLR_2
 *   */
    #define XAVBUF_V_BLEND_BG_CLR_2                                                0X0000A008

    #define XAVBUF_V_BLEND_BG_CLR_2_CLR2_SHIFT                                     0
    #define XAVBUF_V_BLEND_BG_CLR_2_CLR2_WIDTH                                     12
    #define XAVBUF_V_BLEND_BG_CLR_2_CLR2_MASK                                      0X00000FFF

/**
 *  * Register: XAVBUF_V_BLEND_SET_GLOBAL_ALPHA_REG
 *   */
    #define XAVBUF_V_BLEND_SET_GLOBAL_ALPHA_REG                                    0X0000A00C

    #define XAVBUF_V_BLEND_SET_GLOBAL_ALPHA_REG_VALUE_SHIFT                        1
    #define XAVBUF_V_BLEND_SET_GLOBAL_ALPHA_REG_VALUE_WIDTH                        8
    #define XAVBUF_V_BLEND_SET_GLOBAL_ALPHA_REG_VALUE_MASK                         0X000001FE

    #define XAVBUF_V_BLEND_SET_GLOBAL_ALPHA_REG_EN_SHIFT                           0
    #define XAVBUF_V_BLEND_SET_GLOBAL_ALPHA_REG_EN_WIDTH                           1
    #define XAVBUF_V_BLEND_SET_GLOBAL_ALPHA_REG_EN_MASK                            0X00000001

/**
 *  * Register: XAVBUF_V_BLEND_OUTPUT_VID_FORMAT
 *   */
    #define XAVBUF_V_BLEND_OUTPUT_VID_FORMAT                                       0X0000A014

    #define XAVBUF_V_BLEND_OUTPUT_VID_FORMAT_EN_DOWNSAMPLE_SHIFT                   4
    #define XAVBUF_V_BLEND_OUTPUT_VID_FORMAT_EN_DOWNSAMPLE_WIDTH                   1
    #define XAVBUF_V_BLEND_OUTPUT_VID_FORMAT_EN_DOWNSAMPLE_MASK                    0X00000010

    #define XAVBUF_V_BLEND_OUTPUT_VID_FORMAT_VID_FORMAT_SHIFT                      0
    #define XAVBUF_V_BLEND_OUTPUT_VID_FORMAT_VID_FORMAT_WIDTH                      3
    #define XAVBUF_V_BLEND_OUTPUT_VID_FORMAT_VID_FORMAT_MASK                       0X00000007

/**
 *  * Register: XAVBUF_V_BLEND_LAYER0_CONTROL
 *   */
    #define XAVBUF_V_BLEND_LAYER0_CONTROL                                          0X0000A018

    #define XAVBUF_V_BLEND_LAYER0_CONTROL_BYPASS_SHIFT                             8
    #define XAVBUF_V_BLEND_LAYER0_CONTROL_BYPASS_WIDTH                             1
    #define XAVBUF_V_BLEND_LAYER0_CONTROL_BYPASS_MASK                              0X00000100

    #define XAVBUF_V_BLEND_LAYER0_CONTROL_RGB_MODE_SHIFT                           1
    #define XAVBUF_V_BLEND_LAYER0_CONTROL_RGB_MODE_WIDTH                           1
    #define XAVBUF_V_BLEND_LAYER0_CONTROL_RGB_MODE_MASK                            0X00000002

    #define XAVBUF_V_BLEND_LAYER0_CONTROL_EN_US_SHIFT                              0
    #define XAVBUF_V_BLEND_LAYER0_CONTROL_EN_US_WIDTH                              1
    #define XAVBUF_V_BLEND_LAYER0_CONTROL_EN_US_MASK                               0X00000001

/**
 *  * Register: XAVBUF_V_BLEND_LAYER1_CONTROL
 *   */
    #define XAVBUF_V_BLEND_LAYER1_CONTROL                                          0X0000A01C

    #define XAVBUF_V_BLEND_LAYER1_CONTROL_BYPASS_SHIFT                             8
    #define XAVBUF_V_BLEND_LAYER1_CONTROL_BYPASS_WIDTH                             1
    #define XAVBUF_V_BLEND_LAYER1_CONTROL_BYPASS_MASK                              0X00000100

    #define XAVBUF_V_BLEND_LAYER1_CONTROL_RGB_MODE_SHIFT                           1
    #define XAVBUF_V_BLEND_LAYER1_CONTROL_RGB_MODE_WIDTH                           1
    #define XAVBUF_V_BLEND_LAYER1_CONTROL_RGB_MODE_MASK                            0X00000002

    #define XAVBUF_V_BLEND_LAYER1_CONTROL_EN_US_SHIFT                              0
    #define XAVBUF_V_BLEND_LAYER1_CONTROL_EN_US_WIDTH                              1
    #define XAVBUF_V_BLEND_LAYER1_CONTROL_EN_US_MASK                               0X00000001

/**
 *  * Register: XAVBUF_V_BLEND_RGB2YCBCR_COEFF0
 *   */
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF0                                        0X0000A020

    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF0_RGB2Y_C0_SHIFT                         0
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF0_RGB2Y_C0_WIDTH                         15
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF0_RGB2Y_C0_MASK                          0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_RGB2YCBCR_COEFF1
 *   */
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF1                                        0X0000A024

    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF1_RGB2Y_C1_SHIFT                         0
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF1_RGB2Y_C1_WIDTH                         15
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF1_RGB2Y_C1_MASK                          0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_RGB2YCBCR_COEFF2
 *   */
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF2                                        0X0000A028

    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF2_RGB2Y_C2_SHIFT                         0
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF2_RGB2Y_C2_WIDTH                         15
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF2_RGB2Y_C2_MASK                          0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_RGB2YCBCR_COEFF3
 *   */
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF3                                        0X0000A02C

    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF3_RGB2Y_C3_SHIFT                         0
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF3_RGB2Y_C3_WIDTH                         15
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF3_RGB2Y_C3_MASK                          0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_RGB2YCBCR_COEFF4
 *   */
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF4                                        0X0000A030

    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF4_RGB2Y_C4_SHIFT                         0
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF4_RGB2Y_C4_WIDTH                         15
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF4_RGB2Y_C4_MASK                          0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_RGB2YCBCR_COEFF5
 *   */
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF5                                        0X0000A034

    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF5_RGB2Y_C5_SHIFT                         0
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF5_RGB2Y_C5_WIDTH                         15
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF5_RGB2Y_C5_MASK                          0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_RGB2YCBCR_COEFF6
 *   */
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF6                                        0X0000A038

    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF6_RGB2Y_C6_SHIFT                         0
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF6_RGB2Y_C6_WIDTH                         15
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF6_RGB2Y_C6_MASK                          0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_RGB2YCBCR_COEFF7
 *   */
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF7                                        0X0000A03C

    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF7_RGB2Y_C7_SHIFT                         0
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF7_RGB2Y_C7_WIDTH                         15
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF7_RGB2Y_C7_MASK                          0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_RGB2YCBCR_COEFF8
 *   */
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF8                                        0X0000A040

    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF8_RGB2Y_C8_SHIFT                         0
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF8_RGB2Y_C8_WIDTH                         15
    #define XAVBUF_V_BLEND_RGB2YCBCR_COEFF8_RGB2Y_C8_MASK                          0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN1CSC_COEFF0
 *   */
    #define XAVBUF_V_BLEND_IN1CSC_COEFF0                                           0X0000A044

    #define XAVBUF_V_BLEND_IN1CSC_COEFF0_Y2R_C0_SHIFT                              0
    #define XAVBUF_V_BLEND_IN1CSC_COEFF0_Y2R_C0_WIDTH                              15
    #define XAVBUF_V_BLEND_IN1CSC_COEFF0_Y2R_C0_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN1CSC_COEFF1
 *   */
    #define XAVBUF_V_BLEND_IN1CSC_COEFF1                                           0X0000A048

    #define XAVBUF_V_BLEND_IN1CSC_COEFF1_Y2R_C1_SHIFT                              0
    #define XAVBUF_V_BLEND_IN1CSC_COEFF1_Y2R_C1_WIDTH                              15
    #define XAVBUF_V_BLEND_IN1CSC_COEFF1_Y2R_C1_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN1CSC_COEFF2
 *   */
    #define XAVBUF_V_BLEND_IN1CSC_COEFF2                                           0X0000A04C

    #define XAVBUF_V_BLEND_IN1CSC_COEFF2_Y2R_C2_SHIFT                              0
    #define XAVBUF_V_BLEND_IN1CSC_COEFF2_Y2R_C2_WIDTH                              15
    #define XAVBUF_V_BLEND_IN1CSC_COEFF2_Y2R_C2_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN1CSC_COEFF3
 *   */
    #define XAVBUF_V_BLEND_IN1CSC_COEFF3                                           0X0000A050

    #define XAVBUF_V_BLEND_IN1CSC_COEFF3_Y2R_C3_SHIFT                              0
    #define XAVBUF_V_BLEND_IN1CSC_COEFF3_Y2R_C3_WIDTH                              15
    #define XAVBUF_V_BLEND_IN1CSC_COEFF3_Y2R_C3_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN1CSC_COEFF4
 *   */
    #define XAVBUF_V_BLEND_IN1CSC_COEFF4                                           0X0000A054

    #define XAVBUF_V_BLEND_IN1CSC_COEFF4_Y2R_C4_SHIFT                              0
    #define XAVBUF_V_BLEND_IN1CSC_COEFF4_Y2R_C4_WIDTH                              15
    #define XAVBUF_V_BLEND_IN1CSC_COEFF4_Y2R_C4_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN1CSC_COEFF5
 *   */
    #define XAVBUF_V_BLEND_IN1CSC_COEFF5                                           0X0000A058

    #define XAVBUF_V_BLEND_IN1CSC_COEFF5_Y2R_C5_SHIFT                              0
    #define XAVBUF_V_BLEND_IN1CSC_COEFF5_Y2R_C5_WIDTH                              15
    #define XAVBUF_V_BLEND_IN1CSC_COEFF5_Y2R_C5_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN1CSC_COEFF6
 *   */
    #define XAVBUF_V_BLEND_IN1CSC_COEFF6                                           0X0000A05C

    #define XAVBUF_V_BLEND_IN1CSC_COEFF6_Y2R_C6_SHIFT                              0
    #define XAVBUF_V_BLEND_IN1CSC_COEFF6_Y2R_C6_WIDTH                              15
    #define XAVBUF_V_BLEND_IN1CSC_COEFF6_Y2R_C6_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN1CSC_COEFF7
 *   */
    #define XAVBUF_V_BLEND_IN1CSC_COEFF7                                           0X0000A060

    #define XAVBUF_V_BLEND_IN1CSC_COEFF7_Y2R_C7_SHIFT                              0
    #define XAVBUF_V_BLEND_IN1CSC_COEFF7_Y2R_C7_WIDTH                              15
    #define XAVBUF_V_BLEND_IN1CSC_COEFF7_Y2R_C7_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN1CSC_COEFF8
 *   */
    #define XAVBUF_V_BLEND_IN1CSC_COEFF8                                           0X0000A064

    #define XAVBUF_V_BLEND_IN1CSC_COEFF8_Y2R_C8_SHIFT                              0
    #define XAVBUF_V_BLEND_IN1CSC_COEFF8_Y2R_C8_WIDTH                              15
    #define XAVBUF_V_BLEND_IN1CSC_COEFF8_Y2R_C8_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_LUMA_IN1CSC_OFFSET
 *   */
    #define XAVBUF_V_BLEND_LUMA_IN1CSC_OFFSET                                      0X0000A068

    #define XAVBUF_V_BLEND_LUMA_IN1CSC_OFFSET_POST_OFFSET_SHIFT                    16
    #define XAVBUF_V_BLEND_LUMA_IN1CSC_OFFSET_POST_OFFSET_WIDTH                    13
    #define XAVBUF_V_BLEND_LUMA_IN1CSC_OFFSET_POST_OFFSET_MASK                     0X1FFF0000

    #define XAVBUF_V_BLEND_LUMA_IN1CSC_OFFSET_PRE_OFFSET_SHIFT                     0
    #define XAVBUF_V_BLEND_LUMA_IN1CSC_OFFSET_PRE_OFFSET_WIDTH                     13
    #define XAVBUF_V_BLEND_LUMA_IN1CSC_OFFSET_PRE_OFFSET_MASK                      0X00001FFF

/**
 *  * Register: XAVBUF_V_BLEND_CR_IN1CSC_OFFSET
 *   */
    #define XAVBUF_V_BLEND_CR_IN1CSC_OFFSET                                        0X0000A06C

    #define XAVBUF_V_BLEND_CR_IN1CSC_OFFSET_POST_OFFSET_SHIFT                      16
    #define XAVBUF_V_BLEND_CR_IN1CSC_OFFSET_POST_OFFSET_WIDTH                      13
    #define XAVBUF_V_BLEND_CR_IN1CSC_OFFSET_POST_OFFSET_MASK                       0X1FFF0000

    #define XAVBUF_V_BLEND_CR_IN1CSC_OFFSET_PRE_OFFSET_SHIFT                       0
    #define XAVBUF_V_BLEND_CR_IN1CSC_OFFSET_PRE_OFFSET_WIDTH                       13
    #define XAVBUF_V_BLEND_CR_IN1CSC_OFFSET_PRE_OFFSET_MASK                        0X00001FFF

/**
 *  * Register: XAVBUF_V_BLEND_CB_IN1CSC_OFFSET
 *   */
    #define XAVBUF_V_BLEND_CB_IN1CSC_OFFSET                                        0X0000A070

    #define XAVBUF_V_BLEND_CB_IN1CSC_OFFSET_POST_OFFSET_SHIFT                      16
    #define XAVBUF_V_BLEND_CB_IN1CSC_OFFSET_POST_OFFSET_WIDTH                      13
    #define XAVBUF_V_BLEND_CB_IN1CSC_OFFSET_POST_OFFSET_MASK                       0X1FFF0000

    #define XAVBUF_V_BLEND_CB_IN1CSC_OFFSET_PRE_OFFSET_SHIFT                       0
    #define XAVBUF_V_BLEND_CB_IN1CSC_OFFSET_PRE_OFFSET_WIDTH                       13
    #define XAVBUF_V_BLEND_CB_IN1CSC_OFFSET_PRE_OFFSET_MASK                        0X00001FFF

/**
 *  * Register: XAVBUF_V_BLEND_LUMA_OUTCSC_OFFSET
 *   */
    #define XAVBUF_V_BLEND_LUMA_OUTCSC_OFFSET                                      0X0000A074

    #define XAVBUF_V_BLEND_LUMA_OUTCSC_OFFSET_POST_OFFSET_SHIFT                    16
    #define XAVBUF_V_BLEND_LUMA_OUTCSC_OFFSET_POST_OFFSET_WIDTH                    13
    #define XAVBUF_V_BLEND_LUMA_OUTCSC_OFFSET_POST_OFFSET_MASK                     0X1FFF0000

    #define XAVBUF_V_BLEND_LUMA_OUTCSC_OFFSET_PRE_OFFSET_SHIFT                     0
    #define XAVBUF_V_BLEND_LUMA_OUTCSC_OFFSET_PRE_OFFSET_WIDTH                     13
    #define XAVBUF_V_BLEND_LUMA_OUTCSC_OFFSET_PRE_OFFSET_MASK                      0X00001FFF

/**
 *  * Register: XAVBUF_V_BLEND_CR_OUTCSC_OFFSET
 *   */
    #define XAVBUF_V_BLEND_CR_OUTCSC_OFFSET                                        0X0000A078

    #define XAVBUF_V_BLEND_CR_OUTCSC_OFFSET_POST_OFFSET_SHIFT                      16
    #define XAVBUF_V_BLEND_CR_OUTCSC_OFFSET_POST_OFFSET_WIDTH                      13
    #define XAVBUF_V_BLEND_CR_OUTCSC_OFFSET_POST_OFFSET_MASK                       0X1FFF0000

    #define XAVBUF_V_BLEND_CR_OUTCSC_OFFSET_PRE_OFFSET_SHIFT                       0
    #define XAVBUF_V_BLEND_CR_OUTCSC_OFFSET_PRE_OFFSET_WIDTH                       13
    #define XAVBUF_V_BLEND_CR_OUTCSC_OFFSET_PRE_OFFSET_MASK                        0X00001FFF

/**
 *  * Register: XAVBUF_V_BLEND_CB_OUTCSC_OFFSET
 *   */
    #define XAVBUF_V_BLEND_CB_OUTCSC_OFFSET                                        0X0000A07C

    #define XAVBUF_V_BLEND_CB_OUTCSC_OFFSET_POST_OFFSET_SHIFT                      16
    #define XAVBUF_V_BLEND_CB_OUTCSC_OFFSET_POST_OFFSET_WIDTH                      13
    #define XAVBUF_V_BLEND_CB_OUTCSC_OFFSET_POST_OFFSET_MASK                       0X1FFF0000

    #define XAVBUF_V_BLEND_CB_OUTCSC_OFFSET_PRE_OFFSET_SHIFT                       0
    #define XAVBUF_V_BLEND_CB_OUTCSC_OFFSET_PRE_OFFSET_WIDTH                       13
    #define XAVBUF_V_BLEND_CB_OUTCSC_OFFSET_PRE_OFFSET_MASK                        0X00001FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN2CSC_COEFF0
 *   */
    #define XAVBUF_V_BLEND_IN2CSC_COEFF0                                           0X0000A080

    #define XAVBUF_V_BLEND_IN2CSC_COEFF0_Y2R_C0_SHIFT                              0
    #define XAVBUF_V_BLEND_IN2CSC_COEFF0_Y2R_C0_WIDTH                              15
    #define XAVBUF_V_BLEND_IN2CSC_COEFF0_Y2R_C0_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN2CSC_COEFF1
 *   */
    #define XAVBUF_V_BLEND_IN2CSC_COEFF1                                           0X0000A084

    #define XAVBUF_V_BLEND_IN2CSC_COEFF1_Y2R_C1_SHIFT                              0
    #define XAVBUF_V_BLEND_IN2CSC_COEFF1_Y2R_C1_WIDTH                              15
    #define XAVBUF_V_BLEND_IN2CSC_COEFF1_Y2R_C1_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN2CSC_COEFF2
 *   */
    #define XAVBUF_V_BLEND_IN2CSC_COEFF2                                           0X0000A088

    #define XAVBUF_V_BLEND_IN2CSC_COEFF2_Y2R_C2_SHIFT                              0
    #define XAVBUF_V_BLEND_IN2CSC_COEFF2_Y2R_C2_WIDTH                              15
    #define XAVBUF_V_BLEND_IN2CSC_COEFF2_Y2R_C2_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN2CSC_COEFF3
 *   */
    #define XAVBUF_V_BLEND_IN2CSC_COEFF3                                           0X0000A08C

    #define XAVBUF_V_BLEND_IN2CSC_COEFF3_Y2R_C3_SHIFT                              0
    #define XAVBUF_V_BLEND_IN2CSC_COEFF3_Y2R_C3_WIDTH                              15
    #define XAVBUF_V_BLEND_IN2CSC_COEFF3_Y2R_C3_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN2CSC_COEFF4
 *   */
    #define XAVBUF_V_BLEND_IN2CSC_COEFF4                                           0X0000A090

    #define XAVBUF_V_BLEND_IN2CSC_COEFF4_Y2R_C4_SHIFT                              0
    #define XAVBUF_V_BLEND_IN2CSC_COEFF4_Y2R_C4_WIDTH                              15
    #define XAVBUF_V_BLEND_IN2CSC_COEFF4_Y2R_C4_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN2CSC_COEFF5
 *   */
    #define XAVBUF_V_BLEND_IN2CSC_COEFF5                                           0X0000A094

    #define XAVBUF_V_BLEND_IN2CSC_COEFF5_Y2R_C5_SHIFT                              0
    #define XAVBUF_V_BLEND_IN2CSC_COEFF5_Y2R_C5_WIDTH                              15
    #define XAVBUF_V_BLEND_IN2CSC_COEFF5_Y2R_C5_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN2CSC_COEFF6
 *   */
    #define XAVBUF_V_BLEND_IN2CSC_COEFF6                                           0X0000A098

    #define XAVBUF_V_BLEND_IN2CSC_COEFF6_Y2R_C6_SHIFT                              0
    #define XAVBUF_V_BLEND_IN2CSC_COEFF6_Y2R_C6_WIDTH                              15
    #define XAVBUF_V_BLEND_IN2CSC_COEFF6_Y2R_C6_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN2CSC_COEFF7
 *   */
    #define XAVBUF_V_BLEND_IN2CSC_COEFF7                                           0X0000A09C

    #define XAVBUF_V_BLEND_IN2CSC_COEFF7_Y2R_C7_SHIFT                              0
    #define XAVBUF_V_BLEND_IN2CSC_COEFF7_Y2R_C7_WIDTH                              15
    #define XAVBUF_V_BLEND_IN2CSC_COEFF7_Y2R_C7_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_IN2CSC_COEFF8
 *   */
    #define XAVBUF_V_BLEND_IN2CSC_COEFF8                                           0X0000A0A0

    #define XAVBUF_V_BLEND_IN2CSC_COEFF8_Y2R_C8_SHIFT                              0
    #define XAVBUF_V_BLEND_IN2CSC_COEFF8_Y2R_C8_WIDTH                              15
    #define XAVBUF_V_BLEND_IN2CSC_COEFF8_Y2R_C8_MASK                               0X00007FFF

/**
 *  * Register: XAVBUF_V_BLEND_LUMA_IN2CSC_OFFSET
 *   */
    #define XAVBUF_V_BLEND_LUMA_IN2CSC_OFFSET                                      0X0000A0A4

    #define XAVBUF_V_BLEND_LUMA_IN2CSC_OFFSET_POST_OFFSET_SHIFT                    16
    #define XAVBUF_V_BLEND_LUMA_IN2CSC_OFFSET_POST_OFFSET_WIDTH                    13
    #define XAVBUF_V_BLEND_LUMA_IN2CSC_OFFSET_POST_OFFSET_MASK                     0X1FFF0000

    #define XAVBUF_V_BLEND_LUMA_IN2CSC_OFFSET_PRE_OFFSET_SHIFT                     0
    #define XAVBUF_V_BLEND_LUMA_IN2CSC_OFFSET_PRE_OFFSET_WIDTH                     13
    #define XAVBUF_V_BLEND_LUMA_IN2CSC_OFFSET_PRE_OFFSET_MASK                      0X00001FFF

/**
 *  * Register: XAVBUF_V_BLEND_CR_IN2CSC_OFFSET
 *   */
    #define XAVBUF_V_BLEND_CR_IN2CSC_OFFSET                                        0X0000A0A8

    #define XAVBUF_V_BLEND_CR_IN2CSC_OFFSET_POST_OFFSET_SHIFT                      16
    #define XAVBUF_V_BLEND_CR_IN2CSC_OFFSET_POST_OFFSET_WIDTH                      13
    #define XAVBUF_V_BLEND_CR_IN2CSC_OFFSET_POST_OFFSET_MASK                       0X1FFF0000

    #define XAVBUF_V_BLEND_CR_IN2CSC_OFFSET_PRE_OFFSET_SHIFT                       0
    #define XAVBUF_V_BLEND_CR_IN2CSC_OFFSET_PRE_OFFSET_WIDTH                       13
    #define XAVBUF_V_BLEND_CR_IN2CSC_OFFSET_PRE_OFFSET_MASK                        0X00001FFF

/**
 *  * Register: XAVBUF_V_BLEND_CB_IN2CSC_OFFSET
 *   */
    #define XAVBUF_V_BLEND_CB_IN2CSC_OFFSET                                        0X0000A0AC

    #define XAVBUF_V_BLEND_CB_IN2CSC_OFFSET_POST_OFFSET_SHIFT                      16
    #define XAVBUF_V_BLEND_CB_IN2CSC_OFFSET_POST_OFFSET_WIDTH                      13
    #define XAVBUF_V_BLEND_CB_IN2CSC_OFFSET_POST_OFFSET_MASK                       0X1FFF0000

    #define XAVBUF_V_BLEND_CB_IN2CSC_OFFSET_PRE_OFFSET_SHIFT                       0
    #define XAVBUF_V_BLEND_CB_IN2CSC_OFFSET_PRE_OFFSET_WIDTH                       13
    #define XAVBUF_V_BLEND_CB_IN2CSC_OFFSET_PRE_OFFSET_MASK                        0X00001FFF

/**
 *  * Register: XAVBUF_V_BLEND_CHROMA_KEY_ENABLE
 *   */
    #define XAVBUF_V_BLEND_CHROMA_KEY_ENABLE                                       0X0000A1D0

    #define XAVBUF_V_BLEND_CHROMA_KEY_ENABLE_M_SEL_SHIFT                           1
    #define XAVBUF_V_BLEND_CHROMA_KEY_ENABLE_M_SEL_WIDTH                           1
    #define XAVBUF_V_BLEND_CHROMA_KEY_ENABLE_M_SEL_MASK                            0X00000002

    #define XAVBUF_V_BLEND_CHROMA_KEY_ENABLE_EN_SHIFT                              0
    #define XAVBUF_V_BLEND_CHROMA_KEY_ENABLE_EN_WIDTH                              1
    #define XAVBUF_V_BLEND_CHROMA_KEY_ENABLE_EN_MASK                               0X00000001

/**
 *  * Register: XAVBUF_V_BLEND_CHROMA_KEY_COMP1
 *   */
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP1                                        0X0000A1D4

    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP1_MAX_SHIFT                              16
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP1_MAX_WIDTH                              12
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP1_MAX_MASK                               0X0FFF0000

    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP1_MIN_SHIFT                              0
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP1_MIN_WIDTH                              12
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP1_MIN_MASK                               0X00000FFF

/**
 *  * Register: XAVBUF_V_BLEND_CHROMA_KEY_COMP2
 *   */
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP2                                        0X0000A1D8

    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP2_MAX_SHIFT                              16
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP2_MAX_WIDTH                              12
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP2_MAX_MASK                               0X0FFF0000

    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP2_MIN_SHIFT                              0
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP2_MIN_WIDTH                              12
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP2_MIN_MASK                               0X00000FFF

/**
 *  * Register: XAVBUF_V_BLEND_CHROMA_KEY_COMP3
 *   */
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP3                                        0X0000A1DC

    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP3_MAX_SHIFT                              16
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP3_MAX_WIDTH                              12
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP3_MAX_MASK                               0X0FFF0000

    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP3_MIN_SHIFT                              0
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP3_MIN_WIDTH                              12
    #define XAVBUF_V_BLEND_CHROMA_KEY_COMP3_MIN_MASK                               0X00000FFF

/**
 *  * Register: XAVBUF_BUF_FORMAT
 *   */
    #define XAVBUF_BUF_FORMAT                                                      0X0000B000

    #define XAVBUF_BUF_FORMAT_NL_GRAPHX_FORMAT_SHIFT                               8
    #define XAVBUF_BUF_FORMAT_NL_GRAPHX_FORMAT_WIDTH                               4
    #define XAVBUF_BUF_FORMAT_NL_GRAPHX_FORMAT_MASK                                0X00000F00

    #define XAVBUF_BUF_FORMAT_NL_VID_FORMAT_SHIFT                                  0
    #define XAVBUF_BUF_FORMAT_NL_VID_FORMAT_WIDTH                                  5
    #define XAVBUF_BUF_FORMAT_NL_VID_FORMAT_MASK                                   0X0000001F

/**
 *  * Register: XAVBUF_BUF_NON_LIVE_LATENCY
 *   */
    #define XAVBUF_BUF_NON_LIVE_LATENCY                                            0X0000B008

    #define XAVBUF_BUF_NON_LIVE_LATENCY_NL_LATENCY_SHIFT                           0
    #define XAVBUF_BUF_NON_LIVE_LATENCY_NL_LATENCY_WIDTH                           10
    #define XAVBUF_BUF_NON_LIVE_LATENCY_NL_LATENCY_MASK                            0X000003FF

/**
 *  * Register: XAVBUF_CHBUF0
 *   */
    #define XAVBUF_CHBUF0                                                          0X0000B010

    #define XAVBUF_CHBUF0_BURST_LEN_SHIFT                                          2
    #define XAVBUF_CHBUF0_BURST_LEN_WIDTH                                          5
    #define XAVBUF_CHBUF0_BURST_LEN_MASK                                           0X0000007C

    #define XAVBUF_CHBUF0_FLUSH_SHIFT                                              1
    #define XAVBUF_CHBUF0_FLUSH_WIDTH                                              1
    #define XAVBUF_CHBUF0_FLUSH_MASK                                               0X00000002

    #define XAVBUF_CHBUF0_EN_SHIFT                                                 0
    #define XAVBUF_CHBUF0_EN_WIDTH                                                 1
    #define XAVBUF_CHBUF0_EN_MASK                                                  0X00000001

/**
 *  * Register: XAVBUF_CHBUF1
 *   */
    #define XAVBUF_CHBUF1                                                          0X0000B014

    #define XAVBUF_CHBUF1_BURST_LEN_SHIFT                                          2
    #define XAVBUF_CHBUF1_BURST_LEN_WIDTH                                          5
    #define XAVBUF_CHBUF1_BURST_LEN_MASK                                           0X0000007C

    #define XAVBUF_CHBUF1_FLUSH_SHIFT                                              1
    #define XAVBUF_CHBUF1_FLUSH_WIDTH                                              1
    #define XAVBUF_CHBUF1_FLUSH_MASK                                               0X00000002

    #define XAVBUF_CHBUF1_EN_SHIFT                                                 0
    #define XAVBUF_CHBUF1_EN_WIDTH                                                 1
    #define XAVBUF_CHBUF1_EN_MASK                                                  0X00000001

/**
 *  * Register: XAVBUF_CHBUF2
 *   */
    #define XAVBUF_CHBUF2                                                          0X0000B018

    #define XAVBUF_CHBUF2_BURST_LEN_SHIFT                                          2
    #define XAVBUF_CHBUF2_BURST_LEN_WIDTH                                          5
    #define XAVBUF_CHBUF2_BURST_LEN_MASK                                           0X0000007C

    #define XAVBUF_CHBUF2_FLUSH_SHIFT                                              1
    #define XAVBUF_CHBUF2_FLUSH_WIDTH                                              1
    #define XAVBUF_CHBUF2_FLUSH_MASK                                               0X00000002

    #define XAVBUF_CHBUF2_EN_SHIFT                                                 0
    #define XAVBUF_CHBUF2_EN_WIDTH                                                 1
    #define XAVBUF_CHBUF2_EN_MASK                                                  0X00000001

/**
 *  * Register: XAVBUF_CHBUF3
 *   */
    #define XAVBUF_CHBUF3                                                          0X0000B01C

    #define XAVBUF_CHBUF3_BURST_LEN_SHIFT                                          2
    #define XAVBUF_CHBUF3_BURST_LEN_WIDTH                                          5
    #define XAVBUF_CHBUF3_BURST_LEN_MASK                                           0X0000007C

    #define XAVBUF_CHBUF3_FLUSH_SHIFT                                              1
    #define XAVBUF_CHBUF3_FLUSH_WIDTH                                              1
    #define XAVBUF_CHBUF3_FLUSH_MASK                                               0X00000002

    #define XAVBUF_CHBUF3_EN_SHIFT                                                 0
    #define XAVBUF_CHBUF3_EN_WIDTH                                                 1
    #define XAVBUF_CHBUF3_EN_MASK                                                  0X00000001

/**
 *  * Register: XAVBUF_CHBUF4
 *   */
    #define XAVBUF_CHBUF4                                                          0X0000B020

    #define XAVBUF_CHBUF4_BURST_LEN_SHIFT                                          2
    #define XAVBUF_CHBUF4_BURST_LEN_WIDTH                                          5
    #define XAVBUF_CHBUF4_BURST_LEN_MASK                                           0X0000007C

    #define XAVBUF_CHBUF4_FLUSH_SHIFT                                              1
    #define XAVBUF_CHBUF4_FLUSH_WIDTH                                              1
    #define XAVBUF_CHBUF4_FLUSH_MASK                                               0X00000002

    #define XAVBUF_CHBUF4_EN_SHIFT                                                 0
    #define XAVBUF_CHBUF4_EN_WIDTH                                                 1
    #define XAVBUF_CHBUF4_EN_MASK                                                  0X00000001

/**
 *  * Register: XAVBUF_CHBUF5
 *   */
    #define XAVBUF_CHBUF5                                                          0X0000B024

    #define XAVBUF_CHBUF5_BURST_LEN_SHIFT                                          2
    #define XAVBUF_CHBUF5_BURST_LEN_WIDTH                                          5
    #define XAVBUF_CHBUF5_BURST_LEN_MASK                                           0X0000007C

    #define XAVBUF_CHBUF5_FLUSH_SHIFT                                              1
    #define XAVBUF_CHBUF5_FLUSH_WIDTH                                              1
    #define XAVBUF_CHBUF5_FLUSH_MASK                                               0X00000002

    #define XAVBUF_CHBUF5_EN_SHIFT                                                 0
    #define XAVBUF_CHBUF5_EN_WIDTH                                                 1
    #define XAVBUF_CHBUF5_EN_MASK                                                  0X00000001

/**
 *  * Register: XAVBUF_BUF_STC_CONTROL
 *   */
    #define XAVBUF_BUF_STC_CONTROL                                                 0X0000B02C

    #define XAVBUF_BUF_STC_CONTROL_EN_SHIFT                                        0
    #define XAVBUF_BUF_STC_CONTROL_EN_WIDTH                                        1
    #define XAVBUF_BUF_STC_CONTROL_EN_MASK                                         0X00000001

/**
 *  * Register: XAVBUF_BUF_STC_INIT_VALUE0
 *   */
    #define XAVBUF_BUF_STC_INIT_VALUE0                                             0X0000B030

    #define XAVBUF_BUF_STC_INIT_VALUE0_INIT_VALUE0_SHIFT                           0
    #define XAVBUF_BUF_STC_INIT_VALUE0_INIT_VALUE0_WIDTH                           32
    #define XAVBUF_BUF_STC_INIT_VALUE0_INIT_VALUE0_MASK                            0XFFFFFFFF

/**
 *  * Register: XAVBUF_BUF_STC_INIT_VALUE1
 *   */
    #define XAVBUF_BUF_STC_INIT_VALUE1                                             0X0000B034

    #define XAVBUF_BUF_STC_INIT_VALUE1_INIT_VALUE1_SHIFT                           0
    #define XAVBUF_BUF_STC_INIT_VALUE1_INIT_VALUE1_WIDTH                           10
    #define XAVBUF_BUF_STC_INIT_VALUE1_INIT_VALUE1_MASK                            0X000003FF

/**
 *  * Register: XAVBUF_BUF_STC_ADJ
 *   */
    #define XAVBUF_BUF_STC_ADJ                                                     0X0000B038

    #define XAVBUF_BUF_STC_ADJ_SIGN_SHIFT                                          31
    #define XAVBUF_BUF_STC_ADJ_SIGN_WIDTH                                          1
    #define XAVBUF_BUF_STC_ADJ_SIGN_MASK                                           0X80000000

    #define XAVBUF_BUF_STC_ADJ_VALUE_SHIFT                                         0
    #define XAVBUF_BUF_STC_ADJ_VALUE_WIDTH                                         31
    #define XAVBUF_BUF_STC_ADJ_VALUE_MASK                                          0X7FFFFFFF

/**
 *  * Register: XAVBUF_BUF_STC_VID_VSYNC_TS_REG0
 *   */
    #define XAVBUF_BUF_STC_VID_VSYNC_TS_REG0                                       0X0000B03C

    #define XAVBUF_BUF_STC_VID_VSYNC_TS_REG0_VSYNC_TS0_SHIFT                       0
    #define XAVBUF_BUF_STC_VID_VSYNC_TS_REG0_VSYNC_TS0_WIDTH                       32
    #define XAVBUF_BUF_STC_VID_VSYNC_TS_REG0_VSYNC_TS0_MASK                        0XFFFFFFFF

/**
 *  * Register: XAVBUF_BUF_STC_VID_VSYNC_TS_REG1
 *   */
    #define XAVBUF_BUF_STC_VID_VSYNC_TS_REG1                                       0X0000B040

    #define XAVBUF_BUF_STC_VID_VSYNC_TS_REG1_VSYNC_TS1_SHIFT                       0
    #define XAVBUF_BUF_STC_VID_VSYNC_TS_REG1_VSYNC_TS1_WIDTH                       10
    #define XAVBUF_BUF_STC_VID_VSYNC_TS_REG1_VSYNC_TS1_MASK                        0X000003FF

/**
 *  * Register: XAVBUF_BUF_STC_EXT_VSYNC_TS_REG0
 *   */
    #define XAVBUF_BUF_STC_EXT_VSYNC_TS_REG0                                       0X0000B044

    #define XAVBUF_BUF_STC_EXT_VSYNC_TS_REG0_EXT_VSYNC_TS0_SHIFT                   0
    #define XAVBUF_BUF_STC_EXT_VSYNC_TS_REG0_EXT_VSYNC_TS0_WIDTH                   32
    #define XAVBUF_BUF_STC_EXT_VSYNC_TS_REG0_EXT_VSYNC_TS0_MASK                    0XFFFFFFFF

/**
 *  * Register: XAVBUF_BUF_STC_EXT_VSYNC_TS_REG1
 *   */
    #define XAVBUF_BUF_STC_EXT_VSYNC_TS_REG1                                       0X0000B048

    #define XAVBUF_BUF_STC_EXT_VSYNC_TS_REG1_EXT_VSYNC_TS1_SHIFT                   0
    #define XAVBUF_BUF_STC_EXT_VSYNC_TS_REG1_EXT_VSYNC_TS1_WIDTH                   10
    #define XAVBUF_BUF_STC_EXT_VSYNC_TS_REG1_EXT_VSYNC_TS1_MASK                    0X000003FF

/**
 *  * Register: XAVBUF_BUF_STC_CUSTOM_EVENT_TS_REG0
 *   */
    #define XAVBUF_BUF_STC_CUSTOM_EVENT_TS_REG0                                    0X0000B04C

    #define XAVBUF_BUF_STC_CUSTOM_EVENT_TS_REG0_CUST_EVENT_TS0_SHIFT               0
    #define XAVBUF_BUF_STC_CUSTOM_EVENT_TS_REG0_CUST_EVENT_TS0_WIDTH               32
    #define XAVBUF_BUF_STC_CUSTOM_EVENT_TS_REG0_CUST_EVENT_TS0_MASK                0XFFFFFFFF

/**
 *  * Register: XAVBUF_BUF_STC_CUSTOM_EVENT_TS_REG1
 *   */
    #define XAVBUF_BUF_STC_CUSTOM_EVENT_TS_REG1                                    0X0000B050

    #define XAVBUF_BUF_STC_CUSTOM_EVENT_TS_REG1_CUST_EVENT_TS1_SHIFT               0
    #define XAVBUF_BUF_STC_CUSTOM_EVENT_TS_REG1_CUST_EVENT_TS1_WIDTH               10
    #define XAVBUF_BUF_STC_CUSTOM_EVENT_TS_REG1_CUST_EVENT_TS1_MASK                0X000003FF

/**
 *  * Register: XAVBUF_BUF_STC_CUSTOM_EVENT2_TS_REG0
 *   */
    #define XAVBUF_BUF_STC_CUSTOM_EVENT2_TS_REG0                                   0X0000B054

    #define XAVBUF_BUF_STC_CUSTOM_EVENT2_TS_REG0_CUST_EVENT2_TS0_SHIFT             0
    #define XAVBUF_BUF_STC_CUSTOM_EVENT2_TS_REG0_CUST_EVENT2_TS0_WIDTH             32
    #define XAVBUF_BUF_STC_CUSTOM_EVENT2_TS_REG0_CUST_EVENT2_TS0_MASK              0XFFFFFFFF

/**
 *  * Register: XAVBUF_BUF_STC_CUSTOM_EVENT2_TS_REG1
 *   */
    #define XAVBUF_BUF_STC_CUSTOM_EVENT2_TS_REG1                                   0X0000B058

    #define XAVBUF_BUF_STC_CUSTOM_EVENT2_TS_REG1_CUST_EVENT2_TS1_SHIFT             0
    #define XAVBUF_BUF_STC_CUSTOM_EVENT2_TS_REG1_CUST_EVENT2_TS1_WIDTH             10
    #define XAVBUF_BUF_STC_CUSTOM_EVENT2_TS_REG1_CUST_EVENT2_TS1_MASK              0X000003FF

/**
 *  * Register: XAVBUF_BUF_STC_SNAPSHOT0
 *   */
    #define XAVBUF_BUF_STC_SNAPSHOT0                                               0X0000B060

    #define XAVBUF_BUF_STC_SNAPSHOT0_STC0_SHIFT                                    0
    #define XAVBUF_BUF_STC_SNAPSHOT0_STC0_WIDTH                                    32
    #define XAVBUF_BUF_STC_SNAPSHOT0_STC0_MASK                                     0XFFFFFFFF

/**
 *  * Register: XAVBUF_BUF_STC_SNAPSHOT1
 *   */
    #define XAVBUF_BUF_STC_SNAPSHOT1                                               0X0000B064

    #define XAVBUF_BUF_STC_SNAPSHOT1_STC1_SHIFT                                    0
    #define XAVBUF_BUF_STC_SNAPSHOT1_STC1_WIDTH                                    10
    #define XAVBUF_BUF_STC_SNAPSHOT1_STC1_MASK                                     0X000003FF

/**
 *  * Register: XAVBUF_BUF_OUTPUT_AUD_VID_SELECT
 *   */
    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT                                       0X0000B070

    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_AUD_STREAM2_SEL_SHIFT                 6
    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_AUD_STREAM2_SEL_WIDTH                 1
    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_AUD_STREAM2_SEL_MASK                  0X00000040

    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_AUD_STREAM1_SEL_SHIFT                 4
    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_AUD_STREAM1_SEL_WIDTH                 2
    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_AUD_STREAM1_SEL_MASK                  0X00000030

    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_VID_STREAM2_SEL_SHIFT                 2
    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_VID_STREAM2_SEL_WIDTH                 2
    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_VID_STREAM2_SEL_MASK                  0X0000000C

    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_VID_STREAM1_SEL_SHIFT                 0
    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_VID_STREAM1_SEL_WIDTH                 2
    #define XAVBUF_BUF_OUTPUT_AUD_VID_SELECT_VID_STREAM1_SEL_MASK                  0X00000003

/**
 *  * Register: XAVBUF_BUF_HCOUNT_VCOUNT_INT0
 *   */
    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT0                                          0X0000B074

    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT0_HCOUNT_SHIFT                             16
    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT0_HCOUNT_WIDTH                             14
    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT0_HCOUNT_MASK                              0X3FFF0000

    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT0_VCOUNT_SHIFT                             0
    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT0_VCOUNT_WIDTH                             14
    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT0_VCOUNT_MASK                              0X00003FFF

/**
 *  * Register: XAVBUF_BUF_HCOUNT_VCOUNT_INT1
 *   */
    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT1                                          0X0000B078

    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT1_HCOUNT_SHIFT                             16
    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT1_HCOUNT_WIDTH                             14
    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT1_HCOUNT_MASK                              0X3FFF0000

    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT1_VCOUNT_SHIFT                             0
    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT1_VCOUNT_WIDTH                             14
    #define XAVBUF_BUF_HCOUNT_VCOUNT_INT1_VCOUNT_MASK                              0X00003FFF

/**
 *  * Register: XAVBUF_BUF_DITHER_CFG
 *   */
    #define XAVBUF_BUF_DITHER_CFG                                                  0X0000B07C

    #define XAVBUF_BUF_DITHER_CFG_TAP_MSB_SHIFT                                    10
    #define XAVBUF_BUF_DITHER_CFG_TAP_MSB_WIDTH                                    1
    #define XAVBUF_BUF_DITHER_CFG_TAP_MSB_MASK                                     0X00000400

    #define XAVBUF_BUF_DITHER_CFG_DW_SEL_SHIFT                                     9
    #define XAVBUF_BUF_DITHER_CFG_DW_SEL_WIDTH                                     1
    #define XAVBUF_BUF_DITHER_CFG_DW_SEL_MASK                                      0X00000200

    #define XAVBUF_BUF_DITHER_CFG_LD_SHIFT                                         8
    #define XAVBUF_BUF_DITHER_CFG_LD_WIDTH                                         1
    #define XAVBUF_BUF_DITHER_CFG_LD_MASK                                          0X00000100

    #define XAVBUF_BUF_DITHER_CFG_TRUNC_PT_SHIFT                                   5
    #define XAVBUF_BUF_DITHER_CFG_TRUNC_PT_WIDTH                                   3
    #define XAVBUF_BUF_DITHER_CFG_TRUNC_PT_MASK                                    0X000000E0

    #define XAVBUF_BUF_DITHER_CFG_MODE_SHIFT                                       3
    #define XAVBUF_BUF_DITHER_CFG_MODE_WIDTH                                       2
    #define XAVBUF_BUF_DITHER_CFG_MODE_MASK                                        0X00000018

    #define XAVBUF_BUF_DITHER_CFG_SIZE_SHIFT                                       0
    #define XAVBUF_BUF_DITHER_CFG_SIZE_WIDTH                                       3
    #define XAVBUF_BUF_DITHER_CFG_SIZE_MASK                                        0X00000007

/**
 *  * Register: XAVBUF_DITHER_CFG_SEED0
 *   */
    #define XAVBUF_DITHER_CFG_SEED0                                                0X0000B080

    #define XAVBUF_DITHER_CFG_SEED0_COLR0_SHIFT                                    0
    #define XAVBUF_DITHER_CFG_SEED0_COLR0_WIDTH                                    16
    #define XAVBUF_DITHER_CFG_SEED0_COLR0_MASK                                     0X0000FFFF

/**
 *  * Register: XAVBUF_DITHER_CFG_SEED1
 *   */
    #define XAVBUF_DITHER_CFG_SEED1                                                0X0000B084

    #define XAVBUF_DITHER_CFG_SEED1_COLR1_SHIFT                                    0
    #define XAVBUF_DITHER_CFG_SEED1_COLR1_WIDTH                                    16
    #define XAVBUF_DITHER_CFG_SEED1_COLR1_MASK                                     0X0000FFFF

/**
 *  * Register: XAVBUF_DITHER_CFG_SEED2
 *   */
    #define XAVBUF_DITHER_CFG_SEED2                                                0X0000B088

    #define XAVBUF_DITHER_CFG_SEED2_COLR2_SHIFT                                    0
    #define XAVBUF_DITHER_CFG_SEED2_COLR2_WIDTH                                    16
    #define XAVBUF_DITHER_CFG_SEED2_COLR2_MASK                                     0X0000FFFF

/**
 *  * Register: XAVBUF_DITHER_CFG_MAX
 *   */
    #define XAVBUF_DITHER_CFG_MAX                                                  0X0000B08C

    #define XAVBUF_DITHER_CFG_MAX_COLR_MAX_SHIFT                                   0
    #define XAVBUF_DITHER_CFG_MAX_COLR_MAX_WIDTH                                   12
    #define XAVBUF_DITHER_CFG_MAX_COLR_MAX_MASK                                    0X00000FFF

/**
 *  * Register: XAVBUF_DITHER_CFG_MIN
 *   */
    #define XAVBUF_DITHER_CFG_MIN                                                  0X0000B090

    #define XAVBUF_DITHER_CFG_MIN_COLR_MIN_SHIFT                                   0
    #define XAVBUF_DITHER_CFG_MIN_COLR_MIN_WIDTH                                   12
    #define XAVBUF_DITHER_CFG_MIN_COLR_MIN_MASK                                    0X00000FFF

/**
 *  * Register: XAVBUF_PATTERN_GEN_SELECT
 *   */
    #define XAVBUF_PATTERN_GEN_SELECT                                              0X0000B100

    #define XAVBUF_PATTERN_GEN_SELECT_OFFSET_EQ_SHIFT                              8
    #define XAVBUF_PATTERN_GEN_SELECT_OFFSET_EQ_WIDTH                              24
    #define XAVBUF_PATTERN_GEN_SELECT_OFFSET_EQ_MASK                               0XFFFFFF00

    #define XAVBUF_PATTERN_GEN_SELECT_AUD_RATE_SEL_SHIFT                           0
    #define XAVBUF_PATTERN_GEN_SELECT_AUD_RATE_SEL_WIDTH                           2
    #define XAVBUF_PATTERN_GEN_SELECT_AUD_RATE_SEL_MASK                            0X00000003

/**
 *  * Register: XAVBUF_AUD_PATTERN_SELECT1
 *   */
    #define XAVBUF_AUD_PATTERN_SELECT1                                             0X0000B104

    #define XAVBUF_AUD_PATTERN_SELECT1_PATTERN_SHIFT                               0
    #define XAVBUF_AUD_PATTERN_SELECT1_PATTERN_WIDTH                               2
    #define XAVBUF_AUD_PATTERN_SELECT1_PATTERN_MASK                                0X00000003

/**
 *  * Register: XAVBUF_AUD_PATTERN_SELECT2
 *   */
    #define XAVBUF_AUD_PATTERN_SELECT2                                             0X0000B108

    #define XAVBUF_AUD_PATTERN_SELECT2_PATTERN_SHIFT                               0
    #define XAVBUF_AUD_PATTERN_SELECT2_PATTERN_WIDTH                               2
    #define XAVBUF_AUD_PATTERN_SELECT2_PATTERN_MASK                                0X00000003

/**
 *  * Register: XAVBUF_BUF_AUD_VID_CLK_SOURCE
 *   */
    #define XAVBUF_BUF_AUD_VID_CLK_SOURCE                                          0X0000B120

    #define XAVBUF_BUF_AUD_VID_CLK_SOURCE_VID_TIMING_SRC_SHIFT                     2
    #define XAVBUF_BUF_AUD_VID_CLK_SOURCE_VID_TIMING_SRC_WIDTH                     1
    #define XAVBUF_BUF_AUD_VID_CLK_SOURCE_VID_TIMING_SRC_MASK                      0X00000004

    #define XAVBUF_BUF_AUD_VID_CLK_SOURCE_AUD_CLK_SRC_SHIFT                        1
    #define XAVBUF_BUF_AUD_VID_CLK_SOURCE_AUD_CLK_SRC_WIDTH                        1
    #define XAVBUF_BUF_AUD_VID_CLK_SOURCE_AUD_CLK_SRC_MASK                         0X00000002

    #define XAVBUF_BUF_AUD_VID_CLK_SOURCE_VID_CLK_SRC_SHIFT                        0
    #define XAVBUF_BUF_AUD_VID_CLK_SOURCE_VID_CLK_SRC_WIDTH                        1
    #define XAVBUF_BUF_AUD_VID_CLK_SOURCE_VID_CLK_SRC_MASK                         0X00000001

/**
 *  * Register: XAVBUF_BUF_SRST_REG
 *   */
    #define XAVBUF_BUF_SRST_REG                                                    0X0000B124

    #define XAVBUF_BUF_SRST_REG_VID_RST_SHIFT                                      1
    #define XAVBUF_BUF_SRST_REG_VID_RST_WIDTH                                      1
    #define XAVBUF_BUF_SRST_REG_VID_RST_MASK                                       0X00000002

/**
 *  * Register: XAVBUF_BUF_AUD_RDY_INTERVAL
 *   */
    #define XAVBUF_BUF_AUD_RDY_INTERVAL                                            0X0000B128

    #define XAVBUF_BUF_AUD_RDY_INTERVAL_CH1_INT_SHIFT                              16
    #define XAVBUF_BUF_AUD_RDY_INTERVAL_CH1_INT_WIDTH                              16
    #define XAVBUF_BUF_AUD_RDY_INTERVAL_CH1_INT_MASK                               0XFFFF0000

    #define XAVBUF_BUF_AUD_RDY_INTERVAL_CH0_INT_SHIFT                              0
    #define XAVBUF_BUF_AUD_RDY_INTERVAL_CH0_INT_WIDTH                              16
    #define XAVBUF_BUF_AUD_RDY_INTERVAL_CH0_INT_MASK                               0X0000FFFF

/**
 *  * Register: XAVBUF_BUF_AUD_CH_CFG
 *   */
    #define XAVBUF_BUF_AUD_CH_CFG                                                  0X0000B12C

    #define XAVBUF_BUF_AUD_CH_CFG_AUD_CH_ID_SHIFT                                  0
    #define XAVBUF_BUF_AUD_CH_CFG_AUD_CH_ID_WIDTH                                  2
    #define XAVBUF_BUF_AUD_CH_CFG_AUD_CH_ID_MASK                                   0X00000003

/**
 *  * Register: XAVBUF_BUF_GRAPHICS_COMP0_SCALE_FACTOR
 *   */
    #define XAVBUF_BUF_GRAPHICS_COMP0_SCALE_FACTOR                                 0X0000B200

    #define XAVBUF_BUF_GRAPHICS_COMP0_SCALE_FACTOR_GRAPHICS_SCALE_FACTOR0_SHIFT    0
    #define XAVBUF_BUF_GRAPHICS_COMP0_SCALE_FACTOR_GRAPHICS_SCALE_FACTOR0_WIDTH    17
    #define XAVBUF_BUF_GRAPHICS_COMP0_SCALE_FACTOR_GRAPHICS_SCALE_FACTOR0_MASK     0X0001FFFF

/**
 *  * Register: XAVBUF_BUF_GRAPHICS_COMP1_SCALE_FACTOR
 *   */
    #define XAVBUF_BUF_GRAPHICS_COMP1_SCALE_FACTOR                                 0X0000B204

    #define XAVBUF_BUF_GRAPHICS_COMP1_SCALE_FACTOR_GRAPHICS_SCALE_FACTOR1_SHIFT    0
    #define XAVBUF_BUF_GRAPHICS_COMP1_SCALE_FACTOR_GRAPHICS_SCALE_FACTOR1_WIDTH    17
    #define XAVBUF_BUF_GRAPHICS_COMP1_SCALE_FACTOR_GRAPHICS_SCALE_FACTOR1_MASK     0X0001FFFF

/**
 *  * Register: XAVBUF_BUF_GRAPHICS_COMP2_SCALE_FACTOR
 *   */
    #define XAVBUF_BUF_GRAPHICS_COMP2_SCALE_FACTOR                                 0X0000B208

    #define XAVBUF_BUF_GRAPHICS_COMP2_SCALE_FACTOR_GRAPHICS_SCALE_FACTOR2_SHIFT    0
    #define XAVBUF_BUF_GRAPHICS_COMP2_SCALE_FACTOR_GRAPHICS_SCALE_FACTOR2_WIDTH    17
    #define XAVBUF_BUF_GRAPHICS_COMP2_SCALE_FACTOR_GRAPHICS_SCALE_FACTOR2_MASK     0X0001FFFF

/**
 *  * Register: XAVBUF_BUF_VID_COMP0_SCALE_FACTOR
 *   */
    #define XAVBUF_BUF_VID_COMP0_SCALE_FACTOR                                      0X0000B20C

    #define XAVBUF_BUF_VID_COMP0_SCALE_FACTOR_VID_SCA_FACT0_SHIFT                  0
    #define XAVBUF_BUF_VID_COMP0_SCALE_FACTOR_VID_SCA_FACT0_WIDTH                  17
    #define XAVBUF_BUF_VID_COMP0_SCALE_FACTOR_VID_SCA_FACT0_MASK                   0X0001FFFF

/**
 *  * Register: XAVBUF_BUF_VID_COMP1_SCALE_FACTOR
 *   */
    #define XAVBUF_BUF_VID_COMP1_SCALE_FACTOR                                      0X0000B210

    #define XAVBUF_BUF_VID_COMP1_SCALE_FACTOR_VID_SCA_FACT1_SHIFT                  0
    #define XAVBUF_BUF_VID_COMP1_SCALE_FACTOR_VID_SCA_FACT1_WIDTH                  17
    #define XAVBUF_BUF_VID_COMP1_SCALE_FACTOR_VID_SCA_FACT1_MASK                   0X0001FFFF

/**
 *  * Register: XAVBUF_BUF_VID_COMP2_SCALE_FACTOR
 *   */
    #define XAVBUF_BUF_VID_COMP2_SCALE_FACTOR                                      0X0000B214

    #define XAVBUF_BUF_VID_COMP2_SCALE_FACTOR_VID_SCA_FACT2_SHIFT                  0
    #define XAVBUF_BUF_VID_COMP2_SCALE_FACTOR_VID_SCA_FACT2_WIDTH                  17
    #define XAVBUF_BUF_VID_COMP2_SCALE_FACTOR_VID_SCA_FACT2_MASK                   0X0001FFFF

/**
 *  * Register: XAVBUF_BUF_LIVE_VID_COMP0_SF
 *   */
    #define XAVBUF_BUF_LIVE_VID_COMP0_SF                                           0X0000B218

    #define XAVBUF_BUF_LIVE_VID_COMP0_SF_LIV_VID_SCA_FACT0_SHIFT                   0
    #define XAVBUF_BUF_LIVE_VID_COMP0_SF_LIV_VID_SCA_FACT0_WIDTH                   17
    #define XAVBUF_BUF_LIVE_VID_COMP0_SF_LIV_VID_SCA_FACT0_MASK                    0X0001FFFF

/**
 *  * Register: XAVBUF_BUF_LIVE_VID_COMP1_SF
 *   */
    #define XAVBUF_BUF_LIVE_VID_COMP1_SF                                           0X0000B21C

    #define XAVBUF_BUF_LIVE_VID_COMP1_SF_LIV_VID_SCA_FACT1_SHIFT                   0
    #define XAVBUF_BUF_LIVE_VID_COMP1_SF_LIV_VID_SCA_FACT1_WIDTH                   17
    #define XAVBUF_BUF_LIVE_VID_COMP1_SF_LIV_VID_SCA_FACT1_MASK                    0X0001FFFF

/**
 *  * Register: XAVBUF_BUF_LIVE_VID_COMP2_SF
 *   */
    #define XAVBUF_BUF_LIVE_VID_COMP2_SF                                           0X0000B220

    #define XAVBUF_BUF_LIVE_VID_COMP2_SF_LIV_VID_SCA_FACT2_SHIFT                   0
    #define XAVBUF_BUF_LIVE_VID_COMP2_SF_LIV_VID_SCA_FACT2_WIDTH                   17
    #define XAVBUF_BUF_LIVE_VID_COMP2_SF_LIV_VID_SCA_FACT2_MASK                    0X0001FFFF

/**
 *  * Register: XAVBUF_BUF_LIVE_VID_CFG
 *   */
    #define XAVBUF_BUF_LIVE_VID_CFG                                                0X0000B224

    #define XAVBUF_BUF_LIVE_VID_CFG_CB_FIRST_SHIFT                                 8
    #define XAVBUF_BUF_LIVE_VID_CFG_CB_FIRST_WIDTH                                 1
    #define XAVBUF_BUF_LIVE_VID_CFG_CB_FIRST_MASK                                  0X00000100

    #define XAVBUF_BUF_LIVE_VID_CFG_FORMAT_SHIFT                                   4
    #define XAVBUF_BUF_LIVE_VID_CFG_FORMAT_WIDTH                                   2
    #define XAVBUF_BUF_LIVE_VID_CFG_FORMAT_MASK                                    0X00000030

    #define XAVBUF_BUF_LIVE_VID_CFG_BPC_SHIFT                                      0
    #define XAVBUF_BUF_LIVE_VID_CFG_BPC_WIDTH                                      3
    #define XAVBUF_BUF_LIVE_VID_CFG_BPC_MASK                                       0X00000007

/**
 *  * Register: XAVBUF_BUF_LIVE_GFX_COMP0_SF
 *   */
    #define XAVBUF_BUF_LIVE_GFX_COMP0_SF                                           0X0000B228

    #define XAVBUF_BUF_LIVE_GFX_COMP0_SF_LIV_VID_SCA_FACT0_SHIFT                   0
    #define XAVBUF_BUF_LIVE_GFX_COMP0_SF_LIV_VID_SCA_FACT0_WIDTH                   17
    #define XAVBUF_BUF_LIVE_GFX_COMP0_SF_LIV_VID_SCA_FACT0_MASK                    0X0001FFFF

/**
 *  * Register: XAVBUF_BUF_LIVE_GFX_COMP1_SF
 *   */
    #define XAVBUF_BUF_LIVE_GFX_COMP1_SF                                           0X0000B22C

    #define XAVBUF_BUF_LIVE_GFX_COMP1_SF_LIV_VID_SCA_FACT1_SHIFT                   0
    #define XAVBUF_BUF_LIVE_GFX_COMP1_SF_LIV_VID_SCA_FACT1_WIDTH                   17
    #define XAVBUF_BUF_LIVE_GFX_COMP1_SF_LIV_VID_SCA_FACT1_MASK                    0X0001FFFF

/**
 *  * Register: XAVBUF_BUF_LIVE_GFX_COMP2_SF
 *   */
    #define XAVBUF_BUF_LIVE_GFX_COMP2_SF                                           0X0000B230

    #define XAVBUF_BUF_LIVE_GFX_COMP2_SF_LIV_VID_SCA_FACT2_SHIFT                   0
    #define XAVBUF_BUF_LIVE_GFX_COMP2_SF_LIV_VID_SCA_FACT2_WIDTH                   17
    #define XAVBUF_BUF_LIVE_GFX_COMP2_SF_LIV_VID_SCA_FACT2_MASK                    0X0001FFFF

/**
 *  * Register: XAVBUF_BUF_LIVE_GFX_CFG
 *   */
    #define XAVBUF_BUF_LIVE_GFX_CFG                                                0X0000B234

    #define XAVBUF_BUF_LIVE_GFX_CFG_CB_FIRST_SHIFT                                 8
    #define XAVBUF_BUF_LIVE_GFX_CFG_CB_FIRST_WIDTH                                 1
    #define XAVBUF_BUF_LIVE_GFX_CFG_CB_FIRST_MASK                                  0X00000100

    #define XAVBUF_BUF_LIVE_GFX_CFG_FORMAT_SHIFT                                   4
    #define XAVBUF_BUF_LIVE_GFX_CFG_FORMAT_WIDTH                                   2
    #define XAVBUF_BUF_LIVE_GFX_CFG_FORMAT_MASK                                    0X00000030

    #define XAVBUF_BUF_LIVE_GFX_CFG_BPC_SHIFT                                      0
    #define XAVBUF_BUF_LIVE_GFX_CFG_BPC_WIDTH                                      3
    #define XAVBUF_BUF_LIVE_GFX_CFG_BPC_MASK                                       0X00000007

/**
 *  * Register: XAVBUF_AUD_MIXER_VOLUME_CONTROL
 *   */
    #define XAVBUF_AUD_MIXER_VOLUME_CONTROL                                        0X0000C000

    #define XAVBUF_AUD_MIXER_VOLUME_CONTROL_VOL_CTRL_CH1_SHIFT                     16
    #define XAVBUF_AUD_MIXER_VOLUME_CONTROL_VOL_CTRL_CH1_WIDTH                     16
    #define XAVBUF_AUD_MIXER_VOLUME_CONTROL_VOL_CTRL_CH1_MASK                      0XFFFF0000

    #define XAVBUF_AUD_MIXER_VOLUME_CONTROL_VOL_CTRL_CH0_SHIFT                     0
    #define XAVBUF_AUD_MIXER_VOLUME_CONTROL_VOL_CTRL_CH0_WIDTH                     16
    #define XAVBUF_AUD_MIXER_VOLUME_CONTROL_VOL_CTRL_CH0_MASK                      0X0000FFFF

/**
 *  * Register: XAVBUF_AUD_MIXER_META_DATA
 *   */
    #define XAVBUF_AUD_MIXER_META_DATA                                             0X0000C004

    #define XAVBUF_AUD_MIXER_META_DATA_AUD_META_DATA_SEL_SHIFT                     0
    #define XAVBUF_AUD_MIXER_META_DATA_AUD_META_DATA_SEL_WIDTH                     1
    #define XAVBUF_AUD_MIXER_META_DATA_AUD_META_DATA_SEL_MASK                      0X00000001

/**
 *  * Register: XAVBUF_AUD_CH_STATUS_REG0
 *   */
    #define XAVBUF_AUD_CH_STATUS_REG0                                              0X0000C008

    #define XAVBUF_AUD_CH_STATUS_REG0_STATUS0_SHIFT                                0
    #define XAVBUF_AUD_CH_STATUS_REG0_STATUS0_WIDTH                                32
    #define XAVBUF_AUD_CH_STATUS_REG0_STATUS0_MASK                                 0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_STATUS_REG1
 *   */
    #define XAVBUF_AUD_CH_STATUS_REG1                                              0X0000C00C

    #define XAVBUF_AUD_CH_STATUS_REG1_STATUS1_SHIFT                                0
    #define XAVBUF_AUD_CH_STATUS_REG1_STATUS1_WIDTH                                32
    #define XAVBUF_AUD_CH_STATUS_REG1_STATUS1_MASK                                 0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_STATUS_REG2
 *   */
    #define XAVBUF_AUD_CH_STATUS_REG2                                              0X0000C010

    #define XAVBUF_AUD_CH_STATUS_REG2_STATUS2_SHIFT                                0
    #define XAVBUF_AUD_CH_STATUS_REG2_STATUS2_WIDTH                                32
    #define XAVBUF_AUD_CH_STATUS_REG2_STATUS2_MASK                                 0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_STATUS_REG3
 *   */
    #define XAVBUF_AUD_CH_STATUS_REG3                                              0X0000C014

    #define XAVBUF_AUD_CH_STATUS_REG3_STATUS3_SHIFT                                0
    #define XAVBUF_AUD_CH_STATUS_REG3_STATUS3_WIDTH                                32
    #define XAVBUF_AUD_CH_STATUS_REG3_STATUS3_MASK                                 0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_STATUS_REG4
 *   */
    #define XAVBUF_AUD_CH_STATUS_REG4                                              0X0000C018

    #define XAVBUF_AUD_CH_STATUS_REG4_STATUS4_SHIFT                                0
    #define XAVBUF_AUD_CH_STATUS_REG4_STATUS4_WIDTH                                32
    #define XAVBUF_AUD_CH_STATUS_REG4_STATUS4_MASK                                 0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_STATUS_REG5
 *   */
    #define XAVBUF_AUD_CH_STATUS_REG5                                              0X0000C01C

    #define XAVBUF_AUD_CH_STATUS_REG5_STATUS5_SHIFT                                0
    #define XAVBUF_AUD_CH_STATUS_REG5_STATUS5_WIDTH                                32
    #define XAVBUF_AUD_CH_STATUS_REG5_STATUS5_MASK                                 0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_A_DATA_REG0
 *   */
    #define XAVBUF_AUD_CH_A_DATA_REG0                                              0X0000C020

    #define XAVBUF_AUD_CH_A_DATA_REG0_USER_DATA0_SHIFT                             0
    #define XAVBUF_AUD_CH_A_DATA_REG0_USER_DATA0_WIDTH                             32
    #define XAVBUF_AUD_CH_A_DATA_REG0_USER_DATA0_MASK                              0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_A_DATA_REG1
 *   */
    #define XAVBUF_AUD_CH_A_DATA_REG1                                              0X0000C024

    #define XAVBUF_AUD_CH_A_DATA_REG1_USER_DATA1_SHIFT                             0
    #define XAVBUF_AUD_CH_A_DATA_REG1_USER_DATA1_WIDTH                             32
    #define XAVBUF_AUD_CH_A_DATA_REG1_USER_DATA1_MASK                              0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_A_DATA_REG2
 *   */
    #define XAVBUF_AUD_CH_A_DATA_REG2                                              0X0000C028

    #define XAVBUF_AUD_CH_A_DATA_REG2_USER_DATA2_SHIFT                             0
    #define XAVBUF_AUD_CH_A_DATA_REG2_USER_DATA2_WIDTH                             32
    #define XAVBUF_AUD_CH_A_DATA_REG2_USER_DATA2_MASK                              0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_A_DATA_REG3
 *   */
    #define XAVBUF_AUD_CH_A_DATA_REG3                                              0X0000C02C

    #define XAVBUF_AUD_CH_A_DATA_REG3_USER_DATA3_SHIFT                             0
    #define XAVBUF_AUD_CH_A_DATA_REG3_USER_DATA3_WIDTH                             32
    #define XAVBUF_AUD_CH_A_DATA_REG3_USER_DATA3_MASK                              0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_A_DATA_REG4
 *   */
    #define XAVBUF_AUD_CH_A_DATA_REG4                                              0X0000C030

    #define XAVBUF_AUD_CH_A_DATA_REG4_USER_DATA4_SHIFT                             0
    #define XAVBUF_AUD_CH_A_DATA_REG4_USER_DATA4_WIDTH                             32
    #define XAVBUF_AUD_CH_A_DATA_REG4_USER_DATA4_MASK                              0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_A_DATA_REG5
 *   */
    #define XAVBUF_AUD_CH_A_DATA_REG5                                              0X0000C034

    #define XAVBUF_AUD_CH_A_DATA_REG5_USER_DATA5_SHIFT                             0
    #define XAVBUF_AUD_CH_A_DATA_REG5_USER_DATA5_WIDTH                             32
    #define XAVBUF_AUD_CH_A_DATA_REG5_USER_DATA5_MASK                              0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_B_DATA_REG0
 *   */
    #define XAVBUF_AUD_CH_B_DATA_REG0                                              0X0000C038

    #define XAVBUF_AUD_CH_B_DATA_REG0_USER_DATA0_SHIFT                             0
    #define XAVBUF_AUD_CH_B_DATA_REG0_USER_DATA0_WIDTH                             32
    #define XAVBUF_AUD_CH_B_DATA_REG0_USER_DATA0_MASK                              0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_B_DATA_REG1
 *   */
    #define XAVBUF_AUD_CH_B_DATA_REG1                                              0X0000C03C

    #define XAVBUF_AUD_CH_B_DATA_REG1_USER_DATA1_SHIFT                             0
    #define XAVBUF_AUD_CH_B_DATA_REG1_USER_DATA1_WIDTH                             32
    #define XAVBUF_AUD_CH_B_DATA_REG1_USER_DATA1_MASK                              0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_B_DATA_REG2
 *   */
    #define XAVBUF_AUD_CH_B_DATA_REG2                                              0X0000C040

    #define XAVBUF_AUD_CH_B_DATA_REG2_USER_DATA2_SHIFT                             0
    #define XAVBUF_AUD_CH_B_DATA_REG2_USER_DATA2_WIDTH                             32
    #define XAVBUF_AUD_CH_B_DATA_REG2_USER_DATA2_MASK                              0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_B_DATA_REG3
 *   */
    #define XAVBUF_AUD_CH_B_DATA_REG3                                              0X0000C044

    #define XAVBUF_AUD_CH_B_DATA_REG3_USER_DATA3_SHIFT                             0
    #define XAVBUF_AUD_CH_B_DATA_REG3_USER_DATA3_WIDTH                             32
    #define XAVBUF_AUD_CH_B_DATA_REG3_USER_DATA3_MASK                              0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_B_DATA_REG4
 *   */
    #define XAVBUF_AUD_CH_B_DATA_REG4                                              0X0000C048

    #define XAVBUF_AUD_CH_B_DATA_REG4_USER_DATA4_SHIFT                             0
    #define XAVBUF_AUD_CH_B_DATA_REG4_USER_DATA4_WIDTH                             32
    #define XAVBUF_AUD_CH_B_DATA_REG4_USER_DATA4_MASK                              0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_CH_B_DATA_REG5
 *   */
    #define XAVBUF_AUD_CH_B_DATA_REG5                                              0X0000C04C

    #define XAVBUF_AUD_CH_B_DATA_REG5_USER_DATA5_SHIFT                             0
    #define XAVBUF_AUD_CH_B_DATA_REG5_USER_DATA5_WIDTH                             32
    #define XAVBUF_AUD_CH_B_DATA_REG5_USER_DATA5_MASK                              0XFFFFFFFF

/**
 *  * Register: XAVBUF_AUD_SOFT_RST
 *   */
    #define XAVBUF_AUD_SOFT_RST                                                    0X0000CC00

    #define XAVBUF_AUD_SOFT_RST_EXTRA_BS_CONTROL_SHIFT                             2
    #define XAVBUF_AUD_SOFT_RST_EXTRA_BS_CONTROL_WIDTH                             1
    #define XAVBUF_AUD_SOFT_RST_EXTRA_BS_CONTROL_MASK                              0X00000004

    #define XAVBUF_AUD_SOFT_RST_LINE_RST_DISABLE_SHIFT                             1
    #define XAVBUF_AUD_SOFT_RST_LINE_RST_DISABLE_WIDTH                             1
    #define XAVBUF_AUD_SOFT_RST_LINE_RST_DISABLE_MASK                              0X00000002

    #define XAVBUF_AUD_SOFT_RST_AUD_SRST_SHIFT                                     0
    #define XAVBUF_AUD_SOFT_RST_AUD_SRST_WIDTH                                     1
    #define XAVBUF_AUD_SOFT_RST_AUD_SRST_MASK                                      0X00000001

/**
 *  * Register: XAVBUF_PATGEN_CRC_R
 *   */
    #define XAVBUF_PATGEN_CRC_R                                                    0X0000CC10

    #define XAVBUF_PATGEN_CRC_R_CRC_R_SHIFT                                        0
    #define XAVBUF_PATGEN_CRC_R_CRC_R_WIDTH                                        16
    #define XAVBUF_PATGEN_CRC_R_CRC_R_MASK                                         0X0000FFFF

/**
 *  * Register: XAVBUF_PATGEN_CRC_G
 *   */
    #define XAVBUF_PATGEN_CRC_G                                                    0X0000CC14

    #define XAVBUF_PATGEN_CRC_G_CRC_G_SHIFT                                        0
    #define XAVBUF_PATGEN_CRC_G_CRC_G_WIDTH                                        16
    #define XAVBUF_PATGEN_CRC_G_CRC_G_MASK                                         0X0000FFFF

/**
 *  * Register: XAVBUF_PATGEN_CRC_B
 *   */
    #define XAVBUF_PATGEN_CRC_B                                                    0X0000CC18

    #define XAVBUF_PATGEN_CRC_B_CRC_B_SHIFT                                        0
    #define XAVBUF_PATGEN_CRC_B_CRC_B_WIDTH                                        16
    #define XAVBUF_PATGEN_CRC_B_CRC_B_MASK                                         0X0000FFFF

    #define XAVBUF_NUM_SUPPORTED                                                   52

    #define XAVBUF_BUF_4BIT_SF                                                     0x11111
    #define XAVBUF_BUF_5BIT_SF                                                     0x10842
    #define XAVBUF_BUF_6BIT_SF                                                     0x10410
    #define XAVBUF_BUF_8BIT_SF                                                     0x10101
    #define XAVBUF_BUF_10BIT_SF                                                    0x10040
    #define XAVBUF_BUF_12BIT_SF                                                    0x10000

    #define XAVBUF_BUF_6BPC                                                        0x000
    #define XAVBUF_BUF_8BPC                                                        0x001
    #define XAVBUF_BUF_10BPC                                                       0x010
    #define XAVBUF_BUF_12BPC                                                       0x011

    #define XAVBUF_CHBUF_V_BURST_LEN                                               0xF
    #define XAVBUF_CHBUF_A_BURST_LEN                                               0x3

    #define XAVBUF_PL_CLK                                                          0x0
    #define XAVBUF_PS_CLK                                                          0x1

    #define XAVBUF_NUM_SUPPORTED_NLVID                                             25
    #define XAVBUF_NUM_SUPPORTED_NLGFX                                             14
    #define XAVBUF_NUM_SUPPORTED_LIVE                                              14
    #define XAVBUF_NUM_OUTPUT_FORMATS                                              14

/**
 * Address mapping for PLL (CRF and CRL)
 */

/* Base Address for CLOCK in FPD. */
    #define XAVBUF_CLK_FPD_BASEADDR                 0XFD1A0000

/* Base Address for CLOCK in LPD. */
    #define XAVBUF_CLK_LPD_BASEADDR                 0XFF5E0000

/**
 * The following constants define values to manipulate
 * the bits of the VPLL control register.
 */
    #define XAVBUF_PLL_CTRL                         0X00000020

    #define XAVBUF_PLL_CTRL_POST_SRC_SHIFT          24
    #define XAVBUF_PLL_CTRL_POST_SRC_WIDTH          3
    #define XAVBUF_PLL_CTRL_POST_SRC_MASK           0X07000000

    #define XAVBUF_PLL_CTRL_PRE_SRC_SHIFT           20
    #define XAVBUF_VPLL_CTRL_PRE_SRC_WIDTH          3
    #define XAVBUF_VPLL_CTRL_PRE_SRC_MASK           0X00700000

    #define XAVBUF_PLL_CTRL_CLKOUTDIV_SHIFT         17
    #define XAVBUF_PLL_CTRL_CLKOUTDIV_WIDTH         1
    #define XAVBUF_PLL_CTRL_CLKOUTDIV_MASK          0X00020000

    #define XAVBUF_PLL_CTRL_DIV2_SHIFT              16
    #define XAVBUF_PLL_CTRL_DIV2_WIDTH              1
    #define XAVBUF_PLL_CTRL_DIV2_MASK               0X00010000

    #define XAVBUF_PLL_CTRL_FBDIV_SHIFT             8
    #define XAVBUF_PLL_CTRL_FBDIV_WIDTH             7
    #define XAVBUF_PLL_CTRL_FBDIV_MASK              0X00007F00

    #define XAVBUF_PLL_CTRL_BYPASS_SHIFT            3
    #define XAVBUF_PLL_CTRL_BYPASS_WIDTH            1
    #define XAVBUF_PLL_CTRL_BYPASS_MASK             0X00000008

    #define XAVBUF_PLL_CTRL_RESET_SHIFT             0
    #define XAVBUF_PLL_CTRL_RESET_WIDTH             1
    #define XAVBUF_PLL_CTRL_RESET_MASK              0X00000001

/**
 * The following constants define values to manipulate
 * the bits of the PLL config register.
 */
    #define XAVBUF_PLL_CFG                          0X00000024

    #define XAVBUF_PLL_CFG_LOCK_DLY_SHIFT           25
    #define XAVBUF_PLL_CFG_LOCK_DLY_WIDTH           7
    #define XAVBUF_PLL_CFG_LOCK_DLY_MASK            0XFE000000

    #define XAVBUF_PLL_CFG_LOCK_CNT_SHIFT           13
    #define XAVBUF_PLL_CFG_LOCK_CNT_WIDTH           10
    #define XAVBUF_PLL_CFG_LOCK_CNT_MASK            0X007FE000

    #define XAVBUF_PLL_CFG_LFHF_SHIFT               10
    #define XAVBUF_PLL_CFG_LFHF_WIDTH               2
    #define XAVBUF_PLL_CFG_LFHF_MASK                0X00000C00

    #define XAVBUF_PLL_CFG_CP_SHIFT                 5
    #define XAVBUF_PLL_CFG_CP_WIDTH                 4
    #define XAVBUF_PLL_CFG_CP_MASK                  0X000001E0

    #define XAVBUF_PLL_CFG_RES_SHIFT                0
    #define XAVBUF_PLL_CFG_RES_WIDTH                4
    #define XAVBUF_PLL_CFG_RES_MASK                 0X0000000F

/**
 * The following constants define values to manipulate
 * the bits of the VPLL fractional config register.
 */
    #define XAVBUF_PLL_FRAC_CFG                     0X00000028

    #define XAVBUF_PLL_FRAC_CFG_ENABLED_SHIFT       31
    #define XAVBUF_PLL_FRAC_CFG_ENABLED_WIDTH       1
    #define XAVBUF_PLL_FRAC_CFG_ENABLED_MASK        0X80000000

    #define XAVBUF_PLL_FRAC_CFG_SEED_SHIFT          22
    #define XAVBUF_PLL_FRAC_CFG_SEED_WIDTH          3
    #define XAVBUF_PLL_FRAC_CFG_SEED_MASK           0X01C00000

    #define XAVBUF_PLL_FRAC_CFG_ALGRTHM_SHIFT       19
    #define XAVBUF_PLL_FRAC_CFG_ALGRTHM_WIDTH       1
    #define XAVBUF_PLL_FRAC_CFG_ALGRTHM_MASK        0X00080000

    #define XAVBUF_PLL_FRAC_CFG_ORDER_SHIFT         18
    #define XAVBUF_PLL_FRAC_CFG_ORDER_WIDTH         1
    #define XAVBUF_PLL_FRAC_CFG_ORDER_MASK          0X00040000

    #define XAVBUF_PLL_FRAC_CFG_DATA_SHIFT          0
    #define XAVBUF_PLL_FRAC_CFG_DATA_WIDTH          16
    #define XAVBUF_PLL_FRAC_CFG_DATA_MASK           0X0000FFFF

/**
 * The following constants define values to manipulate
 * the bits of the PLL STATUS register.
 */
    #define XAVBUF_PLL_STATUS                       0X00000044

    #define XAVBUF_PLL_STATUS_VPLL_STABLE_SHIFT     5
    #define XAVBUF_PLL_STATUS_VPLL_STABLE_WIDTH     1
    #define XAVBUF_PLL_STATUS_VPLL_STABLE_MASK      0X00000020

    #define XAVBUF_PLL_STATUS_DPLL_STABLE_SHIFT     4
    #define XAVBUF_PLL_STATUS_DPLL_STABLE_WIDTH     1
    #define XAVBUF_PLL_STATUS_DPLL_STABLE_MASK      0X00000010

    #define XAVBUF_PLL_STATUS_APLL_STABLE_SHIFT     3
    #define XAVBUF_PLL_STATUS_APLL_STABLE_WIDTH     1
    #define XAVBUF_PLL_STATUS_APLL_STABLE_MASK      0X00000008

    #define XAVBUF_PLL_STATUS_VPLL_LOCK_SHIFT       2
    #define XAVBUF_PLL_STATUS_VPLL_LOCK_WIDTH       1
    #define XAVBUF_PLL_STATUS_VPLL_LOCK_MASK        0X00000004

    #define XAVBUF_PLL_STATUS_DPLL_LOCK_SHIFT       1
    #define XAVBUF_PLL_STATUS_DPLL_LOCK_WIDTH       1
    #define XAVBUF_PLL_STATUS_DPLL_LOCK_MASK        0X00000002

    #define XAVBUF_PLL_STATUS_APLL_LOCK_SHIFT       0
    #define XAVBUF_PLL_STATUS_APLL_LOCK_WIDTH       1
    #define XAVBUF_PLL_STATUS_APLL_LOCK_MASK        0X00000001

/**
 * The following constants define values to manipulate
 * the bits of the VIDEO reference control register.
 */
    #define XAVBUF_VIDEO_REF_CTRL                   0X00000070

    #define XAVBUF_VIDEO_REF_CTRL_CLKACT_SHIFT      24
    #define XAVBUF_VIDEO_REF_CTRL_CLKACT_WIDTH      1
    #define XAVBUF_VIDEO_REF_CTRL_CLKACT_MASK       0X01000000

    #define XAVBUF_VIDEO_REF_CTRL_DIVISOR1_SHIFT    16
    #define XAVBUF_VIDEO_REF_CTRL_DIVISOR1_WIDTH    6
    #define XAVBUF_VIDEO_REF_CTRL_DIVISOR1_MASK     0X003F0000

    #define XAVBUF_VIDEO_REF_CTRL_DIVISOR0_SHIFT    8
    #define XAVBUF_VIDEO_REF_CTRL_DIVISOR0_WIDTH    6
    #define XAVBUF_VIDEO_REF_CTRL_DIVISOR0_MASK     0X00003F00

    #define XAVBUF_VIDEO_REF_CTRL_SRCSEL_SHIFT      0
    #define XAVBUF_VIDEO_REF_CTRL_SRCSEL_WIDTH      3
    #define XAVBUF_VIDEO_REF_CTRL_SRCSEL_MASK       0X00000007

/**
 * The following constants define values to manipulate
 * the bits of the AUDIO reference control register.
 */
    #define XAVBUF_AUDIO_REF_CTRL                   0X00000074

    #define XAVBUF_AUDIO_REF_CTRL_CLKACT_SHIFT      24
    #define XAVBUF_AUDIO_REF_CTRL_CLKACT_WIDTH      1
    #define XAVBUF_AUDIO_REF_CTRL_CLKACT_MASK       0X01000000

    #define XAVBUF_AUDIO_REF_CTRL_DIVISOR1_SHIFT    16
    #define XAVBUF_AUDIO_REF_CTRL_DIVISOR1_WIDTH    6
    #define XAVBUF_AUDIO_REF_CTRL_DIVISOR1_MASK     0X003F0000

    #define XAVBUF_AUDIO_REF_CTRL_DIVISOR0_SHIFT    8
    #define XAVBUF_AUDIO_REF_CTRL_DIVISOR0_WIDTH    6
    #define XAVBUF_AUDIO_REF_CTRL_DIVISOR0_MASK     0X00003F00

    #define XAVBUF_AUDIO_REF_CTRL_SRCSEL_SHIFT      0
    #define XAVBUF_AUDIO_REF_CTRL_SRCSEL_WIDTH      3
    #define XAVBUF_AUDIO_REF_CTRL_SRCSEL_MASK       0X00000007

/**
 * The following constants define values to manipulate
 * the bits of the Domain Switch register.
 * For eg. FPD to LPD.
 */
    #define XAVBUF_DOMAIN_SWITCH_CTRL               0X00000044

    #define XAVBUF_DOMAIN_SWITCH_DIVISOR0_SHIFT     8
    #define XAVBUF_DOMAIN_SWITCH_DIVISOR0_WIDTH     6
    #define XAVBUF_DOMAIN_SWITCH_DIVISOR0_MASK      0X00003F00

/**
 * The following constants define values to Reference
 * clock.
 */
    #define XAVBUF_Pss_Ref_Clk                      0
    #define XAVBUF_Video_Clk                        4
    #define XAVBUF_Pss_alt_Ref_Clk                  5
    #define XAVBUF_Aux_Ref_clk                      6
    #define XAVBUF_Gt_Crx_Ref_Clk                   7

/**
 * The following constants define values to manipulate
 * the bits of any register.
 */
    #define XAVBUF_ENABLE_BIT                       1
    #define XAVBUF_DISABLE_BIT                      0

/**
 * The following constants define values available
 * PLL source to Audio and Video.
 */
    #define XAVBUF_VPLL_SRC_SEL                     0
    #define XAVBUF_DPLL_SRC_SEL                     2
    #define XAVBUF_RPLL_TO_FPD_SRC_SEL              3

/******************* Macros (Inline Functions) Definitions ********************/

/** @name Register access macro definitions.
 * @{
 */
    #define XAVBuf_In32     Xil_In32
    #define XAVBuf_Out32    Xil_Out32
/* @} */

/******************************************************************************/

/**
 * This is a low-level function that reads from the specified register.
 *
 * @param	BaseAddress is the base address of the device.
 * @param	RegOffset is the register offset to be read from.
 *
 * @return	The 32-bit value of the specified register.
 *
 * @note	C-style signature:
 *		u32 XAVBuf_ReadReg(u32 BaseAddress, u32 RegOffset)
 *
 *******************************************************************************/
    #define XAVBuf_ReadReg( BaseAddress, RegOffset ) \
    XAVBuf_In32( ( BaseAddress ) + ( RegOffset ) )

/******************************************************************************/

/**
 * This is a low-level function that writes to the specified register.
 *
 * @param	BaseAddress is the base address of the device.
 * @param	RegOffset is the register offset to write to.
 * @param	Data is the 32-bit data to write to the specified register.
 *
 * @return	None.
 *
 * @note	C-style signature:
 *		void XAVBuf_WriteReg(u32 BaseAddress, u32 RegOffset, u32 Data)
 *
 *******************************************************************************/
    #define XAVBuf_WriteReg( BaseAddress, RegOffset, Data ) \
    XAVBuf_Out32( ( BaseAddress ) + ( RegOffset ), ( Data ) )


    #ifdef __cplusplus
}
    #endif


#endif //XAVBUF_H_
