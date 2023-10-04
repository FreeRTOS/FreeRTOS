/******************************************************************************
*
* Copyright (C) 2010 - 2017 Xilinx, Inc. All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a
* copy of this software and associated documentation files (the "Software"),
* to deal in the Software without restriction, including without limitation
* the rights to use, copy, modify, merge, publish, distribute, sublicense,
* and/or sell copies of the Software, and to permit persons to whom the
* Software is furnished to do so, subject to the following conditions:
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
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/

/*****************************************************************************/

/**
 *
 * @file xdpdma_hw.h
 *
 * This header file contains identifiers and low-level driver functions (or
 * macros) that can be used to access the device. High-level driver functions
 * are defined in xdpdma.h
 *
 * @note	None.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver	Who   Date     Changes
 * ---- ----- -------- ----------------------------------------------------
 * 1.0  aad   04/12/16 Initial release.
 *
 *****************************************************************************/


#ifndef XDPDMAHW_H_
/* Prevent circular inclusions by using protection macros. */
    #define XDPDMAHW_H_

    #ifdef __cplusplus
    extern "C" {
    #endif

/***************************** Include Files **********************************/

    #include "xil_io.h"

/************************** Constant Definitions ******************************/

/******************************************************************************/

/**
 * Address mapping for the DPDMA.
 */
/******************************************************************************/

/** @name DPDMA registers
 *  @{
 */

    #define XDPDMA_BASEADDR                        0XFD4C0000

/**
 * Register: XDPDMA_ERR_CTRL
 */
    #define XDPDMA_ERR_CTRL                        0X0000

    #define XDPDMA_ERR_CTRL_APB_ERR_RES_SHIFT      0
    #define XDPDMA_ERR_CTRL_APB_ERR_RES_WIDTH      1
    #define XDPDMA_ERR_CTRL_APB_ERR_RES_MASK       0X1

/**
 * Register: XDPDMA_ISR
 */
    #define XDPDMA_ISR                             0X0004

    #define XDPDMA_ISR_VSYNC_INT_SHIFT             27
    #define XDPDMA_ISR_VSYNC_INT_WIDTH             1
    #define XDPDMA_ISR_VSYNC_INT_MASK              0X08000000

    #define XDPDMA_ISR_AXI_RD_4K_CROSS_SHIFT       26
    #define XDPDMA_ISR_AXI_RD_4K_CROSS_WIDTH       1
    #define XDPDMA_ISR_AXI_RD_4K_CROSS_MASK        0X04000000

    #define XDPDMA_ISR_WR_DATA_FIFO_FULL_SHIFT     25
    #define XDPDMA_ISR_WR_DATA_FIFO_FULL_WIDTH     1
    #define XDPDMA_ISR_WR_DATA_FIFO_FULL_MASK      0X02000000

    #define XDPDMA_ISR_WR_CMD_FIFO_FULL_SHIFT      24
    #define XDPDMA_ISR_WR_CMD_FIFO_FULL_WIDTH      1
    #define XDPDMA_ISR_WR_CMD_FIFO_FULL_MASK       0X01000000

    #define XDPDMA_ISR_DSCR_ERR5_SHIFT             23
    #define XDPDMA_ISR_DSCR_ERR5_WIDTH             1
    #define XDPDMA_ISR_DSCR_ERR5_MASK              0X800000

    #define XDPDMA_ISR_DSCR_ERR4_SHIFT             22
    #define XDPDMA_ISR_DSCR_ERR4_WIDTH             1
    #define XDPDMA_ISR_DSCR_ERR4_MASK              0X400000

    #define XDPDMA_ISR_DSCR_ERR3_SHIFT             21
    #define XDPDMA_ISR_DSCR_ERR3_WIDTH             1
    #define XDPDMA_ISR_DSCR_ERR3_MASK              0X200000

    #define XDPDMA_ISR_DSCR_ERR2_SHIFT             20
    #define XDPDMA_ISR_DSCR_ERR2_WIDTH             1
    #define XDPDMA_ISR_DSCR_ERR2_MASK              0X100000

    #define XDPDMA_ISR_DSCR_ERR1_SHIFT             19
    #define XDPDMA_ISR_DSCR_ERR1_WIDTH             1
    #define XDPDMA_ISR_DSCR_ERR1_MASK              0X80000

    #define XDPDMA_ISR_DSCR_ERR0_SHIFT             18
    #define XDPDMA_ISR_DSCR_ERR0_WIDTH             1
    #define XDPDMA_ISR_DSCR_ERR0_MASK              0X40000

    #define XDPDMA_ISR_DATA_AXI_ERR5_SHIFT         17
    #define XDPDMA_ISR_DATA_AXI_ERR5_WIDTH         1
    #define XDPDMA_ISR_DATA_AXI_ERR5_MASK          0X20000

    #define XDPDMA_ISR_DATA_AXI_ERR4_SHIFT         16
    #define XDPDMA_ISR_DATA_AXI_ERR4_WIDTH         1
    #define XDPDMA_ISR_DATA_AXI_ERR4_MASK          0X10000

    #define XDPDMA_ISR_DATA_AXI_ERR3_SHIFT         15
    #define XDPDMA_ISR_DATA_AXI_ERR3_WIDTH         1
    #define XDPDMA_ISR_DATA_AXI_ERR3_MASK          0X8000

    #define XDPDMA_ISR_DATA_AXI_ERR2_SHIFT         14
    #define XDPDMA_ISR_DATA_AXI_ERR2_WIDTH         1
    #define XDPDMA_ISR_DATA_AXI_ERR2_MASK          0X4000

    #define XDPDMA_ISR_DATA_AXI_ERR1_SHIFT         13
    #define XDPDMA_ISR_DATA_AXI_ERR1_WIDTH         1
    #define XDPDMA_ISR_DATA_AXI_ERR1_MASK          0X2000

    #define XDPDMA_ISR_DATA_AXI_ERR0_SHIFT         12
    #define XDPDMA_ISR_DATA_AXI_ERR0_WIDTH         1
    #define XDPDMA_ISR_DATA_AXI_ERR0_MASK          0X1000

    #define XDPDMA_ISR_NO_OSTAND_TRAN5_SHIFT       11
    #define XDPDMA_ISR_NO_OSTAND_TRAN5_WIDTH       1
    #define XDPDMA_ISR_NO_OSTAND_TRAN5_MASK        0X0800

    #define XDPDMA_ISR_NO_OSTAND_TRAN4_SHIFT       10
    #define XDPDMA_ISR_NO_OSTAND_TRAN4_WIDTH       1
    #define XDPDMA_ISR_NO_OSTAND_TRAN4_MASK        0X0400

    #define XDPDMA_ISR_NO_OSTAND_TRAN3_SHIFT       9
    #define XDPDMA_ISR_NO_OSTAND_TRAN3_WIDTH       1
    #define XDPDMA_ISR_NO_OSTAND_TRAN3_MASK        0X0200

    #define XDPDMA_ISR_NO_OSTAND_TRAN2_SHIFT       8
    #define XDPDMA_ISR_NO_OSTAND_TRAN2_WIDTH       1
    #define XDPDMA_ISR_NO_OSTAND_TRAN2_MASK        0X0100

    #define XDPDMA_ISR_NO_OSTAND_TRAN1_SHIFT       7
    #define XDPDMA_ISR_NO_OSTAND_TRAN1_WIDTH       1
    #define XDPDMA_ISR_NO_OSTAND_TRAN1_MASK        0X80

    #define XDPDMA_ISR_NO_OSTAND_TRAN0_SHIFT       6
    #define XDPDMA_ISR_NO_OSTAND_TRAN0_WIDTH       1
    #define XDPDMA_ISR_NO_OSTAND_TRAN0_MASK        0X40

    #define XDPDMA_ISR_DSCR_DONE5_SHIFT            5
    #define XDPDMA_ISR_DSCR_DONE5_WIDTH            1
    #define XDPDMA_ISR_DSCR_DONE5_MASK             0X20

    #define XDPDMA_ISR_DSCR_DONE4_SHIFT            4
    #define XDPDMA_ISR_DSCR_DONE4_WIDTH            1
    #define XDPDMA_ISR_DSCR_DONE4_MASK             0X10

    #define XDPDMA_ISR_DSCR_DONE3_SHIFT            3
    #define XDPDMA_ISR_DSCR_DONE3_WIDTH            1
    #define XDPDMA_ISR_DSCR_DONE3_MASK             0X8

    #define XDPDMA_ISR_DSCR_DONE2_SHIFT            2
    #define XDPDMA_ISR_DSCR_DONE2_WIDTH            1
    #define XDPDMA_ISR_DSCR_DONE2_MASK             0X4

    #define XDPDMA_ISR_DSCR_DONE1_SHIFT            1
    #define XDPDMA_ISR_DSCR_DONE1_WIDTH            1
    #define XDPDMA_ISR_DSCR_DONE1_MASK             0X2

    #define XDPDMA_ISR_DSCR_DONE0_SHIFT            0
    #define XDPDMA_ISR_DSCR_DONE0_WIDTH            1
    #define XDPDMA_ISR_DSCR_DONE0_MASK             0X1

/**
 * Register: XDPDMA_IMR
 */
    #define XDPDMA_IMR                             0X0008

    #define XDPDMA_IMR_VSYNC_INT_SHIFT             27
    #define XDPDMA_IMR_VSYNC_INT_WIDTH             1
    #define XDPDMA_IMR_VSYNC_INT_MASK              0X08000000

    #define XDPDMA_IMR_AXI_RD_4K_CROSS_SHIFT       26
    #define XDPDMA_IMR_AXI_RD_4K_CROSS_WIDTH       1
    #define XDPDMA_IMR_AXI_RD_4K_CROSS_MASK        0X04000000

    #define XDPDMA_IMR_WR_DATA_FIFO_FULL_SHIFT     25
    #define XDPDMA_IMR_WR_DATA_FIFO_FULL_WIDTH     1
    #define XDPDMA_IMR_WR_DATA_FIFO_FULL_MASK      0X02000000

    #define XDPDMA_IMR_WR_CMD_FIFO_FULL_SHIFT      24
    #define XDPDMA_IMR_WR_CMD_FIFO_FULL_WIDTH      1
    #define XDPDMA_IMR_WR_CMD_FIFO_FULL_MASK       0X01000000

    #define XDPDMA_IMR_DSCR_ERR5_SHIFT             23
    #define XDPDMA_IMR_DSCR_ERR5_WIDTH             1
    #define XDPDMA_IMR_DSCR_ERR5_MASK              0X800000

    #define XDPDMA_IMR_DSCR_ERR4_SHIFT             22
    #define XDPDMA_IMR_DSCR_ERR4_WIDTH             1
    #define XDPDMA_IMR_DSCR_ERR4_MASK              0X400000

    #define XDPDMA_IMR_DSCR_ERR3_SHIFT             21
    #define XDPDMA_IMR_DSCR_ERR3_WIDTH             1
    #define XDPDMA_IMR_DSCR_ERR3_MASK              0X200000

    #define XDPDMA_IMR_DSCR_ERR2_SHIFT             20
    #define XDPDMA_IMR_DSCR_ERR2_WIDTH             1
    #define XDPDMA_IMR_DSCR_ERR2_MASK              0X100000

    #define XDPDMA_IMR_DSCR_ERR1_SHIFT             19
    #define XDPDMA_IMR_DSCR_ERR1_WIDTH             1
    #define XDPDMA_IMR_DSCR_ERR1_MASK              0X80000

    #define XDPDMA_IMR_DSCR_ERR0_SHIFT             18
    #define XDPDMA_IMR_DSCR_ERR0_WIDTH             1
    #define XDPDMA_IMR_DSCR_ERR0_MASK              0X40000

    #define XDPDMA_IMR_DATA_AXI_ERR5_SHIFT         17
    #define XDPDMA_IMR_DATA_AXI_ERR5_WIDTH         1
    #define XDPDMA_IMR_DATA_AXI_ERR5_MASK          0X20000

    #define XDPDMA_IMR_DATA_AXI_ERR4_SHIFT         16
    #define XDPDMA_IMR_DATA_AXI_ERR4_WIDTH         1
    #define XDPDMA_IMR_DATA_AXI_ERR4_MASK          0X10000

    #define XDPDMA_IMR_DATA_AXI_ERR3_SHIFT         15
    #define XDPDMA_IMR_DATA_AXI_ERR3_WIDTH         1
    #define XDPDMA_IMR_DATA_AXI_ERR3_MASK          0X8000

    #define XDPDMA_IMR_DATA_AXI_ERR2_SHIFT         14
    #define XDPDMA_IMR_DATA_AXI_ERR2_WIDTH         1
    #define XDPDMA_IMR_DATA_AXI_ERR2_MASK          0X4000

    #define XDPDMA_IMR_DATA_AXI_ERR1_SHIFT         13
    #define XDPDMA_IMR_DATA_AXI_ERR1_WIDTH         1
    #define XDPDMA_IMR_DATA_AXI_ERR1_MASK          0X2000

    #define XDPDMA_IMR_DATA_AXI_ERR0_SHIFT         12
    #define XDPDMA_IMR_DATA_AXI_ERR0_WIDTH         1
    #define XDPDMA_IMR_DATA_AXI_ERR0_MASK          0X1000

    #define XDPDMA_IMR_NO_OSTAND_TRAN5_SHIFT       11
    #define XDPDMA_IMR_NO_OSTAND_TRAN5_WIDTH       1
    #define XDPDMA_IMR_NO_OSTAND_TRAN5_MASK        0X0800

    #define XDPDMA_IMR_NO_OSTAND_TRAN4_SHIFT       10
    #define XDPDMA_IMR_NO_OSTAND_TRAN4_WIDTH       1
    #define XDPDMA_IMR_NO_OSTAND_TRAN4_MASK        0X0400

    #define XDPDMA_IMR_NO_OSTAND_TRAN3_SHIFT       9
    #define XDPDMA_IMR_NO_OSTAND_TRAN3_WIDTH       1
    #define XDPDMA_IMR_NO_OSTAND_TRAN3_MASK        0X0200

    #define XDPDMA_IMR_NO_OSTAND_TRAN2_SHIFT       8
    #define XDPDMA_IMR_NO_OSTAND_TRAN2_WIDTH       1
    #define XDPDMA_IMR_NO_OSTAND_TRAN2_MASK        0X0100

    #define XDPDMA_IMR_NO_OSTAND_TRAN1_SHIFT       7
    #define XDPDMA_IMR_NO_OSTAND_TRAN1_WIDTH       1
    #define XDPDMA_IMR_NO_OSTAND_TRAN1_MASK        0X80

    #define XDPDMA_IMR_NO_OSTAND_TRAN0_SHIFT       6
    #define XDPDMA_IMR_NO_OSTAND_TRAN0_WIDTH       1
    #define XDPDMA_IMR_NO_OSTAND_TRAN0_MASK        0X40

    #define XDPDMA_IMR_DSCR_DONE5_SHIFT            5
    #define XDPDMA_IMR_DSCR_DONE5_WIDTH            1
    #define XDPDMA_IMR_DSCR_DONE5_MASK             0X20

    #define XDPDMA_IMR_DSCR_DONE4_SHIFT            4
    #define XDPDMA_IMR_DSCR_DONE4_WIDTH            1
    #define XDPDMA_IMR_DSCR_DONE4_MASK             0X10

    #define XDPDMA_IMR_DSCR_DONE3_SHIFT            3
    #define XDPDMA_IMR_DSCR_DONE3_WIDTH            1
    #define XDPDMA_IMR_DSCR_DONE3_MASK             0X8

    #define XDPDMA_IMR_DSCR_DONE2_SHIFT            2
    #define XDPDMA_IMR_DSCR_DONE2_WIDTH            1
    #define XDPDMA_IMR_DSCR_DONE2_MASK             0X4

    #define XDPDMA_IMR_DSCR_DONE1_SHIFT            1
    #define XDPDMA_IMR_DSCR_DONE1_WIDTH            1
    #define XDPDMA_IMR_DSCR_DONE1_MASK             0X2

    #define XDPDMA_IMR_DSCR_DONE0_SHIFT            0
    #define XDPDMA_IMR_DSCR_DONE0_WIDTH            1
    #define XDPDMA_IMR_DSCR_DONE0_MASK             0X1

/**
 * Register: XDPDMA_IEN
 */
    #define XDPDMA_IEN                             0X000C

    #define XDPDMA_IEN_VSYNC_INT_SHIFT             27
    #define XDPDMA_IEN_VSYNC_INT_WIDTH             1
    #define XDPDMA_IEN_VSYNC_INT_MASK              0X08000000

    #define XDPDMA_IEN_AXI_RD_4K_CROSS_SHIFT       26
    #define XDPDMA_IEN_AXI_RD_4K_CROSS_WIDTH       1
    #define XDPDMA_IEN_AXI_RD_4K_CROSS_MASK        0X04000000

    #define XDPDMA_IEN_WR_DATA_FIFO_FULL_SHIFT     25
    #define XDPDMA_IEN_WR_DATA_FIFO_FULL_WIDTH     1
    #define XDPDMA_IEN_WR_DATA_FIFO_FULL_MASK      0X02000000

    #define XDPDMA_IEN_WR_CMD_FIFO_FULL_SHIFT      24
    #define XDPDMA_IEN_WR_CMD_FIFO_FULL_WIDTH      1
    #define XDPDMA_IEN_WR_CMD_FIFO_FULL_MASK       0X01000000

    #define XDPDMA_IEN_DSCR_ERR5_SHIFT             23
    #define XDPDMA_IEN_DSCR_ERR5_WIDTH             1
    #define XDPDMA_IEN_DSCR_ERR5_MASK              0X800000

    #define XDPDMA_IEN_DSCR_ERR4_SHIFT             22
    #define XDPDMA_IEN_DSCR_ERR4_WIDTH             1
    #define XDPDMA_IEN_DSCR_ERR4_MASK              0X400000

    #define XDPDMA_IEN_DSCR_ERR3_SHIFT             21
    #define XDPDMA_IEN_DSCR_ERR3_WIDTH             1
    #define XDPDMA_IEN_DSCR_ERR3_MASK              0X200000

    #define XDPDMA_IEN_DSCR_ERR2_SHIFT             20
    #define XDPDMA_IEN_DSCR_ERR2_WIDTH             1
    #define XDPDMA_IEN_DSCR_ERR2_MASK              0X100000

    #define XDPDMA_IEN_DSCR_ERR1_SHIFT             19
    #define XDPDMA_IEN_DSCR_ERR1_WIDTH             1
    #define XDPDMA_IEN_DSCR_ERR1_MASK              0X80000

    #define XDPDMA_IEN_DSCR_ERR0_SHIFT             18
    #define XDPDMA_IEN_DSCR_ERR0_WIDTH             1
    #define XDPDMA_IEN_DSCR_ERR0_MASK              0X40000

    #define XDPDMA_IEN_DATA_AXI_ERR5_SHIFT         17
    #define XDPDMA_IEN_DATA_AXI_ERR5_WIDTH         1
    #define XDPDMA_IEN_DATA_AXI_ERR5_MASK          0X20000

    #define XDPDMA_IEN_DATA_AXI_ERR4_SHIFT         16
    #define XDPDMA_IEN_DATA_AXI_ERR4_WIDTH         1
    #define XDPDMA_IEN_DATA_AXI_ERR4_MASK          0X10000

    #define XDPDMA_IEN_DATA_AXI_ERR3_SHIFT         15
    #define XDPDMA_IEN_DATA_AXI_ERR3_WIDTH         1
    #define XDPDMA_IEN_DATA_AXI_ERR3_MASK          0X8000

    #define XDPDMA_IEN_DATA_AXI_ERR2_SHIFT         14
    #define XDPDMA_IEN_DATA_AXI_ERR2_WIDTH         1
    #define XDPDMA_IEN_DATA_AXI_ERR2_MASK          0X4000

    #define XDPDMA_IEN_DATA_AXI_ERR1_SHIFT         13
    #define XDPDMA_IEN_DATA_AXI_ERR1_WIDTH         1
    #define XDPDMA_IEN_DATA_AXI_ERR1_MASK          0X2000

    #define XDPDMA_IEN_DATA_AXI_ERR0_SHIFT         12
    #define XDPDMA_IEN_DATA_AXI_ERR0_WIDTH         1
    #define XDPDMA_IEN_DATA_AXI_ERR0_MASK          0X1000

    #define XDPDMA_IEN_NO_OSTAND_TRAN5_SHIFT       11
    #define XDPDMA_IEN_NO_OSTAND_TRAN5_WIDTH       1
    #define XDPDMA_IEN_NO_OSTAND_TRAN5_MASK        0X0800

    #define XDPDMA_IEN_NO_OSTAND_TRAN4_SHIFT       10
    #define XDPDMA_IEN_NO_OSTAND_TRAN4_WIDTH       1
    #define XDPDMA_IEN_NO_OSTAND_TRAN4_MASK        0X0400

    #define XDPDMA_IEN_NO_OSTAND_TRAN3_SHIFT       9
    #define XDPDMA_IEN_NO_OSTAND_TRAN3_WIDTH       1
    #define XDPDMA_IEN_NO_OSTAND_TRAN3_MASK        0X0200

    #define XDPDMA_IEN_NO_OSTAND_TRAN2_SHIFT       8
    #define XDPDMA_IEN_NO_OSTAND_TRAN2_WIDTH       1
    #define XDPDMA_IEN_NO_OSTAND_TRAN2_MASK        0X0100

    #define XDPDMA_IEN_NO_OSTAND_TRAN1_SHIFT       7
    #define XDPDMA_IEN_NO_OSTAND_TRAN1_WIDTH       1
    #define XDPDMA_IEN_NO_OSTAND_TRAN1_MASK        0X80

    #define XDPDMA_IEN_NO_OSTAND_TRAN0_SHIFT       6
    #define XDPDMA_IEN_NO_OSTAND_TRAN0_WIDTH       1
    #define XDPDMA_IEN_NO_OSTAND_TRAN0_MASK        0X40

    #define XDPDMA_IEN_DSCR_DONE5_SHIFT            5
    #define XDPDMA_IEN_DSCR_DONE5_WIDTH            1
    #define XDPDMA_IEN_DSCR_DONE5_MASK             0X20

    #define XDPDMA_IEN_DSCR_DONE4_SHIFT            4
    #define XDPDMA_IEN_DSCR_DONE4_WIDTH            1
    #define XDPDMA_IEN_DSCR_DONE4_MASK             0X10

    #define XDPDMA_IEN_DSCR_DONE3_SHIFT            3
    #define XDPDMA_IEN_DSCR_DONE3_WIDTH            1
    #define XDPDMA_IEN_DSCR_DONE3_MASK             0X8

    #define XDPDMA_IEN_DSCR_DONE2_SHIFT            2
    #define XDPDMA_IEN_DSCR_DONE2_WIDTH            1
    #define XDPDMA_IEN_DSCR_DONE2_MASK             0X4

    #define XDPDMA_IEN_DSCR_DONE1_SHIFT            1
    #define XDPDMA_IEN_DSCR_DONE1_WIDTH            1
    #define XDPDMA_IEN_DSCR_DONE1_MASK             0X2

    #define XDPDMA_IEN_DSCR_DONE0_SHIFT            0
    #define XDPDMA_IEN_DSCR_DONE0_WIDTH            1
    #define XDPDMA_IEN_DSCR_DONE0_MASK             0X1

/**
 * Register: XDPDMA_IDS
 */
    #define XDPDMA_IDS                             0X0010

    #define XDPDMA_IDS_VSYNC_INT_SHIFT             27
    #define XDPDMA_IDS_VSYNC_INT_WIDTH             1
    #define XDPDMA_IDS_VSYNC_INT_MASK              0X08000000

    #define XDPDMA_IDS_AXI_RD_4K_CROSS_SHIFT       26
    #define XDPDMA_IDS_AXI_RD_4K_CROSS_WIDTH       1
    #define XDPDMA_IDS_AXI_RD_4K_CROSS_MASK        0X04000000

    #define XDPDMA_IDS_WR_DATA_FIFO_FULL_SHIFT     25
    #define XDPDMA_IDS_WR_DATA_FIFO_FULL_WIDTH     1
    #define XDPDMA_IDS_WR_DATA_FIFO_FULL_MASK      0X02000000

    #define XDPDMA_IDS_WR_CMD_FIFO_FULL_SHIFT      24
    #define XDPDMA_IDS_WR_CMD_FIFO_FULL_WIDTH      1
    #define XDPDMA_IDS_WR_CMD_FIFO_FULL_MASK       0X01000000

    #define XDPDMA_IDS_DSCR_ERR5_SHIFT             23
    #define XDPDMA_IDS_DSCR_ERR5_WIDTH             1
    #define XDPDMA_IDS_DSCR_ERR5_MASK              0X800000

    #define XDPDMA_IDS_DSCR_ERR4_SHIFT             22
    #define XDPDMA_IDS_DSCR_ERR4_WIDTH             1
    #define XDPDMA_IDS_DSCR_ERR4_MASK              0X400000

    #define XDPDMA_IDS_DSCR_ERR3_SHIFT             21
    #define XDPDMA_IDS_DSCR_ERR3_WIDTH             1
    #define XDPDMA_IDS_DSCR_ERR3_MASK              0X200000

    #define XDPDMA_IDS_DSCR_ERR2_SHIFT             20
    #define XDPDMA_IDS_DSCR_ERR2_WIDTH             1
    #define XDPDMA_IDS_DSCR_ERR2_MASK              0X100000

    #define XDPDMA_IDS_DSCR_ERR1_SHIFT             19
    #define XDPDMA_IDS_DSCR_ERR1_WIDTH             1
    #define XDPDMA_IDS_DSCR_ERR1_MASK              0X80000

    #define XDPDMA_IDS_DSCR_ERR0_SHIFT             18
    #define XDPDMA_IDS_DSCR_ERR0_WIDTH             1
    #define XDPDMA_IDS_DSCR_ERR0_MASK              0X40000

    #define XDPDMA_IDS_DATA_AXI_ERR5_SHIFT         17
    #define XDPDMA_IDS_DATA_AXI_ERR5_WIDTH         1
    #define XDPDMA_IDS_DATA_AXI_ERR5_MASK          0X20000

    #define XDPDMA_IDS_DATA_AXI_ERR4_SHIFT         16
    #define XDPDMA_IDS_DATA_AXI_ERR4_WIDTH         1
    #define XDPDMA_IDS_DATA_AXI_ERR4_MASK          0X10000

    #define XDPDMA_IDS_DATA_AXI_ERR3_SHIFT         15
    #define XDPDMA_IDS_DATA_AXI_ERR3_WIDTH         1
    #define XDPDMA_IDS_DATA_AXI_ERR3_MASK          0X8000

    #define XDPDMA_IDS_DATA_AXI_ERR2_SHIFT         14
    #define XDPDMA_IDS_DATA_AXI_ERR2_WIDTH         1
    #define XDPDMA_IDS_DATA_AXI_ERR2_MASK          0X4000

    #define XDPDMA_IDS_DATA_AXI_ERR1_SHIFT         13
    #define XDPDMA_IDS_DATA_AXI_ERR1_WIDTH         1
    #define XDPDMA_IDS_DATA_AXI_ERR1_MASK          0X2000

    #define XDPDMA_IDS_DATA_AXI_ERR0_SHIFT         12
    #define XDPDMA_IDS_DATA_AXI_ERR0_WIDTH         1
    #define XDPDMA_IDS_DATA_AXI_ERR0_MASK          0X1000

    #define XDPDMA_IDS_NO_OSTAND_TRAN5_SHIFT       11
    #define XDPDMA_IDS_NO_OSTAND_TRAN5_WIDTH       1
    #define XDPDMA_IDS_NO_OSTAND_TRAN5_MASK        0X0800

    #define XDPDMA_IDS_NO_OSTAND_TRAN4_SHIFT       10
    #define XDPDMA_IDS_NO_OSTAND_TRAN4_WIDTH       1
    #define XDPDMA_IDS_NO_OSTAND_TRAN4_MASK        0X0400

    #define XDPDMA_IDS_NO_OSTAND_TRAN3_SHIFT       9
    #define XDPDMA_IDS_NO_OSTAND_TRAN3_WIDTH       1
    #define XDPDMA_IDS_NO_OSTAND_TRAN3_MASK        0X0200

    #define XDPDMA_IDS_NO_OSTAND_TRAN2_SHIFT       8
    #define XDPDMA_IDS_NO_OSTAND_TRAN2_WIDTH       1
    #define XDPDMA_IDS_NO_OSTAND_TRAN2_MASK        0X0100

    #define XDPDMA_IDS_NO_OSTAND_TRAN1_SHIFT       7
    #define XDPDMA_IDS_NO_OSTAND_TRAN1_WIDTH       1
    #define XDPDMA_IDS_NO_OSTAND_TRAN1_MASK        0X80

    #define XDPDMA_IDS_NO_OSTAND_TRAN0_SHIFT       6
    #define XDPDMA_IDS_NO_OSTAND_TRAN0_WIDTH       1
    #define XDPDMA_IDS_NO_OSTAND_TRAN0_MASK        0X40

    #define XDPDMA_IDS_DSCR_DONE5_SHIFT            5
    #define XDPDMA_IDS_DSCR_DONE5_WIDTH            1
    #define XDPDMA_IDS_DSCR_DONE5_MASK             0X20

    #define XDPDMA_IDS_DSCR_DONE4_SHIFT            4
    #define XDPDMA_IDS_DSCR_DONE4_WIDTH            1
    #define XDPDMA_IDS_DSCR_DONE4_MASK             0X10

    #define XDPDMA_IDS_DSCR_DONE3_SHIFT            3
    #define XDPDMA_IDS_DSCR_DONE3_WIDTH            1
    #define XDPDMA_IDS_DSCR_DONE3_MASK             0X8

    #define XDPDMA_IDS_DSCR_DONE2_SHIFT            2
    #define XDPDMA_IDS_DSCR_DONE2_WIDTH            1
    #define XDPDMA_IDS_DSCR_DONE2_MASK             0X4

    #define XDPDMA_IDS_DSCR_DONE1_SHIFT            1
    #define XDPDMA_IDS_DSCR_DONE1_WIDTH            1
    #define XDPDMA_IDS_DSCR_DONE1_MASK             0X2

    #define XDPDMA_IDS_DSCR_DONE0_SHIFT            0
    #define XDPDMA_IDS_DSCR_DONE0_WIDTH            1
    #define XDPDMA_IDS_DSCR_DONE0_MASK             0X1

/**
 * Register: XDPDMA_EISR
 */
    #define XDPDMA_EISR                            0X0014

    #define XDPDMA_EISR_RD_CMD_FIFO_FULL_SHIFT     31
    #define XDPDMA_EISR_RD_CMD_FIFO_FULL_WIDTH     1
    #define XDPDMA_EISR_RD_CMD_FIFO_FULL_MASK      0X80000000

    #define XDPDMA_EISR_DSCR_DONE_ERR5_SHIFT       30
    #define XDPDMA_EISR_DSCR_DONE_ERR5_WIDTH       1
    #define XDPDMA_EISR_DSCR_DONE_ERR5_MASK        0X40000000

    #define XDPDMA_EISR_DSCR_DONE_ERR4_SHIFT       29
    #define XDPDMA_EISR_DSCR_DONE_ERR4_WIDTH       1
    #define XDPDMA_EISR_DSCR_DONE_ERR4_MASK        0X20000000

    #define XDPDMA_EISR_DSCR_DONE_ERR3_SHIFT       28
    #define XDPDMA_EISR_DSCR_DONE_ERR3_WIDTH       1
    #define XDPDMA_EISR_DSCR_DONE_ERR3_MASK        0X10000000

    #define XDPDMA_EISR_DSCR_DONE_ERR2_SHIFT       27
    #define XDPDMA_EISR_DSCR_DONE_ERR2_WIDTH       1
    #define XDPDMA_EISR_DSCR_DONE_ERR2_MASK        0X08000000

    #define XDPDMA_EISR_DSCR_DONE_ERR1_SHIFT       26
    #define XDPDMA_EISR_DSCR_DONE_ERR1_WIDTH       1
    #define XDPDMA_EISR_DSCR_DONE_ERR1_MASK        0X04000000

    #define XDPDMA_EISR_DSCR_DONE_ERR0_SHIFT       25
    #define XDPDMA_EISR_DSCR_DONE_ERR0_WIDTH       1
    #define XDPDMA_EISR_DSCR_DONE_ERR0_MASK        0X02000000

    #define XDPDMA_EISR_DSCR_WR_AXI_ERR5_SHIFT     24
    #define XDPDMA_EISR_DSCR_WR_AXI_ERR5_WIDTH     1
    #define XDPDMA_EISR_DSCR_WR_AXI_ERR5_MASK      0X01000000

    #define XDPDMA_EISR_DSCR_WR_AXI_ERR4_SHIFT     23
    #define XDPDMA_EISR_DSCR_WR_AXI_ERR4_WIDTH     1
    #define XDPDMA_EISR_DSCR_WR_AXI_ERR4_MASK      0X800000

    #define XDPDMA_EISR_DSCR_WR_AXI_ERR3_SHIFT     22
    #define XDPDMA_EISR_DSCR_WR_AXI_ERR3_WIDTH     1
    #define XDPDMA_EISR_DSCR_WR_AXI_ERR3_MASK      0X400000

    #define XDPDMA_EISR_DSCR_WR_AXI_ERR2_SHIFT     21
    #define XDPDMA_EISR_DSCR_WR_AXI_ERR2_WIDTH     1
    #define XDPDMA_EISR_DSCR_WR_AXI_ERR2_MASK      0X200000

    #define XDPDMA_EISR_DSCR_WR_AXI_ERR1_SHIFT     20
    #define XDPDMA_EISR_DSCR_WR_AXI_ERR1_WIDTH     1
    #define XDPDMA_EISR_DSCR_WR_AXI_ERR1_MASK      0X100000

    #define XDPDMA_EISR_DSCR_WR_AXI_ERR0_SHIFT     19
    #define XDPDMA_EISR_DSCR_WR_AXI_ERR0_WIDTH     1
    #define XDPDMA_EISR_DSCR_WR_AXI_ERR0_MASK      0X80000

    #define XDPDMA_EISR_DSCR_CRC_ERR5_SHIFT        18
    #define XDPDMA_EISR_DSCR_CRC_ERR5_WIDTH        1
    #define XDPDMA_EISR_DSCR_CRC_ERR5_MASK         0X40000

    #define XDPDMA_EISR_DSCR_CRC_ERR4_SHIFT        17
    #define XDPDMA_EISR_DSCR_CRC_ERR4_WIDTH        1
    #define XDPDMA_EISR_DSCR_CRC_ERR4_MASK         0X20000

    #define XDPDMA_EISR_DSCR_CRC_ERR3_SHIFT        16
    #define XDPDMA_EISR_DSCR_CRC_ERR3_WIDTH        1
    #define XDPDMA_EISR_DSCR_CRC_ERR3_MASK         0X10000

    #define XDPDMA_EISR_DSCR_CRC_ERR2_SHIFT        15
    #define XDPDMA_EISR_DSCR_CRC_ERR2_WIDTH        1
    #define XDPDMA_EISR_DSCR_CRC_ERR2_MASK         0X8000

    #define XDPDMA_EISR_DSCR_CRC_ERR1_SHIFT        14
    #define XDPDMA_EISR_DSCR_CRC_ERR1_WIDTH        1
    #define XDPDMA_EISR_DSCR_CRC_ERR1_MASK         0X4000

    #define XDPDMA_EISR_DSCR_CRC_ERR0_SHIFT        13
    #define XDPDMA_EISR_DSCR_CRC_ERR0_WIDTH        1
    #define XDPDMA_EISR_DSCR_CRC_ERR0_MASK         0X2000

    #define XDPDMA_EISR_DSCR_PRE_ERR5_SHIFT        12
    #define XDPDMA_EISR_DSCR_PRE_ERR5_WIDTH        1
    #define XDPDMA_EISR_DSCR_PRE_ERR5_MASK         0X1000

    #define XDPDMA_EISR_DSCR_PRE_ERR4_SHIFT        11
    #define XDPDMA_EISR_DSCR_PRE_ERR4_WIDTH        1
    #define XDPDMA_EISR_DSCR_PRE_ERR4_MASK         0X0800

    #define XDPDMA_EISR_DSCR_PRE_ERR3_SHIFT        10
    #define XDPDMA_EISR_DSCR_PRE_ERR3_WIDTH        1
    #define XDPDMA_EISR_DSCR_PRE_ERR3_MASK         0X0400

    #define XDPDMA_EISR_DSCR_PRE_ERR2_SHIFT        9
    #define XDPDMA_EISR_DSCR_PRE_ERR2_WIDTH        1
    #define XDPDMA_EISR_DSCR_PRE_ERR2_MASK         0X0200

    #define XDPDMA_EISR_DSCR_PRE_ERR1_SHIFT        8
    #define XDPDMA_EISR_DSCR_PRE_ERR1_WIDTH        1
    #define XDPDMA_EISR_DSCR_PRE_ERR1_MASK         0X0100

    #define XDPDMA_EISR_DSCR_PRE_ERR0_SHIFT        7
    #define XDPDMA_EISR_DSCR_PRE_ERR0_WIDTH        1
    #define XDPDMA_EISR_DSCR_PRE_ERR0_MASK         0X80

    #define XDPDMA_EISR_DSCR_RD_AXI_ERR5_SHIFT     6
    #define XDPDMA_EISR_DSCR_RD_AXI_ERR5_WIDTH     1
    #define XDPDMA_EISR_DSCR_RD_AXI_ERR5_MASK      0X40

    #define XDPDMA_EISR_DSCR_RD_AXI_ERR4_SHIFT     5
    #define XDPDMA_EISR_DSCR_RD_AXI_ERR4_WIDTH     1
    #define XDPDMA_EISR_DSCR_RD_AXI_ERR4_MASK      0X20

    #define XDPDMA_EISR_DSCR_RD_AXI_ERR3_SHIFT     4
    #define XDPDMA_EISR_DSCR_RD_AXI_ERR3_WIDTH     1
    #define XDPDMA_EISR_DSCR_RD_AXI_ERR3_MASK      0X10

    #define XDPDMA_EISR_DSCR_RD_AXI_ERR2_SHIFT     3
    #define XDPDMA_EISR_DSCR_RD_AXI_ERR2_WIDTH     1
    #define XDPDMA_EISR_DSCR_RD_AXI_ERR2_MASK      0X8

    #define XDPDMA_EISR_DSCR_RD_AXI_ERR1_SHIFT     2
    #define XDPDMA_EISR_DSCR_RD_AXI_ERR1_WIDTH     1
    #define XDPDMA_EISR_DSCR_RD_AXI_ERR1_MASK      0X4

    #define XDPDMA_EISR_DSCR_RD_AXI_ERR0_SHIFT     1
    #define XDPDMA_EISR_DSCR_RD_AXI_ERR0_WIDTH     1
    #define XDPDMA_EISR_DSCR_RD_AXI_ERR0_MASK      0X2

    #define XDPDMA_EISR_INV_APB_SHIFT              0
    #define XDPDMA_EISR_INV_APB_WIDTH              1
    #define XDPDMA_EISR_INV_APB_MASK               0X1

/**
 * Register: XDPDMA_EIMR
 */
    #define XDPDMA_EIMR                            0X0018

    #define XDPDMA_EIMR_RD_CMD_FIFO_FULL_SHIFT     31
    #define XDPDMA_EIMR_RD_CMD_FIFO_FULL_WIDTH     1
    #define XDPDMA_EIMR_RD_CMD_FIFO_FULL_MASK      0X80000000

    #define XDPDMA_EIMR_DSCR_DONE_ERR5_SHIFT       30
    #define XDPDMA_EIMR_DSCR_DONE_ERR5_WIDTH       1
    #define XDPDMA_EIMR_DSCR_DONE_ERR5_MASK        0X40000000

    #define XDPDMA_EIMR_DSCR_DONE_ERR4_SHIFT       29
    #define XDPDMA_EIMR_DSCR_DONE_ERR4_WIDTH       1
    #define XDPDMA_EIMR_DSCR_DONE_ERR4_MASK        0X20000000

    #define XDPDMA_EIMR_DSCR_DONE_ERR3_SHIFT       28
    #define XDPDMA_EIMR_DSCR_DONE_ERR3_WIDTH       1
    #define XDPDMA_EIMR_DSCR_DONE_ERR3_MASK        0X10000000

    #define XDPDMA_EIMR_DSCR_DONE_ERR2_SHIFT       27
    #define XDPDMA_EIMR_DSCR_DONE_ERR2_WIDTH       1
    #define XDPDMA_EIMR_DSCR_DONE_ERR2_MASK        0X08000000

    #define XDPDMA_EIMR_DSCR_DONE_ERR1_SHIFT       26
    #define XDPDMA_EIMR_DSCR_DONE_ERR1_WIDTH       1
    #define XDPDMA_EIMR_DSCR_DONE_ERR1_MASK        0X04000000

    #define XDPDMA_EIMR_DSCR_DONE_ERR0_SHIFT       25
    #define XDPDMA_EIMR_DSCR_DONE_ERR0_WIDTH       1
    #define XDPDMA_EIMR_DSCR_DONE_ERR0_MASK        0X02000000

    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR5_SHIFT     24
    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR5_WIDTH     1
    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR5_MASK      0X01000000

    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR4_SHIFT     23
    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR4_WIDTH     1
    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR4_MASK      0X800000

    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR3_SHIFT     22
    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR3_WIDTH     1
    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR3_MASK      0X400000

    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR2_SHIFT     21
    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR2_WIDTH     1
    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR2_MASK      0X200000

    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR1_SHIFT     20
    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR1_WIDTH     1
    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR1_MASK      0X100000

    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR0_SHIFT     19
    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR0_WIDTH     1
    #define XDPDMA_EIMR_DSCR_WR_AXI_ERR0_MASK      0X80000

    #define XDPDMA_EIMR_DSCR_CRC_ERR5_SHIFT        18
    #define XDPDMA_EIMR_DSCR_CRC_ERR5_WIDTH        1
    #define XDPDMA_EIMR_DSCR_CRC_ERR5_MASK         0X40000

    #define XDPDMA_EIMR_DSCR_CRC_ERR4_SHIFT        17
    #define XDPDMA_EIMR_DSCR_CRC_ERR4_WIDTH        1
    #define XDPDMA_EIMR_DSCR_CRC_ERR4_MASK         0X20000

    #define XDPDMA_EIMR_DSCR_CRC_ERR3_SHIFT        16
    #define XDPDMA_EIMR_DSCR_CRC_ERR3_WIDTH        1
    #define XDPDMA_EIMR_DSCR_CRC_ERR3_MASK         0X10000

    #define XDPDMA_EIMR_DSCR_CRC_ERR2_SHIFT        15
    #define XDPDMA_EIMR_DSCR_CRC_ERR2_WIDTH        1
    #define XDPDMA_EIMR_DSCR_CRC_ERR2_MASK         0X8000

    #define XDPDMA_EIMR_DSCR_CRC_ERR1_SHIFT        14
    #define XDPDMA_EIMR_DSCR_CRC_ERR1_WIDTH        1
    #define XDPDMA_EIMR_DSCR_CRC_ERR1_MASK         0X4000

    #define XDPDMA_EIMR_DSCR_CRC_ERR0_SHIFT        13
    #define XDPDMA_EIMR_DSCR_CRC_ERR0_WIDTH        1
    #define XDPDMA_EIMR_DSCR_CRC_ERR0_MASK         0X2000

    #define XDPDMA_EIMR_DSCR_PRE_ERR5_SHIFT        12
    #define XDPDMA_EIMR_DSCR_PRE_ERR5_WIDTH        1
    #define XDPDMA_EIMR_DSCR_PRE_ERR5_MASK         0X1000

    #define XDPDMA_EIMR_DSCR_PRE_ERR4_SHIFT        11
    #define XDPDMA_EIMR_DSCR_PRE_ERR4_WIDTH        1
    #define XDPDMA_EIMR_DSCR_PRE_ERR4_MASK         0X0800

    #define XDPDMA_EIMR_DSCR_PRE_ERR3_SHIFT        10
    #define XDPDMA_EIMR_DSCR_PRE_ERR3_WIDTH        1
    #define XDPDMA_EIMR_DSCR_PRE_ERR3_MASK         0X0400

    #define XDPDMA_EIMR_DSCR_PRE_ERR2_SHIFT        9
    #define XDPDMA_EIMR_DSCR_PRE_ERR2_WIDTH        1
    #define XDPDMA_EIMR_DSCR_PRE_ERR2_MASK         0X0200

    #define XDPDMA_EIMR_DSCR_PRE_ERR1_SHIFT        8
    #define XDPDMA_EIMR_DSCR_PRE_ERR1_WIDTH        1
    #define XDPDMA_EIMR_DSCR_PRE_ERR1_MASK         0X0100

    #define XDPDMA_EIMR_DSCR_PRE_ERR0_SHIFT        7
    #define XDPDMA_EIMR_DSCR_PRE_ERR0_WIDTH        1
    #define XDPDMA_EIMR_DSCR_PRE_ERR0_MASK         0X80

    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR5_SHIFT     6
    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR5_WIDTH     1
    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR5_MASK      0X40

    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR4_SHIFT     5
    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR4_WIDTH     1
    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR4_MASK      0X20

    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR3_SHIFT     4
    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR3_WIDTH     1
    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR3_MASK      0X10

    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR2_SHIFT     3
    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR2_WIDTH     1
    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR2_MASK      0X8

    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR1_SHIFT     2
    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR1_WIDTH     1
    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR1_MASK      0X4

    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR0_SHIFT     1
    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR0_WIDTH     1
    #define XDPDMA_EIMR_DSCR_RD_AXI_ERR0_MASK      0X2

    #define XDPDMA_EIMR_INV_APB_SHIFT              0
    #define XDPDMA_EIMR_INV_APB_WIDTH              1
    #define XDPDMA_EIMR_INV_APB_MASK               0X1

/**
 * Register: XDPDMA_EIEN
 */
    #define XDPDMA_EIEN                            0X001C

    #define XDPDMA_EIEN_RD_CMD_FIFO_FULL_SHIFT     31
    #define XDPDMA_EIEN_RD_CMD_FIFO_FULL_WIDTH     1
    #define XDPDMA_EIEN_RD_CMD_FIFO_FULL_MASK      0X80000000

    #define XDPDMA_EIEN_DSCR_DONE_ERR5_SHIFT       30
    #define XDPDMA_EIEN_DSCR_DONE_ERR5_WIDTH       1
    #define XDPDMA_EIEN_DSCR_DONE_ERR5_MASK        0X40000000

    #define XDPDMA_EIEN_DSCR_DONE_ERR4_SHIFT       29
    #define XDPDMA_EIEN_DSCR_DONE_ERR4_WIDTH       1
    #define XDPDMA_EIEN_DSCR_DONE_ERR4_MASK        0X20000000

    #define XDPDMA_EIEN_DSCR_DONE_ERR3_SHIFT       28
    #define XDPDMA_EIEN_DSCR_DONE_ERR3_WIDTH       1
    #define XDPDMA_EIEN_DSCR_DONE_ERR3_MASK        0X10000000

    #define XDPDMA_EIEN_DSCR_DONE_ERR2_SHIFT       27
    #define XDPDMA_EIEN_DSCR_DONE_ERR2_WIDTH       1
    #define XDPDMA_EIEN_DSCR_DONE_ERR2_MASK        0X08000000

    #define XDPDMA_EIEN_DSCR_DONE_ERR1_SHIFT       26
    #define XDPDMA_EIEN_DSCR_DONE_ERR1_WIDTH       1
    #define XDPDMA_EIEN_DSCR_DONE_ERR1_MASK        0X04000000

    #define XDPDMA_EIEN_DSCR_DONE_ERR0_SHIFT       25
    #define XDPDMA_EIEN_DSCR_DONE_ERR0_WIDTH       1
    #define XDPDMA_EIEN_DSCR_DONE_ERR0_MASK        0X02000000

    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR5_SHIFT     24
    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR5_WIDTH     1
    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR5_MASK      0X01000000

    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR4_SHIFT     23
    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR4_WIDTH     1
    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR4_MASK      0X800000

    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR3_SHIFT     22
    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR3_WIDTH     1
    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR3_MASK      0X400000

    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR2_SHIFT     21
    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR2_WIDTH     1
    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR2_MASK      0X200000

    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR1_SHIFT     20
    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR1_WIDTH     1
    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR1_MASK      0X100000

    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR0_SHIFT     19
    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR0_WIDTH     1
    #define XDPDMA_EIEN_DSCR_WR_AXI_ERR0_MASK      0X80000

    #define XDPDMA_EIEN_DSCR_CRC_ERR5_SHIFT        18
    #define XDPDMA_EIEN_DSCR_CRC_ERR5_WIDTH        1
    #define XDPDMA_EIEN_DSCR_CRC_ERR5_MASK         0X40000

    #define XDPDMA_EIEN_DSCR_CRC_ERR4_SHIFT        17
    #define XDPDMA_EIEN_DSCR_CRC_ERR4_WIDTH        1
    #define XDPDMA_EIEN_DSCR_CRC_ERR4_MASK         0X20000

    #define XDPDMA_EIEN_DSCR_CRC_ERR3_SHIFT        16
    #define XDPDMA_EIEN_DSCR_CRC_ERR3_WIDTH        1
    #define XDPDMA_EIEN_DSCR_CRC_ERR3_MASK         0X10000

    #define XDPDMA_EIEN_DSCR_CRC_ERR2_SHIFT        15
    #define XDPDMA_EIEN_DSCR_CRC_ERR2_WIDTH        1
    #define XDPDMA_EIEN_DSCR_CRC_ERR2_MASK         0X8000

    #define XDPDMA_EIEN_DSCR_CRC_ERR1_SHIFT        14
    #define XDPDMA_EIEN_DSCR_CRC_ERR1_WIDTH        1
    #define XDPDMA_EIEN_DSCR_CRC_ERR1_MASK         0X4000

    #define XDPDMA_EIEN_DSCR_CRC_ERR0_SHIFT        13
    #define XDPDMA_EIEN_DSCR_CRC_ERR0_WIDTH        1
    #define XDPDMA_EIEN_DSCR_CRC_ERR0_MASK         0X2000

    #define XDPDMA_EIEN_DSCR_PRE_ERR5_SHIFT        12
    #define XDPDMA_EIEN_DSCR_PRE_ERR5_WIDTH        1
    #define XDPDMA_EIEN_DSCR_PRE_ERR5_MASK         0X1000

    #define XDPDMA_EIEN_DSCR_PRE_ERR4_SHIFT        11
    #define XDPDMA_EIEN_DSCR_PRE_ERR4_WIDTH        1
    #define XDPDMA_EIEN_DSCR_PRE_ERR4_MASK         0X0800

    #define XDPDMA_EIEN_DSCR_PRE_ERR3_SHIFT        10
    #define XDPDMA_EIEN_DSCR_PRE_ERR3_WIDTH        1
    #define XDPDMA_EIEN_DSCR_PRE_ERR3_MASK         0X0400

    #define XDPDMA_EIEN_DSCR_PRE_ERR2_SHIFT        9
    #define XDPDMA_EIEN_DSCR_PRE_ERR2_WIDTH        1
    #define XDPDMA_EIEN_DSCR_PRE_ERR2_MASK         0X0200

    #define XDPDMA_EIEN_DSCR_PRE_ERR1_SHIFT        8
    #define XDPDMA_EIEN_DSCR_PRE_ERR1_WIDTH        1
    #define XDPDMA_EIEN_DSCR_PRE_ERR1_MASK         0X0100

    #define XDPDMA_EIEN_DSCR_PRE_ERR0_SHIFT        7
    #define XDPDMA_EIEN_DSCR_PRE_ERR0_WIDTH        1
    #define XDPDMA_EIEN_DSCR_PRE_ERR0_MASK         0X80

    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR5_SHIFT     6
    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR5_WIDTH     1
    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR5_MASK      0X40

    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR4_SHIFT     5
    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR4_WIDTH     1
    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR4_MASK      0X20

    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR3_SHIFT     4
    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR3_WIDTH     1
    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR3_MASK      0X10

    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR2_SHIFT     3
    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR2_WIDTH     1
    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR2_MASK      0X8

    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR1_SHIFT     2
    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR1_WIDTH     1
    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR1_MASK      0X4

    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR0_SHIFT     1
    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR0_WIDTH     1
    #define XDPDMA_EIEN_DSCR_RD_AXI_ERR0_MASK      0X2

    #define XDPDMA_EIEN_INV_APB_SHIFT              0
    #define XDPDMA_EIEN_INV_APB_WIDTH              1
    #define XDPDMA_EIEN_INV_APB_MASK               0X1

/**
 * Register: XDPDMA_EIDS
 */
    #define XDPDMA_EIDS                            0X0020

    #define XDPDMA_EIDS_RD_CMD_FIFO_FULL_SHIFT     31
    #define XDPDMA_EIDS_RD_CMD_FIFO_FULL_WIDTH     1
    #define XDPDMA_EIDS_RD_CMD_FIFO_FULL_MASK      0X80000000

    #define XDPDMA_EIDS_DSCR_DONE_ERR5_SHIFT       30
    #define XDPDMA_EIDS_DSCR_DONE_ERR5_WIDTH       1
    #define XDPDMA_EIDS_DSCR_DONE_ERR5_MASK        0X40000000

    #define XDPDMA_EIDS_DSCR_DONE_ERR4_SHIFT       29
    #define XDPDMA_EIDS_DSCR_DONE_ERR4_WIDTH       1
    #define XDPDMA_EIDS_DSCR_DONE_ERR4_MASK        0X20000000

    #define XDPDMA_EIDS_DSCR_DONE_ERR3_SHIFT       28
    #define XDPDMA_EIDS_DSCR_DONE_ERR3_WIDTH       1
    #define XDPDMA_EIDS_DSCR_DONE_ERR3_MASK        0X10000000

    #define XDPDMA_EIDS_DSCR_DONE_ERR2_SHIFT       27
    #define XDPDMA_EIDS_DSCR_DONE_ERR2_WIDTH       1
    #define XDPDMA_EIDS_DSCR_DONE_ERR2_MASK        0X08000000

    #define XDPDMA_EIDS_DSCR_DONE_ERR1_SHIFT       26
    #define XDPDMA_EIDS_DSCR_DONE_ERR1_WIDTH       1
    #define XDPDMA_EIDS_DSCR_DONE_ERR1_MASK        0X04000000

    #define XDPDMA_EIDS_DSCR_DONE_ERR0_SHIFT       25
    #define XDPDMA_EIDS_DSCR_DONE_ERR0_WIDTH       1
    #define XDPDMA_EIDS_DSCR_DONE_ERR0_MASK        0X02000000

    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR5_SHIFT     24
    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR5_WIDTH     1
    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR5_MASK      0X01000000

    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR4_SHIFT     23
    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR4_WIDTH     1
    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR4_MASK      0X800000

    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR3_SHIFT     22
    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR3_WIDTH     1
    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR3_MASK      0X400000

    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR2_SHIFT     21
    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR2_WIDTH     1
    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR2_MASK      0X200000

    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR1_SHIFT     20
    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR1_WIDTH     1
    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR1_MASK      0X100000

    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR0_SHIFT     19
    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR0_WIDTH     1
    #define XDPDMA_EIDS_DSCR_WR_AXI_ERR0_MASK      0X80000

    #define XDPDMA_EIDS_DSCR_CRC_ERR5_SHIFT        18
    #define XDPDMA_EIDS_DSCR_CRC_ERR5_WIDTH        1
    #define XDPDMA_EIDS_DSCR_CRC_ERR5_MASK         0X40000

    #define XDPDMA_EIDS_DSCR_CRC_ERR4_SHIFT        17
    #define XDPDMA_EIDS_DSCR_CRC_ERR4_WIDTH        1
    #define XDPDMA_EIDS_DSCR_CRC_ERR4_MASK         0X20000

    #define XDPDMA_EIDS_DSCR_CRC_ERR3_SHIFT        16
    #define XDPDMA_EIDS_DSCR_CRC_ERR3_WIDTH        1
    #define XDPDMA_EIDS_DSCR_CRC_ERR3_MASK         0X10000

    #define XDPDMA_EIDS_DSCR_CRC_ERR2_SHIFT        15
    #define XDPDMA_EIDS_DSCR_CRC_ERR2_WIDTH        1
    #define XDPDMA_EIDS_DSCR_CRC_ERR2_MASK         0X8000

    #define XDPDMA_EIDS_DSCR_CRC_ERR1_SHIFT        14
    #define XDPDMA_EIDS_DSCR_CRC_ERR1_WIDTH        1
    #define XDPDMA_EIDS_DSCR_CRC_ERR1_MASK         0X4000

    #define XDPDMA_EIDS_DSCR_CRC_ERR0_SHIFT        13
    #define XDPDMA_EIDS_DSCR_CRC_ERR0_WIDTH        1
    #define XDPDMA_EIDS_DSCR_CRC_ERR0_MASK         0X2000

    #define XDPDMA_EIDS_DSCR_PRE_ERR5_SHIFT        12
    #define XDPDMA_EIDS_DSCR_PRE_ERR5_WIDTH        1
    #define XDPDMA_EIDS_DSCR_PRE_ERR5_MASK         0X1000

    #define XDPDMA_EIDS_DSCR_PRE_ERR4_SHIFT        11
    #define XDPDMA_EIDS_DSCR_PRE_ERR4_WIDTH        1
    #define XDPDMA_EIDS_DSCR_PRE_ERR4_MASK         0X0800

    #define XDPDMA_EIDS_DSCR_PRE_ERR3_SHIFT        10
    #define XDPDMA_EIDS_DSCR_PRE_ERR3_WIDTH        1
    #define XDPDMA_EIDS_DSCR_PRE_ERR3_MASK         0X0400

    #define XDPDMA_EIDS_DSCR_PRE_ERR2_SHIFT        9
    #define XDPDMA_EIDS_DSCR_PRE_ERR2_WIDTH        1
    #define XDPDMA_EIDS_DSCR_PRE_ERR2_MASK         0X0200

    #define XDPDMA_EIDS_DSCR_PRE_ERR1_SHIFT        8
    #define XDPDMA_EIDS_DSCR_PRE_ERR1_WIDTH        1
    #define XDPDMA_EIDS_DSCR_PRE_ERR1_MASK         0X0100

    #define XDPDMA_EIDS_DSCR_PRE_ERR0_SHIFT        7
    #define XDPDMA_EIDS_DSCR_PRE_ERR0_WIDTH        1
    #define XDPDMA_EIDS_DSCR_PRE_ERR0_MASK         0X80

    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR5_SHIFT     6
    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR5_WIDTH     1
    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR5_MASK      0X40

    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR4_SHIFT     5
    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR4_WIDTH     1
    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR4_MASK      0X20

    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR3_SHIFT     4
    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR3_WIDTH     1
    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR3_MASK      0X10

    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR2_SHIFT     3
    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR2_WIDTH     1
    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR2_MASK      0X8

    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR1_SHIFT     2
    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR1_WIDTH     1
    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR1_MASK      0X4

    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR0_SHIFT     1
    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR0_WIDTH     1
    #define XDPDMA_EIDS_DSCR_RD_AXI_ERR0_MASK      0X2

    #define XDPDMA_EIDS_INV_APB_SHIFT              0
    #define XDPDMA_EIDS_INV_APB_WIDTH              1
    #define XDPDMA_EIDS_INV_APB_MASK               0X1

/**
 * Register: XDPDMA_CNTL
 */
    #define XDPDMA_CNTL                            0X0100

/**
 * Register: XDPDMA_GBL
 */
    #define XDPDMA_GBL                             0X0104

    #define XDPDMA_GBL_RTRG_CH5_SHIFT              11
    #define XDPDMA_GBL_RTRG_CH5_WIDTH              1
    #define XDPDMA_GBL_RTRG_CH5_MASK               0X0800

    #define XDPDMA_GBL_RTRG_CH4_SHIFT              10
    #define XDPDMA_GBL_RTRG_CH4_WIDTH              1
    #define XDPDMA_GBL_RTRG_CH4_MASK               0X0400

    #define XDPDMA_GBL_RTRG_CH3_SHIFT              9
    #define XDPDMA_GBL_RTRG_CH3_WIDTH              1
    #define XDPDMA_GBL_RTRG_CH3_MASK               0X0200

    #define XDPDMA_GBL_RTRG_CH2_SHIFT              8
    #define XDPDMA_GBL_RTRG_CH2_WIDTH              1
    #define XDPDMA_GBL_RTRG_CH2_MASK               0X0100

    #define XDPDMA_GBL_RTRG_CH1_SHIFT              7
    #define XDPDMA_GBL_RTRG_CH1_WIDTH              1
    #define XDPDMA_GBL_RTRG_CH1_MASK               0X80

    #define XDPDMA_GBL_RTRG_CH0_SHIFT              6
    #define XDPDMA_GBL_RTRG_CH0_WIDTH              1
    #define XDPDMA_GBL_RTRG_CH0_MASK               0X40

    #define XDPDMA_GBL_TRG_CH5_SHIFT               5
    #define XDPDMA_GBL_TRG_CH5_WIDTH               1
    #define XDPDMA_GBL_TRG_CH5_MASK                0X20

    #define XDPDMA_GBL_TRG_CH4_SHIFT               4
    #define XDPDMA_GBL_TRG_CH4_WIDTH               1
    #define XDPDMA_GBL_TRG_CH4_MASK                0X10

    #define XDPDMA_GBL_TRG_CH3_SHIFT               3
    #define XDPDMA_GBL_TRG_CH3_WIDTH               1
    #define XDPDMA_GBL_TRG_CH3_MASK                0X8

    #define XDPDMA_GBL_TRG_CH2_SHIFT               2
    #define XDPDMA_GBL_TRG_CH2_WIDTH               1
    #define XDPDMA_GBL_TRG_CH2_MASK                0X4

    #define XDPDMA_GBL_TRG_CH1_SHIFT               1
    #define XDPDMA_GBL_TRG_CH1_WIDTH               1
    #define XDPDMA_GBL_TRG_CH1_MASK                0X2

    #define XDPDMA_GBL_TRG_CH0_SHIFT               0
    #define XDPDMA_GBL_TRG_CH0_WIDTH               1
    #define XDPDMA_GBL_TRG_CH0_MASK                0X1

/**
 * Register: XDPDMA_CH0_DSCR_STRT_ADDRE
 */
    #define XDPDMA_CH0_DSCR_STRT_ADDRE             0X0200

/**
 * Register: XDPDMA_CH0_DSCR_STRT_ADDR
 */
    #define XDPDMA_CH0_DSCR_STRT_ADDR              0X0204

/**
 * Register: XDPDMA_CH0_DSCR_NEXT_ADDRE
 */
    #define XDPDMA_CH0_DSCR_NEXT_ADDRE             0X0208

/**
 * Register: XDPDMA_CH0_DSCR_NEXT_ADDR
 */
    #define XDPDMA_CH0_DSCR_NEXT_ADDR              0X020C

/**
 * Register: XDPDMA_CH0_PYLD_CUR_ADDRE
 */
    #define XDPDMA_CH0_PYLD_CUR_ADDRE              0X0210

/**
 * Register: XDPDMA_CH0_PYLD_CUR_ADDR
 */
    #define XDPDMA_CH0_PYLD_CUR_ADDR               0X0214

/**
 * Register: XDPDMA_CH0_CNTL
 */
    #define XDPDMA_CH0_CNTL                        0X0218

    #define XDPDMA_CNTL_QOS_VIDEO                  0x11

/**
 * Register: XDPDMA_CH0_STATUS
 */
    #define XDPDMA_CH0_STATUS                      0X021C

/**
 * Register: XDPDMA_CH0_VDO
 */
    #define XDPDMA_CH0_VDO                         0X0220

/**
 * Register: XDPDMA_CH0_PYLD_SZ
 */
    #define XDPDMA_CH0_PYLD_SZ                     0X0224

/**
 * Register: XDPDMA_CH0_DSCR_ID
 */
    #define XDPDMA_CH0_DSCR_ID                     0X0228

/**
 * Register: XDPDMA_CH1_DSCR_STRT_ADDRE
 */
    #define XDPDMA_CH1_DSCR_STRT_ADDRE             0X0300

/**
 * Register: XDPDMA_CH1_DSCR_STRT_ADDR
 */
    #define XDPDMA_CH1_DSCR_STRT_ADDR              0X0304

/**
 * Register: XDPDMA_CH1_DSCR_NEXT_ADDRE
 */
    #define XDPDMA_CH1_DSCR_NEXT_ADDRE             0X0308

/**
 * Register: XDPDMA_CH1_DSCR_NEXT_ADDR
 */
    #define XDPDMA_CH1_DSCR_NEXT_ADDR              0X030C

/**
 * Register: XDPDMA_CH1_PYLD_CUR_ADDRE
 */
    #define XDPDMA_CH1_PYLD_CUR_ADDRE              0X0310

/**
 * Register: XDPDMA_CH1_PYLD_CUR_ADDR
 */
    #define XDPDMA_CH1_PYLD_CUR_ADDR               0X0314

/**
 * Register: XDPDMA_CH1_CNTL
 */
    #define XDPDMA_CH1_CNTL                        0X0318

/**
 * Register: XDPDMA_CH1_STATUS
 */
    #define XDPDMA_CH1_STATUS                      0X031C

/**
 * Register: XDPDMA_CH1_VDO
 */
    #define XDPDMA_CH1_VDO                         0X0320

/**
 * Register: XDPDMA_CH1_PYLD_SZ
 */
    #define XDPDMA_CH1_PYLD_SZ                     0X0324

/**
 * Register: XDPDMA_CH1_DSCR_ID
 */
    #define XDPDMA_CH1_DSCR_ID                     0X0328

/**
 * Register: XDPDMA_CH2_DSCR_STRT_ADDRE
 */
    #define XDPDMA_CH2_DSCR_STRT_ADDRE             0X0400

/**
 * Register: XDPDMA_CH2_DSCR_STRT_ADDR
 */
    #define XDPDMA_CH2_DSCR_STRT_ADDR              0X0404

/**
 * Register: XDPDMA_CH2_DSCR_NEXT_ADDRE
 */
    #define XDPDMA_CH2_DSCR_NEXT_ADDRE             0X0408

/**
 * Register: XDPDMA_CH2_DSCR_NEXT_ADDR
 */
    #define XDPDMA_CH2_DSCR_NEXT_ADDR              0X040C

/**
 * Register: XDPDMA_CH2_PYLD_CUR_ADDRE
 */
    #define XDPDMA_CH2_PYLD_CUR_ADDRE              0X0410

/**
 * Register: XDPDMA_CH2_PYLD_CUR_ADDR
 */
    #define XDPDMA_CH2_PYLD_CUR_ADDR               0X0414

/**
 * Register: XDPDMA_CH2_CNTL
 */
    #define XDPDMA_CH2_CNTL                        0X0418

/**
 * Register: XDPDMA_CH2_STATUS
 */
    #define XDPDMA_CH2_STATUS                      0X041C

/**
 * Register: XDPDMA_CH2_VDO
 */
    #define XDPDMA_CH2_VDO                         0X0420

/**
 * Register: XDPDMA_CH2_PYLD_SZ
 */
    #define XDPDMA_CH2_PYLD_SZ                     0X0424

/**
 * Register: XDPDMA_CH2_DSCR_ID
 */
    #define XDPDMA_CH2_DSCR_ID                     0X0428

/**
 * Register: XDPDMA_CH3_DSCR_STRT_ADDRE
 */
    #define XDPDMA_CH3_DSCR_STRT_ADDRE             0X0500

/**
 * Register: XDPDMA_CH3_DSCR_STRT_ADDR
 */
    #define XDPDMA_CH3_DSCR_STRT_ADDR              0X0504

/**
 * Register: XDPDMA_CH3_DSCR_NEXT_ADDRE
 */
    #define XDPDMA_CH3_DSCR_NEXT_ADDRE             0X0508

/**
 * Register: XDPDMA_CH3_DSCR_NEXT_ADDR
 */
    #define XDPDMA_CH3_DSCR_NEXT_ADDR              0X050C

/**
 * Register: XDPDMA_CH3_PYLD_CUR_ADDRE
 */
    #define XDPDMA_CH3_PYLD_CUR_ADDRE              0X0510

/**
 * Register: XDPDMA_CH3_PYLD_CUR_ADDR
 */
    #define XDPDMA_CH3_PYLD_CUR_ADDR               0X0514

/**
 * Register: XDPDMA_CH3_CNTL
 */
    #define XDPDMA_CH3_CNTL                        0X0518

/**
 * Register: XDPDMA_CH3_STATUS
 */
    #define XDPDMA_CH3_STATUS                      0X051C

/**
 * Register: XDPDMA_CH3_VDO
 */
    #define XDPDMA_CH3_VDO                         0X0520

/**
 * Register: XDPDMA_CH3_PYLD_SZ
 */
    #define XDPDMA_CH3_PYLD_SZ                     0X0524

/**
 * Register: XDPDMA_CH3_DSCR_ID
 */
    #define XDPDMA_CH3_DSCR_ID                     0X0528

/**
 * Register: XDPDMA_CH4_DSCR_STRT_ADDRE
 */
    #define XDPDMA_CH4_DSCR_STRT_ADDRE             0X0600

/**
 * Register: XDPDMA_CH4_DSCR_STRT_ADDR
 */
    #define XDPDMA_CH4_DSCR_STRT_ADDR              0X0604

/**
 * Register: XDPDMA_CH4_DSCR_NEXT_ADDRE
 */
    #define XDPDMA_CH4_DSCR_NEXT_ADDRE             0X0608

/**
 * Register: XDPDMA_CH4_DSCR_NEXT_ADDR
 */
    #define XDPDMA_CH4_DSCR_NEXT_ADDR              0X060C

/**
 * Register: XDPDMA_CH4_PYLD_CUR_ADDRE
 */
    #define XDPDMA_CH4_PYLD_CUR_ADDRE              0X0610

/**
 * Register: XDPDMA_CH4_PYLD_CUR_ADDR
 */
    #define XDPDMA_CH4_PYLD_CUR_ADDR               0X0614

/**
 * Register: XDPDMA_CH4_CNTL
 */
    #define XDPDMA_CH4_CNTL                        0X0618

/**
 * Register: XDPDMA_CH4_STATUS
 */
    #define XDPDMA_CH4_STATUS                      0X061C

/**
 * Register: XDPDMA_CH4_VDO
 */
    #define XDPDMA_CH4_VDO                         0X0620

/**
 * Register: XDPDMA_CH4_PYLD_SZ
 */
    #define XDPDMA_CH4_PYLD_SZ                     0X0624

/**
 * Register: XDPDMA_CH4_DSCR_ID
 */
    #define XDPDMA_CH4_DSCR_ID                     0X0628

/**
 * Register: XDPDMA_CH5_DSCR_STRT_ADDRE
 */
    #define XDPDMA_CH5_DSCR_STRT_ADDRE             0X0700

/**
 * Register: XDPDMA_CH5_DSCR_STRT_ADDR
 */
    #define XDPDMA_CH5_DSCR_STRT_ADDR              0X0704

/**
 * Register: XDPDMA_CH5_DSCR_NEXT_ADDRE
 */
    #define XDPDMA_CH5_DSCR_NEXT_ADDRE             0X0708

/**
 * Register: XDPDMA_CH5_DSCR_NEXT_ADDR
 */
    #define XDPDMA_CH5_DSCR_NEXT_ADDR              0X070C

/**
 * Register: XDPDMA_CH5_PYLD_CUR_ADDRE
 */
    #define XDPDMA_CH5_PYLD_CUR_ADDRE              0X0710

/**
 * Register: XDPDMA_CH5_PYLD_CUR_ADDR
 */
    #define XDPDMA_CH5_PYLD_CUR_ADDR               0X0714

/**
 * Register: XDPDMA_CH5_CNTL
 */
    #define XDPDMA_CH5_CNTL                        0X0718

/**
 * Register: XDPDMA_CH5_STATUS
 */
    #define XDPDMA_CH5_STATUS                      0X071C

/**
 * Register: XDPDMA_CH5_VDO
 */
    #define XDPDMA_CH5_VDO                         0X0720

/**
 * Register: XDPDMA_CH5_PYLD_SZ
 */
    #define XDPDMA_CH5_PYLD_SZ                     0X0724

/**
 * Register: XDPDMA_CH5_DSCR_ID
 */
    #define XDPDMA_CH5_DSCR_ID                     0X0728


    #define XDPDMA_CH_DSCR_STRT_ADDRE_MSB_SHIFT    0
    #define XDPDMA_CH_DSCR_STRT_ADDRE_MSB_WIDTH    16
    #define XDPDMA_CH_DSCR_STRT_ADDRE_MSB_MASK     0XFFFF


    #define XDPDMA_CH_DSCR_STRT_ADDR_LSB_SHIFT     0
    #define XDPDMA_CH_DSCR_STRT_ADDR_LSB_WIDTH     32
    #define XDPDMA_CH_DSCR_STRT_ADDR_LSB_MASK      0XFFFFFFFF


    #define XDPDMA_CH_DSCR_NEXT_ADDRE_MSB_SHIFT    0
    #define XDPDMA_CH_DSCR_NEXT_ADDRE_MSB_WIDTH    16
    #define XDPDMA_CH_DSCR_NEXT_ADDRE_MSB_MASK     0XFFFF


    #define XDPDMA_CH_DSCR_NEXT_ADDR_LSB_SHIFT     0
    #define XDPDMA_CH_DSCR_NEXT_ADDR_LSB_WIDTH     32
    #define XDPDMA_CH_DSCR_NEXT_ADDR_LSB_MASK      0XFFFFFFFF


    #define XDPDMA_CH_PYLD_CUR_ADDRE_MSB_SHIFT     0
    #define XDPDMA_CH_PYLD_CUR_ADDRE_MSB_WIDTH     16
    #define XDPDMA_CH_PYLD_CUR_ADDRE_MSB_MASK      0XFFFF

    #define XDPDMA_CH_PYLD_CUR_ADDR_LSB_SHIFT      0
    #define XDPDMA_CH_PYLD_CUR_ADDR_LSB_WIDTH      32
    #define XDPDMA_CH_PYLD_CUR_ADDR_LSB_MASK       0XFFFFFFFF

    #define XDPDMA_CH_CNTL_DSCR_AXCACHE_SHIFT      16
    #define XDPDMA_CH_CNTL_DSCR_AXCACHE_WIDTH      4
    #define XDPDMA_CH_CNTL_DSCR_AXCACHE_MASK       0XF0000

    #define XDPDMA_CH_CNTL_DSCR_AXPROT_SHIFT       14
    #define XDPDMA_CH_CNTL_DSCR_AXPROT_WIDTH       2
    #define XDPDMA_CH_CNTL_DSCR_AXPROT_MASK        0XC000

    #define XDPDMA_CH_CNTL_QOS_DATA_RD_SHIFT       10
    #define XDPDMA_CH_CNTL_QOS_DATA_RD_WIDTH       4
    #define XDPDMA_CH_CNTL_QOS_DATA_RD_MASK        0X3C00

    #define XDPDMA_CH_CNTL_QOS_DSCR_RD_SHIFT       6
    #define XDPDMA_CH_CNTL_QOS_DSCR_RD_WIDTH       4
    #define XDPDMA_CH_CNTL_QOS_DSCR_RD_MASK        0X03C0

    #define XDPDMA_CH_CNTL_QOS_DSCR_WR_SHIFT       2
    #define XDPDMA_CH_CNTL_QOS_DSCR_WR_WIDTH       4
    #define XDPDMA_CH_CNTL_QOS_DSCR_WR_MASK        0X3C

    #define XDPDMA_CH_CNTL_PAUSE_SHIFT             1
    #define XDPDMA_CH_CNTL_PAUSE_WIDTH             1
    #define XDPDMA_CH_CNTL_PAUSE_MASK              0X2

    #define XDPDMA_CH_CNTL_EN_SHIFT                0
    #define XDPDMA_CH_CNTL_EN_WIDTH                1
    #define XDPDMA_CH_CNTL_EN_MASK                 0X1


    #define XDPDMA_CH_STATUS_OTRAN_CNT_SHIFT       21
    #define XDPDMA_CH_STATUS_OTRAN_CNT_WIDTH       4
    #define XDPDMA_CH_STATUS_OTRAN_CNT_MASK        0X01E00000

    #define XDPDMA_CH_STATUS_PREAMBLE_SHIFT        13
    #define XDPDMA_CH_STATUS_PREAMBLE_WIDTH        8
    #define XDPDMA_CH_STATUS_PREAMBLE_MASK         0X1FE000

    #define XDPDMA_CH_STATUS_EN_DSCR_INTR_SHIFT    12
    #define XDPDMA_CH_STATUS_EN_DSCR_INTR_WIDTH    1
    #define XDPDMA_CH_STATUS_EN_DSCR_INTR_MASK     0X1000

    #define XDPDMA_CH_STATUS_EN_DSCR_UP_SHIFT      11
    #define XDPDMA_CH_STATUS_EN_DSCR_UP_WIDTH      1
    #define XDPDMA_CH_STATUS_EN_DSCR_UP_MASK       0X0800

    #define XDPDMA_CH_STATUS_DSCR_DONE_SHIFT       10
    #define XDPDMA_CH_STATUS_DSCR_DONE_WIDTH       1
    #define XDPDMA_CH_STATUS_DSCR_DONE_MASK        0X0400

    #define XDPDMA_CH_STATUS_IGNR_DONE_SHIFT       9
    #define XDPDMA_CH_STATUS_IGNR_DONE_WIDTH       1
    #define XDPDMA_CH_STATUS_IGNR_DONE_MASK        0X0200

    #define XDPDMA_CH_STATUS_LDSCR_FRAME_SHIFT     8
    #define XDPDMA_CH_STATUS_LDSCR_FRAME_WIDTH     1
    #define XDPDMA_CH_STATUS_LDSCR_FRAME_MASK      0X0100

    #define XDPDMA_CH_STATUS_LAST_DSCR_SHIFT       7
    #define XDPDMA_CH_STATUS_LAST_DSCR_WIDTH       1
    #define XDPDMA_CH_STATUS_LAST_DSCR_MASK        0X80

    #define XDPDMA_CH_STATUS_EN_CRC_SHIFT          6
    #define XDPDMA_CH_STATUS_EN_CRC_WIDTH          1
    #define XDPDMA_CH_STATUS_EN_CRC_MASK           0X40

    #define XDPDMA_CH_STATUS_MODE_SHIFT            5
    #define XDPDMA_CH_STATUS_MODE_WIDTH            1
    #define XDPDMA_CH_STATUS_MODE_MASK             0X20

    #define XDPDMA_CH_STATUS_BURST_TYPE_SHIFT      4
    #define XDPDMA_CH_STATUS_BURST_TYPE_WIDTH      1
    #define XDPDMA_CH_STATUS_BURST_TYPE_MASK       0X10

    #define XDPDMA_CH_STATUS_BURST_LEN_SHIFT       0
    #define XDPDMA_CH_STATUS_BURST_LEN_WIDTH       4
    #define XDPDMA_CH_STATUS_BURST_LEN_MASK        0XF


    #define XDPDMA_CH_VDO_LINE_LENGTH_SHIFT        14
    #define XDPDMA_CH_VDO_LINE_LENGTH_WIDTH        18
    #define XDPDMA_CH_VDO_LINE_LENGTH_MASK         0XFFFFC000

    #define XDPDMA_CH_VDO_STRIDE_SHIFT             0
    #define XDPDMA_CH_VDO_STRIDE_WIDTH             14
    #define XDPDMA_CH_VDO_STRIDE_MASK              0X3FFF

    #define XDPDMA_CH_PYLD_SZ_BYTE_SHIFT           0
    #define XDPDMA_CH_PYLD_SZ_BYTE_WIDTH           32
    #define XDPDMA_CH_PYLD_SZ_BYTE_MASK            0XFFFFFFFF

    #define XDPDMA_CH_DSCR_ID_VAL_SHIFT            0
    #define XDPDMA_CH_DSCR_ID_VAL_WIDTH            16
    #define XDPDMA_CH_DSCR_ID_VAL_MASK             0XFFFF

/**
 * Register: XDPDMA_ECO
 */
    #define XDPDMA_ECO                             0X0FFC

    #define XDPDMA_ECO_VAL_SHIFT                   0
    #define XDPDMA_ECO_VAL_WIDTH                   32
    #define XDPDMA_ECO_VAL_MASK                    0XFFFFFFFF

/**
 * DPDMA descriptor
 */

    #define XDPDMA_DESCRIPTOR_CONTROL_PREAMBLE_SHIFT           0
    #define XDPDMA_DESCRIPTOR_CONTROL_PREAMBLE_WIDTH           8
    #define XDPDMA_DESCRIPTOR_CONTROL_PREAMBLE_MASK            0XFF

    #define XDPDMA_DESCRIPTOR_CONTROL_EN_COMP_INTR_SHIFT       8
    #define XDPDMA_DESCRIPTOR_CONTROL_EN_COMP_INTR_WIDTH       1
    #define XDPDMA_DESCRIPTOR_CONTROL_EN_COMP_INTR_MASK        0X0100

    #define XDPDMA_DESCRIPTOR_CONTROL_EN_DESC_UPDATE_SHIFT     9
    #define XDPDMA_DESCRIPTOR_CONTROL_EN_DESC_UPDATE_WIDTH     1
    #define XDPDMA_DESCRIPTOR_CONTROL_EN_DESC_UPDATE_MASK      0X0200

    #define XDPDMA_DESCRIPTOR_CONTROL_IGNORE_DONE_SHIFT        10
    #define XDPDMA_DESCRIPTOR_CONTROL_IGNORE_DONE_WIDTH        1
    #define XDPDMA_DESCRIPTOR_CONTROL_IGNORE_DONE_MASK         0X0400

    #define XDPDMA_DESCRIPTOR_CONTROL_AXI_BURST_TYPE_SHIFT     11
    #define XDPDMA_DESCRIPTOR_CONTROL_AXI_BURST_TYPE_WIDTH     1
    #define XDPDMA_DESCRIPTOR_CONTROL_AXI_BURST_TYPE_MASK      0X0800

    #define XDPDMA_DESCRIPTOR_CONTROL_AXACACHE_SHIFT           12
    #define XDPDMA_DESCRIPTOR_CONTROL_AXACACHE_WIDTH           4
    #define XDPDMA_DESCRIPTOR_CONTROL_AXACACHE_MASK            0XF000

    #define XDPDMA_DESCRIPTOR_CONTROL_AXPROT_SHIFT             16
    #define XDPDMA_DESCRIPTOR_CONTROL_AXPROT_WIDTH             2
    #define XDPDMA_DESCRIPTOR_CONTROL_AXPROT_MASK              0X30000

    #define XDPDMA_DESCRIPTOR_CONTROL_MODE_SHIFT               18
    #define XDPDMA_DESCRIPTOR_CONTROL_MODE_WIDTH               1
    #define XDPDMA_DESCRIPTOR_CONTROL_MODE_MASK                0X40000

    #define XDPDMA_DESCRIPTOR_CONTROL_LAST_DESC_SHIFT          19
    #define XDPDMA_DESCRIPTOR_CONTROL_LAST_DESC_WIDTH          1
    #define XDPDMA_DESCRIPTOR_CONTROL_LAST_DESC_MASK           0X80000

    #define XDPDMA_DESCRIPTOR_CONTROL_ENABLE_CRC_SHIFT         20
    #define XDPDMA_DESCRIPTOR_CONTROL_ENABLE_CRC_WIDTH         1
    #define XDPDMA_DESCRIPTOR_CONTROL_ENABLE_CRC_MASK          0x00100000

    #define XDPDMA_DESCRIPTOR_CONTROL_LAST_DESC_FRAME_SHIFT    21
    #define XDPDMA_DESCRIPTOR_CONTROL_LAST_DESC_FRAME_WIDTH    1
    #define XDPDMA_DESCRIPTOR_CONTROL_LAST_DESC_FRAME_MASK     0X200000

    #define XDPDMA_DESCRIPTOR_DSCR_ID_SHIFT                    0
    #define XDPDMA_DESCRIPTOR_DSCR_ID_WIDTH                    16
    #define XDPDMA_DESCRIPTOR_DSCR_ID_MASK                     0XFFFF

    #define XDPDMA_DESCRIPTOR_XFER_SIZE_SHIFT                  0
    #define XDPDMA_DESCRIPTOR_XFER_SIZE_WIDTH                  32
    #define XDPDMA_DESCRIPTOR_XFER_SIZE_MASK                   0x0000FFFF

    #define XDPDMA_DESCRIPTOR_LINE_SIZE_HZ_RES_SHIFT           0
    #define XDPDMA_DESCRIPTOR_LINE_SIZE_HZ_RES_WIDTH           18
    #define XDPDMA_DESCRIPTOR_LINE_SIZE_HZ_RES_MASK            0X3FFFF

    #define XDPDMA_DESCRIPTOR_LINE_SIZE_STRIDE_SHIFT           18
    #define XDPDMA_DESCRIPTOR_LINE_SIZE_STRIDE_WIDTH           14
    #define XDPDMA_DESCRIPTOR_LINE_SIZE_STRIDE_MASK            0XFFFC0000

    #define XDPDMA_DESCRIPTOR_TS_LSB_SHIFT                     0
    #define XDPDMA_DESCRIPTOR_TS_LSB_WIDTH                     32
    #define XDPDMA_DESCRIPTOR_TS_LSB_MASK                      0XFFFFFFFF

    #define XDPDMA_DESCRIPTOR_TS_MSB_SHIFT                     0
    #define XDPDMA_DESCRIPTOR_TS_MSB_WIDTH                     32
    #define XDPDMA_DESCRIPTOR_TS_MSB_MASK                      0XFFFFFFFF

    #define XDPDMA_DESCRIPTOR_TS_MSB_TS_SHIFT                  0
    #define XDPDMA_DESCRIPTOR_TS_MSB_TS_WIDTH                  9
    #define XDPDMA_DESCRIPTOR_TS_MSB_TS_MASK                   0X01FF

    #define XDPDMA_DESCRIPTOR_TS_MSB_STATUS_SHIFT              31
    #define XDPDMA_DESCRIPTOR_TS_MSB_STATUS_WIDTH              1
    #define XDPDMA_DESCRIPTOR_TS_MSB_STATUS_MASK               0X80000000

    #define XDPDMA_DESCRIPTOR_ADDR_EXT_DSC_NXT_SHIFT           0
    #define XDPDMA_DESCRIPTOR_ADDR_EXT_DSC_NXT_WIDTH           16
    #define XDPDMA_DESCRIPTOR_ADDR_EXT_DSC_NXT_MASK            0XFFFF

    #define XDPDMA_DESCRIPTOR_ADDR_EXT_SRC_ADDR_EXT_SHIFT      16
    #define XDPDMA_DESCRIPTOR_ADDR_EXT_SRC_ADDR_EXT_WIDTH      16
    #define XDPDMA_DESCRIPTOR_ADDR_EXT_SRC_ADDR_EXT_MASK       0XFFFF0000

    #define XDPDMA_DESCRIPTOR_ADDR_EXT23_2_SHIFT               0
    #define XDPDMA_DESCRIPTOR_ADDR_EXT23_2_WIDTH               16
    #define XDPDMA_DESCRIPTOR_ADDR_EXT23_2_MASK                0XFFFF

    #define XDPDMA_DESCRIPTOR_ADDR_EXT23_3_SHIFT               16
    #define XDPDMA_DESCRIPTOR_ADDR_EXT23_3_WIDTH               16
    #define XDPDMA_DESCRIPTOR_ADDR_EXT23_3_MASK                0xFFFF0000

    #define XDPDMA_DESCRIPTOR_ADDR_EXT45_4_SHIFT               0
    #define XDPDMA_DESCRIPTOR_ADDR_EXT45_4_WIDTH               16
    #define XDPDMA_DESCRIPTOR_ADDR_EXT45_4_MASK                0XFFFF

    #define XDPDMA_DESCRIPTOR_ADDR_EXT45_5_SHIFT               16
    #define XDPDMA_DESCRIPTOR_ADDR_EXT45_5_WIDTH               16
    #define XDPDMA_DESCRIPTOR_ADDR_EXT45_5_MASK                0XFFFF0000

    #define XDPDMA_DESCRIPTOR_NEXT_DESR_SHIFT                  0
    #define XDPDMA_DESCRIPTOR_NEXT_DESR_WIDTH                  32
    #define XDPDMA_DESCRIPTOR_NEXT_DESR_MASK                   0XFFFFFFFF

    #define XDPDMA_DESCRIPTOR_SRC_ADDR_SHIFT                   0
    #define XDPDMA_DESCRIPTOR_SRC_ADDR_WIDTH                   32
    #define XDPDMA_DESCRIPTOR_SRC_ADDR_MASK                    0XFFFFFFFF

    #define XDPDMA_DESCRIPTOR_SRC_ADDR2_SHIFT                  0
    #define XDPDMA_DESCRIPTOR_SRC_ADDR2_WIDTH                  32
    #define XDPDMA_DESCRIPTOR_SRC_ADDR2_MASK                   0XFFFFFFFF

    #define XDPDMA_DESCRIPTOR_SRC_ADDR3_SHIFT                  0
    #define XDPDMA_DESCRIPTOR_SRC_ADDR3_WIDTH                  32
    #define XDPDMA_DESCRIPTOR_SRC_ADDR3_MASK                   0XFFFFFFFF

    #define XDPDMA_DESCRIPTOR_SRC_ADDR4_SHIFT                  0
    #define XDPDMA_DESCRIPTOR_SRC_ADDR4_WIDTH                  32
    #define XDPDMA_DESCRIPTOR_SRC_ADDR4_MASK                   0XFFFFFFFF

    #define XDPDMA_DESCRIPTOR_SRC_ADDR5_SHIFT                  0
    #define XDPDMA_DESCRIPTOR_SRC_ADDR5_WIDTH                  32
    #define XDPDMA_DESCRIPTOR_SRC_ADDR5_MASK                   0XFFFFFFFF

    #define XDPDMA_TRIGGER_EN                                  1
    #define XDPDMA_RETRIGGER_EN                                2
    #define XDPDMA_TRIGGER_DONE                                0
    #define XDPDMA_RETRIGGER_DONE                              0
/* @} */

/******************* Macros (Inline Functions Definitions ********************/

/** @name Register access macro definitions.
 * @{
 */
    #define XDpDma_In32     Xil_In32
    #define XDpDma_Out32    Xil_Out32
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
 *		u32 XDpDma_ReadReg(u32 BaseAddress, u32 RegOffset
 *
 *******************************************************************************/
    #define XDpDma_ReadReg( BaseAddress, RegOffset ) \
    XDpDma_In32( ( BaseAddress ) + ( RegOffset ) )

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
 *		void XDpDma_WriteReg(u32 BaseAddress, u32 RegOffset, u32 Data)
 *
 *******************************************************************************/
    #define XDpDma_WriteReg( BaseAddress, RegOffset, Data ) \
    XDpDma_Out32( ( BaseAddress ) + ( RegOffset ), ( Data ) )


/******************************************************************************/

/**
 * This is a low-level function that writes to the specified register.
 *
 * @param	BaseAddress is the base address of the device.
 * @param	RegOffset is the register offset to write to.
 * @param	Data is the 32-bit data to write to the specified register.
 * @param	Mask is the 32-bit field to which data is to be written
 *
 * @return	None.
 *
 * @note	C-style signature:
 *		void XDpDma_ReadModifyWrite(u32 BaseAddress,
 *							u32 RegOffset, u32 Data)
 *
 *******************************************************************************/
    #define XDpDma_ReadModifyWrite( BaseAddress, RegOffset, Data, Mask ) \
    XDpDma_WriteReg( ( BaseAddress ), ( RegOffset ),                     \
                     ( ( XDpDma_ReadReg( BaseAddress, RegOffset ) &      \
                         ~( Mask ) ) | Data ) )

    #ifdef __cplusplus
}
    #endif


#endif /* _XDPDMAHW_H_ */
