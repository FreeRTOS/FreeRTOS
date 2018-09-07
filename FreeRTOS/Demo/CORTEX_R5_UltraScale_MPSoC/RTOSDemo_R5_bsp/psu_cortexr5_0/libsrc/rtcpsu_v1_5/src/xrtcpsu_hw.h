/******************************************************************************
*
* Copyright (C) 2015 Xilinx, Inc.  All rights reserved.
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
* @file xrtcpsu_hw.h
* @addtogroup rtcpsu_v1_5
* @{
*
* This header file contains the identifiers and basic driver functions (or
* macros) that can be used to access the device. Other driver functions
* are defined in xrtcpsu.h.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- -----  -------- -----------------------------------------------
* 1.00a kvn	  04/21/15 First release
* 1.1   kvn   09/25/15 Modify control register to enable battery
*                      switching when vcc_psaux is not available.
*
* </pre>
*
******************************************************************************/

#ifndef XRTC_HW_H_		/* prevent circular inclusions */
#define XRTC_HW_H_		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/

/**
 * Xrtc Base Address
 */
#define XRTC_BASEADDR      0xFFA60000U

/**
 * Register: XrtcSetTimeWr
 */
#define XRTC_SET_TIME_WR_OFFSET    0x00000000U
#define XRTC_SET_TIME_WR_RSTVAL   0x00000000U

#define XRTC_SET_TIME_WR_VAL_SHIFT   0U
#define XRTC_SET_TIME_WR_VAL_WIDTH   32U
#define XRTC_SET_TIME_WR_VAL_MASK    0xffffffffU
#define XRTC_SET_TIME_WR_VAL_DEFVAL  0x0U

/**
 * Register: XrtcSetTimeRd
 */
#define XRTC_SET_TIME_RD_OFFSET    0x00000004U
#define XRTC_SET_TIME_RD_RSTVAL   0x00000000U

#define XRTC_SET_TIME_RD_VAL_SHIFT   0U
#define XRTC_SET_TIME_RD_VAL_WIDTH   32U
#define XRTC_SET_TIME_RD_VAL_MASK    0xffffffffU
#define XRTC_SET_TIME_RD_VAL_DEFVAL  0x0U

/**
 * Register: XrtcCalibWr
 */
#define XRTC_CALIB_WR_OFFSET    0x00000008U
#define XRTC_CALIB_WR_RSTVAL   0x00000000U

#define XRTC_CALIB_WR_FRACTN_EN_SHIFT   20U
#define XRTC_CALIB_WR_FRACTN_EN_WIDTH   1U
#define XRTC_CALIB_WR_FRACTN_EN_MASK    0x00100000U
#define XRTC_CALIB_WR_FRACTN_EN_DEFVAL  0x0U

#define XRTC_CALIB_WR_FRACTN_DATA_SHIFT   16U
#define XRTC_CALIB_WR_FRACTN_DATA_WIDTH   4U
#define XRTC_CALIB_WR_FRACTN_DATA_MASK    0x000f0000U
#define XRTC_CALIB_WR_FRACTN_DATA_DEFVAL  0x0U

#define XRTC_CALIB_WR_MAX_TCK_SHIFT   0U
#define XRTC_CALIB_WR_MAX_TCK_WIDTH   16U
#define XRTC_CALIB_WR_MAX_TCK_MASK    0x0000ffffU
#define XRTC_CALIB_WR_MAX_TCK_DEFVAL  0x0U

/**
 * Register: XrtcCalibRd
 */
#define XRTC_CALIB_RD_OFFSET    0x0000000CU
#define XRTC_CALIB_RD_RSTVAL   0x00000000U

#define XRTC_CALIB_RD_FRACTN_EN_SHIFT   20U
#define XRTC_CALIB_RD_FRACTN_EN_WIDTH   1U
#define XRTC_CALIB_RD_FRACTN_EN_MASK    0x00100000U
#define XRTC_CALIB_RD_FRACTN_EN_DEFVAL  0x0U

#define XRTC_CALIB_RD_FRACTN_DATA_SHIFT   16U
#define XRTC_CALIB_RD_FRACTN_DATA_WIDTH   4U
#define XRTC_CALIB_RD_FRACTN_DATA_MASK    0x000f0000U
#define XRTC_CALIB_RD_FRACTN_DATA_DEFVAL  0x0U

#define XRTC_CALIB_RD_MAX_TCK_SHIFT   0U
#define XRTC_CALIB_RD_MAX_TCK_WIDTH   16U
#define XRTC_CALIB_RD_MAX_TCK_MASK    0x0000ffffU
#define XRTC_CALIB_RD_MAX_TCK_DEFVAL  0x0U

/**
 * Register: XrtcCurTime
 */
#define XRTC_CUR_TIME_OFFSET    0x00000010U
#define XRTC_CUR_TIME_RSTVAL   0x00000000U

#define XRTC_CUR_TIME_VAL_SHIFT   0U
#define XRTC_CUR_TIME_VAL_WIDTH   32U
#define XRTC_CUR_TIME_VAL_MASK    0xffffffffU
#define XRTC_CUR_TIME_VAL_DEFVAL  0x0U

/**
 * Register: XrtcCurTck
 */
#define XRTC_CUR_TCK_OFFSET    0x00000014U
#define XRTC_CUR_TCK_RSTVAL   0x00000000U

#define XRTC_CUR_TCK_VAL_SHIFT   0U
#define XRTC_CUR_TCK_VAL_WIDTH   16U
#define XRTC_CUR_TCK_VAL_MASK    0x0000ffffU
#define XRTC_CUR_TCK_VAL_DEFVAL  0x0U

/**
 * Register: XrtcAlrm
 */
#define XRTC_ALRM_OFFSET    0x00000018U
#define XRTC_ALRM_RSTVAL   0x00000000U

#define XRTC_ALRM_VAL_SHIFT   0U
#define XRTC_ALRM_VAL_WIDTH   32U
#define XRTC_ALRM_VAL_MASK    0xffffffffU
#define XRTC_ALRM_VAL_DEFVAL  0x0U

/**
 * Register: XrtcIntSts
 */
#define XRTC_INT_STS_OFFSET    0x00000020U
#define XRTC_INT_STS_RSTVAL   0x00000000U

#define XRTC_INT_STS_ALRM_SHIFT   1U
#define XRTC_INT_STS_ALRM_WIDTH   1U
#define XRTC_INT_STS_ALRM_MASK    0x00000002U
#define XRTC_INT_STS_ALRM_DEFVAL  0x0U

#define XRTC_INT_STS_SECS_SHIFT   0U
#define XRTC_INT_STS_SECS_WIDTH   1U
#define XRTC_INT_STS_SECS_MASK    0x00000001U
#define XRTC_INT_STS_SECS_DEFVAL  0x0U

/**
 * Register: XrtcIntMsk
 */
#define XRTC_INT_MSK_OFFSET    0x00000024U
#define XRTC_INT_MSK_RSTVAL   0x00000003U

#define XRTC_INT_MSK_ALRM_SHIFT   1U
#define XRTC_INT_MSK_ALRM_WIDTH   1U
#define XRTC_INT_MSK_ALRM_MASK    0x00000002U
#define XRTC_INT_MSK_ALRM_DEFVAL  0x1U

#define XRTC_INT_MSK_SECS_SHIFT   0U
#define XRTC_INT_MSK_SECS_WIDTH   1U
#define XRTC_INT_MSK_SECS_MASK    0x00000001U
#define XRTC_INT_MSK_SECS_DEFVAL  0x1U

/**
 * Register: XrtcIntEn
 */
#define XRTC_INT_EN_OFFSET    0x00000028U
#define XRTC_INT_EN_RSTVAL   0x00000000U

#define XRTC_INT_EN_ALRM_SHIFT   1U
#define XRTC_INT_EN_ALRM_WIDTH   1U
#define XRTC_INT_EN_ALRM_MASK    0x00000002U
#define XRTC_INT_EN_ALRM_DEFVAL  0x0U

#define XRTC_INT_EN_SECS_SHIFT   0U
#define XRTC_INT_EN_SECS_WIDTH   1U
#define XRTC_INT_EN_SECS_MASK    0x00000001U
#define XRTC_INT_EN_SECS_DEFVAL  0x0U

/**
 * Register: XrtcIntDis
 */
#define XRTC_INT_DIS_OFFSET    0x0000002CU
#define XRTC_INT_DIS_RSTVAL   0x00000000U

#define XRTC_INT_DIS_ALRM_SHIFT   1U
#define XRTC_INT_DIS_ALRM_WIDTH   1U
#define XRTC_INT_DIS_ALRM_MASK    0x00000002U
#define XRTC_INT_DIS_ALRM_DEFVAL  0x0U

#define XRTC_INT_DIS_SECS_SHIFT   0U
#define XRTC_INT_DIS_SECS_WIDTH   1U
#define XRTC_INT_DIS_SECS_MASK    0x00000001U
#define XRTC_INT_DIS_SECS_DEFVAL  0x0U

/**
 * Register: XrtcAddErr
 */
#define XRTC_ADD_ERR_OFFSET    0x00000030U
#define XRTC_ADD_ERR_RSTVAL   0x00000000U

#define XRTC_ADD_ERR_STS_SHIFT   0U
#define XRTC_ADD_ERR_STS_WIDTH   1U
#define XRTC_ADD_ERR_STS_MASK    0x00000001U
#define XRTC_ADD_ERR_STS_DEFVAL  0x0U

/**
 * Register: XrtcAddErrIntMsk
 */
#define XRTC_ADD_ERR_INT_MSK_OFFSET    0x00000034U
#define XRTC_ADD_ERR_INT_MSK_RSTVAL   0x00000001U

#define XRTC_ADD_ERR_INT_MSK_SHIFT   0U
#define XRTC_ADD_ERR_INT_MSK_WIDTH   1U
#define XRTC_ADD_ERR_INT_MSK_MASK    0x00000001U
#define XRTC_ADD_ERR_INT_MSK_DEFVAL  0x1U

/**
 * Register: XrtcAddErrIntEn
 */
#define XRTC_ADD_ERR_INT_EN_OFFSET    0x00000038U
#define XRTC_ADD_ERR_INT_EN_RSTVAL   0x00000000U

#define XRTC_ADD_ERR_INT_EN_MSK_SHIFT   0U
#define XRTC_ADD_ERR_INT_EN_MSK_WIDTH   1U
#define XRTC_ADD_ERR_INT_EN_MSK_MASK    0x00000001U
#define XRTC_ADD_ERR_INT_EN_MSK_DEFVAL  0x0U

/**
 * Register: XrtcAddErrIntDis
 */
#define XRTC_ADD_ERR_INT_DIS_OFFSET    0x0000003CU
#define XRTC_ADD_ERR_INT_DIS_RSTVAL   0x00000000U

#define XRTC_ADD_ERR_INT_DIS_MSK_SHIFT   0U
#define XRTC_ADD_ERR_INT_DIS_MSK_WIDTH   1U
#define XRTC_ADD_ERR_INT_DIS_MSK_MASK    0x00000001U
#define XRTC_ADD_ERR_INT_DIS_MSK_DEFVAL  0x0U

/**
 * Register: XrtcCtl
 */
#define XRTC_CTL_OFFSET    0x00000040U
#define XRTC_CTL_RSTVAL   0x01000000U

#define XRTC_CTL_BATTERY_EN_SHIFT   31U
#define XRTC_CTL_BATTERY_EN_WIDTH   1U
#define XRTC_CTL_BATTERY_EN_MASK    0x80000000U
#define XRTC_CTL_BATTERY_EN_DEFVAL  0x0U

#define XRTC_CTL_OSC_SHIFT   24U
#define XRTC_CTL_OSC_WIDTH   4U
#define XRTC_CTL_OSC_MASK    0x0f000000U
#define XRTC_CTL_OSC_DEFVAL  0x1U

#define XRTC_CTL_SLVERR_EN_SHIFT   0U
#define XRTC_CTL_SLVERR_EN_WIDTH   1U
#define XRTC_CTL_SLVERR_EN_MASK    0x00000001U
#define XRTC_CTL_SLVERR_EN_DEFVAL  0x0U

/**
 * Register: XrtcSftyChk
 */
#define XRTC_SFTY_CHK_OFFSET    0x00000050U
#define XRTC_SFTY_CHK_RSTVAL   0x00000000U

#define XRTC_SFTY_CHK_REG_SHIFT   0U
#define XRTC_SFTY_CHK_REG_WIDTH   32U
#define XRTC_SFTY_CHK_REG_MASK    0xffffffffU
#define XRTC_SFTY_CHK_REG_DEFVAL  0x0U

/**
 * Register: XrtcEco
 */
#define XRTC_ECO_OFFSET    0x00000060U
#define XRTC_ECO_RSTVAL   0x00000000U

#define XRTC_ECO_REG_SHIFT   0U
#define XRTC_ECO_REG_WIDTH   32U
#define XRTC_ECO_REG_MASK    0xffffffffU
#define XRTC_ECO_REG_DEFVAL  0x0U

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* This macro reads the given register.
*
* @param	RegisterAddr is the register address in the address
* 			space of the RTC device.
*
* @return	The 32-bit value of the register
*
* @note		None.
*
*****************************************************************************/
#define XRtcPsu_ReadReg(RegisterAddr) Xil_In32(RegisterAddr)

/****************************************************************************/
/**
*
* This macro writes the given register.
*
* @param	RegisterAddr is the register address in the address
* 			space of the RTC device.
* @param	Data is the 32-bit value to write to the register.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
#define XRtcPsu_WriteReg(RegisterAddr, Data) Xil_Out32(RegisterAddr, (u32)(Data))

#ifdef __cplusplus
}
#endif

#endif /* XRTC_HW_H_ */
/** @} */
