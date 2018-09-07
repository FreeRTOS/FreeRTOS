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
 * @file xusbps_endpoint.h
* @addtogroup usbpsu_v1_3
* @{
 *
 * This is an internal file containing the definitions for endpoints. It is
 * included by the xusbps_endpoint.c which is implementing the endpoint
 * functions and by xusbps_intr.c.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- --------------------------------------------------------
 * 1.0   sg  06/06/16  First release
 * 1.4 	 bk  12/01/18  Modify USBPSU driver code to fit USB common example code
 *		       for all USB IPs.
 *
 * </pre>
 *
 ******************************************************************************/
#ifndef XUSBPSU_ENDPOINT_H
#define XUSBPSU_ENDPOINT_H

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_cache.h"
#include "xusb_wrapper.h"
#include "xil_types.h"

/**************************** Type Definitions *******************************/

/************************** Constant Definitions *****************************/

/* Device Generic Command Register */
#define XUSBPSU_DGCMD_SET_LMP                   0x00000001U
#define XUSBPSU_DGCMD_SET_PERIODIC_PAR          0x00000002U
#define XUSBPSU_DGCMD_XMIT_FUNCTION             0x00000003U

/* These apply for core versions 1.94a and later */
#define XUSBPSU_DGCMD_SET_SCRATCHPAD_ADDR_LO    0x00000004U
#define XUSBPSU_DGCMD_SET_SCRATCHPAD_ADDR_HI    0x00000005U

#define XUSBPSU_DGCMD_SELECTED_FIFO_FLUSH       0x00000009U
#define XUSBPSU_DGCMD_ALL_FIFO_FLUSH            0x0000000aU
#define XUSBPSU_DGCMD_SET_ENDPOINT_NRDY         0x0000000cU
#define XUSBPSU_DGCMD_RUN_SOC_BUS_LOOPBACK      0x00000010U

#define XUSBPSU_DGCMD_STATUS(n)                 (((u32)(n) >> 15) & 1)
#define XUSBPSU_DGCMD_CMDACT                    (0x00000001U << 10)
#define XUSBPSU_DGCMD_CMDIOC                    (0x00000001U << 8)

/* Device Generic Command Parameter Register */
#define XUSBPSU_DGCMDPAR_FORCE_LINKPM_ACCEPT    (0x00000001U << 0)
#define XUSBPSU_DGCMDPAR_FIFO_NUM(n)            ((u32)(n) << 0)
#define XUSBPSU_DGCMDPAR_RX_FIFO                (0x00000000U << 5)
#define XUSBPSU_DGCMDPAR_TX_FIFO                (0x00000001U << 5)
#define XUSBPSU_DGCMDPAR_LOOPBACK_DIS           (0x00000000U << 0)
#define XUSBPSU_DGCMDPAR_LOOPBACK_ENA           (0x00000001U << 0)

/* Device Endpoint Command Register */
#define XUSBPSU_DEPCMD_PARAM_SHIFT              16U
#define XUSBPSU_DEPCMD_PARAM(x)         ((u32)(x) << XUSBPSU_DEPCMD_PARAM_SHIFT)
#define XUSBPSU_DEPCMD_GET_RSC_IDX(x)  (((u32)(x) >> XUSBPSU_DEPCMD_PARAM_SHIFT) & \
                                        (u32)0x0000007fU)
#define XUSBPSU_DEPCMD_STATUS(x)                (((u32)(x) >> 12) & (u32)0xF)
#define XUSBPSU_DEPCMD_HIPRI_FORCERM            (0x00000001U << 11)
#define XUSBPSU_DEPCMD_CMDACT                   (0x00000001U << 10)
#define XUSBPSU_DEPCMD_CMDIOC                   (0x00000001U << 8)

#define XUSBPSU_DEPCMD_DEPSTARTCFG              0x00000009U
#define XUSBPSU_DEPCMD_ENDTRANSFER              0x00000008U
#define XUSBPSU_DEPCMD_UPDATETRANSFER           0x00000007U
#define XUSBPSU_DEPCMD_STARTTRANSFER            0x00000006U
#define XUSBPSU_DEPCMD_CLEARSTALL               0x00000005U
#define XUSBPSU_DEPCMD_SETSTALL                 0x00000004U
#define XUSBPSU_DEPCMD_GETEPSTATE               0x00000003U
#define XUSBPSU_DEPCMD_SETTRANSFRESOURCE        0x00000002U
#define XUSBPSU_DEPCMD_SETEPCONFIG              0x00000001U

/* The EP number goes 0..31 so ep0 is always out and ep1 is always in */
#define XUSBPSU_DALEPENA_EP(n)                  (0x00000001U << (n))

#define XUSBPSU_DEPCFG_INT_NUM(n)               ((u32)(n) << 0)
#define XUSBPSU_DEPCFG_XFER_COMPLETE_EN         (0x00000001U << 8)
#define XUSBPSU_DEPCFG_XFER_IN_PROGRESS_EN      (0x00000001U << 9)
#define XUSBPSU_DEPCFG_XFER_NOT_READY_EN        (0x00000001U << 10)
#define XUSBPSU_DEPCFG_FIFO_ERROR_EN            (0x00000001U << 11)
#define XUSBPSU_DEPCFG_STREAM_EVENT_EN          (0x00000001U << 13)
#define XUSBPSU_DEPCFG_BINTERVAL_M1(n)          ((u32)(n) << 16)
#define XUSBPSU_DEPCFG_STREAM_CAPABLE           (0x00000001U << 24)
#define XUSBPSU_DEPCFG_EP_NUMBER(n)             ((u32)(n) << 25)
#define XUSBPSU_DEPCFG_BULK_BASED               (0x00000001U << 30)
#define XUSBPSU_DEPCFG_FIFO_BASED               (0x00000001U << 31)

/* DEPCFG parameter 0 */
#define XUSBPSU_DEPCFG_EP_TYPE(n)               ((u32)(n) << 1)
#define XUSBPSU_DEPCFG_MAX_PACKET_SIZE(n)       ((u32)(n) << 3)
#define XUSBPSU_DEPCFG_FIFO_NUMBER(n)           ((u32)(n) << 17)
#define XUSBPSU_DEPCFG_BURST_SIZE(n)            ((u32)(n) << 22)
#define XUSBPSU_DEPCFG_DATA_SEQ_NUM(n)          ((u32)(n) << 26)
/* This applies for core versions earlier than 1.94a */
#define XUSBPSU_DEPCFG_IGN_SEQ_NUM              (0x00000001U << 31)
/* These apply for core versions 1.94a and later */
#define XUSBPSU_DEPCFG_ACTION_INIT              (0x00000000U << 30)
#define XUSBPSU_DEPCFG_ACTION_RESTORE           (0x00000001U << 30)
#define XUSBPSU_DEPCFG_ACTION_MODIFY            (0x00000002U << 30)

/* DEPXFERCFG parameter 0 */
#define XUSBPSU_DEPXFERCFG_NUM_XFER_RES(n) ((u32)(n) & (u32)0xffff)

#define XUSBPSU_DEPCMD_TYPE_BULK                2U
#define XUSBPSU_DEPCMD_TYPE_INTR                3U

/* TRB Length, PCM and Status */
#define XUSBPSU_TRB_SIZE_MASK           (0x00ffffffU)
#define XUSBPSU_TRB_SIZE_LENGTH(n)      ((u32)(n) & XUSBPSU_TRB_SIZE_MASK)
#define XUSBPSU_TRB_SIZE_PCM1(n)        (((u32)(n) & (u32)0x03) << 24)
#define XUSBPSU_TRB_SIZE_TRBSTS(n)      (((u32)(n) & ((u32)0x0f << 28)) >> 28)

#define XUSBPSU_TRBSTS_OK               0U
#define XUSBPSU_TRBSTS_MISSED_ISOC      1U
#define XUSBPSU_TRBSTS_SETUP_PENDING    2U
#define XUSBPSU_TRB_STS_XFER_IN_PROG    4U

/* TRB Control */
#define XUSBPSU_TRB_CTRL_HWO            ((u32)0x00000001U << 0)
#define XUSBPSU_TRB_CTRL_LST            ((u32)0x00000001U << 1)
#define XUSBPSU_TRB_CTRL_CHN            ((u32)0x00000001U << 2)
#define XUSBPSU_TRB_CTRL_CSP            ((u32)0x00000001U << 3)
#define XUSBPSU_TRB_CTRL_TRBCTL(n)      (((u32)(n) & (u32)0x3f) << 4)
#define XUSBPSU_TRB_CTRL_ISP_IMI        (0x00000001U << 10)
#define XUSBPSU_TRB_CTRL_IOC            (0x00000001U << 11)
#define XUSBPSU_TRB_CTRL_SID_SOFN(n)    (((u32)(n) & (u32)0xffff) << 14)

#define XUSBPSU_TRBCTL_NORMAL                   XUSBPSU_TRB_CTRL_TRBCTL(1)
#define XUSBPSU_TRBCTL_CONTROL_SETUP            XUSBPSU_TRB_CTRL_TRBCTL(2)
#define XUSBPSU_TRBCTL_CONTROL_STATUS2          XUSBPSU_TRB_CTRL_TRBCTL(3)
#define XUSBPSU_TRBCTL_CONTROL_STATUS3          XUSBPSU_TRB_CTRL_TRBCTL(4)
#define XUSBPSU_TRBCTL_CONTROL_DATA             XUSBPSU_TRB_CTRL_TRBCTL(5)
#define XUSBPSU_TRBCTL_ISOCHRONOUS_FIRST        XUSBPSU_TRB_CTRL_TRBCTL(6)
#define XUSBPSU_TRBCTL_ISOCHRONOUS              XUSBPSU_TRB_CTRL_TRBCTL(7)
#define XUSBPSU_TRBCTL_LINK_TRB                 XUSBPSU_TRB_CTRL_TRBCTL(8)

#ifdef __cplusplus
}
#endif

#endif /* XUSBPSU_ENDPOINT_H */
/** @} */
