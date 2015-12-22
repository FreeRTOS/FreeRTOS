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
/****************************************************************************/
/**
*
* @file xusbpsu_hw.h
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- -----  -------- -----------------------------------------------------
* 1.00a bss    01/22/15 First release
*
* </pre>
*
*****************************************************************************/

#ifndef XUSBPSU_HW_H	/* Prevent circular inclusions */
#define XUSBPSU_HW_H	/* by using protection macros  */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/

/************************** Constant Definitions ****************************/

/**@name Register offsets
 *
 * The following constants provide access to each of the registers of the
 * USBPSU device.
 * @{
 */

/* XUSBPSU registers memory space boundries */
#define XUSBPSU_GLOBALS_REGS_START              0xc100
#define XUSBPSU_GLOBALS_REGS_END                0xc6ff
#define XUSBPSU_DEVICE_REGS_START               0xc700
#define XUSBPSU_DEVICE_REGS_END                 0xcbff
#define XUSBPSU_OTG_REGS_START                  0xcc00
#define XUSBPSU_OTG_REGS_END                    0xccff

/* Global Registers */
#define XUSBPSU_GSBUSCFG0                       0xc100
#define XUSBPSU_GSBUSCFG1                       0xc104
#define XUSBPSU_GTXTHRCFG                       0xc108
#define XUSBPSU_GRXTHRCFG                       0xc10c
#define XUSBPSU_GCTL                            0xc110
#define XUSBPSU_GEVTEN                          0xc114
#define XUSBPSU_GSTS                            0xc118
#define XUSBPSU_GSNPSID                         0xc120
#define XUSBPSU_GGPIO                           0xc124
#define XUSBPSU_GUID                            0xc128
#define XUSBPSU_GUCTL                           0xc12c
#define XUSBPSU_GBUSERRADDR0                    0xc130
#define XUSBPSU_GBUSERRADDR1                    0xc134
#define XUSBPSU_GPRTBIMAP0                      0xc138
#define XUSBPSU_GPRTBIMAP1                      0xc13c
#define XUSBPSU_GHWPARAMS0_OFFSET               0xc140
#define XUSBPSU_GHWPARAMS1_OFFSET               0xc144
#define XUSBPSU_GHWPARAMS2_OFFSET               0xc148
#define XUSBPSU_GHWPARAMS3_OFFSET               0xc14c
#define XUSBPSU_GHWPARAMS4_OFFSET               0xc150
#define XUSBPSU_GHWPARAMS5_OFFSET               0xc154
#define XUSBPSU_GHWPARAMS6_OFFSET               0xc158
#define XUSBPSU_GHWPARAMS7_OFFSET               0xc15c
#define XUSBPSU_GDBGFIFOSPACE                   0xc160
#define XUSBPSU_GDBGLTSSM                       0xc164
#define XUSBPSU_GPRTBIMAP_HS0                   0xc180
#define XUSBPSU_GPRTBIMAP_HS1                   0xc184
#define XUSBPSU_GPRTBIMAP_FS0                   0xc188
#define XUSBPSU_GPRTBIMAP_FS1                   0xc18c

#define XUSBPSU_GUSB2PHYCFG(n)                  (0xc200 + (n * 0x04))
#define XUSBPSU_GUSB2I2CCTL(n)                  (0xc240 + (n * 0x04))

#define XUSBPSU_GUSB2PHYACC(n)                  (0xc280 + (n * 0x04))

#define XUSBPSU_GUSB3PIPECTL(n)                 (0xc2c0 + (n * 0x04))

#define XUSBPSU_GTXFIFOSIZ(n)                   (0xc300 + (n * 0x04))
#define XUSBPSU_GRXFIFOSIZ(n)                   (0xc380 + (n * 0x04))

#define XUSBPSU_GEVNTADRLO(n)                   (0xc400 + (n * 0x10))
#define XUSBPSU_GEVNTADRHI(n)                   (0xc404 + (n * 0x10))
#define XUSBPSU_GEVNTSIZ(n)                     (0xc408 + (n * 0x10))
#define XUSBPSU_GEVNTCOUNT(n)                   (0xc40c + (n * 0x10))

#define XUSBPSU_GHWPARAMS8                      0xc600

/* Device Registers */
#define XUSBPSU_DCFG                            0xc700
#define XUSBPSU_DCTL                            0xc704
#define XUSBPSU_DEVTEN                          0xc708
#define XUSBPSU_DSTS                            0xc70c
#define XUSBPSU_DGCMDPAR                        0xc710
#define XUSBPSU_DGCMD                           0xc714
#define XUSBPSU_DALEPENA                        0xc720
#define XUSBPSU_DEPCMDPAR2(n)                   (0xc800 + (n * 0x10))
#define XUSBPSU_DEPCMDPAR1(n)                   (0xc804 + (n * 0x10))
#define XUSBPSU_DEPCMDPAR0(n)                   (0xc808 + (n * 0x10))
#define XUSBPSU_DEPCMD(n)                       (0xc80c + (n * 0x10))

/* OTG Registers */
#define XUSBPSU_OCFG                            0xcc00
#define XUSBPSU_OCTL                            0xcc04
#define XUSBPSU_OEVT                            0xcc08
#define XUSBPSU_OEVTEN                          0xcc0C
#define XUSBPSU_OSTS                            0xcc10

/* Bit fields */

/* Global Configuration Register */
#define XUSBPSU_GCTL_PWRDNSCALE(n)              ((n) << 19)
#define XUSBPSU_GCTL_U2RSTECN                   (1 << 16)
#define XUSBPSU_GCTL_RAMCLKSEL(x)       (((x) & XUSBPSU_GCTL_CLK_MASK) << 6)
#define XUSBPSU_GCTL_CLK_BUS                    (0)
#define XUSBPSU_GCTL_CLK_PIPE                   (1)
#define XUSBPSU_GCTL_CLK_PIPEHALF               (2)
#define XUSBPSU_GCTL_CLK_MASK                   (3)

#define XUSBPSU_GCTL_PRTCAP(n)                  (((n) & (3 << 12)) >> 12)
#define XUSBPSU_GCTL_PRTCAPDIR(n)               ((n) << 12)
#define XUSBPSU_GCTL_PRTCAP_HOST                1
#define XUSBPSU_GCTL_PRTCAP_DEVICE              2
#define XUSBPSU_GCTL_PRTCAP_OTG                 3

#define XUSBPSU_GCTL_CORESOFTRESET              (1 << 11)
#define XUSBPSU_GCTL_SOFITPSYNC                 (1 << 10)
#define XUSBPSU_GCTL_SCALEDOWN(n)               ((n) << 4)
#define XUSBPSU_GCTL_SCALEDOWN_MASK             XUSBPSU_GCTL_SCALEDOWN(3)
#define XUSBPSU_GCTL_DISSCRAMBLE                (1 << 3)
#define XUSBPSU_GCTL_GBLHIBERNATIONEN           (1 << 1)
#define XUSBPSU_GCTL_DSBLCLKGTNG                (1 << 0)

/* Global Status Register Device Interrupt Mask */
#define XUSBPSU_GSTS_DEVICE_IP_MASK 			0x00000040

/* Global USB2 PHY Configuration Register */
#define XUSBPSU_GUSB2PHYCFG_PHYSOFTRST          (1 << 31)
#define XUSBPSU_GUSB2PHYCFG_SUSPHY              (1 << 6)

/* Global USB3 PIPE Control Register */
#define XUSBPSU_GUSB3PIPECTL_PHYSOFTRST         (1 << 31)
#define XUSBPSU_GUSB3PIPECTL_SUSPHY             (1 << 17)

/* Global TX Fifo Size Register */
#define XUSBPSU_GTXFIFOSIZ_TXFDEF(n)            ((n) & 0xffff)
#define XUSBPSU_GTXFIFOSIZ_TXFSTADDR(n)         ((n) & 0xffff0000)

/* Global Event Size Registers */
#define XUSBPSU_GEVNTSIZ_INTMASK                (1 << 31)
#define XUSBPSU_GEVNTSIZ_SIZE(n)                ((n) & 0xffff)

/* Global HWPARAMS1 Register */
#define XUSBPSU_GHWPARAMS1_EN_PWROPT(n)         (((n) & (3 << 24)) >> 24)
#define XUSBPSU_GHWPARAMS1_EN_PWROPT_NO         0
#define XUSBPSU_GHWPARAMS1_EN_PWROPT_CLK        1
#define XUSBPSU_GHWPARAMS1_EN_PWROPT_HIB        2
#define XUSBPSU_GHWPARAMS1_PWROPT(n)            ((n) << 24)
#define XUSBPSU_GHWPARAMS1_PWROPT_MASK          XUSBPSU_GHWPARAMS1_PWROPT(3)

/* Global HWPARAMS4 Register */
#define XUSBPSU_GHWPARAMS4_HIBER_SCRATCHBUFS(n) (((n) & (0x0f << 13)) >> 13)
#define XUSBPSU_MAX_HIBER_SCRATCHBUFS           15

/* Device Configuration Register */
#define XUSBPSU_DCFG_DEVADDR(addr)              ((addr) << 3)
#define XUSBPSU_DCFG_DEVADDR_MASK               XUSBPSU_DCFG_DEVADDR(0x7f)

#define XUSBPSU_DCFG_SPEED_MASK					7
#define XUSBPSU_DCFG_SUPERSPEED					4
#define XUSBPSU_DCFG_HIGHSPEED					0
#define XUSBPSU_DCFG_FULLSPEED2					1
#define XUSBPSU_DCFG_LOWSPEED					2
#define XUSBPSU_DCFG_FULLSPEED1					3

#define XUSBPSU_DCFG_LPM_CAP                    (1 << 22)

/* Device Control Register */
#define XUSBPSU_DCTL_RUN_STOP                   (1 << 31)
#define XUSBPSU_DCTL_CSFTRST                    (1 << 30)
#define XUSBPSU_DCTL_LSFTRST                    (1 << 29)

#define XUSBPSU_DCTL_HIRD_THRES_MASK            (0x1f << 24)
#define XUSBPSU_DCTL_HIRD_THRES(n)              ((n) << 24)

#define XUSBPSU_DCTL_APPL1RES                   (1 << 23)

/* These apply for core versions 1.87a and earlier */
#define XUSBPSU_DCTL_TRGTULST_MASK              (0x0f << 17)
#define XUSBPSU_DCTL_TRGTULST(n)                ((n) << 17)
#define XUSBPSU_DCTL_TRGTULST_U2                (XUSBPSU_DCTL_TRGTULST(2))
#define XUSBPSU_DCTL_TRGTULST_U3                (XUSBPSU_DCTL_TRGTULST(3))
#define XUSBPSU_DCTL_TRGTULST_SS_DIS            (XUSBPSU_DCTL_TRGTULST(4))
#define XUSBPSU_DCTL_TRGTULST_RX_DET            (XUSBPSU_DCTL_TRGTULST(5))
#define XUSBPSU_DCTL_TRGTULST_SS_INACT          (XUSBPSU_DCTL_TRGTULST(6))

/* These apply for core versions 1.94a and later */
#define XUSBPSU_DCTL_KEEP_CONNECT               (1 << 19)
#define XUSBPSU_DCTL_L1_HIBER_EN                (1 << 18)
#define XUSBPSU_DCTL_CRS                        (1 << 17)
#define XUSBPSU_DCTL_CSS                        (1 << 16)

#define XUSBPSU_DCTL_INITU2ENA                  (1 << 12)
#define XUSBPSU_DCTL_ACCEPTU2ENA                (1 << 11)
#define XUSBPSU_DCTL_INITU1ENA                  (1 << 10)
#define XUSBPSU_DCTL_ACCEPTU1ENA                (1 << 9)
#define XUSBPSU_DCTL_TSTCTRL_MASK               (0xf << 1)

#define XUSBPSU_DCTL_ULSTCHNGREQ_MASK           (0x0f << 5)
#define XUSBPSU_DCTL_ULSTCHNGREQ(n) (((n) << 5) & XUSBPSU_DCTL_ULSTCHNGREQ_MASK)

#define XUSBPSU_DCTL_ULSTCHNG_NO_ACTION         (XUSBPSU_DCTL_ULSTCHNGREQ(0))
#define XUSBPSU_DCTL_ULSTCHNG_SS_DISABLED       (XUSBPSU_DCTL_ULSTCHNGREQ(4))
#define XUSBPSU_DCTL_ULSTCHNG_RX_DETECT         (XUSBPSU_DCTL_ULSTCHNGREQ(5))
#define XUSBPSU_DCTL_ULSTCHNG_SS_INACTIVE       (XUSBPSU_DCTL_ULSTCHNGREQ(6))
#define XUSBPSU_DCTL_ULSTCHNG_RECOVERY          (XUSBPSU_DCTL_ULSTCHNGREQ(8))
#define XUSBPSU_DCTL_ULSTCHNG_COMPLIANCE        (XUSBPSU_DCTL_ULSTCHNGREQ(10))
#define XUSBPSU_DCTL_ULSTCHNG_LOOPBACK          (XUSBPSU_DCTL_ULSTCHNGREQ(11))

/* Device Event Enable Register */
#define XUSBPSU_DEVTEN_VNDRDEVTSTRCVEDEN        (1 << 12)
#define XUSBPSU_DEVTEN_EVNTOVERFLOWEN           (1 << 11)
#define XUSBPSU_DEVTEN_CMDCMPLTEN               (1 << 10)
#define XUSBPSU_DEVTEN_ERRTICERREN              (1 << 9)
#define XUSBPSU_DEVTEN_SOFEN                    (1 << 7)
#define XUSBPSU_DEVTEN_EOPFEN                   (1 << 6)
#define XUSBPSU_DEVTEN_HIBERNATIONREQEVTEN      (1 << 5)
#define XUSBPSU_DEVTEN_WKUPEVTEN                (1 << 4)
#define XUSBPSU_DEVTEN_ULSTCNGEN                (1 << 3)
#define XUSBPSU_DEVTEN_CONNECTDONEEN            (1 << 2)
#define XUSBPSU_DEVTEN_USBRSTEN                 (1 << 1)
#define XUSBPSU_DEVTEN_DISCONNEVTEN             (1 << 0)

/* Device Status Register */
#define XUSBPSU_DSTS_DCNRD                      (1 << 29)

/* This applies for core versions 1.87a and earlier */
#define XUSBPSU_DSTS_PWRUPREQ                   (1 << 24)

/* These apply for core versions 1.94a and later */
#define XUSBPSU_DSTS_RSS                        (1 << 25)
#define XUSBPSU_DSTS_SSS                        (1 << 24)

#define XUSBPSU_DSTS_COREIDLE                   (1 << 23)
#define XUSBPSU_DSTS_DEVCTRLHLT                 (1 << 22)

#define XUSBPSU_DSTS_USBLNKST_MASK              (0x0f << 18)
#define XUSBPSU_DSTS_USBLNKST(n) (((n) & XUSBPSU_DSTS_USBLNKST_MASK) >> 18)

#define XUSBPSU_DSTS_RXFIFOEMPTY                (1 << 17)

#define XUSBPSU_DSTS_SOFFN_MASK                 (0x3fff << 3)
#define XUSBPSU_DSTS_SOFFN(n)           (((n) & XUSBPSU_DSTS_SOFFN_MASK) >> 3)

#define XUSBPSU_DSTS_CONNECTSPD                 (7 << 0)

#define XUSBPSU_DSTS_SUPERSPEED                 (4 << 0)
#define XUSBPSU_DSTS_HIGHSPEED                  (0 << 0)
#define XUSBPSU_DSTS_FULLSPEED2                 (1 << 0)
#define XUSBPSU_DSTS_LOWSPEED                   (2 << 0)
#define XUSBPSU_DSTS_FULLSPEED1                 (3 << 0)

/* Device Generic Command Register */
#define XUSBPSU_DGCMD_SET_LMP                   0x01
#define XUSBPSU_DGCMD_SET_PERIODIC_PAR          0x02
#define XUSBPSU_DGCMD_XMIT_FUNCTION             0x03

/* These apply for core versions 1.94a and later */
#define XUSBPSU_DGCMD_SET_SCRATCHPAD_ADDR_LO    0x04
#define XUSBPSU_DGCMD_SET_SCRATCHPAD_ADDR_HI    0x05

#define XUSBPSU_DGCMD_SELECTED_FIFO_FLUSH       0x09
#define XUSBPSU_DGCMD_ALL_FIFO_FLUSH            0x0a
#define XUSBPSU_DGCMD_SET_ENDPOINT_NRDY         0x0c
#define XUSBPSU_DGCMD_RUN_SOC_BUS_LOOPBACK      0x10

#define XUSBPSU_DGCMD_STATUS(n)                 (((n) >> 15) & 1)
#define XUSBPSU_DGCMD_CMDACT                    (1 << 10)
#define XUSBPSU_DGCMD_CMDIOC                    (1 << 8)

/* Device Generic Command Parameter Register */
#define XUSBPSU_DGCMDPAR_FORCE_LINKPM_ACCEPT    (1 << 0)
#define XUSBPSU_DGCMDPAR_FIFO_NUM(n)            ((n) << 0)
#define XUSBPSU_DGCMDPAR_RX_FIFO                (0 << 5)
#define XUSBPSU_DGCMDPAR_TX_FIFO                (1 << 5)
#define XUSBPSU_DGCMDPAR_LOOPBACK_DIS           (0 << 0)
#define XUSBPSU_DGCMDPAR_LOOPBACK_ENA           (1 << 0)

/* Device Endpoint Command Register */
#define XUSBPSU_DEPCMD_PARAM_SHIFT              16
#define XUSBPSU_DEPCMD_PARAM(x)         ((x) << XUSBPSU_DEPCMD_PARAM_SHIFT)
#define XUSBPSU_DEPCMD_GET_RSC_IDX(x)	(((x) >> XUSBPSU_DEPCMD_PARAM_SHIFT) & \
					0x7f)
#define XUSBPSU_DEPCMD_STATUS(x)                (((x) >> 12) & 0xF)
#define XUSBPSU_DEPCMD_HIPRI_FORCERM            (1 << 11)
#define XUSBPSU_DEPCMD_CMDACT                   (1 << 10)
#define XUSBPSU_DEPCMD_CMDIOC                   (1 << 8)

#define XUSBPSU_DEPCMD_DEPSTARTCFG              0x09
#define XUSBPSU_DEPCMD_ENDTRANSFER              0x08
#define XUSBPSU_DEPCMD_UPDATETRANSFER           0x07
#define XUSBPSU_DEPCMD_STARTTRANSFER            0x06
#define XUSBPSU_DEPCMD_CLEARSTALL               0x05
#define XUSBPSU_DEPCMD_SETSTALL                 0x04
#define XUSBPSU_DEPCMD_GETEPSTATE               0x03
#define XUSBPSU_DEPCMD_SETTRANSFRESOURCE        0x02
#define XUSBPSU_DEPCMD_SETEPCONFIG              0x01

/* The EP number goes 0..31 so ep0 is always out and ep1 is always in */
#define XUSBPSU_DALEPENA_EP(n)                  (1 << n)

#define XUSBPSU_DEPCFG_INT_NUM(n)               ((n) << 0)
#define XUSBPSU_DEPCFG_XFER_COMPLETE_EN         (1 << 8)
#define XUSBPSU_DEPCFG_XFER_IN_PROGRESS_EN      (1 << 9)
#define XUSBPSU_DEPCFG_XFER_NOT_READY_EN        (1 << 10)
#define XUSBPSU_DEPCFG_FIFO_ERROR_EN            (1 << 11)
#define XUSBPSU_DEPCFG_STREAM_EVENT_EN          (1 << 13)
#define XUSBPSU_DEPCFG_BINTERVAL_M1(n)          ((n) << 16)
#define XUSBPSU_DEPCFG_STREAM_CAPABLE           (1 << 24)
#define XUSBPSU_DEPCFG_EP_NUMBER(n)             ((n) << 25)
#define XUSBPSU_DEPCFG_BULK_BASED               (1 << 30)
#define XUSBPSU_DEPCFG_FIFO_BASED               (1 << 31)

/* DEPCFG parameter 0 */
#define XUSBPSU_DEPCFG_EP_TYPE(n)               ((n) << 1)
#define XUSBPSU_DEPCFG_MAX_PACKET_SIZE(n)       ((n) << 3)
#define XUSBPSU_DEPCFG_FIFO_NUMBER(n)           ((n) << 17)
#define XUSBPSU_DEPCFG_BURST_SIZE(n)            ((n) << 22)
#define XUSBPSU_DEPCFG_DATA_SEQ_NUM(n)          ((n) << 26)
/* This applies for core versions earlier than 1.94a */
#define XUSBPSU_DEPCFG_IGN_SEQ_NUM              (1 << 31)
/* These apply for core versions 1.94a and later */
#define XUSBPSU_DEPCFG_ACTION_INIT              (0 << 30)
#define XUSBPSU_DEPCFG_ACTION_RESTORE           (1 << 30)
#define XUSBPSU_DEPCFG_ACTION_MODIFY            (2 << 30)

/* DEPXFERCFG parameter 0 */
#define XUSBPSU_DEPXFERCFG_NUM_XFER_RES(n) ((n) & 0xffff)

#define XUSBPSU_DEPCMD_TYPE_BULK                2
#define XUSBPSU_DEPCMD_TYPE_INTR                3

/* TRB Length, PCM and Status */
#define XUSBPSU_TRB_SIZE_MASK           (0x00ffffff)
#define XUSBPSU_TRB_SIZE_LENGTH(n)      ((n) & XUSBPSU_TRB_SIZE_MASK)
#define XUSBPSU_TRB_SIZE_PCM1(n)        (((n) & 0x03) << 24)
#define XUSBPSU_TRB_SIZE_TRBSTS(n)      (((n) & (0x0f << 28)) >> 28)

#define XUSBPSU_TRBSTS_OK               0
#define XUSBPSU_TRBSTS_MISSED_ISOC      1
#define XUSBPSU_TRBSTS_SETUP_PENDING    2
#define XUSBPSU_TRB_STS_XFER_IN_PROG    4

/* TRB Control */
#define XUSBPSU_TRB_CTRL_HWO            (1 << 0)
#define XUSBPSU_TRB_CTRL_LST            (1 << 1)
#define XUSBPSU_TRB_CTRL_CHN            (1 << 2)
#define XUSBPSU_TRB_CTRL_CSP            (1 << 3)
#define XUSBPSU_TRB_CTRL_TRBCTL(n)      (((n) & 0x3f) << 4)
#define XUSBPSU_TRB_CTRL_ISP_IMI        (1 << 10)
#define XUSBPSU_TRB_CTRL_IOC            (1 << 11)
#define XUSBPSU_TRB_CTRL_SID_SOFN(n)    (((n) & 0xffff) << 14)

#define XUSBPSU_TRBCTL_NORMAL                   XUSBPSU_TRB_CTRL_TRBCTL(1)
#define XUSBPSU_TRBCTL_CONTROL_SETUP            XUSBPSU_TRB_CTRL_TRBCTL(2)
#define XUSBPSU_TRBCTL_CONTROL_STATUS2          XUSBPSU_TRB_CTRL_TRBCTL(3)
#define XUSBPSU_TRBCTL_CONTROL_STATUS3          XUSBPSU_TRB_CTRL_TRBCTL(4)
#define XUSBPSU_TRBCTL_CONTROL_DATA             XUSBPSU_TRB_CTRL_TRBCTL(5)
#define XUSBPSU_TRBCTL_ISOCHRONOUS_FIRST        XUSBPSU_TRB_CTRL_TRBCTL(6)
#define XUSBPSU_TRBCTL_ISOCHRONOUS              XUSBPSU_TRB_CTRL_TRBCTL(7)
#define XUSBPSU_TRBCTL_LINK_TRB                 XUSBPSU_TRB_CTRL_TRBCTL(8)

/*@}*/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/*****************************************************************************/
/**
*
* Read a register of the USBPS8 device. This macro provides register
* access to all registers using the register offsets defined above.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	Offset is the offset of the register to read.
*
* @return	The contents of the register.
*
* @note		C-style Signature:
*		u32 XUsbPsu_ReadReg(struct XUsbPsu *InstancePtr, u32 Offset);
*
******************************************************************************/
#define XUsbPsu_ReadReg(InstancePtr, Offset) \
	Xil_In32((InstancePtr)->ConfigPtr->BaseAddress + (Offset))

/*****************************************************************************/
/**
*
* Write a register of the USBPS8 device. This macro provides
* register access to all registers using the register offsets defined above.
*
* @param	InstancePtr is a pointer to the XUsbPsu instance.
* @param	RegOffset is the offset of the register to write.
* @param	Data is the value to write to the register.
*
* @return	None.
*
* @note 	C-style Signature:
*		void XUsbPsu_WriteReg(struct XUsbPsu *InstancePtr,
*								u32 Offset,u32 Data)
*
******************************************************************************/
#define XUsbPsu_WriteReg(InstancePtr, Offset, Data) \
	Xil_Out32((InstancePtr)->ConfigPtr->BaseAddress + (Offset), (Data))

/************************** Function Prototypes ******************************/

#ifdef __cplusplus
}
#endif

#endif  /* End of protection macro. */
