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
/****************************************************************************/
/**
*
* @file xusbpsu_hw.h
* @addtogroup usbpsu_v1_3
* @{
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- -----  -------- -----------------------------------------------------
* 1.0   sg    06/06/16 First release
* 1.4   myk   12/01/18 Added support of hibernation
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

/**/
#define XUSBPSU_PORTSC_30						0x430
#define XUSBPSU_PORTMSC_30						0x434

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
#define XUSBPSU_GHWPARAMS0_OFFSET               0xc140U
#define XUSBPSU_GHWPARAMS1_OFFSET               0xc144U
#define XUSBPSU_GHWPARAMS2_OFFSET               0xc148U
#define XUSBPSU_GHWPARAMS3_OFFSET               0xc14cU
#define XUSBPSU_GHWPARAMS4_OFFSET               0xc150U
#define XUSBPSU_GHWPARAMS5_OFFSET               0xc154U
#define XUSBPSU_GHWPARAMS6_OFFSET               0xc158U
#define XUSBPSU_GHWPARAMS7_OFFSET               0xc15cU
#define XUSBPSU_GDBGFIFOSPACE                   0xc160
#define XUSBPSU_GDBGLTSSM                       0xc164
#define XUSBPSU_GPRTBIMAP_HS0                   0xc180
#define XUSBPSU_GPRTBIMAP_HS1                   0xc184
#define XUSBPSU_GPRTBIMAP_FS0                   0xc188
#define XUSBPSU_GPRTBIMAP_FS1                   0xc18c

#define XUSBPSU_GUSB2PHYCFG(n)                  ((u32)0xc200 + ((u32)(n) * (u32)0x04))
#define XUSBPSU_GUSB2I2CCTL(n)                  ((u32)0xc240 + ((u32)(n) * (u32)0x04))

#define XUSBPSU_GUSB2PHYACC(n)                  ((u32)0xc280 + ((u32)(n) * (u32)0x04))

#define XUSBPSU_GUSB3PIPECTL(n)                 ((u32)0xc2c0 + ((u32)(n) * (u32)0x04))

#define XUSBPSU_GTXFIFOSIZ(n)                   ((u32)0xc300 + ((u32)(n) * (u32)0x04))
#define XUSBPSU_GRXFIFOSIZ(n)                   ((u32)0xc380 + ((u32)(n) * (u32)0x04))

#define XUSBPSU_GEVNTADRLO(n)                   ((u32)0xc400 + ((u32)(n) * (u32)0x10))
#define XUSBPSU_GEVNTADRHI(n)                   ((u32)0xc404 + ((u32)(n) * (u32)0x10))
#define XUSBPSU_GEVNTSIZ(n)                     ((u32)0xc408 + ((u32)(n) * (u32)0x10))
#define XUSBPSU_GEVNTCOUNT(n)                   ((u32)0xc40c + ((u32)(n) * (u32)0x10))

#define XUSBPSU_GHWPARAMS8                      0x0000c600U

/* Device Registers */
#define XUSBPSU_DCFG                            0x0000c700U
#define XUSBPSU_DCTL                            0x0000c704U
#define XUSBPSU_DEVTEN                          0x0000c708U
#define XUSBPSU_DSTS                            0x0000c70cU
#define XUSBPSU_DGCMDPAR                        0x0000c710U
#define XUSBPSU_DGCMD                           0x0000c714U
#define XUSBPSU_DALEPENA                        0x0000c720U
#define XUSBPSU_DEPCMDPAR2(n)                   ((u32)0xc800 + ((u32)n * (u32)0x10))
#define XUSBPSU_DEPCMDPAR1(n)                   ((u32)0xc804 + ((u32)n * (u32)0x10))
#define XUSBPSU_DEPCMDPAR0(n)                   ((u32)0xc808 + ((u32)n * (u32)0x10))
#define XUSBPSU_DEPCMD(n)                       ((u32)0xc80c + ((u32)n * (u32)0x10))

/* OTG Registers */
#define XUSBPSU_OCFG                            0x0000cc00U
#define XUSBPSU_OCTL                            0x0000cc04U
#define XUSBPSU_OEVT                            0xcc08U
#define XUSBPSU_OEVTEN                          0xcc0CU
#define XUSBPSU_OSTS                            0xcc10U

/* Bit fields */

/* Global Configuration Register */
#define XUSBPSU_GCTL_PWRDNSCALE(n)              ((n) << 19)
#define XUSBPSU_GCTL_U2RSTECN                   (1 << 16)
#define XUSBPSU_GCTL_RAMCLKSEL(x)       (((x) & XUSBPSU_GCTL_CLK_MASK) << 6)
#define XUSBPSU_GCTL_CLK_BUS                    (0U)
#define XUSBPSU_GCTL_CLK_PIPE                   (1U)
#define XUSBPSU_GCTL_CLK_PIPEHALF               (2U)
#define XUSBPSU_GCTL_CLK_MASK                   (3U)

#define XUSBPSU_GCTL_PRTCAP(n)                  (((n) & (3 << 12)) >> 12)
#define XUSBPSU_GCTL_PRTCAPDIR(n)               ((n) << 12)
#define XUSBPSU_GCTL_PRTCAP_HOST                1U
#define XUSBPSU_GCTL_PRTCAP_DEVICE              2U
#define XUSBPSU_GCTL_PRTCAP_OTG                 3U

#define XUSBPSU_GCTL_CORESOFTRESET              (0x00000001U << 11)
#define XUSBPSU_GCTL_SOFITPSYNC                 (0x00000001U << 10)
#define XUSBPSU_GCTL_SCALEDOWN(n)               ((u32)(n) << 4)
#define XUSBPSU_GCTL_SCALEDOWN_MASK             XUSBPSU_GCTL_SCALEDOWN(3)
#define XUSBPSU_GCTL_DISSCRAMBLE                (0x00000001U << 3)
#define XUSBPSU_GCTL_U2EXIT_LFPS                (0x00000001U << 2)
#define XUSBPSU_GCTL_GBLHIBERNATIONEN           (0x00000001U << 1)
#define XUSBPSU_GCTL_DSBLCLKGTNG                (0x00000001U << 0)

/* Global Status Register Device Interrupt Mask */
#define XUSBPSU_GSTS_DEVICE_IP_MASK 			0x00000040
#define XUSBPSU_GSTS_CUR_MODE			(0x00000001U << 0)

/* Global USB2 PHY Configuration Register */
#define XUSBPSU_GUSB2PHYCFG_PHYSOFTRST          (0x00000001U << 31)
#define XUSBPSU_GUSB2PHYCFG_SUSPHY              (0x00000001U << 6)

/* Global USB3 PIPE Control Register */
#define XUSBPSU_GUSB3PIPECTL_PHYSOFTRST         (0x00000001U << 31)
#define XUSBPSU_GUSB3PIPECTL_SUSPHY             (0x00000001U << 17)

/* Global TX Fifo Size Register */
#define XUSBPSU_GTXFIFOSIZ_TXFDEF(n)            ((u32)(n) & (u32)0xffffU)
#define XUSBPSU_GTXFIFOSIZ_TXFSTADDR(n)         ((u32)(n) & 0xffff0000U)

/* Global Event Size Registers */
#define XUSBPSU_GEVNTSIZ_INTMASK                ((u32)0x00000001U << 31U)
#define XUSBPSU_GEVNTSIZ_SIZE(n)                ((u32)(n) & (u32)0xffffU)

/* Global HWPARAMS1 Register */
#define XUSBPSU_GHWPARAMS1_EN_PWROPT(n)         (((u32)(n) & ((u32)3 << 24)) >> 24)
#define XUSBPSU_GHWPARAMS1_EN_PWROPT_NO         0U
#define XUSBPSU_GHWPARAMS1_EN_PWROPT_CLK        1U
#define XUSBPSU_GHWPARAMS1_EN_PWROPT_HIB        2U
#define XUSBPSU_GHWPARAMS1_PWROPT(n)            ((u32)(n) << 24)
#define XUSBPSU_GHWPARAMS1_PWROPT_MASK          XUSBPSU_GHWPARAMS1_PWROPT(3)

/* Global HWPARAMS4 Register */
#define XUSBPSU_GHWPARAMS4_HIBER_SCRATCHBUFS(n) (((u32)(n) & ((u32)0x0f << 13)) >> 13)
#define XUSBPSU_MAX_HIBER_SCRATCHBUFS           15U

/* Device Configuration Register */
#define XUSBPSU_DCFG_DEVADDR(addr)              ((u32)(addr) << 3)
#define XUSBPSU_DCFG_DEVADDR_MASK               XUSBPSU_DCFG_DEVADDR(0x7f)

#define XUSBPSU_DCFG_SPEED_MASK					7U
#define XUSBPSU_DCFG_SUPERSPEED					4U
#define XUSBPSU_DCFG_HIGHSPEED					0U
#define XUSBPSU_DCFG_FULLSPEED2					1U
#define XUSBPSU_DCFG_LOWSPEED					2U
#define XUSBPSU_DCFG_FULLSPEED1					3U

#define XUSBPSU_DCFG_LPM_CAP                    (0x00000001U << 22U)

/* Device Control Register */
#define XUSBPSU_DCTL_RUN_STOP                   (0x00000001U << 31U)
#define XUSBPSU_DCTL_CSFTRST                    ((u32)0x00000001U << 30U)
#define XUSBPSU_DCTL_LSFTRST                    (0x00000001U << 29U)

#define XUSBPSU_DCTL_HIRD_THRES_MASK            (0x0000001fU << 24U)
#define XUSBPSU_DCTL_HIRD_THRES(n)              ((u32)(n) << 24)

#define XUSBPSU_DCTL_APPL1RES                   (0x00000001U << 23)

/* These apply for core versions 1.87a and earlier */
#define XUSBPSU_DCTL_TRGTULST_MASK              (0x0000000fU << 17)
#define XUSBPSU_DCTL_TRGTULST(n)                ((u32)(n) << 17)
#define XUSBPSU_DCTL_TRGTULST_U2                (XUSBPSU_DCTL_TRGTULST(2))
#define XUSBPSU_DCTL_TRGTULST_U3                (XUSBPSU_DCTL_TRGTULST(3))
#define XUSBPSU_DCTL_TRGTULST_SS_DIS            (XUSBPSU_DCTL_TRGTULST(4))
#define XUSBPSU_DCTL_TRGTULST_RX_DET            (XUSBPSU_DCTL_TRGTULST(5))
#define XUSBPSU_DCTL_TRGTULST_SS_INACT          (XUSBPSU_DCTL_TRGTULST(6))

/* These apply for core versions 1.94a and later */
#define XUSBPSU_DCTL_KEEP_CONNECT               (0x00000001U << 19)
#define XUSBPSU_DCTL_L1_HIBER_EN                (0x00000001U << 18)
#define XUSBPSU_DCTL_CRS                        (0x00000001U << 17)
#define XUSBPSU_DCTL_CSS                        (0x00000001U << 16)

#define XUSBPSU_DCTL_INITU2ENA                  (0x00000001U << 12)
#define XUSBPSU_DCTL_ACCEPTU2ENA                (0x00000001U << 11)
#define XUSBPSU_DCTL_INITU1ENA                  (0x00000001U << 10)
#define XUSBPSU_DCTL_ACCEPTU1ENA                (0x00000001U << 9)
#define XUSBPSU_DCTL_TSTCTRL_MASK               (0x0000000fU << 1)

#define XUSBPSU_DCTL_ULSTCHNGREQ_MASK           (0x0000000fU << 5)
#define XUSBPSU_DCTL_ULSTCHNGREQ(n) (((u32)(n) << 5) & XUSBPSU_DCTL_ULSTCHNGREQ_MASK)

#define XUSBPSU_DCTL_ULSTCHNG_NO_ACTION         (XUSBPSU_DCTL_ULSTCHNGREQ(0))
#define XUSBPSU_DCTL_ULSTCHNG_SS_DISABLED       (XUSBPSU_DCTL_ULSTCHNGREQ(4))
#define XUSBPSU_DCTL_ULSTCHNG_RX_DETECT         (XUSBPSU_DCTL_ULSTCHNGREQ(5))
#define XUSBPSU_DCTL_ULSTCHNG_SS_INACTIVE       (XUSBPSU_DCTL_ULSTCHNGREQ(6))
#define XUSBPSU_DCTL_ULSTCHNG_RECOVERY          (XUSBPSU_DCTL_ULSTCHNGREQ(8))
#define XUSBPSU_DCTL_ULSTCHNG_COMPLIANCE        (XUSBPSU_DCTL_ULSTCHNGREQ(10))
#define XUSBPSU_DCTL_ULSTCHNG_LOOPBACK          (XUSBPSU_DCTL_ULSTCHNGREQ(11))

/* Device Event Enable Register */
#define XUSBPSU_DEVTEN_VNDRDEVTSTRCVEDEN        ((u32)0x00000001 << 12)
#define XUSBPSU_DEVTEN_EVNTOVERFLOWEN           ((u32)0x00000001 << 11)
#define XUSBPSU_DEVTEN_CMDCMPLTEN               ((u32)0x00000001 << 10)
#define XUSBPSU_DEVTEN_ERRTICERREN              ((u32)0x00000001 << 9)
#define XUSBPSU_DEVTEN_SOFEN                    ((u32)0x00000001 << 7)
#define XUSBPSU_DEVTEN_EOPFEN                   ((u32)0x00000001 << 6)
#define XUSBPSU_DEVTEN_HIBERNATIONREQEVTEN      ((u32)0x00000001 << 5)
#define XUSBPSU_DEVTEN_WKUPEVTEN                ((u32)0x00000001 << 4)
#define XUSBPSU_DEVTEN_ULSTCNGEN                ((u32)0x00000001 << 3)
#define XUSBPSU_DEVTEN_CONNECTDONEEN            ((u32)0x00000001 << 2)
#define XUSBPSU_DEVTEN_USBRSTEN                 ((u32)0x00000001 << 1)
#define XUSBPSU_DEVTEN_DISCONNEVTEN             ((u32)0x00000001 << 0)

/* Device Status Register */
#define XUSBPSU_DSTS_DCNRD                      (0x00000001U << 29)

/* This applies for core versions 1.87a and earlier */
#define XUSBPSU_DSTS_PWRUPREQ                   (0x00000001U << 24)

/* These apply for core versions 1.94a and later */
#define XUSBPSU_DSTS_RSS                        (0x00000001U << 25)
#define XUSBPSU_DSTS_SSS                        (0x00000001U << 24)

#define XUSBPSU_DSTS_COREIDLE                   (0x00000001U << 23)
#define XUSBPSU_DSTS_DEVCTRLHLT                 (0x00000001U << 22)

#define XUSBPSU_DSTS_USBLNKST_MASK              (0x0000000fU << 18)
#define XUSBPSU_DSTS_USBLNKST(n) (((u32)(n) & XUSBPSU_DSTS_USBLNKST_MASK) >> 18)

#define XUSBPSU_DSTS_RXFIFOEMPTY                (0x00000001U << 17)

#define XUSBPSU_DSTS_SOFFN_MASK                 (0x00003fffU << 3)
#define XUSBPSU_DSTS_SOFFN(n)           (((u32)(n) & XUSBPSU_DSTS_SOFFN_MASK) >> 3)

#define XUSBPSU_DSTS_CONNECTSPD                 (0x00000007U << 0)

#define XUSBPSU_DSTS_SUPERSPEED                 (4U << 0)
#define XUSBPSU_DSTS_HIGHSPEED                  (0U << 0)
#define XUSBPSU_DSTS_FULLSPEED2                 (1U << 0)
#define XUSBPSU_DSTS_LOWSPEED                   (2U << 0)
#define XUSBPSU_DSTS_FULLSPEED1                 (3U << 0)

/*Portpmsc 3.0 bit field*/
#define XUSBPSU_PORTMSC_30_FLA_MASK				(1U << 16)
#define XUSBPSU_PORTMSC_30_U2_TIMEOUT_MASK		(0xffU << 8)
#define XUSBPSU_PORTMSC_30_U2_TIMEOUT_SHIFT		(8U)
#define XUSBPSU_PORTMSC_30_U1_TIMEOUT_MASK		(0xffU << 0)
#define XUSBPSU_PORTMSC_30_U1_TIMEOUT_SHIFT		(0U)

/* Register for LPD block */
#define RST_LPD_TOP				0x23C
#define USB0_CORE_RST				(1 << 6)
#define USB1_CORE_RST				(1 << 7)

/* Vendor registers for Xilinx */
#define XIL_CUR_PWR_STATE			0x00
#define XIL_PME_ENABLE				0x34
#define XIL_REQ_PWR_STATE			0x3c
#define XIL_PWR_CONFIG_USB3			0x48

#define XIL_REQ_PWR_STATE_D0			0
#define XIL_REQ_PWR_STATE_D3			3
#define XIL_PME_ENABLE_SIG_GEN			1
#define XIL_CUR_PWR_STATE_D0			0
#define XIL_CUR_PWR_STATE_D3			3
#define XIL_CUR_PWR_STATE_BITMASK		0x03

#define VENDOR_BASE_ADDRESS			0xFF9D0000
#define LPD_BASE_ADDRESS			0xFF5E0000

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
	Xil_In32((InstancePtr)->ConfigPtr->BaseAddress + (u32)(Offset))

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
	Xil_Out32((InstancePtr)->ConfigPtr->BaseAddress + (u32)(Offset), (u32)(Data))

/*****************************************************************************/
/**
*
* Read a vendor register of the USBPS8 device.
*
* @param       Offset is the offset of the register to read.
*
* @return      The contents of the register.
*
* @note                C-style Signature:
*              u32 XUsbPsu_ReadVendorReg(struct XUsbPsu *InstancePtr, u32 Offset);
*
******************************************************************************/
#define XUsbPsu_ReadVendorReg(Offset) \
       Xil_In32(VENDOR_BASE_ADDRESS + (u32)(Offset))

/*****************************************************************************/
/**
*
* Write a Vendor register of the USBPS8 device.
*
* @param       RegOffset is the offset of the register to write.
* @param       Data is the value to write to the register.
*
* @return      None.
*
* @note        C-style Signature:
*              void XUsbPsu_WriteVendorReg(struct XUsbPsu *InstancePtr,
*                                                              u32 Offset,u32 Data)
*
******************************************************************************/
#define XUsbPsu_WriteVendorReg(Offset, Data) \
       Xil_Out32(VENDOR_BASE_ADDRESS + (u32)(Offset), (u32)(Data))

/*****************************************************************************/
/**
*
* Read a LPD register of the USBPS8 device.
*
* @param       InstancePtr is a pointer to the XUsbPsu instance.
* @param       Offset is the offset of the register to read.
*
* @return      The contents of the register.
*
* @note                C-style Signature:
*              u32 XUsbPsu_ReadLpdReg(struct XUsbPsu *InstancePtr, u32 Offset);
*
******************************************************************************/
#define XUsbPsu_ReadLpdReg(Offset) \
       Xil_In32(LPD_BASE_ADDRESS + (u32)(Offset))

/*****************************************************************************/
/**
*
* Write a LPD register of the USBPS8 device.
*
* @param       InstancePtr is a pointer to the XUsbPsu instance.
* @param       RegOffset is the offset of the register to write.
* @param       Data is the value to write to the register.
*
* @return      None.
*
* @note        C-style Signature:
*              void XUsbPsu_WriteLpdReg(struct XUsbPsu *InstancePtr,
*                                                              u32 Offset,u32 Data)
*
******************************************************************************/
#define XUsbPsu_WriteLpdReg(Offset, Data) \
       Xil_Out32(LPD_BASE_ADDRESS + (u32)(Offset), (u32)(Data))

/************************** Function Prototypes ******************************/

#ifdef __cplusplus
}
#endif

#endif  /* End of protection macro. */
/** @} */
