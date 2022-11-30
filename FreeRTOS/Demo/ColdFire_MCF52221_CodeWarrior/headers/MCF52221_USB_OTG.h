/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2008/05/23 Revision: 0.95
 *
 * (c) Copyright UNIS, a.s. 1997-2008
 * UNIS, a.s.
 * Jundrovska 33
 * 624 00 Brno
 * Czech Republic
 * http      : www.processorexpert.com
 * mail      : info@processorexpert.com
 */

#ifndef __MCF52221_USB_OTG_H__
#define __MCF52221_USB_OTG_H__


/*********************************************************************
*
* Universal Serial Bus - OTG Controller (USB_OTG)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_USB_OTG_PER_ID                   (*(vuint8 *)(0x401C0000))
#define MCF_USB_OTG_ID_COMP                  (*(vuint8 *)(0x401C0004))
#define MCF_USB_OTG_REV                      (*(vuint8 *)(0x401C0008))
#define MCF_USB_OTG_ADD_INFO                 (*(vuint8 *)(0x401C000C))
#define MCF_USB_OTG_OTG_INT_STAT             (*(vuint8 *)(0x401C0010))
#define MCF_USB_OTG_OTG_INT_EN               (*(vuint8 *)(0x401C0014))
#define MCF_USB_OTG_OTG_STAT                 (*(vuint8 *)(0x401C0018))
#define MCF_USB_OTG_OTG_CTRL                 (*(vuint8 *)(0x401C001C))
#define MCF_USB_OTG_INT_STAT                 (*(vuint8 *)(0x401C0080))
#define MCF_USB_OTG_INT_ENB                  (*(vuint8 *)(0x401C0084))
#define MCF_USB_OTG_ERR_STAT                 (*(vuint8 *)(0x401C0088))
#define MCF_USB_OTG_ERR_ENB                  (*(vuint8 *)(0x401C008C))
#define MCF_USB_OTG_STAT                     (*(vuint8 *)(0x401C0090))
#define MCF_USB_OTG_CTL                      (*(vuint8 *)(0x401C0094))
#define MCF_USB_OTG_ADDR                     (*(vuint8 *)(0x401C0098))
#define MCF_USB_OTG_BDT_PAGE_01              (*(vuint8 *)(0x401C009C))
#define MCF_USB_OTG_FRM_NUML                 (*(vuint8 *)(0x401C00A0))
#define MCF_USB_OTG_FRM_NUMH                 (*(vuint8 *)(0x401C00A4))
#define MCF_USB_OTG_TOKEN                    (*(vuint8 *)(0x401C00A8))
#define MCF_USB_OTG_SOF_THLD                 (*(vuint8 *)(0x401C00AC))
#define MCF_USB_OTG_BDT_PAGE_02              (*(vuint8 *)(0x401C00B0))
#define MCF_USB_OTG_BDT_PAGE_03              (*(vuint8 *)(0x401C00B4))
#define MCF_USB_OTG_ENDPT0                   (*(vuint8 *)(0x401C00C0))
#define MCF_USB_OTG_ENDPT1                   (*(vuint8 *)(0x401C00C4))
#define MCF_USB_OTG_ENDPT2                   (*(vuint8 *)(0x401C00C8))
#define MCF_USB_OTG_ENDPT3                   (*(vuint8 *)(0x401C00CC))
#define MCF_USB_OTG_ENDPT4                   (*(vuint8 *)(0x401C00D0))
#define MCF_USB_OTG_ENDPT5                   (*(vuint8 *)(0x401C00D4))
#define MCF_USB_OTG_ENDPT6                   (*(vuint8 *)(0x401C00D8))
#define MCF_USB_OTG_ENDPT7                   (*(vuint8 *)(0x401C00DC))
#define MCF_USB_OTG_ENDPT8                   (*(vuint8 *)(0x401C00E0))
#define MCF_USB_OTG_ENDPT9                   (*(vuint8 *)(0x401C00E4))
#define MCF_USB_OTG_ENDPT10                  (*(vuint8 *)(0x401C00E8))
#define MCF_USB_OTG_ENDPT11                  (*(vuint8 *)(0x401C00EC))
#define MCF_USB_OTG_ENDPT12                  (*(vuint8 *)(0x401C00F0))
#define MCF_USB_OTG_ENDPT13                  (*(vuint8 *)(0x401C00F4))
#define MCF_USB_OTG_ENDPT14                  (*(vuint8 *)(0x401C00F8))
#define MCF_USB_OTG_ENDPT15                  (*(vuint8 *)(0x401C00FC))
#define MCF_USB_OTG_USB_CTRL                 (*(vuint8 *)(0x401C0100))
#define MCF_USB_OTG_USB_OTG_OBSERVE          (*(vuint8 *)(0x401C0104))
#define MCF_USB_OTG_USB_OTG_CONTROL          (*(vuint8 *)(0x401C0108))
#define MCF_USB_OTG_ENDPT(x)                 (*(vuint8 *)(0x401C00C0 + ((x)*0x4)))

/* Other macros */
#define MCF_USB_OTG_FRM_NUM                  (MCF_USB_OTG_INT_STAT=MCF_USB_OTG_INT_STAT_SOF_TOK ,MCF_USB_OTG_FRM_NUML | (((vuint16)MCF_USB_OTG_FRM_NUMH)<<8))


/* Bit definitions and macros for MCF_USB_OTG_PER_ID */
#define MCF_USB_OTG_PER_ID_ID(x)             (((x)&0x3F)<<0)

/* Bit definitions and macros for MCF_USB_OTG_ID_COMP */
#define MCF_USB_OTG_ID_COMP_NID(x)           (((x)&0x3F)<<0)

/* Bit definitions and macros for MCF_USB_OTG_REV */
#define MCF_USB_OTG_REV_REV(x)               (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_USB_OTG_ADD_INFO */
#define MCF_USB_OTG_ADD_INFO_IEHOST          (0x1)
#define MCF_USB_OTG_ADD_INFO_IRQ_NUM(x)      (((x)&0x1F)<<0x3)

/* Bit definitions and macros for MCF_USB_OTG_OTG_INT_STAT */
#define MCF_USB_OTG_OTG_INT_STAT_A_VBUS_CHG  (0x1)
#define MCF_USB_OTG_OTG_INT_STAT_B_SESS_CHG  (0x4)
#define MCF_USB_OTG_OTG_INT_STAT_SESS_VLD_CHG (0x8)
#define MCF_USB_OTG_OTG_INT_STAT_LINE_STATE_CHG (0x20)
#define MCF_USB_OTG_OTG_INT_STAT_1_MSEC      (0x40)
#define MCF_USB_OTG_OTG_INT_STAT_ID_CHG      (0x80)

/* Bit definitions and macros for MCF_USB_OTG_OTG_INT_EN */
#define MCF_USB_OTG_OTG_INT_EN_A_VBUS_EN     (0x1)
#define MCF_USB_OTG_OTG_INT_EN_B_SESS_EN     (0x4)
#define MCF_USB_OTG_OTG_INT_EN_SESS_VLD_EN   (0x8)
#define MCF_USB_OTG_OTG_INT_EN_LINE_STATE_EN (0x20)
#define MCF_USB_OTG_OTG_INT_EN_1_MSEC_EN     (0x40)
#define MCF_USB_OTG_OTG_INT_EN_ID_EN         (0x80)

/* Bit definitions and macros for MCF_USB_OTG_OTG_STAT */
#define MCF_USB_OTG_OTG_STAT_A_VBUS_VLD      (0x1)
#define MCF_USB_OTG_OTG_STAT_B_SESS_END      (0x4)
#define MCF_USB_OTG_OTG_STAT_SESS_VLD        (0x8)
#define MCF_USB_OTG_OTG_STAT_LINE_STATE_STABLE (0x20)
#define MCF_USB_OTG_OTG_STAT_1_MSEC_EN       (0x40)
#define MCF_USB_OTG_OTG_STAT_ID              (0x80)

/* Bit definitions and macros for MCF_USB_OTG_OTG_CTRL */
#define MCF_USB_OTG_OTG_CTRL_VBUS_DSCHG      (0x1)
#define MCF_USB_OTG_OTG_CTRL_VBUS_CHG        (0x2)
#define MCF_USB_OTG_OTG_CTRL_OTG_EN          (0x4)
#define MCF_USB_OTG_OTG_CTRL_VBUS_ON         (0x8)
#define MCF_USB_OTG_OTG_CTRL_DM_LOW          (0x10)
#define MCF_USB_OTG_OTG_CTRL_DP_LOW          (0x20)
#define MCF_USB_OTG_OTG_CTRL_DP_HIGH         (0x80)

/* Bit definitions and macros for MCF_USB_OTG_INT_STAT */
#define MCF_USB_OTG_INT_STAT_USB_RST         (0x1)
#define MCF_USB_OTG_INT_STAT_ERROR           (0x2)
#define MCF_USB_OTG_INT_STAT_SOF_TOK         (0x4)
#define MCF_USB_OTG_INT_STAT_TOK_DNE         (0x8)
#define MCF_USB_OTG_INT_STAT_SLEEP           (0x10)
#define MCF_USB_OTG_INT_STAT_RESUME          (0x20)
#define MCF_USB_OTG_INT_STAT_ATTACH          (0x40)
#define MCF_USB_OTG_INT_STAT_STALL           (0x80)

/* Bit definitions and macros for MCF_USB_OTG_INT_ENB */
#define MCF_USB_OTG_INT_ENB_USB_RST_EN       (0x1)
#define MCF_USB_OTG_INT_ENB_ERROR_EN         (0x2)
#define MCF_USB_OTG_INT_ENB_SOF_TOK_EN       (0x4)
#define MCF_USB_OTG_INT_ENB_TOK_DNE_EN       (0x8)
#define MCF_USB_OTG_INT_ENB_SLEEP_EN         (0x10)
#define MCF_USB_OTG_INT_ENB_RESUME_EN        (0x20)
#define MCF_USB_OTG_INT_ENB_ATTACH_EN        (0x40)
#define MCF_USB_OTG_INT_ENB_STALL_EN         (0x80)

/* Bit definitions and macros for MCF_USB_OTG_ERR_STAT */
#define MCF_USB_OTG_ERR_STAT_PID_ERR         (0x1)
#define MCF_USB_OTG_ERR_STAT_CRC5_EOF        (0x2)
#define MCF_USB_OTG_ERR_STAT_CRC16           (0x4)
#define MCF_USB_OTG_ERR_STAT_DFN8            (0x8)
#define MCF_USB_OTG_ERR_STAT_BTO_ERR         (0x10)
#define MCF_USB_OTG_ERR_STAT_DMA_ERR         (0x20)
#define MCF_USB_OTG_ERR_STAT_BTS_ERR         (0x80)

/* Bit definitions and macros for MCF_USB_OTG_ERR_ENB */
#define MCF_USB_OTG_ERR_ENB_PID_ERR_EN       (0x1)
#define MCF_USB_OTG_ERR_ENB_CRC5_EOF_EN      (0x2)
#define MCF_USB_OTG_ERR_ENB_CRC16_EN         (0x4)
#define MCF_USB_OTG_ERR_ENB_DFN8_EN          (0x8)
#define MCF_USB_OTG_ERR_ENB_BTO_ERR_EN       (0x10)
#define MCF_USB_OTG_ERR_ENB_DMA_ERR_EN       (0x20)
#define MCF_USB_OTG_ERR_ENB_BTS_ERR_EN       (0x80)

/* Bit definitions and macros for MCF_USB_OTG_STAT */
#define MCF_USB_OTG_STAT_ODD                 (0x4)
#define MCF_USB_OTG_STAT_TX                  (0x8)
#define MCF_USB_OTG_STAT_ENDP(x)             (((x)&0xF)<<0x4)

/* Bit definitions and macros for MCF_USB_OTG_CTL */
#define MCF_USB_OTG_CTL_USB_EN_SOF_EN        (0x1)
#define MCF_USB_OTG_CTL_ODD_RST              (0x2)
#define MCF_USB_OTG_CTL_RESUME               (0x4)
#define MCF_USB_OTG_CTL_HOST_MODE_EN         (0x8)
#define MCF_USB_OTG_CTL_RESET                (0x10)
#define MCF_USB_OTG_CTL_TXSUSPEND_TOKENBUSY  (0x20)
#define MCF_USB_OTG_CTL_SE0                  (0x40)
#define MCF_USB_OTG_CTL_JSTATE               (0x80)

/* Bit definitions and macros for MCF_USB_OTG_ADDR */
#define MCF_USB_OTG_ADDR_ADDR(x)             (((x)&0x7F)<<0)
#define MCF_USB_OTG_ADDR_LS_EN               (0x80)

/* Bit definitions and macros for MCF_USB_OTG_BDT_PAGE_01 */
#define MCF_USB_OTG_BDT_PAGE_01_BDT_BA9      (0x2)
#define MCF_USB_OTG_BDT_PAGE_01_BDT_BA10     (0x4)
#define MCF_USB_OTG_BDT_PAGE_01_BDT_BA11     (0x8)
#define MCF_USB_OTG_BDT_PAGE_01_BDT_BA12     (0x10)
#define MCF_USB_OTG_BDT_PAGE_01_BDT_BA13     (0x20)
#define MCF_USB_OTG_BDT_PAGE_01_BDT_BA14     (0x40)
#define MCF_USB_OTG_BDT_PAGE_01_BDT_BA15     (0x80)

/* Bit definitions and macros for MCF_USB_OTG_FRM_NUML */
#define MCF_USB_OTG_FRM_NUML_FRM0            (0x1)
#define MCF_USB_OTG_FRM_NUML_FRM1            (0x2)
#define MCF_USB_OTG_FRM_NUML_FRM2            (0x4)
#define MCF_USB_OTG_FRM_NUML_FRM3            (0x8)
#define MCF_USB_OTG_FRM_NUML_FRM4            (0x10)
#define MCF_USB_OTG_FRM_NUML_FRM5            (0x20)
#define MCF_USB_OTG_FRM_NUML_FRM6            (0x40)
#define MCF_USB_OTG_FRM_NUML_FRM7            (0x80)

/* Bit definitions and macros for MCF_USB_OTG_FRM_NUMH */
#define MCF_USB_OTG_FRM_NUMH_FRM8            (0x1)
#define MCF_USB_OTG_FRM_NUMH_FRM9            (0x2)
#define MCF_USB_OTG_FRM_NUMH_FRM10           (0x4)

/* Bit definitions and macros for MCF_USB_OTG_TOKEN */
#define MCF_USB_OTG_TOKEN_TOKEN_ENDPT(x)     (((x)&0xF)<<0)
#define MCF_USB_OTG_TOKEN_TOKEN_PID(x)       (((x)&0xF)<<0x4)
#define MCF_USB_OTG_TOKEN_TOKEN_PID_OUT      (0x10)
#define MCF_USB_OTG_TOKEN_TOKEN_PID_IN       (0x90)
#define MCF_USB_OTG_TOKEN_TOKEN_PID_SETUP    (0xD0)

/* Bit definitions and macros for MCF_USB_OTG_SOF_THLD */
#define MCF_USB_OTG_SOF_THLD_CNT0            (0x1)
#define MCF_USB_OTG_SOF_THLD_CNT1            (0x2)
#define MCF_USB_OTG_SOF_THLD_CNT2            (0x4)
#define MCF_USB_OTG_SOF_THLD_CNT3            (0x8)
#define MCF_USB_OTG_SOF_THLD_CNT4            (0x10)
#define MCF_USB_OTG_SOF_THLD_CNT5            (0x20)
#define MCF_USB_OTG_SOF_THLD_CNT6            (0x40)
#define MCF_USB_OTG_SOF_THLD_CNT7            (0x80)

/* Bit definitions and macros for MCF_USB_OTG_BDT_PAGE_02 */
#define MCF_USB_OTG_BDT_PAGE_02_BDT_BA16     (0x1)
#define MCF_USB_OTG_BDT_PAGE_02_BDT_BA17     (0x2)
#define MCF_USB_OTG_BDT_PAGE_02_BDT_BA18     (0x4)
#define MCF_USB_OTG_BDT_PAGE_02_BDT_BA19     (0x8)
#define MCF_USB_OTG_BDT_PAGE_02_BDT_BA20     (0x10)
#define MCF_USB_OTG_BDT_PAGE_02_BDT_BA21     (0x20)
#define MCF_USB_OTG_BDT_PAGE_02_BDT_BA22     (0x40)
#define MCF_USB_OTG_BDT_PAGE_02_BDT_BA23     (0x80)

/* Bit definitions and macros for MCF_USB_OTG_BDT_PAGE_03 */
#define MCF_USB_OTG_BDT_PAGE_03_BDT_BA24     (0x1)
#define MCF_USB_OTG_BDT_PAGE_03_BDT_BA25     (0x2)
#define MCF_USB_OTG_BDT_PAGE_03_BDT_BA26     (0x4)
#define MCF_USB_OTG_BDT_PAGE_03_BDT_BA27     (0x8)
#define MCF_USB_OTG_BDT_PAGE_03_BDT_BA28     (0x10)
#define MCF_USB_OTG_BDT_PAGE_03_BDT_BA29     (0x20)
#define MCF_USB_OTG_BDT_PAGE_03_BDT_BA30     (0x40)
#define MCF_USB_OTG_BDT_PAGE_03_BDT_BA31     (0x80)

/* Bit definitions and macros for MCF_USB_OTG_ENDPT */
#define MCF_USB_OTG_ENDPT_EP_HSHK            (0x1)
#define MCF_USB_OTG_ENDPT_EP_STALL           (0x2)
#define MCF_USB_OTG_ENDPT_EP_TX_EN           (0x4)
#define MCF_USB_OTG_ENDPT_EP_RX_EN           (0x8)
#define MCF_USB_OTG_ENDPT_EP_CTL_DIS         (0x10)
#define MCF_USB_OTG_ENDPT_RETRY_DIS          (0x40)
#define MCF_USB_OTG_ENDPT_HOST_WO_HUB        (0x80)

/* Bit definitions and macros for MCF_USB_OTG_USB_CTRL */
#define MCF_USB_OTG_USB_CTRL_CLK_SRC(x)      (((x)&0x3)<<0)
#define MCF_USB_OTG_USB_CTRL_CLK_SRC_ALTCLK  (0)
#define MCF_USB_OTG_USB_CTRL_CLK_SRC_OSCCLK  (0x1)
#define MCF_USB_OTG_USB_CTRL_CLK_SRC_SYSCLK  (0x3)
#define MCF_USB_OTG_USB_CTRL_PDE             (0x40)
#define MCF_USB_OTG_USB_CTRL_SUSP            (0x80)

/* Bit definitions and macros for MCF_USB_OTG_USB_OTG_OBSERVE */
#define MCF_USB_OTG_USB_OTG_OBSERVE_VBUSDIS  (0x2)
#define MCF_USB_OTG_USB_OTG_OBSERVE_VBUSCHG  (0x4)
#define MCF_USB_OTG_USB_OTG_OBSERVE_VBUSE    (0x8)
#define MCF_USB_OTG_USB_OTG_OBSERVE_DM_PD    (0x10)
#define MCF_USB_OTG_USB_OTG_OBSERVE_DP_PD    (0x40)
#define MCF_USB_OTG_USB_OTG_OBSERVE_DP_PU    (0x80)

/* Bit definitions and macros for MCF_USB_OTG_USB_OTG_CONTROL */
#define MCF_USB_OTG_USB_OTG_CONTROL_SESSEND  (0x1)
#define MCF_USB_OTG_USB_OTG_CONTROL_SESSVLD  (0x2)
#define MCF_USB_OTG_USB_OTG_CONTROL_VBUSVLD  (0x4)
#define MCF_USB_OTG_USB_OTG_CONTROL_ID       (0x8)
#define MCF_USB_OTG_USB_OTG_CONTROL_VBUSD    (0x10)


#endif /* __MCF52221_USB_OTG_H__ */
