/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_FlexCAN_H__
#define __MCF5282_FlexCAN_H__


/*********************************************************************
*
* Flex Controller Area Network (FlexCAN)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_FlexCAN_CANMCR                   (*(vuint16*)(&__IPSBAR[0x1C0000]))
#define MCF_FlexCAN_CANCTRL0                 (*(vuint8 *)(&__IPSBAR[0x1C0006]))
#define MCF_FlexCAN_CANCTRL1                 (*(vuint8 *)(&__IPSBAR[0x1C0007]))
#define MCF_FlexCAN_PRESDIV                  (*(vuint8 *)(&__IPSBAR[0x1C0008]))
#define MCF_FlexCAN_CANCTRL2                 (*(vuint8 *)(&__IPSBAR[0x1C0009]))
#define MCF_FlexCAN_TIMER                    (*(vuint16*)(&__IPSBAR[0x1C000A]))
#define MCF_FlexCAN_RXGMASK                  (*(vuint32*)(&__IPSBAR[0x1C0010]))
#define MCF_FlexCAN_RX14MASK                 (*(vuint32*)(&__IPSBAR[0x1C0014]))
#define MCF_FlexCAN_RX15MASK                 (*(vuint32*)(&__IPSBAR[0x1C0018]))
#define MCF_FlexCAN_ESTAT                    (*(vuint16*)(&__IPSBAR[0x1C0020]))
#define MCF_FlexCAN_IMASK                    (*(vuint16*)(&__IPSBAR[0x1C0022]))
#define MCF_FlexCAN_IFLAG                    (*(vuint16*)(&__IPSBAR[0x1C0024]))
#define MCF_FlexCAN_RXECTR                   (*(vuint8 *)(&__IPSBAR[0x1C0026]))
#define MCF_FlexCAN_TXECTR                   (*(vuint8 *)(&__IPSBAR[0x1C0028]))



/* Bit definitions and macros for MCF_FlexCAN_CANMCR */
#define MCF_FlexCAN_CANMCR_STOPACK           (0x10)
#define MCF_FlexCAN_CANMCR_APS               (0x20)
#define MCF_FlexCAN_CANMCR_SELFWAKE          (0x40)
#define MCF_FlexCAN_CANMCR_SUPV              (0x80)
#define MCF_FlexCAN_CANMCR_FRZACK            (0x100)
#define MCF_FlexCAN_CANMCR_SOFTRST           (0x200)
#define MCF_FlexCAN_CANMCR_WAKEMSK           (0x400)
#define MCF_FlexCAN_CANMCR_NOTRDY            (0x800)
#define MCF_FlexCAN_CANMCR_HALT              (0x1000)
#define MCF_FlexCAN_CANMCR_FRZ               (0x4000)
#define MCF_FlexCAN_CANMCR_STOP              (0x8000)

/* Bit definitions and macros for MCF_FlexCAN_CANCTRL0 */
#define MCF_FlexCAN_CANCTRL0_TXMODE(x)       (((x)&0x3)<<0)
#define MCF_FlexCAN_CANCTRL0_RXMODE          (0x4)
#define MCF_FlexCAN_CANCTRL0_ERRMSK          (0x40)
#define MCF_FlexCAN_CANCTRL0_BOFFMSK         (0x80)

/* Bit definitions and macros for MCF_FlexCAN_CANCTRL1 */
#define MCF_FlexCAN_CANCTRL1_PROPSEG(x)      (((x)&0x7)<<0)
#define MCF_FlexCAN_CANCTRL1_LOM             (0x8)
#define MCF_FlexCAN_CANCTRL1_LBUF            (0x10)
#define MCF_FlexCAN_CANCTRL1_TSYNC           (0x20)
#define MCF_FlexCAN_CANCTRL1_SAMP            (0x80)

/* Bit definitions and macros for MCF_FlexCAN_PRESDIV */
#define MCF_FlexCAN_PRESDIV_PRES_DIV(x)      (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_FlexCAN_CANCTRL2 */
#define MCF_FlexCAN_CANCTRL2_PSEG2(x)        (((x)&0x7)<<0)
#define MCF_FlexCAN_CANCTRL2_PSEG1(x)        (((x)&0x7)<<0x3)
#define MCF_FlexCAN_CANCTRL2_RJW(x)          (((x)&0x3)<<0x6)

/* Bit definitions and macros for MCF_FlexCAN_TIMER */
#define MCF_FlexCAN_TIMER_TIMER(x)           (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_FlexCAN_RXGMASK */
#define MCF_FlexCAN_RXGMASK_MID(x)           (((x)&0x7FFFFFFF)<<0x1)

/* Bit definitions and macros for MCF_FlexCAN_RX14MASK */
#define MCF_FlexCAN_RX14MASK_MID(x)          (((x)&0x7FFFFFFF)<<0x1)

/* Bit definitions and macros for MCF_FlexCAN_RX15MASK */
#define MCF_FlexCAN_RX15MASK_MID(x)          (((x)&0x7FFFFFFF)<<0x1)

/* Bit definitions and macros for MCF_FlexCAN_ESTAT */
#define MCF_FlexCAN_ESTAT_WAKEINT            (0x1)
#define MCF_FlexCAN_ESTAT_BOFFINT            (0x2)
#define MCF_FlexCAN_ESTAT_ERRINT             (0x4)
#define MCF_FlexCAN_ESTAT_FCS(x)             (((x)&0x3)<<0x4)
#define MCF_FlexCAN_ESTAT_FCS_ACTIVE         (0)
#define MCF_FlexCAN_ESTAT_FCS_PASSIVE        (0x10)
#define MCF_FlexCAN_ESTAT_TXRX               (0x40)
#define MCF_FlexCAN_ESTAT_IDLE               (0x80)
#define MCF_FlexCAN_ESTAT_RXWARN             (0x100)
#define MCF_FlexCAN_ESTAT_TXWARN             (0x200)
#define MCF_FlexCAN_ESTAT_STUFFERR           (0x400)
#define MCF_FlexCAN_ESTAT_FORMERR            (0x800)
#define MCF_FlexCAN_ESTAT_CRCERR             (0x1000)
#define MCF_FlexCAN_ESTAT_ACKERR             (0x2000)
#define MCF_FlexCAN_ESTAT_BITERR(x)          (((x)&0x3)<<0xE)

/* Bit definitions and macros for MCF_FlexCAN_IMASK */
#define MCF_FlexCAN_IMASK_BUF0M              (0x1)
#define MCF_FlexCAN_IMASK_BUF1M              (0x2)
#define MCF_FlexCAN_IMASK_BUF2M              (0x4)
#define MCF_FlexCAN_IMASK_BUF3M              (0x8)
#define MCF_FlexCAN_IMASK_BUF4M              (0x10)
#define MCF_FlexCAN_IMASK_BUF5M              (0x20)
#define MCF_FlexCAN_IMASK_BUF6M              (0x40)
#define MCF_FlexCAN_IMASK_BUF7M              (0x80)
#define MCF_FlexCAN_IMASK_BUF8M              (0x100)
#define MCF_FlexCAN_IMASK_BUF9M              (0x200)
#define MCF_FlexCAN_IMASK_BUF10M             (0x400)
#define MCF_FlexCAN_IMASK_BUF11M             (0x800)
#define MCF_FlexCAN_IMASK_BUF12M             (0x1000)
#define MCF_FlexCAN_IMASK_BUF13M             (0x2000)
#define MCF_FlexCAN_IMASK_BUF14M             (0x4000)
#define MCF_FlexCAN_IMASK_BUF15M             (0x8000)
#define MCF_FlexCAN_IMASK_BUF(x)             (0x1<<(x))

/* Bit definitions and macros for MCF_FlexCAN_IFLAG */
#define MCF_FlexCAN_IFLAG_BUF0I              (0x1)
#define MCF_FlexCAN_IFLAG_BUF1I              (0x2)
#define MCF_FlexCAN_IFLAG_BUF2I              (0x4)
#define MCF_FlexCAN_IFLAG_BUF3I              (0x8)
#define MCF_FlexCAN_IFLAG_BUF4I              (0x10)
#define MCF_FlexCAN_IFLAG_BUF5I              (0x20)
#define MCF_FlexCAN_IFLAG_BUF6I              (0x40)
#define MCF_FlexCAN_IFLAG_BUF7I              (0x80)
#define MCF_FlexCAN_IFLAG_BUF8I              (0x100)
#define MCF_FlexCAN_IFLAG_BUF9I              (0x200)
#define MCF_FlexCAN_IFLAG_BUF10I             (0x400)
#define MCF_FlexCAN_IFLAG_BUF11I             (0x800)
#define MCF_FlexCAN_IFLAG_BUF12I             (0x1000)
#define MCF_FlexCAN_IFLAG_BUF13I             (0x2000)
#define MCF_FlexCAN_IFLAG_BUF14I             (0x4000)
#define MCF_FlexCAN_IFLAG_BUF15I             (0x8000)
#define MCF_FlexCAN_IFLAG_BUF(x)             (0x1<<(x))

/* Bit definitions and macros for MCF_FlexCAN_RXECTR */
#define MCF_FlexCAN_RXECTR_RXECTR(x)         (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_FlexCAN_TXECTR */
#define MCF_FlexCAN_TXECTR_TXECTR(x)         (((x)&0xFF)<<0)


#endif /* __MCF5282_FlexCAN_H__ */
