/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.91
 */

#ifndef __MCF52235_FlexCAN_H__
#define __MCF52235_FlexCAN_H__


/*********************************************************************
*
* Flex Controller Area Network (FlexCAN)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_FlexCAN_CANMCR                   (*(vuint32*)(&__IPSBAR[0x1C0000]))
#define MCF_FlexCAN_CANCTRL                  (*(vuint32*)(&__IPSBAR[0x1C0004]))
#define MCF_FlexCAN_TIMER                    (*(vuint32*)(&__IPSBAR[0x1C0008]))
#define MCF_FlexCAN_RXGMASK                  (*(vuint32*)(&__IPSBAR[0x1C0010]))
#define MCF_FlexCAN_RX14MASK                 (*(vuint32*)(&__IPSBAR[0x1C0014]))
#define MCF_FlexCAN_RX15MASK                 (*(vuint32*)(&__IPSBAR[0x1C0018]))
#define MCF_FlexCAN_ERRCNT                   (*(vuint32*)(&__IPSBAR[0x1C001C]))
#define MCF_FlexCAN_ERRSTAT                  (*(vuint32*)(&__IPSBAR[0x1C0020]))
#define MCF_FlexCAN_IMASK                    (*(vuint32*)(&__IPSBAR[0x1C0028]))
#define MCF_FlexCAN_IFLAG                    (*(vuint32*)(&__IPSBAR[0x1C0030]))



/* Bit definitions and macros for MCF_FlexCAN_CANMCR */
#define MCF_FlexCAN_CANMCR_MAXMB(x)          (((x)&0xF)<<0)
#define MCF_FlexCAN_CANMCR_LPMACK            (0x100000)
#define MCF_FlexCAN_CANMCR_SUPV              (0x800000)
#define MCF_FlexCAN_CANMCR_FRZACK            (0x1000000)
#define MCF_FlexCAN_CANMCR_SOFTRST           (0x2000000)
#define MCF_FlexCAN_CANMCR_NOTRDY            (0x8000000)
#define MCF_FlexCAN_CANMCR_HALT              (0x10000000)
#define MCF_FlexCAN_CANMCR_FRZ               (0x40000000)
#define MCF_FlexCAN_CANMCR_MDIS              (0x80000000)

/* Bit definitions and macros for MCF_FlexCAN_CANCTRL */
#define MCF_FlexCAN_CANCTRL_PROPSEG(x)       (((x)&0x7)<<0)
#define MCF_FlexCAN_CANCTRL_LOM              (0x8)
#define MCF_FlexCAN_CANCTRL_LBUF             (0x10)
#define MCF_FlexCAN_CANCTRL_TSYNC            (0x20)
#define MCF_FlexCAN_CANCTRL_BOFFREC          (0x40)
#define MCF_FlexCAN_CANCTRL_SAMP             (0x80)
#define MCF_FlexCAN_CANCTRL_LPB              (0x1000)
#define MCF_FlexCAN_CANCTRL_CLK_SRC          (0x2000)
#define MCF_FlexCAN_CANCTRL_ERRMSK           (0x4000)
#define MCF_FlexCAN_CANCTRL_BOFFMSK          (0x8000)
#define MCF_FlexCAN_CANCTRL_PSEG2(x)         (((x)&0x7)<<0x10)
#define MCF_FlexCAN_CANCTRL_PSEG1(x)         (((x)&0x7)<<0x13)
#define MCF_FlexCAN_CANCTRL_RJW(x)           (((x)&0x3)<<0x16)
#define MCF_FlexCAN_CANCTRL_PRESDIV(x)       (((x)&0xFF)<<0x18)

/* Bit definitions and macros for MCF_FlexCAN_TIMER */
#define MCF_FlexCAN_TIMER_TIMER(x)           (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_FlexCAN_RXGMASK */
#define MCF_FlexCAN_RXGMASK_MI(x)            (((x)&0x1FFFFFFF)<<0)

/* Bit definitions and macros for MCF_FlexCAN_RX14MASK */
#define MCF_FlexCAN_RX14MASK_MI(x)           (((x)&0x1FFFFFFF)<<0)

/* Bit definitions and macros for MCF_FlexCAN_RX15MASK */
#define MCF_FlexCAN_RX15MASK_MI(x)           (((x)&0x1FFFFFFF)<<0)

/* Bit definitions and macros for MCF_FlexCAN_ERRCNT */
#define MCF_FlexCAN_ERRCNT_TXECTR(x)         (((x)&0xFF)<<0)
#define MCF_FlexCAN_ERRCNT_RXECTR(x)         (((x)&0xFF)<<0x8)

/* Bit definitions and macros for MCF_FlexCAN_ERRSTAT */
#define MCF_FlexCAN_ERRSTAT_ERRINT           (0x2)
#define MCF_FlexCAN_ERRSTAT_BOFFINT          (0x4)
#define MCF_FlexCAN_ERRSTAT_FLTCONF(x)       (((x)&0x3)<<0x4)
#define MCF_FlexCAN_ERRSTAT_FLTCONF_ACTIVE   (0)
#define MCF_FlexCAN_ERRSTAT_FLTCONF_PASSIVE  (0x10)
#define MCF_FlexCAN_ERRSTAT_FLTCONF_BUSOFF   (0x20)
#define MCF_FlexCAN_ERRSTAT_TXRX             (0x40)
#define MCF_FlexCAN_ERRSTAT_IDLE             (0x80)
#define MCF_FlexCAN_ERRSTAT_RXWRN            (0x100)
#define MCF_FlexCAN_ERRSTAT_TXWRN            (0x200)
#define MCF_FlexCAN_ERRSTAT_STFERR           (0x400)
#define MCF_FlexCAN_ERRSTAT_FRMERR           (0x800)
#define MCF_FlexCAN_ERRSTAT_CRCERR           (0x1000)
#define MCF_FlexCAN_ERRSTAT_ACKERR           (0x2000)
#define MCF_FlexCAN_ERRSTAT_BIT0ERR          (0x4000)
#define MCF_FlexCAN_ERRSTAT_BIT1ERR          (0x8000)

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


#endif /* __MCF52235_FlexCAN_H__ */
