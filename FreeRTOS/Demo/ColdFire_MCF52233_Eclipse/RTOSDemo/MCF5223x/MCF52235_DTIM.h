/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.91
 */

#ifndef __MCF52235_DTIM_H__
#define __MCF52235_DTIM_H__


/*********************************************************************
*
* DMA Timers (DTIM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_DTIM0_DTMR                       (*(vuint16*)(&__IPSBAR[0x400]))
#define MCF_DTIM0_DTXMR                      (*(vuint8 *)(&__IPSBAR[0x402]))
#define MCF_DTIM0_DTER                       (*(vuint8 *)(&__IPSBAR[0x403]))
#define MCF_DTIM0_DTRR                       (*(vuint32*)(&__IPSBAR[0x404]))
#define MCF_DTIM0_DTCR                       (*(vuint32*)(&__IPSBAR[0x408]))
#define MCF_DTIM0_DTCN                       (*(vuint32*)(&__IPSBAR[0x40C]))

#define MCF_DTIM1_DTMR                       (*(vuint16*)(&__IPSBAR[0x440]))
#define MCF_DTIM1_DTXMR                      (*(vuint8 *)(&__IPSBAR[0x442]))
#define MCF_DTIM1_DTER                       (*(vuint8 *)(&__IPSBAR[0x443]))
#define MCF_DTIM1_DTRR                       (*(vuint32*)(&__IPSBAR[0x444]))
#define MCF_DTIM1_DTCR                       (*(vuint32*)(&__IPSBAR[0x448]))
#define MCF_DTIM1_DTCN                       (*(vuint32*)(&__IPSBAR[0x44C]))

#define MCF_DTIM2_DTMR                       (*(vuint16*)(&__IPSBAR[0x480]))
#define MCF_DTIM2_DTXMR                      (*(vuint8 *)(&__IPSBAR[0x482]))
#define MCF_DTIM2_DTER                       (*(vuint8 *)(&__IPSBAR[0x483]))
#define MCF_DTIM2_DTRR                       (*(vuint32*)(&__IPSBAR[0x484]))
#define MCF_DTIM2_DTCR                       (*(vuint32*)(&__IPSBAR[0x488]))
#define MCF_DTIM2_DTCN                       (*(vuint32*)(&__IPSBAR[0x48C]))

#define MCF_DTIM3_DTMR                       (*(vuint16*)(&__IPSBAR[0x4C0]))
#define MCF_DTIM3_DTXMR                      (*(vuint8 *)(&__IPSBAR[0x4C2]))
#define MCF_DTIM3_DTER                       (*(vuint8 *)(&__IPSBAR[0x4C3]))
#define MCF_DTIM3_DTRR                       (*(vuint32*)(&__IPSBAR[0x4C4]))
#define MCF_DTIM3_DTCR                       (*(vuint32*)(&__IPSBAR[0x4C8]))
#define MCF_DTIM3_DTCN                       (*(vuint32*)(&__IPSBAR[0x4CC]))

#define MCF_DTIM_DTMR(x)                     (*(vuint16*)(&__IPSBAR[0x400 + ((x)*0x40)]))
#define MCF_DTIM_DTXMR(x)                    (*(vuint8 *)(&__IPSBAR[0x402 + ((x)*0x40)]))
#define MCF_DTIM_DTER(x)                     (*(vuint8 *)(&__IPSBAR[0x403 + ((x)*0x40)]))
#define MCF_DTIM_DTRR(x)                     (*(vuint32*)(&__IPSBAR[0x404 + ((x)*0x40)]))
#define MCF_DTIM_DTCR(x)                     (*(vuint32*)(&__IPSBAR[0x408 + ((x)*0x40)]))
#define MCF_DTIM_DTCN(x)                     (*(vuint32*)(&__IPSBAR[0x40C + ((x)*0x40)]))


/* Bit definitions and macros for MCF_DTIM_DTMR */
#define MCF_DTIM_DTMR_RST                    (0x1)
#define MCF_DTIM_DTMR_CLK(x)                 (((x)&0x3)<<0x1)
#define MCF_DTIM_DTMR_CLK_STOP               (0)
#define MCF_DTIM_DTMR_CLK_DIV1               (0x2)
#define MCF_DTIM_DTMR_CLK_DIV16              (0x4)
#define MCF_DTIM_DTMR_CLK_DTIN               (0x6)
#define MCF_DTIM_DTMR_FRR                    (0x8)
#define MCF_DTIM_DTMR_ORRI                   (0x10)
#define MCF_DTIM_DTMR_OM                     (0x20)
#define MCF_DTIM_DTMR_CE(x)                  (((x)&0x3)<<0x6)
#define MCF_DTIM_DTMR_CE_NONE                (0)
#define MCF_DTIM_DTMR_CE_RISE                (0x40)
#define MCF_DTIM_DTMR_CE_FALL                (0x80)
#define MCF_DTIM_DTMR_CE_ANY                 (0xC0)
#define MCF_DTIM_DTMR_PS(x)                  (((x)&0xFF)<<0x8)

/* Bit definitions and macros for MCF_DTIM_DTXMR */
#define MCF_DTIM_DTXMR_MODE16                (0x1)
#define MCF_DTIM_DTXMR_HALTED                (0x40)
#define MCF_DTIM_DTXMR_DMAEN                 (0x80)

/* Bit definitions and macros for MCF_DTIM_DTER */
#define MCF_DTIM_DTER_CAP                    (0x1)
#define MCF_DTIM_DTER_REF                    (0x2)

/* Bit definitions and macros for MCF_DTIM_DTRR */
#define MCF_DTIM_DTRR_REF(x)                 (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_DTIM_DTCR */
#define MCF_DTIM_DTCR_CAP(x)                 (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_DTIM_DTCN */
#define MCF_DTIM_DTCN_CNT(x)                 (((x)&0xFFFFFFFF)<<0)


#endif /* __MCF52235_DTIM_H__ */
