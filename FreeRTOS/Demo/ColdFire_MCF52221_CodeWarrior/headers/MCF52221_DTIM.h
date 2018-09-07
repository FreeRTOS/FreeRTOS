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

#ifndef __MCF52221_DTIM_H__
#define __MCF52221_DTIM_H__


/*********************************************************************
*
* DMA Timers (DTIM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_DTIM0_DTMR                       (*(vuint16*)(0x40000400))
#define MCF_DTIM0_DTXMR                      (*(vuint8 *)(0x40000402))
#define MCF_DTIM0_DTER                       (*(vuint8 *)(0x40000403))
#define MCF_DTIM0_DTRR                       (*(vuint32*)(0x40000404))
#define MCF_DTIM0_DTCR                       (*(vuint32*)(0x40000408))
#define MCF_DTIM0_DTCN                       (*(vuint32*)(0x4000040C))

#define MCF_DTIM1_DTMR                       (*(vuint16*)(0x40000440))
#define MCF_DTIM1_DTXMR                      (*(vuint8 *)(0x40000442))
#define MCF_DTIM1_DTER                       (*(vuint8 *)(0x40000443))
#define MCF_DTIM1_DTRR                       (*(vuint32*)(0x40000444))
#define MCF_DTIM1_DTCR                       (*(vuint32*)(0x40000448))
#define MCF_DTIM1_DTCN                       (*(vuint32*)(0x4000044C))

#define MCF_DTIM2_DTMR                       (*(vuint16*)(0x40000480))
#define MCF_DTIM2_DTXMR                      (*(vuint8 *)(0x40000482))
#define MCF_DTIM2_DTER                       (*(vuint8 *)(0x40000483))
#define MCF_DTIM2_DTRR                       (*(vuint32*)(0x40000484))
#define MCF_DTIM2_DTCR                       (*(vuint32*)(0x40000488))
#define MCF_DTIM2_DTCN                       (*(vuint32*)(0x4000048C))

#define MCF_DTIM3_DTMR                       (*(vuint16*)(0x400004C0))
#define MCF_DTIM3_DTXMR                      (*(vuint8 *)(0x400004C2))
#define MCF_DTIM3_DTER                       (*(vuint8 *)(0x400004C3))
#define MCF_DTIM3_DTRR                       (*(vuint32*)(0x400004C4))
#define MCF_DTIM3_DTCR                       (*(vuint32*)(0x400004C8))
#define MCF_DTIM3_DTCN                       (*(vuint32*)(0x400004CC))

#define MCF_DTIM_DTMR(x)                     (*(vuint16*)(0x40000400 + ((x)*0x40)))
#define MCF_DTIM_DTXMR(x)                    (*(vuint8 *)(0x40000402 + ((x)*0x40)))
#define MCF_DTIM_DTER(x)                     (*(vuint8 *)(0x40000403 + ((x)*0x40)))
#define MCF_DTIM_DTRR(x)                     (*(vuint32*)(0x40000404 + ((x)*0x40)))
#define MCF_DTIM_DTCR(x)                     (*(vuint32*)(0x40000408 + ((x)*0x40)))
#define MCF_DTIM_DTCN(x)                     (*(vuint32*)(0x4000040C + ((x)*0x40)))


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


#endif /* __MCF52221_DTIM_H__ */
