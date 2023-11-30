/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2008/02/26 Revision: 0.1
 *
 * (c) Copyright UNIS, spol. s r.o. 1997-2008
 * UNIS, spol. s r.o.
 * Jundrovska 33
 * 624 00 Brno
 * Czech Republic
 * http      : www.processorexpert.com
 * mail      : info@processorexpert.com
 */

#ifndef __MCF52259_TMR_H__
#define __MCF52259_TMR_H__


/*********************************************************************
*
* Timer Module (TMR)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_TMR0_TMR                         (*(vuint16*)(0x40000400))
#define MCF_TMR0_TRR                         (*(vuint16*)(0x40000404))
#define MCF_TMR0_TCR                         (*(vuint16*)(0x40000408))
#define MCF_TMR0_TCN                         (*(vuint16*)(0x4000040C))
#define MCF_TMR0_TER                         (*(vuint8 *)(0x40000411))

#define MCF_TMR1_TMR                         (*(vuint16*)(0x40000440))
#define MCF_TMR1_TRR                         (*(vuint16*)(0x40000444))
#define MCF_TMR1_TCR                         (*(vuint16*)(0x40000448))
#define MCF_TMR1_TCN                         (*(vuint16*)(0x4000044C))
#define MCF_TMR1_TER                         (*(vuint8 *)(0x40000451))

#define MCF_TMR2_TMR                         (*(vuint16*)(0x40000480))
#define MCF_TMR2_TRR                         (*(vuint16*)(0x40000484))
#define MCF_TMR2_TCR                         (*(vuint16*)(0x40000488))
#define MCF_TMR2_TCN                         (*(vuint16*)(0x4000048C))
#define MCF_TMR2_TER                         (*(vuint8 *)(0x40000491))

#define MCF_TMR3_TMR                         (*(vuint16*)(0x400004C0))
#define MCF_TMR3_TRR                         (*(vuint16*)(0x400004C4))
#define MCF_TMR3_TCR                         (*(vuint16*)(0x400004C8))
#define MCF_TMR3_TCN                         (*(vuint16*)(0x400004CC))
#define MCF_TMR3_TER                         (*(vuint8 *)(0x400004D1))

#define MCF_TMR_TMR(x)                       (*(vuint16*)(0x40000400 + ((x)*0x40)))
#define MCF_TMR_TRR(x)                       (*(vuint16*)(0x40000404 + ((x)*0x40)))
#define MCF_TMR_TCR(x)                       (*(vuint16*)(0x40000408 + ((x)*0x40)))
#define MCF_TMR_TCN(x)                       (*(vuint16*)(0x4000040C + ((x)*0x40)))
#define MCF_TMR_TER(x)                       (*(vuint8 *)(0x40000411 + ((x)*0x40)))


/* Bit definitions and macros for MCF_TMR_TMR */
#define MCF_TMR_TMR_RST                      (0x1)
#define MCF_TMR_TMR_CLK(x)                   (((x)&0x3)<<0x1)
#define MCF_TMR_TMR_CLK_STOP                 (0)
#define MCF_TMR_TMR_CLK_SYSCLK               (0x2)
#define MCF_TMR_TMR_CLK_DIV16                (0x4)
#define MCF_TMR_TMR_CLK_TIN                  (0x6)
#define MCF_TMR_TMR_FRR                      (0x8)
#define MCF_TMR_TMR_ORI                      (0x10)
#define MCF_TMR_TMR_OM                       (0x20)
#define MCF_TMR_TMR_CE(x)                    (((x)&0x3)<<0x6)
#define MCF_TMR_TMR_CE_NONE                  (0)
#define MCF_TMR_TMR_CE_RISE                  (0x40)
#define MCF_TMR_TMR_CE_FALL                  (0x80)
#define MCF_TMR_TMR_CE_ANY                   (0xC0)
#define MCF_TMR_TMR_PS(x)                    (((x)&0xFF)<<0x8)

/* Bit definitions and macros for MCF_TMR_TRR */
#define MCF_TMR_TRR_REF(x)                   (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_TMR_TCR */
#define MCF_TMR_TCR_CAP(x)                   (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_TMR_TCN */
#define MCF_TMR_TCN_COUNT(x)                 (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_TMR_TER */
#define MCF_TMR_TER_CAP                      (0x1)
#define MCF_TMR_TER_REF                      (0x2)


#endif /* __MCF52259_TMR_H__ */
