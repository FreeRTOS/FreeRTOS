/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2008/04/17 Revision: 0.2
 *
 * (c) Copyright UNIS, spol. s r.o. 1997-2008
 * UNIS, spol. s r.o.
 * Jundrovska 33
 * 624 00 Brno
 * Czech Republic
 * http      : www.processorexpert.com
 * mail      : info@processorexpert.com
 */

#ifndef __MCF52259_PIT_H__
#define __MCF52259_PIT_H__


/*********************************************************************
*
* Programmable Interrupt Timer (PIT)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_PIT0_PCSR                        (*(vuint16*)(0x40150000))
#define MCF_PIT0_PMR                         (*(vuint16*)(0x40150002))
#define MCF_PIT0_PCNTR                       (*(vuint16*)(0x40150004))

#define MCF_PIT1_PCSR                        (*(vuint16*)(0x40160000))
#define MCF_PIT1_PMR                         (*(vuint16*)(0x40160002))
#define MCF_PIT1_PCNTR                       (*(vuint16*)(0x40160004))

#define MCF_PIT_PCSR(x)                      (*(vuint16*)(0x40150000 + ((x)*0x10000)))
#define MCF_PIT_PMR(x)                       (*(vuint16*)(0x40150002 + ((x)*0x10000)))
#define MCF_PIT_PCNTR(x)                     (*(vuint16*)(0x40150004 + ((x)*0x10000)))


/* Bit definitions and macros for MCF_PIT_PCSR */
#define MCF_PIT_PCSR_EN                      (0x1)
#define MCF_PIT_PCSR_RLD                     (0x2)
#define MCF_PIT_PCSR_PIF                     (0x4)
#define MCF_PIT_PCSR_PIE                     (0x8)
#define MCF_PIT_PCSR_OVW                     (0x10)
#define MCF_PIT_PCSR_DBG                     (0x20)
#define MCF_PIT_PCSR_DOZE                    (0x40)
#define MCF_PIT_PCSR_PRE(x)                  (((x)&0xF)<<0x8)

/* Bit definitions and macros for MCF_PIT_PMR */
#define MCF_PIT_PMR_PM(x)                    (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_PIT_PCNTR */
#define MCF_PIT_PCNTR_PC(x)                  (((x)&0xFFFF)<<0)


#endif /* __MCF52259_PIT_H__ */
