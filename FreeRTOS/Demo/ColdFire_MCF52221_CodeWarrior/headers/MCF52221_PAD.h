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

#ifndef __MCF52221_PAD_H__
#define __MCF52221_PAD_H__


/*********************************************************************
*
* Common GPIO
*
*********************************************************************/

/* Register read/write macros */
#define MCF_PAD_PSRR                         (*(vuint32*)(0x40100078))
#define MCF_PAD_PDSR                         (*(vuint32*)(0x4010007C))


/* Bit definitions and macros for MCF_PAD_PSRR */
#define MCF_PAD_PSRR_PSRR0                   (0x1)
#define MCF_PAD_PSRR_PSRR1                   (0x2)
#define MCF_PAD_PSRR_PSRR2                   (0x4)
#define MCF_PAD_PSRR_PSRR3                   (0x8)
#define MCF_PAD_PSRR_PSRR4                   (0x10)
#define MCF_PAD_PSRR_PSRR5                   (0x20)
#define MCF_PAD_PSRR_PSRR6                   (0x40)
#define MCF_PAD_PSRR_PSRR7                   (0x80)
#define MCF_PAD_PSRR_PSRR8                   (0x100)
#define MCF_PAD_PSRR_PSRR9                   (0x200)
#define MCF_PAD_PSRR_PSRR10                  (0x400)
#define MCF_PAD_PSRR_PSRR11                  (0x800)
#define MCF_PAD_PSRR_PSRR12                  (0x1000)
#define MCF_PAD_PSRR_PSRR13                  (0x2000)
#define MCF_PAD_PSRR_PSRR14                  (0x4000)
#define MCF_PAD_PSRR_PSRR15                  (0x8000)
#define MCF_PAD_PSRR_PSRR16                  (0x10000)
#define MCF_PAD_PSRR_PSRR17                  (0x20000)
#define MCF_PAD_PSRR_PSRR18                  (0x40000)
#define MCF_PAD_PSRR_PSRR19                  (0x80000)
#define MCF_PAD_PSRR_PSRR20                  (0x100000)
#define MCF_PAD_PSRR_PSRR21                  (0x200000)
#define MCF_PAD_PSRR_PSRR22                  (0x400000)
#define MCF_PAD_PSRR_PSRR23                  (0x800000)
#define MCF_PAD_PSRR_PSRR24                  (0x1000000)
#define MCF_PAD_PSRR_PSRR25                  (0x2000000)
#define MCF_PAD_PSRR_PSRR26                  (0x4000000)
#define MCF_PAD_PSRR_PSRR27                  (0x8000000)

/* Bit definitions and macros for MCF_PAD_PDSR */
#define MCF_PAD_PDSR_PDSR0                   (0x1)
#define MCF_PAD_PDSR_PDSR1                   (0x2)
#define MCF_PAD_PDSR_PDSR2                   (0x4)
#define MCF_PAD_PDSR_PDSR3                   (0x8)
#define MCF_PAD_PDSR_PDSR4                   (0x10)
#define MCF_PAD_PDSR_PDSR5                   (0x20)
#define MCF_PAD_PDSR_PDSR6                   (0x40)
#define MCF_PAD_PDSR_PDSR7                   (0x80)
#define MCF_PAD_PDSR_PDSR8                   (0x100)
#define MCF_PAD_PDSR_PDSR9                   (0x200)
#define MCF_PAD_PDSR_PDSR10                  (0x400)
#define MCF_PAD_PDSR_PDSR11                  (0x800)
#define MCF_PAD_PDSR_PDSR12                  (0x1000)
#define MCF_PAD_PDSR_PDSR13                  (0x2000)
#define MCF_PAD_PDSR_PDSR14                  (0x4000)
#define MCF_PAD_PDSR_PDSR15                  (0x8000)
#define MCF_PAD_PDSR_PDSR16                  (0x10000)
#define MCF_PAD_PDSR_PDSR17                  (0x20000)
#define MCF_PAD_PDSR_PDSR18                  (0x40000)
#define MCF_PAD_PDSR_PDSR19                  (0x80000)
#define MCF_PAD_PDSR_PDSR20                  (0x100000)
#define MCF_PAD_PDSR_PDSR21                  (0x200000)
#define MCF_PAD_PDSR_PDSR22                  (0x400000)
#define MCF_PAD_PDSR_PDSR23                  (0x800000)
#define MCF_PAD_PDSR_PDSR24                  (0x1000000)
#define MCF_PAD_PDSR_PDSR25                  (0x2000000)
#define MCF_PAD_PDSR_PDSR26                  (0x4000000)
#define MCF_PAD_PDSR_PDSR27                  (0x8000000)


#endif /* __MCF52221_PAD_H__ */
