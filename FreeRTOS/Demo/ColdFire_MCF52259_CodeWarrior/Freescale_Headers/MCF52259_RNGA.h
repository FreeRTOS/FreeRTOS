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

#ifndef __MCF52259_RNGA_H__
#define __MCF52259_RNGA_H__


/*********************************************************************
*
* Random Number Generator (RNG)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_RNGA_RNGCR                       (*(vuint32*)(0x401F0000))
#define MCF_RNGA_RNGSR                       (*(vuint32*)(0x401F0004))
#define MCF_RNGA_RNGER                       (*(vuint32*)(0x401F0008))
#define MCF_RNGA_RNGOUT                      (*(vuint32*)(0x401F000C))


/* Bit definitions and macros for MCF_RNGA_RNGCR */
#define MCF_RNGA_RNGCR_GO                    (0x1)
#define MCF_RNGA_RNGCR_HA                    (0x2)
#define MCF_RNGA_RNGCR_IM                    (0x4)
#define MCF_RNGA_RNGCR_CI                    (0x8)
#define MCF_RNGA_RNGCR_SLM                   (0x10)

/* Bit definitions and macros for MCF_RNGA_RNGSR */
#define MCF_RNGA_RNGSR_SV                    (0x1)
#define MCF_RNGA_RNGSR_LRS                   (0x2)
#define MCF_RNGA_RNGSR_FUF                   (0x4)
#define MCF_RNGA_RNGSR_EI                    (0x8)
#define MCF_RNGA_RNGSR_SLP                   (0x10)
#define MCF_RNGA_RNGSR_OFL(x)                (((x)&0xFF)<<0x8)
#define MCF_RNGA_RNGSR_OFS(x)                (((x)&0xFF)<<0x10)

/* Bit definitions and macros for MCF_RNGA_RNGER */
#define MCF_RNGA_RNGER_ENT(x)                (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_RNGA_RNGOUT */
#define MCF_RNGA_RNGOUT_RANDOM_OUTPUT(x)     (((x)&0xFFFFFFFF)<<0)


#endif /* __MCF52259_RNGA_H__ */
