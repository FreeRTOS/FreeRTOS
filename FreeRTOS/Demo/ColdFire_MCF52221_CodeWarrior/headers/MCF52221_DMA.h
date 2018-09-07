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

#ifndef __MCF52221_DMA_H__
#define __MCF52221_DMA_H__


/*********************************************************************
*
* DMA Controller (DMA)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_DMA0_SAR                         (*(vuint32*)(0x40000100))
#define MCF_DMA0_DAR                         (*(vuint32*)(0x40000104))
#define MCF_DMA0_DSR                         (*(vuint8 *)(0x40000108))
#define MCF_DMA0_BCR                         (*(vuint32*)(0x40000108))
#define MCF_DMA0_DCR                         (*(vuint32*)(0x4000010C))

#define MCF_DMA1_SAR                         (*(vuint32*)(0x40000110))
#define MCF_DMA1_DAR                         (*(vuint32*)(0x40000114))
#define MCF_DMA1_DSR                         (*(vuint8 *)(0x40000118))
#define MCF_DMA1_BCR                         (*(vuint32*)(0x40000118))
#define MCF_DMA1_DCR                         (*(vuint32*)(0x4000011C))

#define MCF_DMA2_SAR                         (*(vuint32*)(0x40000120))
#define MCF_DMA2_DAR                         (*(vuint32*)(0x40000124))
#define MCF_DMA2_DSR                         (*(vuint8 *)(0x40000128))
#define MCF_DMA2_BCR                         (*(vuint32*)(0x40000128))
#define MCF_DMA2_DCR                         (*(vuint32*)(0x4000012C))

#define MCF_DMA3_SAR                         (*(vuint32*)(0x40000130))
#define MCF_DMA3_DAR                         (*(vuint32*)(0x40000134))
#define MCF_DMA3_DSR                         (*(vuint8 *)(0x40000138))
#define MCF_DMA3_BCR                         (*(vuint32*)(0x40000138))
#define MCF_DMA3_DCR                         (*(vuint32*)(0x4000013C))

#define MCF_DMA_SAR(x)                       (*(vuint32*)(0x40000100 + ((x)*0x10)))
#define MCF_DMA_DAR(x)                       (*(vuint32*)(0x40000104 + ((x)*0x10)))
#define MCF_DMA_DSR(x)                       (*(vuint8 *)(0x40000108 + ((x)*0x10)))
#define MCF_DMA_BCR(x)                       (*(vuint32*)(0x40000108 + ((x)*0x10)))
#define MCF_DMA_DCR(x)                       (*(vuint32*)(0x4000010C + ((x)*0x10)))


/* Bit definitions and macros for MCF_DMA_SAR */
#define MCF_DMA_SAR_SAR(x)                   (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_DMA_DAR */
#define MCF_DMA_DAR_DAR(x)                   (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_DMA_DSR */
#define MCF_DMA_DSR_DONE                     (0x1)
#define MCF_DMA_DSR_BSY                      (0x2)
#define MCF_DMA_DSR_REQ                      (0x4)
#define MCF_DMA_DSR_BED                      (0x10)
#define MCF_DMA_DSR_BES                      (0x20)
#define MCF_DMA_DSR_CE                       (0x40)

/* Bit definitions and macros for MCF_DMA_BCR */
#define MCF_DMA_BCR_BCR(x)                   (((x)&0xFFFFFF)<<0)
#define MCF_DMA_BCR_DSR(x)                   (((x)&0xFF)<<0x18)

/* Bit definitions and macros for MCF_DMA_DCR */
#define MCF_DMA_DCR_LCH2(x)                  (((x)&0x3)<<0)
#define MCF_DMA_DCR_LCH2_CH0                 (0)
#define MCF_DMA_DCR_LCH2_CH1                 (0x1)
#define MCF_DMA_DCR_LCH2_CH2                 (0x2)
#define MCF_DMA_DCR_LCH2_CH3                 (0x3)
#define MCF_DMA_DCR_LCH1(x)                  (((x)&0x3)<<0x2)
#define MCF_DMA_DCR_LCH1_CH0                 (0)
#define MCF_DMA_DCR_LCH1_CH1                 (0x1)
#define MCF_DMA_DCR_LCH1_CH2                 (0x2)
#define MCF_DMA_DCR_LCH1_CH3                 (0x3)
#define MCF_DMA_DCR_LINKCC(x)                (((x)&0x3)<<0x4)
#define MCF_DMA_DCR_D_REQ                    (0x80)
#define MCF_DMA_DCR_DMOD(x)                  (((x)&0xF)<<0x8)
#define MCF_DMA_DCR_DMOD_DIS                 (0)
#define MCF_DMA_DCR_DMOD_16                  (0x1)
#define MCF_DMA_DCR_DMOD_32                  (0x2)
#define MCF_DMA_DCR_DMOD_64                  (0x3)
#define MCF_DMA_DCR_DMOD_128                 (0x4)
#define MCF_DMA_DCR_DMOD_256                 (0x5)
#define MCF_DMA_DCR_DMOD_512                 (0x6)
#define MCF_DMA_DCR_DMOD_1K                  (0x7)
#define MCF_DMA_DCR_DMOD_2K                  (0x8)
#define MCF_DMA_DCR_DMOD_4K                  (0x9)
#define MCF_DMA_DCR_DMOD_8K                  (0xA)
#define MCF_DMA_DCR_DMOD_16K                 (0xB)
#define MCF_DMA_DCR_DMOD_32K                 (0xC)
#define MCF_DMA_DCR_DMOD_64K                 (0xD)
#define MCF_DMA_DCR_DMOD_128K                (0xE)
#define MCF_DMA_DCR_DMOD_256K                (0xF)
#define MCF_DMA_DCR_SMOD(x)                  (((x)&0xF)<<0xC)
#define MCF_DMA_DCR_SMOD_DIS                 (0)
#define MCF_DMA_DCR_SMOD_16                  (0x1)
#define MCF_DMA_DCR_SMOD_32                  (0x2)
#define MCF_DMA_DCR_SMOD_64                  (0x3)
#define MCF_DMA_DCR_SMOD_128                 (0x4)
#define MCF_DMA_DCR_SMOD_256                 (0x5)
#define MCF_DMA_DCR_SMOD_512                 (0x6)
#define MCF_DMA_DCR_SMOD_1K                  (0x7)
#define MCF_DMA_DCR_SMOD_2K                  (0x8)
#define MCF_DMA_DCR_SMOD_4K                  (0x9)
#define MCF_DMA_DCR_SMOD_8K                  (0xA)
#define MCF_DMA_DCR_SMOD_16K                 (0xB)
#define MCF_DMA_DCR_SMOD_32K                 (0xC)
#define MCF_DMA_DCR_SMOD_64K                 (0xD)
#define MCF_DMA_DCR_SMOD_128K                (0xE)
#define MCF_DMA_DCR_SMOD_256K                (0xF)
#define MCF_DMA_DCR_START                    (0x10000)
#define MCF_DMA_DCR_DSIZE(x)                 (((x)&0x3)<<0x11)
#define MCF_DMA_DCR_DSIZE_LONG               (0)
#define MCF_DMA_DCR_DSIZE_BYTE               (0x1)
#define MCF_DMA_DCR_DSIZE_WORD               (0x2)
#define MCF_DMA_DCR_DSIZE_LINE               (0x3)
#define MCF_DMA_DCR_DINC                     (0x80000)
#define MCF_DMA_DCR_SSIZE(x)                 (((x)&0x3)<<0x14)
#define MCF_DMA_DCR_SSIZE_LONG               (0)
#define MCF_DMA_DCR_SSIZE_BYTE               (0x1)
#define MCF_DMA_DCR_SSIZE_WORD               (0x2)
#define MCF_DMA_DCR_SSIZE_LINE               (0x3)
#define MCF_DMA_DCR_SINC                     (0x400000)
#define MCF_DMA_DCR_BWC(x)                   (((x)&0x7)<<0x19)
#define MCF_DMA_DCR_BWC_16K                  (0x1)
#define MCF_DMA_DCR_BWC_32K                  (0x2)
#define MCF_DMA_DCR_BWC_64K                  (0x3)
#define MCF_DMA_DCR_BWC_128K                 (0x4)
#define MCF_DMA_DCR_BWC_256K                 (0x5)
#define MCF_DMA_DCR_BWC_512K                 (0x6)
#define MCF_DMA_DCR_BWC_1024K                (0x7)
#define MCF_DMA_DCR_AA                       (0x10000000)
#define MCF_DMA_DCR_CS                       (0x20000000)
#define MCF_DMA_DCR_EEXT                     (0x40000000)
#define MCF_DMA_DCR_INT                      (0x80000000)


#endif /* __MCF52221_DMA_H__ */
