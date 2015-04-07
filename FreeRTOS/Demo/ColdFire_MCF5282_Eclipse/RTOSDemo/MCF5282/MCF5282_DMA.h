/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_DMA_H__
#define __MCF5282_DMA_H__


/*********************************************************************
*
* DMA Controller (DMA)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_DMA0_SAR                         (*(vuint32*)(&__IPSBAR[0x100]))
#define MCF_DMA0_DAR                         (*(vuint32*)(&__IPSBAR[0x104]))
#define MCF_DMA0_DCR                         (*(vuint32*)(&__IPSBAR[0x108]))
#define MCF_DMA0_BCR                         (*(vuint32*)(&__IPSBAR[0x10C]))
#define MCF_DMA0_DSR                         (*(vuint8 *)(&__IPSBAR[0x110]))

#define MCF_DMA1_SAR                         (*(vuint32*)(&__IPSBAR[0x140]))
#define MCF_DMA1_DAR                         (*(vuint32*)(&__IPSBAR[0x144]))
#define MCF_DMA1_DCR                         (*(vuint32*)(&__IPSBAR[0x148]))
#define MCF_DMA1_BCR                         (*(vuint32*)(&__IPSBAR[0x14C]))
#define MCF_DMA1_DSR                         (*(vuint8 *)(&__IPSBAR[0x150]))

#define MCF_DMA2_SAR                         (*(vuint32*)(&__IPSBAR[0x180]))
#define MCF_DMA2_DAR                         (*(vuint32*)(&__IPSBAR[0x184]))
#define MCF_DMA2_DCR                         (*(vuint32*)(&__IPSBAR[0x188]))
#define MCF_DMA2_BCR                         (*(vuint32*)(&__IPSBAR[0x18C]))
#define MCF_DMA2_DSR                         (*(vuint8 *)(&__IPSBAR[0x190]))

#define MCF_DMA3_SAR                         (*(vuint32*)(&__IPSBAR[0x1C0]))
#define MCF_DMA3_DAR                         (*(vuint32*)(&__IPSBAR[0x1C4]))
#define MCF_DMA3_DCR                         (*(vuint32*)(&__IPSBAR[0x1C8]))
#define MCF_DMA3_BCR                         (*(vuint32*)(&__IPSBAR[0x1CC]))
#define MCF_DMA3_DSR                         (*(vuint8 *)(&__IPSBAR[0x1D0]))

#define MCF_DMA_SAR(x)                       (*(vuint32*)(&__IPSBAR[0x100 + ((x)*0x40)]))
#define MCF_DMA_DAR(x)                       (*(vuint32*)(&__IPSBAR[0x104 + ((x)*0x40)]))
#define MCF_DMA_DCR(x)                       (*(vuint32*)(&__IPSBAR[0x108 + ((x)*0x40)]))
#define MCF_DMA_BCR(x)                       (*(vuint32*)(&__IPSBAR[0x10C + ((x)*0x40)]))
#define MCF_DMA_DSR(x)                       (*(vuint8 *)(&__IPSBAR[0x110 + ((x)*0x40)]))


/* Bit definitions and macros for MCF_DMA_SAR */
#define MCF_DMA_SAR_SAR(x)                   (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_DMA_DAR */
#define MCF_DMA_DAR_DAR(x)                   (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_DMA_DCR */
#define MCF_DMA_DCR_AT                       (0x8000)
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
#define MCF_DMA_DCR_AA                       (0x10000000)
#define MCF_DMA_DCR_CS                       (0x20000000)
#define MCF_DMA_DCR_EEXT                     (0x40000000)
#define MCF_DMA_DCR_INT                      (0x80000000)
#define MCF_DMA_DCR_BWC_DMA                  (0)
#define MCF_DMA_DCR_BWC_512                  (0x2000000)
#define MCF_DMA_DCR_BWC_1024                 (0x4000000)
#define MCF_DMA_DCR_BWC_2048                 (0x6000000)
#define MCF_DMA_DCR_BWC_4096                 (0x8000000)
#define MCF_DMA_DCR_BWC_8192                 (0xA000000)
#define MCF_DMA_DCR_BWC_16384                (0xC000000)
#define MCF_DMA_DCR_BWC_32768                (0xE000000)

/* Bit definitions and macros for MCF_DMA_BCR */
#define MCF_DMA_BCR_BCR(x)                   (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_DMA_DSR */
#define MCF_DMA_DSR_DONE                     (0x1)
#define MCF_DMA_DSR_BSY                      (0x2)
#define MCF_DMA_DSR_REQ                      (0x4)
#define MCF_DMA_DSR_BED                      (0x10)
#define MCF_DMA_DSR_BES                      (0x20)
#define MCF_DMA_DSR_CE                       (0x40)


#endif /* __MCF5282_DMA_H__ */
