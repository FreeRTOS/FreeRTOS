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

#ifndef __MCF52259_CLOCK_H__
#define __MCF52259_CLOCK_H__


/*********************************************************************
*
* Clock Module (CLOCK)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_CLOCK_SYNCR                      (*(vuint16*)(0x40120000))
#define MCF_CLOCK_SYNSR                      (*(vuint8 *)(0x40120002))
#define MCF_CLOCK_ROCR                       (*(vuint16*)(0x40120004))
#define MCF_CLOCK_LPDR                       (*(vuint8 *)(0x40120007))
#define MCF_CLOCK_CCHR                       (*(vuint8 *)(0x40120008))
#define MCF_CLOCK_CCLR                       (*(vuint8 *)(0x40120009))
#define MCF_CLOCK_OCHR                       (*(vuint8 *)(0x4012000A))
#define MCF_CLOCK_OCLR                       (*(vuint8 *)(0x4012000B))
#define MCF_CLOCK_RTCCR                      (*(vuint8 *)(0x40120012))
#define MCF_CLOCK_BWCR                       (*(vuint8 *)(0x40120013))


/* Bit definitions and macros for MCF_CLOCK_SYNCR */
#define MCF_CLOCK_SYNCR_PLLEN                (0x1)
#define MCF_CLOCK_SYNCR_PLLMODE              (0x2)
#define MCF_CLOCK_SYNCR_CLKSRC               (0x4)
#define MCF_CLOCK_SYNCR_FWKUP                (0x20)
#define MCF_CLOCK_SYNCR_DISCLK               (0x40)
#define MCF_CLOCK_SYNCR_LOCEN                (0x80)
#define MCF_CLOCK_SYNCR_RFD(x)               (((x)&0x7)<<0x8)
#define MCF_CLOCK_SYNCR_LOCRE                (0x800)
#define MCF_CLOCK_SYNCR_MFD(x)               (((x)&0x7)<<0xC)
#define MCF_CLOCK_SYNCR_LOLRE                (0x8000)

/* Bit definitions and macros for MCF_CLOCK_SYNSR */
#define MCF_CLOCK_SYNSR_LOCS                 (0x4)
#define MCF_CLOCK_SYNSR_LOCK                 (0x8)
#define MCF_CLOCK_SYNSR_LOCKS                (0x10)
#define MCF_CLOCK_SYNSR_CRYOSC               (0x20)
#define MCF_CLOCK_SYNSR_OCOSC                (0x40)
#define MCF_CLOCK_SYNSR_EXTOSC               (0x80)

/* Bit definitions and macros for MCF_CLOCK_ROCR */
#define MCF_CLOCK_ROCR_TRIM(x)               (((x)&0x3FF)<<0)

/* Bit definitions and macros for MCF_CLOCK_LPDR */
#define MCF_CLOCK_LPDR_LPD(x)                (((x)&0xF)<<0)

/* Bit definitions and macros for MCF_CLOCK_CCHR */
#define MCF_CLOCK_CCHR_CCHR(x)               (((x)&0x7)<<0)

/* Bit definitions and macros for MCF_CLOCK_CCLR */
#define MCF_CLOCK_CCLR_OSCSEL0               (0x1)
#define MCF_CLOCK_CCLR_OSCSEL1               (0x2)

/* Bit definitions and macros for MCF_CLOCK_OCHR */
#define MCF_CLOCK_OCHR_STBY                  (0x40)
#define MCF_CLOCK_OCHR_OCOEN                 (0x80)

/* Bit definitions and macros for MCF_CLOCK_OCLR */
#define MCF_CLOCK_OCLR_RANGE                 (0x10)
#define MCF_CLOCK_OCLR_LPEN                  (0x20)
#define MCF_CLOCK_OCLR_REFS                  (0x40)
#define MCF_CLOCK_OCLR_OSCEN                 (0x80)

/* Bit definitions and macros for MCF_CLOCK_RTCCR */
#define MCF_CLOCK_RTCCR_RTCSEL               (0x1)
#define MCF_CLOCK_RTCCR_LPEN                 (0x2)
#define MCF_CLOCK_RTCCR_REFS                 (0x4)
#define MCF_CLOCK_RTCCR_KHZEN                (0x8)
#define MCF_CLOCK_RTCCR_OSCEN                (0x10)
#define MCF_CLOCK_RTCCR_EXTALEN              (0x40)

/* Bit definitions and macros for MCF_CLOCK_BWCR */
#define MCF_CLOCK_BWCR_BWDSEL                (0x1)
#define MCF_CLOCK_BWCR_BWDSTOP               (0x2)


#endif /* __MCF52259_CLOCK_H__ */
