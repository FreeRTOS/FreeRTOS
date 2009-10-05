/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.91
 */

#ifndef __MCF52235_CLOCK_H__
#define __MCF52235_CLOCK_H__


/*********************************************************************
*
* Clock Module (CLOCK)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_CLOCK_SYNCR                      (*(vuint16*)(&__IPSBAR[0x120000]))
#define MCF_CLOCK_SYNSR                      (*(vuint8 *)(&__IPSBAR[0x120002]))
#define MCF_CLOCK_LPCR                       (*(vuint8 *)(&__IPSBAR[0x120007]))
#define MCF_CLOCK_CCHR                       (*(vuint8 *)(&__IPSBAR[0x120008]))
#define MCF_CLOCK_RTCDR                      (*(vuint32*)(&__IPSBAR[0x12000C]))


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
#define MCF_CLOCK_SYNSR_EXTOSC               (0x80)

/* Bit definitions and macros for MCF_CLOCK_LPCR */
#define MCF_CLOCK_LPCR_LPD(x)                (((x)&0xF)<<0)

/* Bit definitions and macros for MCF_CLOCK_CCHR */
#define MCF_CLOCK_CCHR_CCHR(x)               (((x)&0x7)<<0)

/* Bit definitions and macros for MCF_CLOCK_RTCDR */
#define MCF_CLOCK_RTCDR_RTCDF(x)             (((x)&0xFFFFFFFF)<<0)


#endif /* __MCF52235_CLOCK_H__ */
