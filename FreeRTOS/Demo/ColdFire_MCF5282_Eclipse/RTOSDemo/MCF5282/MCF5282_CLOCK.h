/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_CLOCK_H__
#define __MCF5282_CLOCK_H__


/*********************************************************************
*
* Clock Module (CLOCK)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_CLOCK_SYNCR                      (*(vuint16*)(&__IPSBAR[0x120000]))
#define MCF_CLOCK_SYNSR                      (*(vuint8 *)(&__IPSBAR[0x120002]))


/* Bit definitions and macros for MCF_CLOCK_SYNCR */
#define MCF_CLOCK_SYNCR_STPMD0               (0x4)
#define MCF_CLOCK_SYNCR_STPMD1               (0x8)
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
#define MCF_CLOCK_SYNSR_PLLREF               (0x20)
#define MCF_CLOCK_SYNSR_PLLSEL               (0x40)
#define MCF_CLOCK_SYNSR_PLLMODE              (0x80)


#endif /* __MCF5282_CLOCK_H__ */
