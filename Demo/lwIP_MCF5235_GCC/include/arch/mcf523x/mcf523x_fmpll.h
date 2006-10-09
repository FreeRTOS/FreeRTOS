/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_fmpll.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_FMPLL_H__
#define __MCF523X_FMPLL_H__

/*********************************************************************
*
* Frequency Modulated Phase Locked Loop (FMPLL)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_FMPLL_SYNCR    (*(vuint32*)(void*)(&__IPSBAR[0x120000]))
#define MCF_FMPLL_SYNSR    (*(vuint32*)(void*)(&__IPSBAR[0x120004]))

/* Bit definitions and macros for MCF_FMPLL_SYNCR */
#define MCF_FMPLL_SYNCR_EXP(x)       (((x)&0x000003FF)<<0)
#define MCF_FMPLL_SYNCR_DEPTH(x)     (((x)&0x00000003)<<10)
#define MCF_FMPLL_SYNCR_RATE         (0x00001000)
#define MCF_FMPLL_SYNCR_LOCIRQ       (0x00002000)
#define MCF_FMPLL_SYNCR_LOLIRQ       (0x00004000)
#define MCF_FMPLL_SYNCR_DISCLK       (0x00008000)
#define MCF_FMPLL_SYNCR_LOCRE        (0x00010000)
#define MCF_FMPLL_SYNCR_LOLRE        (0x00020000)
#define MCF_FMPLL_SYNCR_LOCEN        (0x00040000)
#define MCF_FMPLL_SYNCR_RFD(x)       (((x)&0x00000007)<<19)
#define MCF_FMPLL_SYNCR_MFD(x)       (((x)&0x00000007)<<24)

/* Bit definitions and macros for MCF_FMPLL_SYNSR */
#define MCF_FMPLL_SYNSR_CALPASS      (0x00000001)
#define MCF_FMPLL_SYNSR_CALDONE      (0x00000002)
#define MCF_FMPLL_SYNSR_LOCF         (0x00000004)
#define MCF_FMPLL_SYNSR_LOCK         (0x00000008)
#define MCF_FMPLL_SYNSR_LOCKS        (0x00000010)
#define MCF_FMPLL_SYNSR_PLLREF       (0x00000020)
#define MCF_FMPLL_SYNSR_PLLSEL       (0x00000040)
#define MCF_FMPLL_SYNSR_MODE         (0x00000080)
#define MCF_FMPLL_SYNSR_LOC          (0x00000100)
#define MCF_FMPLL_SYNSR_LOLF         (0x00000200)

/********************************************************************/

#endif /* __MCF523X_FMPLL_H__ */
