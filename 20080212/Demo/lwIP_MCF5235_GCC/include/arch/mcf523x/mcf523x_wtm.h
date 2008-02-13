/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_wtm.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_WTM_H__
#define __MCF523X_WTM_H__

/*********************************************************************
*
* Watchdog Timer Modules (WTM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_WTM_WCR      (*(vuint16*)(void*)(&__IPSBAR[0x140000]))
#define MCF_WTM_WMR      (*(vuint16*)(void*)(&__IPSBAR[0x140002]))
#define MCF_WTM_WCNTR    (*(vuint16*)(void*)(&__IPSBAR[0x140004]))
#define MCF_WTM_WSR      (*(vuint16*)(void*)(&__IPSBAR[0x140006]))

/* Bit definitions and macros for MCF_WTM_WCR */
#define MCF_WTM_WCR_EN        (0x0001)
#define MCF_WTM_WCR_HALTED    (0x0002)
#define MCF_WTM_WCR_DOZE      (0x0004)
#define MCF_WTM_WCR_WAIT      (0x0008)

/* Bit definitions and macros for MCF_WTM_WMR */
#define MCF_WTM_WMR_WM0       (0x0001)
#define MCF_WTM_WMR_WM1       (0x0002)
#define MCF_WTM_WMR_WM2       (0x0004)
#define MCF_WTM_WMR_WM3       (0x0008)
#define MCF_WTM_WMR_WM4       (0x0010)
#define MCF_WTM_WMR_WM5       (0x0020)
#define MCF_WTM_WMR_WM6       (0x0040)
#define MCF_WTM_WMR_WM7       (0x0080)
#define MCF_WTM_WMR_WM8       (0x0100)
#define MCF_WTM_WMR_WM9       (0x0200)
#define MCF_WTM_WMR_WM10      (0x0400)
#define MCF_WTM_WMR_WM11      (0x0800)
#define MCF_WTM_WMR_WM12      (0x1000)
#define MCF_WTM_WMR_WM13      (0x2000)
#define MCF_WTM_WMR_WM14      (0x4000)
#define MCF_WTM_WMR_WM15      (0x8000)

/* Bit definitions and macros for MCF_WTM_WCNTR */
#define MCF_WTM_WCNTR_WC0     (0x0001)
#define MCF_WTM_WCNTR_WC1     (0x0002)
#define MCF_WTM_WCNTR_WC2     (0x0004)
#define MCF_WTM_WCNTR_WC3     (0x0008)
#define MCF_WTM_WCNTR_WC4     (0x0010)
#define MCF_WTM_WCNTR_WC5     (0x0020)
#define MCF_WTM_WCNTR_WC6     (0x0040)
#define MCF_WTM_WCNTR_WC7     (0x0080)
#define MCF_WTM_WCNTR_WC8     (0x0100)
#define MCF_WTM_WCNTR_WC9     (0x0200)
#define MCF_WTM_WCNTR_WC10    (0x0400)
#define MCF_WTM_WCNTR_WC11    (0x0800)
#define MCF_WTM_WCNTR_WC12    (0x1000)
#define MCF_WTM_WCNTR_WC13    (0x2000)
#define MCF_WTM_WCNTR_WC14    (0x4000)
#define MCF_WTM_WCNTR_WC15    (0x8000)

/* Bit definitions and macros for MCF_WTM_WSR */
#define MCF_WTM_WSR_WS0       (0x0001)
#define MCF_WTM_WSR_WS1       (0x0002)
#define MCF_WTM_WSR_WS2       (0x0004)
#define MCF_WTM_WSR_WS3       (0x0008)
#define MCF_WTM_WSR_WS4       (0x0010)
#define MCF_WTM_WSR_WS5       (0x0020)
#define MCF_WTM_WSR_WS6       (0x0040)
#define MCF_WTM_WSR_WS7       (0x0080)
#define MCF_WTM_WSR_WS8       (0x0100)
#define MCF_WTM_WSR_WS9       (0x0200)
#define MCF_WTM_WSR_WS10      (0x0400)
#define MCF_WTM_WSR_WS11      (0x0800)
#define MCF_WTM_WSR_WS12      (0x1000)
#define MCF_WTM_WSR_WS13      (0x2000)
#define MCF_WTM_WSR_WS14      (0x4000)
#define MCF_WTM_WSR_WS15      (0x8000)

/********************************************************************/

#endif /* __MCF523X_WTM_H__ */
