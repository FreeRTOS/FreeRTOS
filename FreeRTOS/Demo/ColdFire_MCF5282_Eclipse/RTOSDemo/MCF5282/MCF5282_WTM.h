/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_WTM_H__
#define __MCF5282_WTM_H__


/*********************************************************************
*
* Watchdog Timer Module (WTM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_WTM_WCR                          (*(vuint16*)(&__IPSBAR[0x140000]))
#define MCF_WTM_WMR                          (*(vuint16*)(&__IPSBAR[0x140002]))
#define MCF_WTM_WCNTR                        (*(vuint16*)(&__IPSBAR[0x140004]))
#define MCF_WTM_WSR                          (*(vuint16*)(&__IPSBAR[0x140006]))


/* Bit definitions and macros for MCF_WTM_WCR */
#define MCF_WTM_WCR_EN                       (0x1)
#define MCF_WTM_WCR_HALTED                   (0x2)
#define MCF_WTM_WCR_DOZE                     (0x4)
#define MCF_WTM_WCR_WAIT                     (0x8)

/* Bit definitions and macros for MCF_WTM_WMR */
#define MCF_WTM_WMR_WM(x)                    (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_WTM_WCNTR */
#define MCF_WTM_WCNTR_WC(x)                  (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_WTM_WSR */
#define MCF_WTM_WSR_WS(x)                    (((x)&0xFFFF)<<0)


#endif /* __MCF5282_WTM_H__ */
