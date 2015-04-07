/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.91
 */

#ifndef __MCF52235_RCM_H__
#define __MCF52235_RCM_H__


/*********************************************************************
*
* Reset Controller Module (RCM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_RCM_RCR                          (*(vuint8 *)(&__IPSBAR[0x110000]))
#define MCF_RCM_RSR                          (*(vuint8 *)(&__IPSBAR[0x110001]))
#define MCF_RCM_CCR 		             (*(vuint16*)(&__IPSBAR[0x110004]))
#define MCF_RCM_CIR		             (*(vuint16*)(&__IPSBAR[0x11000A]))

/* Bit definitions and macros for MCF_RCM_RCR */
#define MCF_RCM_RCR_LVDE                     (0x1)
#define MCF_RCM_RCR_LVDRE                    (0x4)
#define MCF_RCM_RCR_LVDIE                    (0x8)
#define MCF_RCM_RCR_LVDF                     (0x10)
#define MCF_RCM_RCR_FRCRSTOUT                (0x40)
#define MCF_RCM_RCR_SOFTRST                  (0x80)

/* Bit definitions and macros for MCF_RCM_RSR */
#define MCF_RCM_RSR_LOL                      (0x1)
#define MCF_RCM_RSR_LOC                      (0x2)
#define MCF_RCM_RSR_EXT                      (0x4)
#define MCF_RCM_RSR_POR                      (0x8)
#define MCF_RCM_RSR_WDR			     (0x10)
#define MCF_RCM_RSR_SOFT                     (0x20)
#define MCF_RCM_RSR_LVD                      (0x40)

/* Bit definitions and macros for MCF_RCM_CCR */
#define MCF_RCM_CCR_LOAD		     (0x8000)


#endif /* __MCF52235_RCM_H__ */
