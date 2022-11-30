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

#ifndef __MCF52259_RCM_H__
#define __MCF52259_RCM_H__


/*********************************************************************
*
* Reset Controller Module (RCM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_RCM_RCR                          (*(vuint8 *)(0x40110000))
#define MCF_RCM_RSR                          (*(vuint8 *)(0x40110001))


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
#define MCF_RCM_RSR_WDR                      (0x10)
#define MCF_RCM_RSR_SOFT                     (0x20)
#define MCF_RCM_RSR_LVD                      (0x40)


#endif /* __MCF52259_RCM_H__ */
