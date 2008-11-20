/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.91
 */

#ifndef __MCF52235_EPHY_H__
#define __MCF52235_EPHY_H__


/*********************************************************************
*
* Ethernet Physical Transceiver (EPHY)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_EPHY_EPHYCTL0                    (*(vuint8 *)(&__IPSBAR[0x1E0000]))
#define MCF_EPHY_EPHYCTL1                    (*(vuint8 *)(&__IPSBAR[0x1E0001]))
#define MCF_EPHY_EPHYSR                      (*(vuint8 *)(&__IPSBAR[0x1E0002]))


/* Bit definitions and macros for MCF_EPHY_EPHYCTL0 */
#define MCF_EPHY_EPHYCTL0_EPHYIEN            (0x1)
#define MCF_EPHY_EPHYCTL0_EPHYWAI            (0x4)
#define MCF_EPHY_EPHYCTL0_LEDEN              (0x8)
#define MCF_EPHY_EPHYCTL0_DIS10              (0x10)
#define MCF_EPHY_EPHYCTL0_DIS100             (0x20)
#define MCF_EPHY_EPHYCTL0_ANDIS              (0x40)
#define MCF_EPHY_EPHYCTL0_EPHYEN             (0x80)

/* Bit definitions and macros for MCF_EPHY_EPHYCTL1 */
#define MCF_EPHY_EPHYCTL1_PHYADD(x)          (((x)&0x1F)<<0)

/* Bit definitions and macros for MCF_EPHY_EPHYSR */
#define MCF_EPHY_EPHYSR_EPHYIF               (0x1)
#define MCF_EPHY_EPHYSR_10DIS                (0x10)
#define MCF_EPHY_EPHYSR_100DIS               (0x20)


#endif /* __MCF52235_EPHY_H__ */
