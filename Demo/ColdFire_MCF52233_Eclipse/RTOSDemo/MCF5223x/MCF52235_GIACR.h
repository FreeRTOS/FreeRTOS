/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.91
 */

#ifndef __MCF52235_GIACR_H__
#define __MCF52235_GIACR_H__


/*********************************************************************
*
* Global Interrupt Acknowledge Control Registers Module (GIACR)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_GIACR_GSWIACK                    (*(vuint8 *)(&__IPSBAR[0xFE0]))
#define MCF_GIACR_GL1IACK                    (*(vuint8 *)(&__IPSBAR[0xFE4]))
#define MCF_GIACR_GL2IACK                    (*(vuint8 *)(&__IPSBAR[0xFE8]))
#define MCF_GIACR_GL3IACK                    (*(vuint8 *)(&__IPSBAR[0xFEC]))
#define MCF_GIACR_GL4IACK                    (*(vuint8 *)(&__IPSBAR[0xFF0]))
#define MCF_GIACR_GL5IACK                    (*(vuint8 *)(&__IPSBAR[0xFF4]))
#define MCF_GIACR_GL6IACK                    (*(vuint8 *)(&__IPSBAR[0xFF8]))
#define MCF_GIACR_GL7IACK                    (*(vuint8 *)(&__IPSBAR[0xFFC]))
#define MCF_GIACR_GLIACK(x)                  (*(vuint8 *)(&__IPSBAR[0xFE4 + ((x-1)*0x4)]))


/* Bit definitions and macros for MCF_GIACR_GSWIACK */
#define MCF_GIACR_GSWIACK_VECTOR(x)          (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_GIACR_GLIACK */
#define MCF_GIACR_GLIACK_VECTOR(x)           (((x)&0xFF)<<0)


#endif /* __MCF52235_GIACR_H__ */
