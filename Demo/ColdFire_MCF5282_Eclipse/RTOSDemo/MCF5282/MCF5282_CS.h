/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_CS_H__
#define __MCF5282_CS_H__


/*********************************************************************
*
* Chip Select Module (CS)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_CS0_CSAR                         (*(vuint16*)(&__IPSBAR[0x80]))
#define MCF_CS0_CSMR                         (*(vuint32*)(&__IPSBAR[0x84]))
#define MCF_CS0_CSCR                         (*(vuint16*)(&__IPSBAR[0x8A]))

#define MCF_CS1_CSAR                         (*(vuint16*)(&__IPSBAR[0x8C]))
#define MCF_CS1_CSMR                         (*(vuint32*)(&__IPSBAR[0x90]))
#define MCF_CS1_CSCR                         (*(vuint16*)(&__IPSBAR[0x96]))

#define MCF_CS2_CSAR                         (*(vuint16*)(&__IPSBAR[0x98]))
#define MCF_CS2_CSMR                         (*(vuint32*)(&__IPSBAR[0x9C]))
#define MCF_CS2_CSCR                         (*(vuint16*)(&__IPSBAR[0xA2]))

#define MCF_CS3_CSAR                         (*(vuint16*)(&__IPSBAR[0xA4]))
#define MCF_CS3_CSMR                         (*(vuint32*)(&__IPSBAR[0xA8]))
#define MCF_CS3_CSCR                         (*(vuint16*)(&__IPSBAR[0xAE]))

#define MCF_CS4_CSAR                         (*(vuint16*)(&__IPSBAR[0xB0]))
#define MCF_CS4_CSMR                         (*(vuint32*)(&__IPSBAR[0xB4]))
#define MCF_CS4_CSCR                         (*(vuint16*)(&__IPSBAR[0xBA]))

#define MCF_CS5_CSAR                         (*(vuint16*)(&__IPSBAR[0xBC]))
#define MCF_CS5_CSMR                         (*(vuint32*)(&__IPSBAR[0xC0]))
#define MCF_CS5_CSCR                         (*(vuint16*)(&__IPSBAR[0xC6]))

#define MCF_CS6_CSAR                         (*(vuint16*)(&__IPSBAR[0xC8]))
#define MCF_CS6_CSMR                         (*(vuint32*)(&__IPSBAR[0xCC]))
#define MCF_CS6_CSCR                         (*(vuint16*)(&__IPSBAR[0xD2]))

#define MCF_CS_CSAR(x)                       (*(vuint16*)(&__IPSBAR[0x80 + ((x)*0xC)]))
#define MCF_CS_CSMR(x)                       (*(vuint32*)(&__IPSBAR[0x84 + ((x)*0xC)]))
#define MCF_CS_CSCR(x)                       (*(vuint16*)(&__IPSBAR[0x8A + ((x)*0xC)]))


/* Bit definitions and macros for MCF_CS_CSAR */
#define MCF_CS_CSAR_BA(x)                    (vuint16)(((x)&0xFFFF0000)>>0x10)

/* Bit definitions and macros for MCF_CS_CSMR */
#define MCF_CS_CSMR_V                        (0x1)
#define MCF_CS_CSMR_UD                       (0x2)
#define MCF_CS_CSMR_UC                       (0x4)
#define MCF_CS_CSMR_SD                       (0x8)
#define MCF_CS_CSMR_SC                       (0x10)
#define MCF_CS_CSMR_CI                       (0x20)
#define MCF_CS_CSMR_AM                       (0x40)
#define MCF_CS_CSMR_WP                       (0x100)
#define MCF_CS_CSMR_BAM(x)                   (((x)&0xFFFF)<<0x10)
#define MCF_CS_CSMR_BAM_4G                   (0xFFFF0000)
#define MCF_CS_CSMR_BAM_2G                   (0x7FFF0000)
#define MCF_CS_CSMR_BAM_1G                   (0x3FFF0000)
#define MCF_CS_CSMR_BAM_1024M                (0x3FFF0000)
#define MCF_CS_CSMR_BAM_512M                 (0x1FFF0000)
#define MCF_CS_CSMR_BAM_256M                 (0xFFF0000)
#define MCF_CS_CSMR_BAM_128M                 (0x7FF0000)
#define MCF_CS_CSMR_BAM_64M                  (0x3FF0000)
#define MCF_CS_CSMR_BAM_32M                  (0x1FF0000)
#define MCF_CS_CSMR_BAM_16M                  (0xFF0000)
#define MCF_CS_CSMR_BAM_8M                   (0x7F0000)
#define MCF_CS_CSMR_BAM_4M                   (0x3F0000)
#define MCF_CS_CSMR_BAM_2M                   (0x1F0000)
#define MCF_CS_CSMR_BAM_1M                   (0xF0000)
#define MCF_CS_CSMR_BAM_1024K                (0xF0000)
#define MCF_CS_CSMR_BAM_512K                 (0x70000)
#define MCF_CS_CSMR_BAM_256K                 (0x30000)
#define MCF_CS_CSMR_BAM_128K                 (0x10000)
#define MCF_CS_CSMR_BAM_64K                  (0)

/* Bit definitions and macros for MCF_CS_CSCR */
#define MCF_CS_CSCR_BSTW                     (0x8)
#define MCF_CS_CSCR_BSTR                     (0x10)
#define MCF_CS_CSCR_BEM                      (0x20)
#define MCF_CS_CSCR_PS(x)                    (((x)&0x3)<<0x6)
#define MCF_CS_CSCR_PS_32                    (0)
#define MCF_CS_CSCR_PS_8                     (0x40)
#define MCF_CS_CSCR_PS_16                    (0x80)
#define MCF_CS_CSCR_AA                       (0x100)
#define MCF_CS_CSCR_WS(x)                    (((x)&0xF)<<0xA)


#endif /* __MCF5282_CS_H__ */
