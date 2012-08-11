/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.91
 */

#ifndef __MCF52235_EPORT_H__
#define __MCF52235_EPORT_H__


/*********************************************************************
*
* Edge Port Module (EPORT)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_EPORT0_EPPAR                     (*(vuint16*)(&__IPSBAR[0x130000]))
#define MCF_EPORT0_EPDDR                     (*(vuint8 *)(&__IPSBAR[0x130002]))
#define MCF_EPORT0_EPIER                     (*(vuint8 *)(&__IPSBAR[0x130003]))
#define MCF_EPORT0_EPDR                      (*(vuint8 *)(&__IPSBAR[0x130004]))
#define MCF_EPORT0_EPPDR                     (*(vuint8 *)(&__IPSBAR[0x130005]))
#define MCF_EPORT0_EPFR                      (*(vuint8 *)(&__IPSBAR[0x130006]))

#define MCF_EPORT1_EPPAR                     (*(vuint16*)(&__IPSBAR[0x140000]))
#define MCF_EPORT1_EPDDR                     (*(vuint8 *)(&__IPSBAR[0x140002]))
#define MCF_EPORT1_EPIER                     (*(vuint8 *)(&__IPSBAR[0x140003]))
#define MCF_EPORT1_EPDR                      (*(vuint8 *)(&__IPSBAR[0x140004]))
#define MCF_EPORT1_EPPDR                     (*(vuint8 *)(&__IPSBAR[0x140005]))
#define MCF_EPORT1_EPFR                      (*(vuint8 *)(&__IPSBAR[0x140006]))

#define MCF_EPORT_EPPAR(x)                   (*(vuint16*)(&__IPSBAR[0x130000 + ((x)*0x10000)]))
#define MCF_EPORT_EPDDR(x)                   (*(vuint8 *)(&__IPSBAR[0x130002 + ((x)*0x10000)]))
#define MCF_EPORT_EPIER(x)                   (*(vuint8 *)(&__IPSBAR[0x130003 + ((x)*0x10000)]))
#define MCF_EPORT_EPDR(x)                    (*(vuint8 *)(&__IPSBAR[0x130004 + ((x)*0x10000)]))
#define MCF_EPORT_EPPDR(x)                   (*(vuint8 *)(&__IPSBAR[0x130005 + ((x)*0x10000)]))
#define MCF_EPORT_EPFR(x)                    (*(vuint8 *)(&__IPSBAR[0x130006 + ((x)*0x10000)]))


/* Bit definitions and macros for MCF_EPORT_EPPAR */
#define MCF_EPORT_EPPAR_EPPA1(x)             (((x)&0x3)<<0x2)
#define MCF_EPORT_EPPAR_EPPA1_LEVEL          (0)
#define MCF_EPORT_EPPAR_EPPA1_RISING         (0x4)
#define MCF_EPORT_EPPAR_EPPA1_FALLING        (0x8)
#define MCF_EPORT_EPPAR_EPPA1_BOTH           (0xC)
#define MCF_EPORT_EPPAR_EPPA2(x)             (((x)&0x3)<<0x4)
#define MCF_EPORT_EPPAR_EPPA2_LEVEL          (0)
#define MCF_EPORT_EPPAR_EPPA2_RISING         (0x10)
#define MCF_EPORT_EPPAR_EPPA2_FALLING        (0x20)
#define MCF_EPORT_EPPAR_EPPA2_BOTH           (0x30)
#define MCF_EPORT_EPPAR_EPPA3(x)             (((x)&0x3)<<0x6)
#define MCF_EPORT_EPPAR_EPPA3_LEVEL          (0)
#define MCF_EPORT_EPPAR_EPPA3_RISING         (0x40)
#define MCF_EPORT_EPPAR_EPPA3_FALLING        (0x80)
#define MCF_EPORT_EPPAR_EPPA3_BOTH           (0xC0)
#define MCF_EPORT_EPPAR_EPPA4(x)             (((x)&0x3)<<0x8)
#define MCF_EPORT_EPPAR_EPPA4_LEVEL          (0)
#define MCF_EPORT_EPPAR_EPPA4_RISING         (0x100)
#define MCF_EPORT_EPPAR_EPPA4_FALLING        (0x200)
#define MCF_EPORT_EPPAR_EPPA4_BOTH           (0x300)
#define MCF_EPORT_EPPAR_EPPA5(x)             (((x)&0x3)<<0xA)
#define MCF_EPORT_EPPAR_EPPA5_LEVEL          (0)
#define MCF_EPORT_EPPAR_EPPA5_RISING         (0x400)
#define MCF_EPORT_EPPAR_EPPA5_FALLING        (0x800)
#define MCF_EPORT_EPPAR_EPPA5_BOTH           (0xC00)
#define MCF_EPORT_EPPAR_EPPA6(x)             (((x)&0x3)<<0xC)
#define MCF_EPORT_EPPAR_EPPA6_LEVEL          (0)
#define MCF_EPORT_EPPAR_EPPA6_RISING         (0x1000)
#define MCF_EPORT_EPPAR_EPPA6_FALLING        (0x2000)
#define MCF_EPORT_EPPAR_EPPA6_BOTH           (0x3000)
#define MCF_EPORT_EPPAR_EPPA7(x)             (((x)&0x3)<<0xE)
#define MCF_EPORT_EPPAR_EPPA7_LEVEL          (0)
#define MCF_EPORT_EPPAR_EPPA7_RISING         (0x4000)
#define MCF_EPORT_EPPAR_EPPA7_FALLING        (0x8000)
#define MCF_EPORT_EPPAR_EPPA7_BOTH           (0xC000)
#define MCF_EPORT_EPPAR_LEVEL                (0)
#define MCF_EPORT_EPPAR_RISING               (0x1)
#define MCF_EPORT_EPPAR_FALLING              (0x2)
#define MCF_EPORT_EPPAR_BOTH                 (0x3)

/* Bit definitions and macros for MCF_EPORT_EPDDR */
#define MCF_EPORT_EPDDR_EPDD1                (0x2)
#define MCF_EPORT_EPDDR_EPDD2                (0x4)
#define MCF_EPORT_EPDDR_EPDD3                (0x8)
#define MCF_EPORT_EPDDR_EPDD4                (0x10)
#define MCF_EPORT_EPDDR_EPDD5                (0x20)
#define MCF_EPORT_EPDDR_EPDD6                (0x40)
#define MCF_EPORT_EPDDR_EPDD7                (0x80)

/* Bit definitions and macros for MCF_EPORT_EPIER */
#define MCF_EPORT_EPIER_EPIE1                (0x2)
#define MCF_EPORT_EPIER_EPIE2                (0x4)
#define MCF_EPORT_EPIER_EPIE3                (0x8)
#define MCF_EPORT_EPIER_EPIE4                (0x10)
#define MCF_EPORT_EPIER_EPIE5                (0x20)
#define MCF_EPORT_EPIER_EPIE6                (0x40)
#define MCF_EPORT_EPIER_EPIE7                (0x80)

/* Bit definitions and macros for MCF_EPORT_EPDR */
#define MCF_EPORT_EPDR_EPD1                  (0x2)
#define MCF_EPORT_EPDR_EPD2                  (0x4)
#define MCF_EPORT_EPDR_EPD3                  (0x8)
#define MCF_EPORT_EPDR_EPD4                  (0x10)
#define MCF_EPORT_EPDR_EPD5                  (0x20)
#define MCF_EPORT_EPDR_EPD6                  (0x40)
#define MCF_EPORT_EPDR_EPD7                  (0x80)

/* Bit definitions and macros for MCF_EPORT_EPPDR */
#define MCF_EPORT_EPPDR_EPPD1                (0x2)
#define MCF_EPORT_EPPDR_EPPD2                (0x4)
#define MCF_EPORT_EPPDR_EPPD3                (0x8)
#define MCF_EPORT_EPPDR_EPPD4                (0x10)
#define MCF_EPORT_EPPDR_EPPD5                (0x20)
#define MCF_EPORT_EPPDR_EPPD6                (0x40)
#define MCF_EPORT_EPPDR_EPPD7                (0x80)

/* Bit definitions and macros for MCF_EPORT_EPFR */
#define MCF_EPORT_EPFR_EPF1                  (0x2)
#define MCF_EPORT_EPFR_EPF2                  (0x4)
#define MCF_EPORT_EPFR_EPF3                  (0x8)
#define MCF_EPORT_EPFR_EPF4                  (0x10)
#define MCF_EPORT_EPFR_EPF5                  (0x20)
#define MCF_EPORT_EPFR_EPF6                  (0x40)
#define MCF_EPORT_EPFR_EPF7                  (0x80)

/* Bit definitions and macros for MCF_EPORT_EPPAR */
#define MCF_EPORT_EPPAR_EPPA8(x)             (((x)&0x3)<<0)
#define MCF_EPORT_EPPAR_EPPA8_LEVEL          (0)
#define MCF_EPORT_EPPAR_EPPA8_RISING         (0x1)
#define MCF_EPORT_EPPAR_EPPA8_FALLING        (0x2)
#define MCF_EPORT_EPPAR_EPPA8_BOTH           (0x3)
#define MCF_EPORT_EPPAR_EPPA9(x)             (((x)&0x3)<<0x2)
#define MCF_EPORT_EPPAR_EPPA9_LEVEL          (0)
#define MCF_EPORT_EPPAR_EPPA9_RISING         (0x4)
#define MCF_EPORT_EPPAR_EPPA9_FALLING        (0x8)
#define MCF_EPORT_EPPAR_EPPA9_BOTH           (0xC)
#define MCF_EPORT_EPPAR_EPPA10(x)            (((x)&0x3)<<0x4)
#define MCF_EPORT_EPPAR_EPPA10_LEVEL         (0)
#define MCF_EPORT_EPPAR_EPPA10_RISING        (0x10)
#define MCF_EPORT_EPPAR_EPPA10_FALLING       (0x20)
#define MCF_EPORT_EPPAR_EPPA10_BOTH          (0x30)
#define MCF_EPORT_EPPAR_EPPA11(x)            (((x)&0x3)<<0x6)
#define MCF_EPORT_EPPAR_EPPA11_LEVEL         (0)
#define MCF_EPORT_EPPAR_EPPA11_RISING        (0x40)
#define MCF_EPORT_EPPAR_EPPA11_FALLING       (0x80)
#define MCF_EPORT_EPPAR_EPPA11_BOTH          (0xC0)
#define MCF_EPORT_EPPAR_EPPA12(x)            (((x)&0x3)<<0x8)
#define MCF_EPORT_EPPAR_EPPA12_LEVEL         (0)
#define MCF_EPORT_EPPAR_EPPA12_RISING        (0x100)
#define MCF_EPORT_EPPAR_EPPA12_FALLING       (0x200)
#define MCF_EPORT_EPPAR_EPPA12_BOTH          (0x300)
#define MCF_EPORT_EPPAR_EPPA13(x)            (((x)&0x3)<<0xA)
#define MCF_EPORT_EPPAR_EPPA13_LEVEL         (0)
#define MCF_EPORT_EPPAR_EPPA13_RISING        (0x400)
#define MCF_EPORT_EPPAR_EPPA13_FALLING       (0x800)
#define MCF_EPORT_EPPAR_EPPA13_BOTH          (0xC00)
#define MCF_EPORT_EPPAR_EPPA14(x)            (((x)&0x3)<<0xC)
#define MCF_EPORT_EPPAR_EPPA14_LEVEL         (0)
#define MCF_EPORT_EPPAR_EPPA14_RISING        (0x1000)
#define MCF_EPORT_EPPAR_EPPA14_FALLING       (0x2000)
#define MCF_EPORT_EPPAR_EPPA14_BOTH          (0x3000)
#define MCF_EPORT_EPPAR_EPPA15(x)            (((x)&0x3)<<0xE)
#define MCF_EPORT_EPPAR_EPPA15_LEVEL         (0)
#define MCF_EPORT_EPPAR_EPPA15_RISING        (0x4000)
#define MCF_EPORT_EPPAR_EPPA15_FALLING       (0x8000)
#define MCF_EPORT_EPPAR_EPPA15_BOTH          (0xC000)

/* Bit definitions and macros for MCF_EPORT_EPDDR */
#define MCF_EPORT_EPDDR_EPDD8                (0x1)
#define MCF_EPORT_EPDDR_EPDD9                (0x2)
#define MCF_EPORT_EPDDR_EPDD10               (0x4)
#define MCF_EPORT_EPDDR_EPDD11               (0x8)
#define MCF_EPORT_EPDDR_EPDD12               (0x10)
#define MCF_EPORT_EPDDR_EPDD13               (0x20)
#define MCF_EPORT_EPDDR_EPDD14               (0x40)
#define MCF_EPORT_EPDDR_EPDD15               (0x80)

/* Bit definitions and macros for MCF_EPORT_EPIER */
#define MCF_EPORT_EPIER_EPIE8                (0x1)
#define MCF_EPORT_EPIER_EPIE9                (0x2)
#define MCF_EPORT_EPIER_EPIE10               (0x4)
#define MCF_EPORT_EPIER_EPIE11               (0x8)
#define MCF_EPORT_EPIER_EPIE12               (0x10)
#define MCF_EPORT_EPIER_EPIE13               (0x20)
#define MCF_EPORT_EPIER_EPIE14               (0x40)
#define MCF_EPORT_EPIER_EPIE15               (0x80)

/* Bit definitions and macros for MCF_EPORT_EPDR */
#define MCF_EPORT_EPDR_EPD8                  (0x1)
#define MCF_EPORT_EPDR_EPD9                  (0x2)
#define MCF_EPORT_EPDR_EPD10                 (0x4)
#define MCF_EPORT_EPDR_EPD11                 (0x8)
#define MCF_EPORT_EPDR_EPD12                 (0x10)
#define MCF_EPORT_EPDR_EPD13                 (0x20)
#define MCF_EPORT_EPDR_EPD14                 (0x40)
#define MCF_EPORT_EPDR_EPD15                 (0x80)

/* Bit definitions and macros for MCF_EPORT_EPPDR */
#define MCF_EPORT_EPPDR_EPPD8                (0x1)
#define MCF_EPORT_EPPDR_EPPD9                (0x2)
#define MCF_EPORT_EPPDR_EPPD10               (0x4)
#define MCF_EPORT_EPPDR_EPPD11               (0x8)
#define MCF_EPORT_EPPDR_EPPD12               (0x10)
#define MCF_EPORT_EPPDR_EPPD13               (0x20)
#define MCF_EPORT_EPPDR_EPPD14               (0x40)
#define MCF_EPORT_EPPDR_EPPD15               (0x80)

/* Bit definitions and macros for MCF_EPORT_EPFR */
#define MCF_EPORT_EPFR_EPF8                  (0x1)
#define MCF_EPORT_EPFR_EPF9                  (0x2)
#define MCF_EPORT_EPFR_EPF10                 (0x4)
#define MCF_EPORT_EPFR_EPF11                 (0x8)
#define MCF_EPORT_EPFR_EPF12                 (0x10)
#define MCF_EPORT_EPFR_EPF13                 (0x20)
#define MCF_EPORT_EPFR_EPF14                 (0x40)
#define MCF_EPORT_EPFR_EPF15                 (0x80)


#endif /* __MCF52235_EPORT_H__ */
