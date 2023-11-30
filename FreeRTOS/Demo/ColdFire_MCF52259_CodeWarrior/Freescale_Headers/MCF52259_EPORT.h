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

#ifndef __MCF52259_EPORT_H__
#define __MCF52259_EPORT_H__


/*********************************************************************
*
* Edge Port Module (EPORT)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_EPORT_EPPAR                      (*(vuint16*)(0x40130000))
#define MCF_EPORT_EPDDR                      (*(vuint8 *)(0x40130002))
#define MCF_EPORT_EPIER                      (*(vuint8 *)(0x40130003))
#define MCF_EPORT_EPDR                       (*(vuint8 *)(0x40130004))
#define MCF_EPORT_EPPDR                      (*(vuint8 *)(0x40130005))
#define MCF_EPORT_EPFR                       (*(vuint8 *)(0x40130006))



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


#endif /* __MCF52259_EPORT_H__ */
