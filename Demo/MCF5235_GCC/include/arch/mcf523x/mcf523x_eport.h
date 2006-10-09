/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_eport.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_EPORT_H__
#define __MCF523X_EPORT_H__

/*********************************************************************
*
* Edge Port Module (EPORT)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_EPORT_EPPAR    (*(vuint16*)(void*)(&__IPSBAR[0x130000]))
#define MCF_EPORT_EPDDR    (*(vuint8 *)(void*)(&__IPSBAR[0x130002]))
#define MCF_EPORT_EPIER    (*(vuint8 *)(void*)(&__IPSBAR[0x130003]))
#define MCF_EPORT_EPDR     (*(vuint8 *)(void*)(&__IPSBAR[0x130004]))
#define MCF_EPORT_EPPDR    (*(vuint8 *)(void*)(&__IPSBAR[0x130005]))
#define MCF_EPORT_EPFR     (*(vuint8 *)(void*)(&__IPSBAR[0x130006]))

/* Bit definitions and macros for MCF_EPORT_EPPAR */
#define MCF_EPORT_EPPAR_EPPA1(x)         (((x)&0x0003)<<2)
#define MCF_EPORT_EPPAR_EPPA2(x)         (((x)&0x0003)<<4)
#define MCF_EPORT_EPPAR_EPPA3(x)         (((x)&0x0003)<<6)
#define MCF_EPORT_EPPAR_EPPA4(x)         (((x)&0x0003)<<8)
#define MCF_EPORT_EPPAR_EPPA5(x)         (((x)&0x0003)<<10)
#define MCF_EPORT_EPPAR_EPPA6(x)         (((x)&0x0003)<<12)
#define MCF_EPORT_EPPAR_EPPA7(x)         (((x)&0x0003)<<14)
#define MCF_EPORT_EPPAR_EPPAx_LEVEL      (0)
#define MCF_EPORT_EPPAR_EPPAx_RISING     (1)
#define MCF_EPORT_EPPAR_EPPAx_FALLING    (2)
#define MCF_EPORT_EPPAR_EPPAx_BOTH       (3)

/* Bit definitions and macros for MCF_EPORT_EPDDR */
#define MCF_EPORT_EPDDR_EPDD1            (0x02)
#define MCF_EPORT_EPDDR_EPDD2            (0x04)
#define MCF_EPORT_EPDDR_EPDD3            (0x08)
#define MCF_EPORT_EPDDR_EPDD4            (0x10)
#define MCF_EPORT_EPDDR_EPDD5            (0x20)
#define MCF_EPORT_EPDDR_EPDD6            (0x40)
#define MCF_EPORT_EPDDR_EPDD7            (0x80)

/* Bit definitions and macros for MCF_EPORT_EPIER */
#define MCF_EPORT_EPIER_EPIE1            (0x02)
#define MCF_EPORT_EPIER_EPIE2            (0x04)
#define MCF_EPORT_EPIER_EPIE3            (0x08)
#define MCF_EPORT_EPIER_EPIE4            (0x10)
#define MCF_EPORT_EPIER_EPIE5            (0x20)
#define MCF_EPORT_EPIER_EPIE6            (0x40)
#define MCF_EPORT_EPIER_EPIE7            (0x80)

/* Bit definitions and macros for MCF_EPORT_EPDR */
#define MCF_EPORT_EPDR_EPD1              (0x02)
#define MCF_EPORT_EPDR_EPD2              (0x04)
#define MCF_EPORT_EPDR_EPD3              (0x08)
#define MCF_EPORT_EPDR_EPD4              (0x10)
#define MCF_EPORT_EPDR_EPD5              (0x20)
#define MCF_EPORT_EPDR_EPD6              (0x40)
#define MCF_EPORT_EPDR_EPD7              (0x80)

/* Bit definitions and macros for MCF_EPORT_EPPDR */
#define MCF_EPORT_EPPDR_EPPD1            (0x02)
#define MCF_EPORT_EPPDR_EPPD2            (0x04)
#define MCF_EPORT_EPPDR_EPPD3            (0x08)
#define MCF_EPORT_EPPDR_EPPD4            (0x10)
#define MCF_EPORT_EPPDR_EPPD5            (0x20)
#define MCF_EPORT_EPPDR_EPPD6            (0x40)
#define MCF_EPORT_EPPDR_EPPD7            (0x80)

/* Bit definitions and macros for MCF_EPORT_EPFR */
#define MCF_EPORT_EPFR_EPF1              (0x02)
#define MCF_EPORT_EPFR_EPF2              (0x04)
#define MCF_EPORT_EPFR_EPF3              (0x08)
#define MCF_EPORT_EPFR_EPF4              (0x10)
#define MCF_EPORT_EPFR_EPF5              (0x20)
#define MCF_EPORT_EPFR_EPF6              (0x40)
#define MCF_EPORT_EPFR_EPF7              (0x80)

/********************************************************************/

#endif /* __MCF523X_EPORT_H__ */
