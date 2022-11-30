/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2008/05/23 Revision: 0.95
 *
 * (c) Copyright UNIS, a.s. 1997-2008
 * UNIS, a.s.
 * Jundrovska 33
 * 624 00 Brno
 * Czech Republic
 * http      : www.processorexpert.com
 * mail      : info@processorexpert.com
 */

#ifndef __MCF52221_QSPI_H__
#define __MCF52221_QSPI_H__


/*********************************************************************
*
* Queued Serial Peripheral Interface (QSPI)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_QSPI_QMR                         (*(vuint16*)(0x40000340))
#define MCF_QSPI_QDLYR                       (*(vuint16*)(0x40000344))
#define MCF_QSPI_QWR                         (*(vuint16*)(0x40000348))
#define MCF_QSPI_QIR                         (*(vuint16*)(0x4000034C))
#define MCF_QSPI_QAR                         (*(vuint16*)(0x40000350))
#define MCF_QSPI_QDR                         (*(vuint16*)(0x40000354))


/* Bit definitions and macros for MCF_QSPI_QMR */
#define MCF_QSPI_QMR_BAUD(x)                 (((x)&0xFF)<<0)
#define MCF_QSPI_QMR_CPHA                    (0x100)
#define MCF_QSPI_QMR_CPOL                    (0x200)
#define MCF_QSPI_QMR_BITS(x)                 (((x)&0xF)<<0xA)
#define MCF_QSPI_QMR_DOHIE                   (0x4000)
#define MCF_QSPI_QMR_MSTR                    (0x8000)

/* Bit definitions and macros for MCF_QSPI_QDLYR */
#define MCF_QSPI_QDLYR_DTL(x)                (((x)&0xFF)<<0)
#define MCF_QSPI_QDLYR_QCD(x)                (((x)&0x7F)<<0x8)
#define MCF_QSPI_QDLYR_SPE                   (0x8000)

/* Bit definitions and macros for MCF_QSPI_QWR */
#define MCF_QSPI_QWR_NEWQP(x)                (((x)&0xF)<<0)
#define MCF_QSPI_QWR_CPTQP(x)                (((x)&0xF)<<0x4)
#define MCF_QSPI_QWR_ENDQP(x)                (((x)&0xF)<<0x8)
#define MCF_QSPI_QWR_CSIV                    (0x1000)
#define MCF_QSPI_QWR_WRTO                    (0x2000)
#define MCF_QSPI_QWR_WREN                    (0x4000)
#define MCF_QSPI_QWR_HALT                    (0x8000)

/* Bit definitions and macros for MCF_QSPI_QIR */
#define MCF_QSPI_QIR_SPIF                    (0x1)
#define MCF_QSPI_QIR_ABRT                    (0x4)
#define MCF_QSPI_QIR_WCEF                    (0x8)
#define MCF_QSPI_QIR_SPIFE                   (0x100)
#define MCF_QSPI_QIR_ABRTE                   (0x400)
#define MCF_QSPI_QIR_WCEFE                   (0x800)
#define MCF_QSPI_QIR_ABRTL                   (0x1000)
#define MCF_QSPI_QIR_ABRTB                   (0x4000)
#define MCF_QSPI_QIR_WCEFB                   (0x8000)

/* Bit definitions and macros for MCF_QSPI_QAR */
#define MCF_QSPI_QAR_ADDR(x)                 (((x)&0x3F)<<0)
#define MCF_QSPI_QAR_TRANS                   (0)
#define MCF_QSPI_QAR_RECV                    (0x10)
#define MCF_QSPI_QAR_CMD                     (0x20)

/* Bit definitions and macros for MCF_QSPI_QDR */
#define MCF_QSPI_QDR_DATA(x)                 (((x)&0xFFFF)<<0)
#define MCF_QSPI_QDR_CONT                    (0x8000)
#define MCF_QSPI_QDR_BITSE                   (0x4000)
#define MCF_QSPI_QDR_DT                      (0x2000)
#define MCF_QSPI_QDR_DSCK                    (0x1000)
#define MCF_QSPI_QDR_QSPI_CS3                (0x800)
#define MCF_QSPI_QDR_QSPI_CS2                (0x400)
#define MCF_QSPI_QDR_QSPI_CS1                (0x200)
#define MCF_QSPI_QDR_QSPI_CS0                (0x100)


#endif /* __MCF52221_QSPI_H__ */
