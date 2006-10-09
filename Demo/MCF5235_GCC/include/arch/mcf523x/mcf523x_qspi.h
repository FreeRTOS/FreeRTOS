/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_qspi.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_QSPI_H__
#define __MCF523X_QSPI_H__

/*********************************************************************
*
* Queued Serial Peripheral Interface (QSPI)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_QSPI_QMR      (*(vuint16*)(void*)(&__IPSBAR[0x000340]))
#define MCF_QSPI_QDLYR    (*(vuint16*)(void*)(&__IPSBAR[0x000344]))
#define MCF_QSPI_QWR      (*(vuint16*)(void*)(&__IPSBAR[0x000348]))
#define MCF_QSPI_QIR      (*(vuint16*)(void*)(&__IPSBAR[0x00034C]))
#define MCF_QSPI_QAR      (*(vuint16*)(void*)(&__IPSBAR[0x000350]))
#define MCF_QSPI_QDR      (*(vuint16*)(void*)(&__IPSBAR[0x000354]))

/* Bit definitions and macros for MCF_QSPI_QMR */
#define MCF_QSPI_QMR_BAUD(x)     (((x)&0x00FF)<<0)
#define MCF_QSPI_QMR_CPHA        (0x0100)
#define MCF_QSPI_QMR_CPOL        (0x0200)
#define MCF_QSPI_QMR_BITS(x)     (((x)&0x000F)<<10)
#define MCF_QSPI_QMR_DOHIE       (0x4000)
#define MCF_QSPI_QMR_MSTR        (0x8000)

/* Bit definitions and macros for MCF_QSPI_QDLYR */
#define MCF_QSPI_QDLYR_DTL(x)    (((x)&0x00FF)<<0)
#define MCF_QSPI_QDLYR_QCD(x)    (((x)&0x007F)<<8)
#define MCF_QSPI_QDLYR_SPE       (0x8000)

/* Bit definitions and macros for MCF_QSPI_QWR */
#define MCF_QSPI_QWR_NEWQP(x)    (((x)&0x000F)<<0)
#define MCF_QSPI_QWR_ENDQP(x)    (((x)&0x000F)<<8)
#define MCF_QSPI_QWR_CSIV        (0x1000)
#define MCF_QSPI_QWR_WRTO        (0x2000)
#define MCF_QSPI_QWR_WREN        (0x4000)
#define MCF_QSPI_QWR_HALT        (0x8000)

/* Bit definitions and macros for MCF_QSPI_QIR */
#define MCF_QSPI_QIR_SPIF        (0x0001)
#define MCF_QSPI_QIR_ABRT        (0x0004)
#define MCF_QSPI_QIR_WCEF        (0x0008)
#define MCF_QSPI_QIR_SPIFE       (0x0100)
#define MCF_QSPI_QIR_ABRTE       (0x0400)
#define MCF_QSPI_QIR_WCEFE       (0x0800)
#define MCF_QSPI_QIR_ABRTL       (0x1000)
#define MCF_QSPI_QIR_ABRTB       (0x4000)
#define MCF_QSPI_QIR_WCEFB       (0x8000)

/* Bit definitions and macros for MCF_QSPI_QAR */
#define MCF_QSPI_QAR_ADDR(x)     (((x)&0x003F)<<0)

/********************************************************************/

#endif /* __MCF523X_QSPI_H__ */
