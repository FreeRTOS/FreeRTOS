/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_sram.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_SRAM_H__
#define __MCF523X_SRAM_H__

/*********************************************************************
*
* 64KByte System SRAM (SRAM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_SRAM_RAMBAR    (*(vuint32*)(void*)(&__IPSBAR[0x20000000]))

/* Bit definitions and macros for MCF_SRAM_RAMBAR */
#define MCF_SRAM_RAMBAR_V        (0x00000001)
#define MCF_SRAM_RAMBAR_UD       (0x00000002)
#define MCF_SRAM_RAMBAR_UC       (0x00000004)
#define MCF_SRAM_RAMBAR_SD       (0x00000008)
#define MCF_SRAM_RAMBAR_SC       (0x00000010)
#define MCF_SRAM_RAMBAR_CI       (0x00000020)
#define MCF_SRAM_RAMBAR_WP       (0x00000100)
#define MCF_SRAM_RAMBAR_SPV      (0x00000200)
#define MCF_SRAM_RAMBAR_PRI2     (0x00000400)
#define MCF_SRAM_RAMBAR_PRI1     (0x00000800)
#define MCF_SRAM_RAMBAR_BA(x)    (((x)&0x0000FFFF)<<16)

/********************************************************************/

#endif /* __MCF523X_SRAM_H__ */
