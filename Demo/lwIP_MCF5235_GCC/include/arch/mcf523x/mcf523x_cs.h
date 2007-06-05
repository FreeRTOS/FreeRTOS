/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_cs.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_CS_H__
#define __MCF523X_CS_H__

/*********************************************************************
*
* Chip Selects (CS)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_CS_CSAR0      (*(vuint16*)(void*)(&__IPSBAR[0x000080]))
#define MCF_CS_CSMR0      (*(vuint32*)(void*)(&__IPSBAR[0x000084]))
#define MCF_CS_CSCR0      (*(vuint16*)(void*)(&__IPSBAR[0x00008A]))
#define MCF_CS_CSAR1      (*(vuint16*)(void*)(&__IPSBAR[0x00008C]))
#define MCF_CS_CSMR1      (*(vuint32*)(void*)(&__IPSBAR[0x000090]))
#define MCF_CS_CSCR1      (*(vuint16*)(void*)(&__IPSBAR[0x000096]))
#define MCF_CS_CSAR2      (*(vuint16*)(void*)(&__IPSBAR[0x000098]))
#define MCF_CS_CSMR2      (*(vuint32*)(void*)(&__IPSBAR[0x00009C]))
#define MCF_CS_CSCR2      (*(vuint16*)(void*)(&__IPSBAR[0x0000A2]))
#define MCF_CS_CSAR3      (*(vuint16*)(void*)(&__IPSBAR[0x0000A4]))
#define MCF_CS_CSMR3      (*(vuint32*)(void*)(&__IPSBAR[0x0000A8]))
#define MCF_CS_CSCR3      (*(vuint16*)(void*)(&__IPSBAR[0x0000AE]))
#define MCF_CS_CSAR4      (*(vuint16*)(void*)(&__IPSBAR[0x0000B0]))
#define MCF_CS_CSMR4      (*(vuint32*)(void*)(&__IPSBAR[0x0000B4]))
#define MCF_CS_CSCR4      (*(vuint16*)(void*)(&__IPSBAR[0x0000BA]))
#define MCF_CS_CSAR5      (*(vuint16*)(void*)(&__IPSBAR[0x0000BC]))
#define MCF_CS_CSMR5      (*(vuint32*)(void*)(&__IPSBAR[0x0000C0]))
#define MCF_CS_CSCR5      (*(vuint16*)(void*)(&__IPSBAR[0x0000C6]))
#define MCF_CS_CSAR6      (*(vuint16*)(void*)(&__IPSBAR[0x0000C8]))
#define MCF_CS_CSMR6      (*(vuint32*)(void*)(&__IPSBAR[0x0000CC]))
#define MCF_CS_CSCR6      (*(vuint16*)(void*)(&__IPSBAR[0x0000D2]))
#define MCF_CS_CSAR7      (*(vuint16*)(void*)(&__IPSBAR[0x0000D4]))
#define MCF_CS_CSMR7      (*(vuint32*)(void*)(&__IPSBAR[0x0000D8]))
#define MCF_CS_CSCR7      (*(vuint16*)(void*)(&__IPSBAR[0x0000DE]))
#define MCF_CS_CSAR(x)    (*(vuint16*)(void*)(&__IPSBAR[0x000080+((x)*0x00C)]))
#define MCF_CS_CSMR(x)    (*(vuint32*)(void*)(&__IPSBAR[0x000084+((x)*0x00C)]))
#define MCF_CS_CSCR(x)    (*(vuint16*)(void*)(&__IPSBAR[0x00008A+((x)*0x00C)]))

/* Bit definitions and macros for MCF_CS_CSAR */
#define MCF_CS_CSAR_BA(x)        ((uint16)(((x)&0xFFFF0000)>>16))

/* Bit definitions and macros for MCF_CS_CSMR */
#define MCF_CS_CSMR_V            (0x00000001)
#define MCF_CS_CSMR_UD           (0x00000002)
#define MCF_CS_CSMR_UC           (0x00000004)
#define MCF_CS_CSMR_SD           (0x00000008)
#define MCF_CS_CSMR_SC           (0x00000010)
#define MCF_CS_CSMR_CI           (0x00000020)
#define MCF_CS_CSMR_AM           (0x00000040)
#define MCF_CS_CSMR_WP           (0x00000100)
#define MCF_CS_CSMR_BAM(x)       (((x)&0x0000FFFF)<<16)
#define MCF_CS_CSMR_BAM_4G       (0xFFFF0000)
#define MCF_CS_CSMR_BAM_2G       (0x7FFF0000)
#define MCF_CS_CSMR_BAM_1G       (0x3FFF0000)
#define MCF_CS_CSMR_BAM_1024M    (0x3FFF0000)
#define MCF_CS_CSMR_BAM_512M     (0x1FFF0000)
#define MCF_CS_CSMR_BAM_256M     (0x0FFF0000)
#define MCF_CS_CSMR_BAM_128M     (0x07FF0000)
#define MCF_CS_CSMR_BAM_64M      (0x03FF0000)
#define MCF_CS_CSMR_BAM_32M      (0x01FF0000)
#define MCF_CS_CSMR_BAM_16M      (0x00FF0000)
#define MCF_CS_CSMR_BAM_8M       (0x007F0000)
#define MCF_CS_CSMR_BAM_4M       (0x003F0000)
#define MCF_CS_CSMR_BAM_2M       (0x001F0000)
#define MCF_CS_CSMR_BAM_1M       (0x000F0000)
#define MCF_CS_CSMR_BAM_1024K    (0x000F0000)
#define MCF_CS_CSMR_BAM_512K     (0x00070000)
#define MCF_CS_CSMR_BAM_256K     (0x00030000)
#define MCF_CS_CSMR_BAM_128K     (0x00010000)
#define MCF_CS_CSMR_BAM_64K      (0x00000000)

/* Bit definitions and macros for MCF_CS_CSCR */
#define MCF_CS_CSCR_SWWS(x)      (((x)&0x0007)<<0)
#define MCF_CS_CSCR_BSTW         (0x0008)
#define MCF_CS_CSCR_BSTR         (0x0010)
#define MCF_CS_CSCR_BEM          (0x0020)
#define MCF_CS_CSCR_PS(x)        (((x)&0x0003)<<6)
#define MCF_CS_CSCR_AA           (0x0100)
#define MCF_CS_CSCR_IWS(x)       (((x)&0x000F)<<10)
#define MCF_CS_CSCR_SRWS(x)      (((x)&0x0003)<<14)
#define MCF_CS_CSCR_PS_8         (0x0040)
#define MCF_CS_CSCR_PS_16        (0x0080)
#define MCF_CS_CSCR_PS_32        (0x0000)

/********************************************************************/

#endif /* __MCF523X_CS_H__ */
