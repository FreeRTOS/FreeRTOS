/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_ccm.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_CCM_H__
#define __MCF523X_CCM_H__

/*********************************************************************
*
* Chip Configuration Module (CCM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_CCM_CCR     (*(vuint16*)(void*)(&__IPSBAR[0x110004]))
#define MCF_CCM_LPCR    (*(vuint8 *)(void*)(&__IPSBAR[0x110007]))
#define MCF_CCM_CIR     (*(vuint16*)(void*)(&__IPSBAR[0x11000A]))
#define MCF_CCM_RCON    (*(vuint16*)(void*)(&__IPSBAR[0x110008]))

/* Bit definitions and macros for MCF_CCM_CCR */
#define MCF_CCM_CCR_BMT(x)        (((x)&0x0007)<<0)
#define MCF_CCM_CCR_BME           (0x0008)
#define MCF_CCM_CCR_SZEN          (0x0040)
#define MCF_CCM_CCR_MODE(x)       (((x)&0x0007)<<8)

/* Bit definitions and macros for MCF_CCM_LPCR */
#define MCF_CCM_LPCR_STPMD(x)     (((x)&0x03)<<3)
#define MCF_CCM_LPCR_LPMD(x)      (((x)&0x03)<<6)
#define MCF_CCM_LPCR_LPMD_STOP    (0xC0)
#define MCF_CCM_LPCR_LPMD_WAIT    (0x80)
#define MCF_CCM_LPCR_LPMD_DOZE    (0x40)
#define MCF_CCM_LPCR_LPMD_RUN     (0x00)

/* Bit definitions and macros for MCF_CCM_CIR */
#define MCF_CCM_CIR_PRN(x)        (((x)&0x003F)<<0)
#define MCF_CCM_CIR_PIN(x)        (((x)&0x03FF)<<6)

/* Bit definitions and macros for MCF_CCM_RCON */
#define MCF_CCM_RCON_MODE         (0x0001)
#define MCF_CCM_RCON_BOOTPS(x)    (((x)&0x0003)<<3)
#define MCF_CCM_RCON_RLOAD        (0x0020)
#define MCF_CCM_RCON_RCSC(x)      (((x)&0x0003)<<8)

/********************************************************************/

#endif /* __MCF523X_CCM_H__ */
