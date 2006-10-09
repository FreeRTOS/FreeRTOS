/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_scm.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_SCM_H__
#define __MCF523X_SCM_H__

/*********************************************************************
*
* System Control Module (SCM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_SCM_IPSBAR     (*(vuint32*)(void*)(&__IPSBAR[0x000000]))
#define MCF_SCM_RAMBAR     (*(vuint32*)(void*)(&__IPSBAR[0x000008]))
#define MCF_SCM_CRSR       (*(vuint8 *)(void*)(&__IPSBAR[0x000010]))
#define MCF_SCM_CWCR       (*(vuint8 *)(void*)(&__IPSBAR[0x000011]))
#define MCF_SCM_LPICR      (*(vuint8 *)(void*)(&__IPSBAR[0x000012]))
#define MCF_SCM_CWSR       (*(vuint8 *)(void*)(&__IPSBAR[0x000013]))
#define MCF_SCM_DMAREQC    (*(vuint32*)(void*)(&__IPSBAR[0x000014]))
#define MCF_SCM_MPARK      (*(vuint32*)(void*)(&__IPSBAR[0x00001C]))
#define MCF_SCM_MPR        (*(vuint8 *)(void*)(&__IPSBAR[0x000020]))
#define MCF_SCM_PACR0      (*(vuint8 *)(void*)(&__IPSBAR[0x000024]))
#define MCF_SCM_PACR1      (*(vuint8 *)(void*)(&__IPSBAR[0x000025]))
#define MCF_SCM_PACR2      (*(vuint8 *)(void*)(&__IPSBAR[0x000026]))
#define MCF_SCM_PACR3      (*(vuint8 *)(void*)(&__IPSBAR[0x000027]))
#define MCF_SCM_PACR4      (*(vuint8 *)(void*)(&__IPSBAR[0x000028]))
#define MCF_SCM_PACR5      (*(vuint8 *)(void*)(&__IPSBAR[0x00002A]))
#define MCF_SCM_PACR6      (*(vuint8 *)(void*)(&__IPSBAR[0x00002B]))
#define MCF_SCM_PACR7      (*(vuint8 *)(void*)(&__IPSBAR[0x00002C]))
#define MCF_SCM_PACR8      (*(vuint8 *)(void*)(&__IPSBAR[0x00002E]))
#define MCF_SCM_GPACR0     (*(vuint8 *)(void*)(&__IPSBAR[0x000030]))

/* Bit definitions and macros for MCF_SCM_IPSBAR */
#define MCF_SCM_IPSBAR_V                 (0x00000001)
#define MCF_SCM_IPSBAR_BA(x)             (((x)&0x00000003)<<30)

/* Bit definitions and macros for MCF_SCM_RAMBAR */
#define MCF_SCM_RAMBAR_BDE               (0x00000200)
#define MCF_SCM_RAMBAR_BA(x)             (((x)&0x0000FFFF)<<16)

/* Bit definitions and macros for MCF_SCM_CRSR */
#define MCF_SCM_CRSR_CWDR                (0x20)
#define MCF_SCM_CRSR_EXT                 (0x80)

/* Bit definitions and macros for MCF_SCM_CWCR */
#define MCF_SCM_CWCR_CWTIC               (0x01)
#define MCF_SCM_CWCR_CWTAVAL             (0x02)
#define MCF_SCM_CWCR_CWTA                (0x04)
#define MCF_SCM_CWCR_CWT(x)              (((x)&0x07)<<3)
#define MCF_SCM_CWCR_CWRI                (0x40)
#define MCF_SCM_CWCR_CWE                 (0x80)

/* Bit definitions and macros for MCF_SCM_LPICR */
#define MCF_SCM_LPICR_XLPM_IPL(x)        (((x)&0x07)<<4)
#define MCF_SCM_LPICR_ENBSTOP            (0x80)

/* Bit definitions and macros for MCF_SCM_DMAREQC */
#define MCF_SCM_DMAREQC_DMAC0(x)         (((x)&0x0000000F)<<0)
#define MCF_SCM_DMAREQC_DMAC1(x)         (((x)&0x0000000F)<<4)
#define MCF_SCM_DMAREQC_DMAC2(x)         (((x)&0x0000000F)<<8)
#define MCF_SCM_DMAREQC_DMAC3(x)         (((x)&0x0000000F)<<12)

/* Bit definitions and macros for MCF_SCM_MPARK */
#define MCF_SCM_MPARK_LCKOUT_TIME(x)     (((x)&0x0000000F)<<8)
#define MCF_SCM_MPARK_PRKLAST            (0x00001000)
#define MCF_SCM_MPARK_TIMEOUT            (0x00002000)
#define MCF_SCM_MPARK_FIXED              (0x00004000)
#define MCF_SCM_MPARK_M1_PRTY(x)         (((x)&0x00000003)<<16)
#define MCF_SCM_MPARK_M0_PRTY(x)         (((x)&0x00000003)<<18)
#define MCF_SCM_MPARK_M2_PRTY(x)         (((x)&0x00000003)<<20)
#define MCF_SCM_MPARK_M3_PRTY(x)         (((x)&0x00000003)<<22)
#define MCF_SCM_MPARK_BCR24BIT           (0x01000000)
#define MCF_SCM_MPARK_M2_P_EN            (0x02000000)

/* Bit definitions and macros for MCF_SCM_MPR */
#define MCF_SCM_MPR_MPR(x)               (((x)&0x0F)<<0)

/* Bit definitions and macros for MCF_SCM_PACR0 */
#define MCF_SCM_PACR0_ACCESS_CTRL0(x)    (((x)&0x07)<<0)
#define MCF_SCM_PACR0_LOCK0              (0x08)
#define MCF_SCM_PACR0_ACCESS_CTRL1(x)    (((x)&0x07)<<4)
#define MCF_SCM_PACR0_LOCK1              (0x80)

/* Bit definitions and macros for MCF_SCM_PACR1 */
#define MCF_SCM_PACR1_ACCESS_CTRL0(x)    (((x)&0x07)<<0)
#define MCF_SCM_PACR1_LOCK0              (0x08)
#define MCF_SCM_PACR1_ACCESS_CTRL1(x)    (((x)&0x07)<<4)
#define MCF_SCM_PACR1_LOCK1              (0x80)

/* Bit definitions and macros for MCF_SCM_PACR2 */
#define MCF_SCM_PACR2_ACCESS_CTRL0(x)    (((x)&0x07)<<0)
#define MCF_SCM_PACR2_LOCK0              (0x08)
#define MCF_SCM_PACR2_ACCESS_CTRL1(x)    (((x)&0x07)<<4)
#define MCF_SCM_PACR2_LOCK1              (0x80)

/* Bit definitions and macros for MCF_SCM_PACR3 */
#define MCF_SCM_PACR3_ACCESS_CTRL0(x)    (((x)&0x07)<<0)
#define MCF_SCM_PACR3_LOCK0              (0x08)
#define MCF_SCM_PACR3_ACCESS_CTRL1(x)    (((x)&0x07)<<4)
#define MCF_SCM_PACR3_LOCK1              (0x80)

/* Bit definitions and macros for MCF_SCM_PACR4 */
#define MCF_SCM_PACR4_ACCESS_CTRL0(x)    (((x)&0x07)<<0)
#define MCF_SCM_PACR4_LOCK0              (0x08)
#define MCF_SCM_PACR4_ACCESS_CTRL1(x)    (((x)&0x07)<<4)
#define MCF_SCM_PACR4_LOCK1              (0x80)

/* Bit definitions and macros for MCF_SCM_PACR5 */
#define MCF_SCM_PACR5_ACCESS_CTRL0(x)    (((x)&0x07)<<0)
#define MCF_SCM_PACR5_LOCK0              (0x08)
#define MCF_SCM_PACR5_ACCESS_CTRL1(x)    (((x)&0x07)<<4)
#define MCF_SCM_PACR5_LOCK1              (0x80)

/* Bit definitions and macros for MCF_SCM_PACR6 */
#define MCF_SCM_PACR6_ACCESS_CTRL0(x)    (((x)&0x07)<<0)
#define MCF_SCM_PACR6_LOCK0              (0x08)
#define MCF_SCM_PACR6_ACCESS_CTRL1(x)    (((x)&0x07)<<4)
#define MCF_SCM_PACR6_LOCK1              (0x80)

/* Bit definitions and macros for MCF_SCM_PACR7 */
#define MCF_SCM_PACR7_ACCESS_CTRL0(x)    (((x)&0x07)<<0)
#define MCF_SCM_PACR7_LOCK0              (0x08)
#define MCF_SCM_PACR7_ACCESS_CTRL1(x)    (((x)&0x07)<<4)
#define MCF_SCM_PACR7_LOCK1              (0x80)

/* Bit definitions and macros for MCF_SCM_PACR8 */
#define MCF_SCM_PACR8_ACCESS_CTRL0(x)    (((x)&0x07)<<0)
#define MCF_SCM_PACR8_LOCK0              (0x08)
#define MCF_SCM_PACR8_ACCESS_CTRL1(x)    (((x)&0x07)<<4)
#define MCF_SCM_PACR8_LOCK1              (0x80)

/* Bit definitions and macros for MCF_SCM_GPACR0 */
#define MCF_SCM_GPACR0_ACCESS_CTRL(x)    (((x)&0x0F)<<0)
#define MCF_SCM_GPACR0_LOCK              (0x80)

/********************************************************************/

#endif /* __MCF523X_SCM_H__ */
