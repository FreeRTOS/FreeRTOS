/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_SCM_H__
#define __MCF5282_SCM_H__


/*********************************************************************
*
* System Control Module (SCM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_SCM_RAMBAR                       (*(vuint32*)(&__IPSBAR[0x8]))
#define MCF_SCM_CRSR                         (*(vuint8 *)(&__IPSBAR[0x10]))
#define MCF_SCM_CWCR                         (*(vuint8 *)(&__IPSBAR[0x11]))
#define MCF_SCM_CWSR                         (*(vuint8 *)(&__IPSBAR[0x13]))
#define MCF_SCM_DMAREQC                      (*(vuint32*)(&__IPSBAR[0x14]))
#define MCF_SCM_MPARK                        (*(vuint32*)(&__IPSBAR[0x1C]))
#define MCF_SCM_MPR                          (*(vuint8 *)(&__IPSBAR[0x20]))
#define MCF_SCM_PACR0                        (*(vuint8 *)(&__IPSBAR[0x24]))
#define MCF_SCM_PACR1                        (*(vuint8 *)(&__IPSBAR[0x25]))
#define MCF_SCM_PACR2                        (*(vuint8 *)(&__IPSBAR[0x26]))
#define MCF_SCM_PACR3                        (*(vuint8 *)(&__IPSBAR[0x27]))
#define MCF_SCM_PACR4                        (*(vuint8 *)(&__IPSBAR[0x28]))
#define MCF_SCM_PACR5                        (*(vuint8 *)(&__IPSBAR[0x2A]))
#define MCF_SCM_PACR6                        (*(vuint8 *)(&__IPSBAR[0x2B]))
#define MCF_SCM_PACR7                        (*(vuint8 *)(&__IPSBAR[0x2C]))
#define MCF_SCM_PACR8                        (*(vuint8 *)(&__IPSBAR[0x2E]))
#define MCF_SCM_GPACR0                       (*(vuint8 *)(&__IPSBAR[0x30]))
#define MCF_SCM_GPACR1                       (*(vuint8 *)(&__IPSBAR[0x31]))
#define MCF_SCM_GPACR(x)                     (*(vuint8 *)(&__IPSBAR[0x30 + ((x)*0x1)]))

/* Other macros */
#define MCF_SCM_IPSBAR                       (*(vuint32*)(&__IPSBAR[0x0]))
#define MCF_SCM_IPSBAR_V                     (0x1)
#define MCF_SCM_IPSBAR_BA(x)                 ((x)&0xC0000000)


/* Bit definitions and macros for MCF_SCM_RAMBAR */
#define MCF_SCM_RAMBAR_BDE                   (0x200)
#define MCF_SCM_RAMBAR_BA(x)                 ((x)&0xFFFF0000)

/* Bit definitions and macros for MCF_SCM_CRSR */
#define MCF_SCM_CRSR_CWDR                    (0x20)
#define MCF_SCM_CRSR_EXT                     (0x80)

/* Bit definitions and macros for MCF_SCM_CWCR */
#define MCF_SCM_CWCR_CWTIF                   (0x1)
#define MCF_SCM_CWCR_CWTAVAL                 (0x2)
#define MCF_SCM_CWCR_CWTA                    (0x4)
#define MCF_SCM_CWCR_CWT(x)                  (((x)&0x7)<<0x3)
#define MCF_SCM_CWCR_CWT_2_9                 (0)
#define MCF_SCM_CWCR_CWT_2_11                (0x8)
#define MCF_SCM_CWCR_CWT_2_13                (0x10)
#define MCF_SCM_CWCR_CWT_2_15                (0x18)
#define MCF_SCM_CWCR_CWT_2_19                (0x20)
#define MCF_SCM_CWCR_CWT_2_23                (0x28)
#define MCF_SCM_CWCR_CWT_2_27                (0x30)
#define MCF_SCM_CWCR_CWT_2_31                (0x38)
#define MCF_SCM_CWCR_CWRI                    (0x40)
#define MCF_SCM_CWCR_CWE                     (0x80)

/* Bit definitions and macros for MCF_SCM_CWSR */
#define MCF_SCM_CWSR_CWSR(x)                 (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_SCM_DMAREQC */
#define MCF_SCM_DMAREQC_DMAC0(x)             (((x)&0xF)<<0)
#define MCF_SCM_DMAREQC_DMAC1(x)             (((x)&0xF)<<0x4)
#define MCF_SCM_DMAREQC_DMAC2(x)             (((x)&0xF)<<0x8)
#define MCF_SCM_DMAREQC_DMAC3(x)             (((x)&0xF)<<0xC)

/* Bit definitions and macros for MCF_SCM_MPARK */
#define MCF_SCM_MPARK_LCKOUT_TIME(x)         (((x)&0xF)<<0x8)
#define MCF_SCM_MPARK_PRKLAST                (0x1000)
#define MCF_SCM_MPARK_TIMEOUT                (0x2000)
#define MCF_SCM_MPARK_FIXED                  (0x4000)
#define MCF_SCM_MPARK_M1_PRTY(x)             (((x)&0x3)<<0x10)
#define MCF_SCM_MPARK_M0_PRTY(x)             (((x)&0x3)<<0x12)
#define MCF_SCM_MPARK_M2_PRTY(x)             (((x)&0x3)<<0x14)
#define MCF_SCM_MPARK_M3_PRTY(x)             (((x)&0x3)<<0x16)
#define MCF_SCM_MPARK_BCR24BIT               (0x1000000)
#define MCF_SCM_MPARK_M2_P_EN                (0x2000000)

/* Bit definitions and macros for MCF_SCM_MPR */
#define MCF_SCM_MPR_MPR(x)                   (((x)&0xF)<<0)

/* Bit definitions and macros for MCF_SCM_PACR0 */
#define MCF_SCM_PACR0_ACCESS_CTRL0(x)        (((x)&0x7)<<0)
#define MCF_SCM_PACR0_LOCK0                  (0x8)
#define MCF_SCM_PACR0_ACCESS_CTRL1(x)        (((x)&0x7)<<0x4)
#define MCF_SCM_PACR0_LOCK1                  (0x80)

/* Bit definitions and macros for MCF_SCM_PACR1 */
#define MCF_SCM_PACR1_ACCESS_CTRL0(x)        (((x)&0x7)<<0)
#define MCF_SCM_PACR1_LOCK0                  (0x8)
#define MCF_SCM_PACR1_ACCESS_CTRL1(x)        (((x)&0x7)<<0x4)
#define MCF_SCM_PACR1_LOCK1                  (0x80)

/* Bit definitions and macros for MCF_SCM_PACR2 */
#define MCF_SCM_PACR2_ACCESS_CTRL0(x)        (((x)&0x7)<<0)
#define MCF_SCM_PACR2_LOCK0                  (0x8)
#define MCF_SCM_PACR2_ACCESS_CTRL1(x)        (((x)&0x7)<<0x4)
#define MCF_SCM_PACR2_LOCK1                  (0x80)

/* Bit definitions and macros for MCF_SCM_PACR3 */
#define MCF_SCM_PACR3_ACCESS_CTRL0(x)        (((x)&0x7)<<0)
#define MCF_SCM_PACR3_LOCK0                  (0x8)
#define MCF_SCM_PACR3_ACCESS_CTRL1(x)        (((x)&0x7)<<0x4)
#define MCF_SCM_PACR3_LOCK1                  (0x80)

/* Bit definitions and macros for MCF_SCM_PACR4 */
#define MCF_SCM_PACR4_ACCESS_CTRL0(x)        (((x)&0x7)<<0)
#define MCF_SCM_PACR4_LOCK0                  (0x8)
#define MCF_SCM_PACR4_ACCESS_CTRL1(x)        (((x)&0x7)<<0x4)
#define MCF_SCM_PACR4_LOCK1                  (0x80)

/* Bit definitions and macros for MCF_SCM_PACR5 */
#define MCF_SCM_PACR5_ACCESS_CTRL0(x)        (((x)&0x7)<<0)
#define MCF_SCM_PACR5_LOCK0                  (0x8)
#define MCF_SCM_PACR5_ACCESS_CTRL1(x)        (((x)&0x7)<<0x4)
#define MCF_SCM_PACR5_LOCK1                  (0x80)

/* Bit definitions and macros for MCF_SCM_PACR6 */
#define MCF_SCM_PACR6_ACCESS_CTRL0(x)        (((x)&0x7)<<0)
#define MCF_SCM_PACR6_LOCK0                  (0x8)
#define MCF_SCM_PACR6_ACCESS_CTRL1(x)        (((x)&0x7)<<0x4)
#define MCF_SCM_PACR6_LOCK1                  (0x80)

/* Bit definitions and macros for MCF_SCM_PACR7 */
#define MCF_SCM_PACR7_ACCESS_CTRL0(x)        (((x)&0x7)<<0)
#define MCF_SCM_PACR7_LOCK0                  (0x8)
#define MCF_SCM_PACR7_ACCESS_CTRL1(x)        (((x)&0x7)<<0x4)
#define MCF_SCM_PACR7_LOCK1                  (0x80)

/* Bit definitions and macros for MCF_SCM_PACR8 */
#define MCF_SCM_PACR8_ACCESS_CTRL0(x)        (((x)&0x7)<<0)
#define MCF_SCM_PACR8_LOCK0                  (0x8)
#define MCF_SCM_PACR8_ACCESS_CTRL1(x)        (((x)&0x7)<<0x4)
#define MCF_SCM_PACR8_LOCK1                  (0x80)

/* Bit definitions and macros for MCF_SCM_GPACR */
#define MCF_SCM_GPACR_ACCESS_CTRL(x)         (((x)&0xF)<<0)
#define MCF_SCM_GPACR_LOCK                   (0x80)


#endif /* __MCF5282_SCM_H__ */
