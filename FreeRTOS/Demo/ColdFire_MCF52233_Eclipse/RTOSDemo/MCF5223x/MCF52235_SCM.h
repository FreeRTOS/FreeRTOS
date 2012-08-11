/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.91
 */

#ifndef __MCF52235_SCM_H__
#define __MCF52235_SCM_H__


/*********************************************************************
*
* System Control Module (SCM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_SCM_RAMBAR                       (*(vuint32*)(&__IPSBAR[0x8]))
#define MCF_SCM_PPMRH                        (*(vuint32*)(&__IPSBAR[0xC]))
#define MCF_SCM_CRSR                         (*(vuint8 *)(&__IPSBAR[0x10]))
#define MCF_SCM_CWCR                         (*(vuint8 *)(&__IPSBAR[0x11]))
#define MCF_SCM_CWSR                         (*(vuint8 *)(&__IPSBAR[0x13]))
#define MCF_SCM_DMAREQC                      (*(vuint32*)(&__IPSBAR[0x14]))
#define MCF_SCM_PPMRL                        (*(vuint32*)(&__IPSBAR[0x18]))
#define MCF_SCM_MPARK                        (*(vuint32*)(&__IPSBAR[0x1C]))
#define MCF_SCM_MPR                          (*(vuint8 *)(&__IPSBAR[0x20]))
#define MCF_SCM_PPMRS                        (*(vuint8 *)(&__IPSBAR[0x21]))
#define MCF_SCM_PPMRC                        (*(vuint8 *)(&__IPSBAR[0x22]))
#define MCF_SCM_IPSBMT                       (*(vuint8 *)(&__IPSBAR[0x23]))
#define MCF_SCM_PACR0                        (*(vuint8 *)(&__IPSBAR[0x24]))
#define MCF_SCM_PACR1                        (*(vuint8 *)(&__IPSBAR[0x25]))
#define MCF_SCM_PACR2                        (*(vuint8 *)(&__IPSBAR[0x26]))
#define MCF_SCM_PACR3                        (*(vuint8 *)(&__IPSBAR[0x27]))
#define MCF_SCM_PACR4                        (*(vuint8 *)(&__IPSBAR[0x28]))
#define MCF_SCM_PACR5                        (*(vuint8 *)(&__IPSBAR[0x29]))
#define MCF_SCM_PACR6                        (*(vuint8 *)(&__IPSBAR[0x2A]))
#define MCF_SCM_PACR7                        (*(vuint8 *)(&__IPSBAR[0x2B]))
#define MCF_SCM_PACR8                        (*(vuint8 *)(&__IPSBAR[0x2C]))
#define MCF_SCM_GPACR0                       (*(vuint8 *)(&__IPSBAR[0x30]))
#define MCF_SCM_GPACR1                       (*(vuint8 *)(&__IPSBAR[0x31]))
#define MCF_SCM_PACR(x)                      (*(vuint8 *)(&__IPSBAR[0x24 + ((x)*0x1)]))
#define MCF_SCM_GPACR(x)                     (*(vuint8 *)(&__IPSBAR[0x30 + ((x)*0x1)]))

/* Other macros */
#define MCF_SCM_IPSBAR                       (*(vuint32*)(&__IPSBAR[0x0]))
#define MCF_SCM_IPSBAR_V                     (0x1)
#define MCF_SCM_IPSBAR_BA(x)                 ((x)&0xC0000000)


/* Bit definitions and macros for MCF_SCM_RAMBAR */
#define MCF_SCM_RAMBAR_BDE                   (0x200)
#define MCF_SCM_RAMBAR_BA(x)                 ((x)&0xFFFF0000)

/* Bit definitions and macros for MCF_SCM_PPMRH */
#define MCF_SCM_PPMRH_CDPORTS                (0x1)
#define MCF_SCM_PPMRH_CDEPORT                (0x2)
#define MCF_SCM_PPMRH_CDPIT0                 (0x8)
#define MCF_SCM_PPMRH_CDPIT1                 (0x10)
#define MCF_SCM_PPMRH_CDADC                  (0x80)
#define MCF_SCM_PPMRH_CDGPT                  (0x100)
#define MCF_SCM_PPMRH_CDPWM                  (0x200)
#define MCF_SCM_PPMRH_CDFCAN                 (0x400)
#define MCF_SCM_PPMRH_CDCFM                  (0x800)
#define MCF_SCM_PPMRH_CDEPHY                 (0x1000)
#define MCF_SCM_PPMRH_CDRNGA                 (0x2000)

/* Bit definitions and macros for MCF_SCM_CRSR */
#define MCF_SCM_CRSR_CWDR  		     (0x20)
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

/* Bit definitions and macros for MCF_SCM_PPMRL */
#define MCF_SCM_PPMRL_CDG                    (0x2)
#define MCF_SCM_PPMRL_CDDMA                  (0x10)
#define MCF_SCM_PPMRL_CDUART0                (0x20)
#define MCF_SCM_PPMRL_CDUART1                (0x40)
#define MCF_SCM_PPMRL_CDUART2                (0x80)
#define MCF_SCM_PPMRL_CDI2C                  (0x200)
#define MCF_SCM_PPMRL_CDQSPI                 (0x400)
#define MCF_SCM_PPMRL_CDRTC                  (0x1000)
#define MCF_SCM_PPMRL_CDTMR0                 (0x2000)
#define MCF_SCM_PPMRL_CDTMR1                 (0x4000)
#define MCF_SCM_PPMRL_CDTMR2                 (0x8000)
#define MCF_SCM_PPMRL_CDTMR3                 (0x10000)
#define MCF_SCM_PPMRL_CDINTC0                (0x20000)
#define MCF_SCM_PPMRL_CDINTC1                (0x40000)
#define MCF_SCM_PPMRL_CDFEC0                 (0x200000)

/* Bit definitions and macros for MCF_SCM_MPARK */
#define MCF_SCM_MPARK_LCKOUT_TIME(x)         (((x)&0xF)<<0x8)
#define MCF_SCM_MPARK_PRKLAST                (0x1000)
#define MCF_SCM_MPARK_TIMEOUT                (0x2000)
#define MCF_SCM_MPARK_FIXED                  (0x4000)
#define MCF_SCM_MPARK_M1_PRTY(x)             (((x)&0x3)<<0x10)
#define MCF_SCM_MPARK_M0_PRTY(x)             (((x)&0x3)<<0x12)
#define MCF_SCM_MPARK_M2_PRTY(x)             (((x)&0x3)<<0x14)
#define MCF_SCM_MPARK_BCR24BIT               (0x1000000)
#define MCF_SCM_MPARK_M2_P_EN                (0x2000000)

/* Bit definitions and macros for MCF_SCM_MPR */
#define MCF_SCM_MPR_MPR(x)                   (((x)&0xF)<<0)

/* Bit definitions and macros for MCF_SCM_PPMRS */
#define MCF_SCM_PPMRS_PPMRS(x)               (((x)&0x7F)<<0)
#define MCF_SCM_PPMRS_DISABLE_ALL            (0x40)
#define MCF_SCM_PPMRS_DISABLE_CFM            (0x2B)
#define MCF_SCM_PPMRS_DISABLE_CAN            (0x2A)
#define MCF_SCM_PPMRS_DISABLE_PWM            (0x29)
#define MCF_SCM_PPMRS_DISABLE_GPT            (0x28)
#define MCF_SCM_PPMRS_DISABLE_ADC            (0x27)
#define MCF_SCM_PPMRS_DISABLE_PIT1           (0x24)
#define MCF_SCM_PPMRS_DISABLE_PIT0           (0x23)
#define MCF_SCM_PPMRS_DISABLE_EPORT          (0x21)
#define MCF_SCM_PPMRS_DISABLE_PORTS          (0x20)
#define MCF_SCM_PPMRS_DISABLE_INTC           (0x11)
#define MCF_SCM_PPMRS_DISABLE_DTIM3          (0x10)
#define MCF_SCM_PPMRS_DISABLE_DTIM2          (0xF)
#define MCF_SCM_PPMRS_DISABLE_DTIM1          (0xE)
#define MCF_SCM_PPMRS_DISABLE_DTIM0          (0xD)
#define MCF_SCM_PPMRS_DISABLE_QSPI           (0xA)
#define MCF_SCM_PPMRS_DISABLE_I2C            (0x9)
#define MCF_SCM_PPMRS_DISABLE_UART2          (0x7)
#define MCF_SCM_PPMRS_DISABLE_UART1          (0x6)
#define MCF_SCM_PPMRS_DISABLE_UART0          (0x5)
#define MCF_SCM_PPMRS_DISABLE_DMA            (0x4)
#define MCF_SCM_PPMRS_SET_CDG                (0x1)

/* Bit definitions and macros for MCF_SCM_PPMRC */
#define MCF_SCM_PPMRC_PPMRC(x)               (((x)&0x7F)<<0)
#define MCF_SCM_PPMRC_ENABLE_ALL             (0x40)
#define MCF_SCM_PPMRC_ENABLE_CFM             (0x2B)
#define MCF_SCM_PPMRC_ENABLE_CAN             (0x2A)
#define MCF_SCM_PPMRC_ENABLE_PWM             (0x29)
#define MCF_SCM_PPMRC_ENABLE_GPT             (0x28)
#define MCF_SCM_PPMRC_ENABLE_ADC             (0x27)
#define MCF_SCM_PPMRC_ENABLE_PIT1            (0x24)
#define MCF_SCM_PPMRC_ENABLE_PIT0            (0x23)
#define MCF_SCM_PPMRC_ENABLE_EPORT           (0x21)
#define MCF_SCM_PPMRC_ENABLE_PORTS           (0x20)
#define MCF_SCM_PPMRC_ENABLE_INTC            (0x11)
#define MCF_SCM_PPMRC_ENABLE_DTIM3           (0x10)
#define MCF_SCM_PPMRC_ENABLE_DTIM2           (0xF)
#define MCF_SCM_PPMRC_ENABLE_DTIM1           (0xE)
#define MCF_SCM_PPMRC_ENABLE_DTIM0           (0xD)
#define MCF_SCM_PPMRC_ENABLE_QSPI            (0xA)
#define MCF_SCM_PPMRC_ENABLE_I2C             (0x9)
#define MCF_SCM_PPMRC_ENABLE_UART2           (0x7)
#define MCF_SCM_PPMRC_ENABLE_UART1           (0x6)
#define MCF_SCM_PPMRC_ENABLE_UART0           (0x5)
#define MCF_SCM_PPMRC_ENABLE_DMA             (0x4)
#define MCF_SCM_PPMRC_CLEAR_CDG              (0x1)

/* Bit definitions and macros for MCF_SCM_IPSBMT */
#define MCF_SCM_IPSBMT_BMT(x)                (((x)&0x7)<<0)
#define MCF_SCM_IPSBMT_BMT_CYCLES_1024       (0)
#define MCF_SCM_IPSBMT_BMT_CYCLES_512        (0x1)
#define MCF_SCM_IPSBMT_BMT_CYCLES_256        (0x2)
#define MCF_SCM_IPSBMT_BMT_CYCLES_128        (0x3)
#define MCF_SCM_IPSBMT_BMT_CYCLES_64         (0x4)
#define MCF_SCM_IPSBMT_BMT_CYCLES_32         (0x5)
#define MCF_SCM_IPSBMT_BMT_CYCLES_16         (0x6)
#define MCF_SCM_IPSBMT_BMT_CYCLES_8          (0x7)
#define MCF_SCM_IPSBMT_BME                   (0x8)

/* Bit definitions and macros for MCF_SCM_PACR */
#define MCF_SCM_PACR_ACCESS_CTRL0(x)         (((x)&0x7)<<0)
#define MCF_SCM_PACR_LOCK0                   (0x8)
#define MCF_SCM_PACR_ACCESS_CTRL1(x)         (((x)&0x7)<<0x4)
#define MCF_SCM_PACR_LOCK1                   (0x80)

/* Bit definitions and macros for MCF_SCM_GPACR */
#define MCF_SCM_GPACR_ACCESS_CTRL(x)         (((x)&0xF)<<0)
#define MCF_SCM_GPACR_LOCK                   (0x80)


#endif /* __MCF52235_SCM_H__ */
