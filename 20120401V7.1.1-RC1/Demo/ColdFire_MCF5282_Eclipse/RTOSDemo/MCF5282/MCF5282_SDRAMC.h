/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_SDRAMC_H__
#define __MCF5282_SDRAMC_H__


/*********************************************************************
*
* Synchronous DRAM Controller (SDRAMC)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_SDRAMC_DCR                       (*(vuint16*)(&__IPSBAR[0x40]))
#define MCF_SDRAMC_DACR0                     (*(vuint32*)(&__IPSBAR[0x48]))
#define MCF_SDRAMC_DMR0                      (*(vuint32*)(&__IPSBAR[0x4C]))
#define MCF_SDRAMC_DACR1                     (*(vuint32*)(&__IPSBAR[0x50]))
#define MCF_SDRAMC_DMR1                      (*(vuint32*)(&__IPSBAR[0x54]))
#define MCF_SDRAMC_DACR(x)                   (*(vuint32*)(&__IPSBAR[0x48 + ((x)*0x8)]))
#define MCF_SDRAMC_DMR(x)                    (*(vuint32*)(&__IPSBAR[0x4C + ((x)*0x8)]))


/* Bit definitions and macros for MCF_SDRAMC_DCR */
#define MCF_SDRAMC_DCR_RC(x)                 (((x)&0x1FF)<<0)
#define MCF_SDRAMC_DCR_RTIM(x)               (((x)&0x3)<<0x9)
#define MCF_SDRAMC_DCR_RTIM_3                (0)
#define MCF_SDRAMC_DCR_RTIM_6                (0x200)
#define MCF_SDRAMC_DCR_RTIM_9                (0x400)
#define MCF_SDRAMC_DCR_IS                    (0x800)
#define MCF_SDRAMC_DCR_COC                   (0x1000)
#define MCF_SDRAMC_DCR_NAM                   (0x2000)

/* Bit definitions and macros for MCF_SDRAMC_DACR */
#define MCF_SDRAMC_DACR_IP                   (0x8)
#define MCF_SDRAMC_DACR_PS(x)                (((x)&0x3)<<0x4)
#define MCF_SDRAMC_DACR_PS_32                (0)
#define MCF_SDRAMC_DACR_PS_8                 (0x10)
#define MCF_SDRAMC_DACR_PS_16                (0x20)
#define MCF_SDRAMC_DACR_IMRS                 (0x40)
#define MCF_SDRAMC_DACR_CBM(x)               (((x)&0x7)<<0x8)
#define MCF_SDRAMC_DACR_CASL(x)              (((x)&0x3)<<0xC)
#define MCF_SDRAMC_DACR_RE                   (0x8000)
#define MCF_SDRAMC_DACR_BA(x)                ((x)&0xFFFC0000)
#define MCF_SDRAMC_DACR_CASL_1               (0)
#define MCF_SDRAMC_DACR_CASL_2               (0x1000)
#define MCF_SDRAMC_DACR_CASL_3               (0x2000)

/* Bit definitions and macros for MCF_SDRAMC_DMR */
#define MCF_SDRAMC_DMR_V                     (0x1)
#define MCF_SDRAMC_DMR_UD                    (0x2)
#define MCF_SDRAMC_DMR_UC                    (0x4)
#define MCF_SDRAMC_DMR_SD                    (0x8)
#define MCF_SDRAMC_DMR_SC                    (0x10)
#define MCF_SDRAMC_DMR_AM                    (0x20)
#define MCF_SDRAMC_DMR_CI                    (0x40)
#define MCF_SDRAMC_DMR_WP                    (0x100)
#define MCF_SDRAMC_DMR_BAM(x)                (((x)&0x3FFF)<<0x12)
#define MCF_SDRAMC_DMR_BAM_4G                (0xFFFC0000)
#define MCF_SDRAMC_DMR_BAM_2G                (0x7FFC0000)
#define MCF_SDRAMC_DMR_BAM_1G                (0x3FFC0000)
#define MCF_SDRAMC_DMR_BAM_1024M             (0x3FFC0000)
#define MCF_SDRAMC_DMR_BAM_512M              (0x1FFC0000)
#define MCF_SDRAMC_DMR_BAM_256M              (0xFFC0000)
#define MCF_SDRAMC_DMR_BAM_128M              (0x7FC0000)
#define MCF_SDRAMC_DMR_BAM_64M               (0x3FC0000)
#define MCF_SDRAMC_DMR_BAM_32M               (0x1FC0000)
#define MCF_SDRAMC_DMR_BAM_16M               (0xFC0000)
#define MCF_SDRAMC_DMR_BAM_8M                (0x7C0000)
#define MCF_SDRAMC_DMR_BAM_4M                (0x3C0000)
#define MCF_SDRAMC_DMR_BAM_2M                (0x1C0000)
#define MCF_SDRAMC_DMR_BAM_1M                (0xC0000)
#define MCF_SDRAMC_DMR_BAM_1024K             (0xC0000)
#define MCF_SDRAMC_DMR_BAM_512K              (0x40000)
#define MCF_SDRAMC_DMR_BAM_256K              (0)


#endif /* __MCF5282_SDRAMC_H__ */
