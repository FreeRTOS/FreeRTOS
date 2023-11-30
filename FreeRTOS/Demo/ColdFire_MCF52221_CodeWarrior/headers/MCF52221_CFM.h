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

#ifndef __MCF52221_CFM_H__
#define __MCF52221_CFM_H__


/*********************************************************************
*
* ColdFire Flash Module (CFM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_CFM_CFMMCR                       (*(vuint16*)(0x401D0000))
#define MCF_CFM_CFMCLKD                      (*(vuint8 *)(0x401D0002))
#define MCF_CFM_CFMSEC                       (*(vuint32*)(0x401D0008))
#define MCF_CFM_CFMPROT                      (*(vuint32*)(0x401D0010))
#define MCF_CFM_CFMSACC                      (*(vuint32*)(0x401D0014))
#define MCF_CFM_CFMDACC                      (*(vuint32*)(0x401D0018))
#define MCF_CFM_CFMUSTAT                     (*(vuint8 *)(0x401D0020))
#define MCF_CFM_CFMCMD                       (*(vuint8 *)(0x401D0024))
#define MCF_CFM_CFMCLKSEL                    (*(vuint16*)(0x401D004A))


/* Bit definitions and macros for MCF_CFM_CFMMCR */
#define MCF_CFM_CFMMCR_KEYACC                (0x20)
#define MCF_CFM_CFMMCR_CCIE                  (0x40)
#define MCF_CFM_CFMMCR_CBEIE                 (0x80)
#define MCF_CFM_CFMMCR_AEIE                  (0x100)
#define MCF_CFM_CFMMCR_PVIE                  (0x200)
#define MCF_CFM_CFMMCR_LOCK                  (0x400)

/* Bit definitions and macros for MCF_CFM_CFMCLKD */
#define MCF_CFM_CFMCLKD_DIV(x)               (((x)&0x3F)<<0)
#define MCF_CFM_CFMCLKD_PRDIV8               (0x40)
#define MCF_CFM_CFMCLKD_DIVLD                (0x80)

/* Bit definitions and macros for MCF_CFM_CFMSEC */
#define MCF_CFM_CFMSEC_SEC(x)                (((x)&0xFFFF)<<0)
#define MCF_CFM_CFMSEC_SECSTAT               (0x40000000)
#define MCF_CFM_CFMSEC_KEYEN                 (0x80000000)

/* Bit definitions and macros for MCF_CFM_CFMPROT */
#define MCF_CFM_CFMPROT_PROTECT(x)           (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_CFM_CFMSACC */
#define MCF_CFM_CFMSACC_SUPV(x)              (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_CFM_CFMDACC */
#define MCF_CFM_CFMDACC_DACC(x)              (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_CFM_CFMUSTAT */
#define MCF_CFM_CFMUSTAT_BLANK               (0x4)
#define MCF_CFM_CFMUSTAT_ACCERR              (0x10)
#define MCF_CFM_CFMUSTAT_PVIOL               (0x20)
#define MCF_CFM_CFMUSTAT_CCIF                (0x40)
#define MCF_CFM_CFMUSTAT_CBEIF               (0x80)

/* Bit definitions and macros for MCF_CFM_CFMCMD */
#define MCF_CFM_CFMCMD_CMD(x)                (((x)&0x7F)<<0)
#define MCF_CFM_CFMCMD_BLANK_CHECK           (0x5)
#define MCF_CFM_CFMCMD_PAGE_ERASE_VERIFY     (0x6)
#define MCF_CFM_CFMCMD_WORD_PROGRAM          (0x20)
#define MCF_CFM_CFMCMD_PAGE_ERASE            (0x40)
#define MCF_CFM_CFMCMD_MASS_ERASE            (0x41)

/* Bit definitions and macros for MCF_CFM_CFMCLKSEL */
#define MCF_CFM_CFMCLKSEL_CLKSEL(x)          (((x)&0x3)<<0)


#endif /* __MCF52221_CFM_H__ */
