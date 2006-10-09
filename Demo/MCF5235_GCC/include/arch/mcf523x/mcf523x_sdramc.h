/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_sdramc.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_SDRAMC_H__
#define __MCF523X_SDRAMC_H__

/*********************************************************************
*
* SDRAM Controller (SDRAMC)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_SDRAMC_DCR      (*(vuint16*)(void*)(&__IPSBAR[0x000040]))
#define MCF_SDRAMC_DACR0    (*(vuint32*)(void*)(&__IPSBAR[0x000048]))
#define MCF_SDRAMC_DMR0     (*(vuint32*)(void*)(&__IPSBAR[0x00004C]))
#define MCF_SDRAMC_DACR1    (*(vuint32*)(void*)(&__IPSBAR[0x000050]))
#define MCF_SDRAMC_DMR1     (*(vuint32*)(void*)(&__IPSBAR[0x000054]))

/* Bit definitions and macros for MCF_SDRAMC_DCR */
#define MCF_SDRAMC_DCR_RC(x)        (((x)&0x01FF)<<0)
#define MCF_SDRAMC_DCR_RTIM(x)      (((x)&0x0003)<<9)
#define MCF_SDRAMC_DCR_IS           (0x0800)
#define MCF_SDRAMC_DCR_COC          (0x1000)
#define MCF_SDRAMC_DCR_NAM          (0x2000)

/* Bit definitions and macros for MCF_SDRAMC_DACR0 */
#define MCF_SDRAMC_DACR0_IP         (0x00000008)
#define MCF_SDRAMC_DACR0_PS(x)      (((x)&0x00000003)<<4)
#define MCF_SDRAMC_DACR0_MRS        (0x00000040)
#define MCF_SDRAMC_DACR0_CBM(x)     (((x)&0x00000007)<<8)
#define MCF_SDRAMC_DACR0_CASL(x)    (((x)&0x00000003)<<12)
#define MCF_SDRAMC_DACR0_RE         (0x00008000)
#define MCF_SDRAMC_DACR0_BA(x)      (((x)&0x00003FFF)<<18)

/* Bit definitions and macros for MCF_SDRAMC_DMR0 */
#define MCF_SDRAMC_DMR0_V           (0x00000001)
#define MCF_SDRAMC_DMR0_WP          (0x00000100)
#define MCF_SDRAMC_DMR0_BAM(x)      (((x)&0x00003FFF)<<18)

/* Bit definitions and macros for MCF_SDRAMC_DACR1 */
#define MCF_SDRAMC_DACR1_IP         (0x00000008)
#define MCF_SDRAMC_DACR1_PS(x)      (((x)&0x00000003)<<4)
#define MCF_SDRAMC_DACR1_MRS        (0x00000040)
#define MCF_SDRAMC_DACR1_CBM(x)     (((x)&0x00000007)<<8)
#define MCF_SDRAMC_DACR1_CASL(x)    (((x)&0x00000003)<<12)
#define MCF_SDRAMC_DACR1_RE         (0x00008000)
#define MCF_SDRAMC_DACR1_BA(x)      (((x)&0x00003FFF)<<18)

/* Bit definitions and macros for MCF_SDRAMC_DMR1 */
#define MCF_SDRAMC_DMR1_V           (0x00000001)
#define MCF_SDRAMC_DMR1_WP          (0x00000100)
#define MCF_SDRAMC_DMR1_BAM(x)      (((x)&0x00003FFF)<<18)

/********************************************************************/

#define MCF_SDRAMC_DMR_BAM_4G			(0xFFFC0000)
#define MCF_SDRAMC_DMR_BAM_2G			(0x7FFC0000)
#define MCF_SDRAMC_DMR_BAM_1G			(0x3FFC0000)
#define MCF_SDRAMC_DMR_BAM_1024M		(0x3FFC0000)
#define MCF_SDRAMC_DMR_BAM_512M			(0x1FFC0000)
#define MCF_SDRAMC_DMR_BAM_256M			(0x0FFC0000)
#define MCF_SDRAMC_DMR_BAM_128M			(0x07FC0000)
#define MCF_SDRAMC_DMR_BAM_64M			(0x03FC0000)
#define MCF_SDRAMC_DMR_BAM_32M			(0x01FC0000)
#define MCF_SDRAMC_DMR_BAM_16M			(0x00FC0000)
#define MCF_SDRAMC_DMR_BAM_8M			(0x007C0000)
#define MCF_SDRAMC_DMR_BAM_4M			(0x003C0000)
#define MCF_SDRAMC_DMR_BAM_2M			(0x001C0000)
#define MCF_SDRAMC_DMR_BAM_1M			(0x000C0000)
#define MCF_SDRAMC_DMR_BAM_1024K		(0x000C0000)
#define MCF_SDRAMC_DMR_BAM_512K			(0x00040000)
#define MCF_SDRAMC_DMR_BAM_256K			(0x00000000)
#define MCF_SDRAMC_DMR_WP				(0x00000100)
#define MCF_SDRAMC_DMR_CI				(0x00000040)
#define MCF_SDRAMC_DMR_AM				(0x00000020)
#define MCF_SDRAMC_DMR_SC				(0x00000010)
#define MCF_SDRAMC_DMR_SD				(0x00000008)
#define MCF_SDRAMC_DMR_UC				(0x00000004)
#define MCF_SDRAMC_DMR_UD				(0x00000002)
#define MCF_SDRAMC_DMR_V				(0x00000001)

#endif /* __MCF523X_SDRAMC_H__ */
