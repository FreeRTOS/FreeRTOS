/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_mdha.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_MDHA_H__
#define __MCF523X_MDHA_H__

/*********************************************************************
*
* Message Digest Hardware Accelerator (MDHA)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_MDHA_MDMR     (*(vuint32*)(void*)(&__IPSBAR[0x190000]))
#define MCF_MDHA_MDCR     (*(vuint32*)(void*)(&__IPSBAR[0x190004]))
#define MCF_MDHA_MDCMR    (*(vuint32*)(void*)(&__IPSBAR[0x190008]))
#define MCF_MDHA_MDSR     (*(vuint32*)(void*)(&__IPSBAR[0x19000C]))
#define MCF_MDHA_MDISR     (*(vuint32*)(void*)(&__IPSBAR[0x190010]))
#define MCF_MDHA_MDIMR    (*(vuint32*)(void*)(&__IPSBAR[0x190014]))
#define MCF_MDHA_MDDSR    (*(vuint32*)(void*)(&__IPSBAR[0x19001C]))
#define MCF_MDHA_MDIN     (*(vuint32*)(void*)(&__IPSBAR[0x190020]))
#define MCF_MDHA_MDA0     (*(vuint32*)(void*)(&__IPSBAR[0x190030]))
#define MCF_MDHA_MDB0     (*(vuint32*)(void*)(&__IPSBAR[0x190034]))
#define MCF_MDHA_MDC0     (*(vuint32*)(void*)(&__IPSBAR[0x190038]))
#define MCF_MDHA_MDD0     (*(vuint32*)(void*)(&__IPSBAR[0x19003C]))
#define MCF_MDHA_MDE0     (*(vuint32*)(void*)(&__IPSBAR[0x190040]))
#define MCF_MDHA_MDMDS    (*(vuint32*)(void*)(&__IPSBAR[0x190044]))
#define MCF_MDHA_MDA1     (*(vuint32*)(void*)(&__IPSBAR[0x190070]))
#define MCF_MDHA_MDB1     (*(vuint32*)(void*)(&__IPSBAR[0x190074]))
#define MCF_MDHA_MDC1     (*(vuint32*)(void*)(&__IPSBAR[0x190078]))
#define MCF_MDHA_MDD1     (*(vuint32*)(void*)(&__IPSBAR[0x19007C]))
#define MCF_MDHA_MDE1     (*(vuint32*)(void*)(&__IPSBAR[0x190080]))

/* Bit definitions and macros for MCF_MDHA_MDMR */
#define MCF_MDHA_MDMR_ALG             (0x00000001)
#define MCF_MDHA_MDMR_PDATA           (0x00000004)
#define MCF_MDHA_MDMR_MAC(x)          (((x)&0x00000003)<<3)
#define MCF_MDHA_MDMR_INIT            (0x00000020)
#define MCF_MDHA_MDMR_IPAD            (0x00000040)
#define MCF_MDHA_MDMR_OPAD            (0x00000080)
#define MCF_MDHA_MDMR_SWAP            (0x00000100)
#define MCF_MDHA_MDMR_MACFULL         (0x00000200)
#define MCF_MDHA_MDMR_SSL             (0x00000400)

/* Bit definitions and macros for MCF_MDHA_MDCR */
#define MCF_MDHA_MDCR_IE              (0x00000001)

/* Bit definitions and macros for MCF_MDHA_MDCMR */
#define MCF_MDHA_MDCMR_SWR             (0x00000001)
#define MCF_MDHA_MDCMR_RI             (0x00000002)
#define MCF_MDHA_MDCMR_CI             (0x00000004)
#define MCF_MDHA_MDCMR_GO             (0x00000008)

/* Bit definitions and macros for MCF_MDHA_MDSR */
#define MCF_MDHA_MDSR_INT             (0x00000001)
#define MCF_MDHA_MDSR_DONE            (0x00000002)
#define MCF_MDHA_MDSR_ERR             (0x00000004)
#define MCF_MDHA_MDSR_RD              (0x00000008)
#define MCF_MDHA_MDSR_BUSY            (0x00000010)
#define MCF_MDHA_MDSR_END             (0x00000020)
#define MCF_MDHA_MDSR_HSH             (0x00000040)
#define MCF_MDHA_MDSR_GNW             (0x00000080)
#define MCF_MDHA_MDSR_FS(x)           (((x)&0x00000007)<<8)
#define MCF_MDHA_MDSR_APD(x)          (((x)&0x00000007)<<13)
#define MCF_MDHA_MDSR_IFL(x)          (((x)&0x000000FF)<<16)

/* Bit definitions and macros for MCF_MDHA_MDIR */
#define MCF_MDHA_MDIR_IFO             (0x00000001)
#define MCF_MDHA_MDIR_NON             (0x00000004)
#define MCF_MDHA_MDIR_IME             (0x00000010)
#define MCF_MDHA_MDIR_IDS             (0x00000020)
#define MCF_MDHA_MDIR_RMDP            (0x00000080)
#define MCF_MDHA_MDIR_ERE             (0x00000100)
#define MCF_MDHA_MDIR_GTDS            (0x00000200)

/* Bit definitions and macros for MCF_MDHA_MDIMR */
#define MCF_MDHA_MDIMR_IFO            (0x00000001)
#define MCF_MDHA_MDIMR_NON            (0x00000004)
#define MCF_MDHA_MDIMR_IME            (0x00000010)
#define MCF_MDHA_MDIMR_IDS            (0x00000020)
#define MCF_MDHA_MDIMR_RMDP           (0x00000080)
#define MCF_MDHA_MDIMR_ERE            (0x00000100)
#define MCF_MDHA_MDIMR_GTDS           (0x00000200)

/* Bit definitions and macros for MCF_MDHA_MDDSR */
#define MCF_MDHA_MDDSR_DATASIZE(x)    (((x)&0x1FFFFFFF)<<0)

/********************************************************************/

#endif /* __MCF523X_MDHA_H__ */
