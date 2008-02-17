/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_skha.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_SKHA_H__
#define __MCF523X_SKHA_H__

/*********************************************************************
*
* Symmetric Key Hardware Accelerator (SKHA)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_SKHA_SKMR         (*(vuint32*)(void*)(&__IPSBAR[0x1B0000]))
#define MCF_SKHA_SKCR         (*(vuint32*)(void*)(&__IPSBAR[0x1B0004]))
#define MCF_SKHA_SKCMR        (*(vuint32*)(void*)(&__IPSBAR[0x1B0008]))
#define MCF_SKHA_SKSR         (*(vuint32*)(void*)(&__IPSBAR[0x1B000C]))
#define MCF_SKHA_SKIR         (*(vuint32*)(void*)(&__IPSBAR[0x1B0010]))
#define MCF_SKHA_SKIMR        (*(vuint32*)(void*)(&__IPSBAR[0x1B0014]))
#define MCF_SKHA_SKKSR        (*(vuint32*)(void*)(&__IPSBAR[0x1B0018]))
#define MCF_SKHA_SKDSR        (*(vuint32*)(void*)(&__IPSBAR[0x1B001C]))
#define MCF_SKHA_SKIN         (*(vuint32*)(void*)(&__IPSBAR[0x1B0020]))
#define MCF_SKHA_SKOUT        (*(vuint32*)(void*)(&__IPSBAR[0x1B0024]))
#define MCF_SKHA_SKKDR0       (*(vuint32*)(void*)(&__IPSBAR[0x1B0030]))
#define MCF_SKHA_SKKDR1       (*(vuint32*)(void*)(&__IPSBAR[0x1B0034]))
#define MCF_SKHA_SKKDR2       (*(vuint32*)(void*)(&__IPSBAR[0x1B0038]))
#define MCF_SKHA_SKKDR3       (*(vuint32*)(void*)(&__IPSBAR[0x1B003C]))
#define MCF_SKHA_SKKDR4       (*(vuint32*)(void*)(&__IPSBAR[0x1B0040]))
#define MCF_SKHA_SKKDR5       (*(vuint32*)(void*)(&__IPSBAR[0x1B0044]))
#define MCF_SKHA_SKKDRn(x)    (*(vuint32*)(void*)(&__IPSBAR[0x1B0030+((x)*0x004)]))
#define MCF_SKHA_SKCR0        (*(vuint32*)(void*)(&__IPSBAR[0x1B0070]))
#define MCF_SKHA_SKCR1        (*(vuint32*)(void*)(&__IPSBAR[0x1B0074]))
#define MCF_SKHA_SKCR2        (*(vuint32*)(void*)(&__IPSBAR[0x1B0078]))
#define MCF_SKHA_SKCR3        (*(vuint32*)(void*)(&__IPSBAR[0x1B007C]))
#define MCF_SKHA_SKCR4        (*(vuint32*)(void*)(&__IPSBAR[0x1B0080]))
#define MCF_SKHA_SKCR5        (*(vuint32*)(void*)(&__IPSBAR[0x1B0084]))
#define MCF_SKHA_SKCR6        (*(vuint32*)(void*)(&__IPSBAR[0x1B0088]))
#define MCF_SKHA_SKCR7        (*(vuint32*)(void*)(&__IPSBAR[0x1B008C]))
#define MCF_SKHA_SKCR8        (*(vuint32*)(void*)(&__IPSBAR[0x1B0090]))
#define MCF_SKHA_SKCR9        (*(vuint32*)(void*)(&__IPSBAR[0x1B0094]))
#define MCF_SKHA_SKCR10       (*(vuint32*)(void*)(&__IPSBAR[0x1B0098]))
#define MCF_SKHA_SKCR11       (*(vuint32*)(void*)(&__IPSBAR[0x1B009C]))
#define MCF_SKHA_SKCRn(x)     (*(vuint32*)(void*)(&__IPSBAR[0x1B0070+((x)*0x004)]))

/* Bit definitions and macros for MCF_SKHA_SKMR */
#define MCF_SKHA_SKMR_ALG(x)         (((x)&0x00000003)<<0)
#define MCF_SKHA_SKMR_DIR            (0x00000004)
#define MCF_SKHA_SKMR_CM(x)          (((x)&0x00000003)<<3)
#define MCF_SKHA_SKMR_DKP            (0x00000100)
#define MCF_SKHA_SKMR_CTRM(x)        (((x)&0x0000000F)<<9)
#define MCF_SKHA_SKMR_CM_ECB         (0x00000000)
#define MCF_SKHA_SKMR_CM_CBC         (0x00000008)
#define MCF_SKHA_SKMR_CM_CTR         (0x00000018)
#define MCF_SKHA_SKMR_DIR_DEC        (0x00000000)
#define MCF_SKHA_SKMR_DIR_ENC        (0x00000004)
#define MCF_SKHA_SKMR_ALG_AES        (0x00000000)
#define MCF_SKHA_SKMR_ALG_DES        (0x00000001)
#define MCF_SKHA_SKMR_ALG_TDES       (0x00000002)

/* Bit definitions and macros for MCF_SKHA_SKCR */
#define MCF_SKHA_SKCR_IE             (0x00000001)

/* Bit definitions and macros for MCF_SKHA_SKCMR */
#define MCF_SKHA_SKCMR_SWR           (0x00000001)
#define MCF_SKHA_SKCMR_RI            (0x00000002)
#define MCF_SKHA_SKCMR_CI            (0x00000004)
#define MCF_SKHA_SKCMR_GO            (0x00000008)

/* Bit definitions and macros for MCF_SKHA_SKSR */
#define MCF_SKHA_SKSR_INT            (0x00000001)
#define MCF_SKHA_SKSR_DONE           (0x00000002)
#define MCF_SKHA_SKSR_ERR            (0x00000004)
#define MCF_SKHA_SKSR_RD             (0x00000008)
#define MCF_SKHA_SKSR_BUSY           (0x00000010)
#define MCF_SKHA_SKSR_IFL(x)         (((x)&0x000000FF)<<16)
#define MCF_SKHA_SKSR_OFL(x)         (((x)&0x000000FF)<<24)

/* Bit definitions and macros for MCF_SKHA_SKIR */
#define MCF_SKHA_SKIR_IFO            (0x00000001)
#define MCF_SKHA_SKIR_OFU            (0x00000002)
#define MCF_SKHA_SKIR_NEIF           (0x00000004)
#define MCF_SKHA_SKIR_NEOF           (0x00000008)
#define MCF_SKHA_SKIR_IME            (0x00000010)
#define MCF_SKHA_SKIR_DSE            (0x00000020)
#define MCF_SKHA_SKIR_KSE            (0x00000040)
#define MCF_SKHA_SKIR_RMDP           (0x00000080)
#define MCF_SKHA_SKIR_ERE            (0x00000100)
#define MCF_SKHA_SKIR_KPE            (0x00000200)
#define MCF_SKHA_SKIR_KRE            (0x00000400)

/* Bit definitions and macros for MCF_SKHA_SKIMR */
#define MCF_SKHA_SKIMR_IFO           (0x00000001)
#define MCF_SKHA_SKIMR_OFU           (0x00000002)
#define MCF_SKHA_SKIMR_NEIF          (0x00000004)
#define MCF_SKHA_SKIMR_NEOF          (0x00000008)
#define MCF_SKHA_SKIMR_IME           (0x00000010)
#define MCF_SKHA_SKIMR_DSE           (0x00000020)
#define MCF_SKHA_SKIMR_KSE           (0x00000040)
#define MCF_SKHA_SKIMR_RMDP          (0x00000080)
#define MCF_SKHA_SKIMR_ERE           (0x00000100)
#define MCF_SKHA_SKIMR_KPE           (0x00000200)
#define MCF_SKHA_SKIMR_KRE           (0x00000400)

/* Bit definitions and macros for MCF_SKHA_SKKSR */
#define MCF_SKHA_SKKSR_KEYSIZE(x)    (((x)&0x0000003F)<<0)

/********************************************************************/

#endif /* __MCF523X_SKHA_H__ */
