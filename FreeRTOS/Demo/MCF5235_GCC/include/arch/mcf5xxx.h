/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:		mcf5xxx.h
 * Purpose:		Definitions common to all ColdFire processors
 *
 * Notes:
 */

#ifndef _CPU_MCF5XXX_H
#define _CPU_MCF5XXX_H

/***********************************************************************/
/*
 * Misc. Defines
 */

#ifdef	FALSE
#undef	FALSE
#endif
#define FALSE	(0)

#ifdef	TRUE
#undef	TRUE
#endif
#define	TRUE	(1)

#ifdef	NULL
#undef	NULL
#endif
#define NULL	(0)

/***********************************************************************/
/*
 * The basic data types
 */

typedef unsigned char		uint8;  /*  8 bits */
typedef unsigned short int	uint16; /* 16 bits */
typedef unsigned long int	uint32; /* 32 bits */

typedef signed char			int8;   /*  8 bits */
typedef signed short int	int16;  /* 16 bits */
typedef signed long int		int32;  /* 32 bits */

typedef volatile uint8		vuint8;  /*  8 bits */
typedef volatile uint16		vuint16; /* 16 bits */
typedef volatile uint32		vuint32; /* 32 bits */

/***********************************************************************/
/*
 * Common M68K & ColdFire definitions
 */

#define ADDRESS			uint32
#define INSTRUCTION		uint16
#define ILLEGAL			0x4AFC
#define CPU_WORD_SIZE	16

#define MCF5XXX_SR_T		(0x8000)
#define MCF5XXX_SR_S		(0x2000)
#define MCF5XXX_SR_M		(0x1000)
#define MCF5XXX_SR_IPL		(0x0700)
#define MCF5XXX_SR_IPL_0	(0x0000)
#define MCF5XXX_SR_IPL_1	(0x0100)
#define MCF5XXX_SR_IPL_2	(0x0200)
#define MCF5XXX_SR_IPL_3	(0x0300)
#define MCF5XXX_SR_IPL_4	(0x0400)
#define MCF5XXX_SR_IPL_5	(0x0500)
#define MCF5XXX_SR_IPL_6	(0x0600)
#define MCF5XXX_SR_IPL_7	(0x0700)
#define MCF5XXX_SR_X		(0x0010)
#define MCF5XXX_SR_N		(0x0008)
#define MCF5XXX_SR_Z		(0x0004)
#define MCF5XXX_SR_V		(0x0002)
#define MCF5XXX_SR_C		(0x0001)

#define MCF5XXX_CACR_CENB		(0x80000000)
#define MCF5XXX_CACR_CPDI		(0x10000000)
#define MCF5XXX_CACR_CPD		(0x10000000)
#define MCF5XXX_CACR_CFRZ		(0x08000000)
#define MCF5XXX_CACR_CINV		(0x01000000)
#define MCF5XXX_CACR_DIDI		(0x00800000)
#define MCF5XXX_CACR_DISD		(0x00400000)
#define MCF5XXX_CACR_INVI		(0x00200000)
#define MCF5XXX_CACR_INVD		(0x00100000)
#define MCF5XXX_CACR_CEIB		(0x00000400)
#define MCF5XXX_CACR_DCM_WR		(0x00000000)
#define MCF5XXX_CACR_DCM_CB		(0x00000100)
#define MCF5XXX_CACR_DCM_IP		(0x00000200)
#define MCF5XXX_CACR_DCM		(0x00000200)
#define MCF5XXX_CACR_DCM_II		(0x00000300)
#define MCF5XXX_CACR_DBWE		(0x00000100)
#define MCF5XXX_CACR_DWP		(0x00000020)
#define MCF5XXX_CACR_EUST		(0x00000010)
#define MCF5XXX_CACR_CLNF_00	(0x00000000)
#define MCF5XXX_CACR_CLNF_01	(0x00000002)
#define MCF5XXX_CACR_CLNF_10	(0x00000004)
#define MCF5XXX_CACR_CLNF_11	(0x00000006)

#define MCF5XXX_ACR_AB(a)		((a)&0xFF000000)
#define MCF5XXX_ACR_AM(a)		(((a)&0xFF000000) >> 8)
#define MCF5XXX_ACR_EN			(0x00008000)
#define MCF5XXX_ACR_SM_USER		(0x00000000)
#define MCF5XXX_ACR_SM_SUPER	(0x00002000)
#define MCF5XXX_ACR_SM_IGNORE	(0x00006000)
#define MCF5XXX_ACR_ENIB		(0x00000080)
#define MCF5XXX_ACR_CM			(0x00000040)
#define MCF5XXX_ACR_DCM_WR		(0x00000000)
#define MCF5XXX_ACR_DCM_CB		(0x00000020)
#define MCF5XXX_ACR_DCM_IP		(0x00000040)
#define MCF5XXX_ACR_DCM_II		(0x00000060)
#define MCF5XXX_ACR_CM			(0x00000040)
#define MCF5XXX_ACR_BWE			(0x00000020)
#define MCF5XXX_ACR_WP			(0x00000004)

#define MCF5XXX_RAMBAR_BA(a)	((a)&0xFFFFC000)
#define MCF5XXX_RAMBAR_PRI_00	(0x00000000)
#define MCF5XXX_RAMBAR_PRI_01	(0x00004000)
#define MCF5XXX_RAMBAR_PRI_10	(0x00008000)
#define MCF5XXX_RAMBAR_PRI_11	(0x0000C000)
#define MCF5XXX_RAMBAR_WP		(0x00000100)
#define MCF5XXX_RAMBAR_CI		(0x00000020)
#define MCF5XXX_RAMBAR_SC		(0x00000010)
#define MCF5XXX_RAMBAR_SD		(0x00000008)
#define MCF5XXX_RAMBAR_UC		(0x00000004)
#define MCF5XXX_RAMBAR_UD		(0x00000002)
#define MCF5XXX_RAMBAR_V		(0x00000001)

/***********************************************************************/
/*
 * The ColdFire family of processors has a simplified exception stack
 * frame that looks like the following:
 *
 *              3322222222221111 111111
 *              1098765432109876 5432109876543210
 *           8 +----------------+----------------+
 *             |         Program Counter         |
 *           4 +----------------+----------------+
 *             |FS/Fmt/Vector/FS|      SR        |
 *   SP -->  0 +----------------+----------------+
 *
 * The stack self-aligns to a 4-byte boundary at an exception, with
 * the FS/Fmt/Vector/FS field indicating the size of the adjustment
 * (SP += 0,1,2,3 bytes).
 */

#define MCF5XXX_RD_SF_FORMAT(PTR)	\
	((*((uint16 *)(PTR)) >> 12) & 0x00FF)

#define MCF5XXX_RD_SF_VECTOR(PTR)	\
	((*((uint16 *)(PTR)) >>  2) & 0x00FF)

#define MCF5XXX_RD_SF_FS(PTR)		\
	( ((*((uint16 *)(PTR)) & 0x0C00) >> 8) | (*((uint16 *)(PTR)) & 0x0003) )

#define MCF5XXX_SF_SR(PTR)	*((uint16 *)(PTR)+1)
#define MCF5XXX_SF_PC(PTR)	*((uint32 *)(PTR)+1)

/********************************************************************/
/*
 * Functions provided by mcf5xxx.s
 */
 
int 	asm_set_ipl (uint32);
void	mcf5xxx_wr_cacr (uint32);
void	mcf5xxx_wr_acr0 (uint32);
void	mcf5xxx_wr_acr1 (uint32);
void	mcf5xxx_wr_acr2 (uint32);
void	mcf5xxx_wr_acr3 (uint32);
void	mcf5xxx_wr_other_a7 (uint32);
void	mcf5xxx_wr_other_sp (uint32);
void	mcf5xxx_wr_vbr (uint32);
void	mcf5xxx_wr_macsr (uint32);
void	mcf5xxx_wr_mask (uint32);
void	mcf5xxx_wr_acc0 (uint32);
void	mcf5xxx_wr_accext01 (uint32);
void	mcf5xxx_wr_accext23 (uint32);
void	mcf5xxx_wr_acc1 (uint32);
void	mcf5xxx_wr_acc2 (uint32);
void	mcf5xxx_wr_acc3 (uint32);
void	mcf5xxx_wr_sr (uint32);
void	mcf5xxx_wr_rambar0 (uint32);
void	mcf5xxx_wr_rambar1 (uint32);
void	mcf5xxx_wr_mbar (uint32);
void	mcf5xxx_wr_mbar0 (uint32);
void	mcf5xxx_wr_mbar1 (uint32);

/********************************************************************/

#endif	/* _CPU_MCF5XXX_H */

