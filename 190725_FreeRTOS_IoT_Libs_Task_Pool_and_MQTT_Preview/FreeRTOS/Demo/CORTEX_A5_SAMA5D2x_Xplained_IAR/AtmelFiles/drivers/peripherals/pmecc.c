/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/** \file */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "trace.h"

#include "peripherals/pmecc.h"
#include "peripherals/pmecc_gallois_field_512.h"
#include "peripherals/pmecc_gallois_field_1024.h"

/*--------------------------------------------------------------------------- */
/*         Local types                                                        */
/*--------------------------------------------------------------------------- */

/** PMECC configuration descriptor */
struct _pmecc_descriptor {
	/** Number of Sectors in one Page */
	uint32_t page_size;

	/** The spare area size is equal to (SPARESIZE+1) bytes */
	uint32_t spare_size;

	/** 0 for 512, 1 for 1024 bytes, like in PMECCFG register */
	uint32_t sector_size;

	/** Coded value of ECC bit number correction
	  * 0 (2 bits), 1 (4 bits), 2 (8 bits), 3 (12 bits), 4 (24 bits), 5 (NU)) */
	uint32_t err_bit_nbr_capability;

	/** Real size in bytes of ECC in spare */
	uint32_t ecc_size_byte;

	/** The first byte address of the ECC area */
	uint32_t ecc_start_address;

	/** The last byte address of the ECC area */
	uint32_t ecc_end_address;

	/** NAND Write Access*/
	uint32_t nand_wr;

	/** Spare Enable */
	uint32_t spare_ena;

	/** Automatic Mode */
	uint32_t mode_auto;

	/** The PMECC Module data path Setup Time is set to CLKCTRL+1. */
	uint32_t clk_ctrl;

	/** */
	uint32_t interrupt;

	/** defines the error correcting capability selected at encoding/decoding time */
	int32_t tt;

	/** degree of the remainders, GF(2**mm) */
	int32_t mm;

	/** length of codeword =  nn=2**mm -1 */
	int32_t nn;

	/** Gallois field table */
	const int16_t *alpha_to;

	/** Index of Gallois field table */
	const int16_t *index_of;

	/** */
	int16_t partial_syn[100];

	/** Holds the current syndrome value, an element of that table belongs to the field.*/
	int16_t si[100];

	/** sigma table */
	int16_t smu[PMECC_NB_ERROR_MAX + 2][2 * PMECC_NB_ERROR_MAX + 1];

	/** polynom order */
	int16_t lmu[PMECC_NB_ERROR_MAX + 1];
};

/*--------------------------------------------------------------------------- */
/*         Local variables                                                    */
/*--------------------------------------------------------------------------- */

/** Pmecc decriptor instance */
struct _pmecc_descriptor pmecc_desc;

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

 /**
 * \brief Build the pseudo syndromes table
 * \param sector Targetted sector.
 */
static void gen_syn(uint32_t sector)
{
	int16_t *remainer;
	uint32_t index;

	remainer = (int16_t*)&HSMC->SMC_REM[sector];
	for (index = 0; index < (uint32_t)pmecc_desc.tt; index++) {
		/* Fill odd syndromes */
		pmecc_desc.partial_syn[1 + (2 * index)] = remainer[index];
	}
}

/**
 * \brief The substitute function evaluates the polynomial remainder,
 * with different values of the field primitive elements.
 */
static uint32_t substitute(void)
{
	int32_t i, j;
	int16_t *si;
	int16_t *p_partial_syn = pmecc_desc.partial_syn;
	const int16_t *alpha_to = pmecc_desc.alpha_to;
	const int16_t *index_of = pmecc_desc.index_of;

	/* si[] is a table that holds the current syndrome value, an element of that table belongs to the field.*/
	si = pmecc_desc.si;

	for (i = 1; i < 2 * PMECC_NB_ERROR_MAX; i++)
		si[i] = 0;

	/* Computation 2t syndromes based on S(x) */
	/* Odd syndromes */
	for (i = 1; i <= 2 * pmecc_desc.tt - 1; i = i + 2) {
		si[i] = 0;
		for (j = 0; j < pmecc_desc.mm; j++) {
			if (p_partial_syn[i] & ((uint16_t)0x1 << j))
				si[i] = alpha_to[(i * j)] ^ si[i];
		}
	}
	/* Even syndrome = (Odd syndrome) ** 2 */
	for (i = 2; i <= 2 * pmecc_desc.tt; i = i + 2) {
		j = i / 2;
		if (si[j] == 0) {
			si[i] = 0;
		} else {
			si[i] = alpha_to[(2 * index_of[si[j]]) % pmecc_desc.nn];
		}
	}
	return 0;
}

/**
 * \brief The substitute function finding the value of the error
 * location polynomial.
 */
static uint32_t get_sigma(void)
{
	uint32_t dmu_0_count;
	int32_t i, j, k;
	int16_t *lmu = pmecc_desc.lmu;
	int16_t *si = pmecc_desc.si;
	int16_t tt = pmecc_desc.tt;

	int32_t mu[PMECC_NB_ERROR_MAX+1]; /* mu */
	int32_t dmu[PMECC_NB_ERROR_MAX+1]; /* discrepancy */
	int32_t delta[PMECC_NB_ERROR_MAX+1]; /* delta order */
	int32_t ro; /* index of largest delta */
	int32_t largest;
	int32_t diff;

	dmu_0_count = 0;

	/* -- First Row -- */

	/* Mu */
	mu[0]  = -1;
	/* Actually -1/2 */
	/* Sigma(x) set to 1 */

	for (i = 0; i < (2 * PMECC_NB_ERROR_MAX + 1); i++)
		pmecc_desc.smu[0][i] = 0;
	pmecc_desc.smu[0][0] = 1;

	/* discrepancy set to 1 */
	dmu[0] = 1;

	/* polynom order set to 0 */
	lmu[0] = 0;

	/* delta set to -1 */
	delta[0]  = (mu[0] * 2 - lmu[0]) >> 1;

	/* -- Second Row -- */

	/* Mu */
	mu[1] = 0;

	/* Sigma(x) set to 1 */
	for (i = 0; i < (2 * PMECC_NB_ERROR_MAX + 1); i++)
		pmecc_desc.smu[1][i] = 0;
	pmecc_desc.smu[1][0] = 1;

	/* discrepancy set to S1 */
	dmu[1] = si[1];

	/* polynom order set to 0 */
	lmu[1] = 0;

	/* delta set to 0 */
	delta[1]  = (mu[1] * 2 - lmu[1]) >> 1;

	/* Init the Sigma(x) last row */
	for (i = 0; i < (2 * PMECC_NB_ERROR_MAX + 1); i++)
		pmecc_desc.smu[tt + 1][i] = 0;

	for (i = 1; i <= tt; i++) {
		mu[i+1] = i << 1;

		/* Compute Sigma (Mu+1)             */
		/* And L(mu)                        */
		/* check if discrepancy is set to 0 */
		if ( dmu[i] == 0) {
			dmu_0_count++;
			if (( tt - (lmu[i] >> 1) - 1) & 0x1) {
				if (dmu_0_count == (uint32_t)((tt - (lmu[i] >> 1) - 1) / 2) + 2) {
					for (j = 0; j <= (lmu[i] >> 1) + 1; j++)
						pmecc_desc.smu[tt+1][j] = pmecc_desc.smu[i][j];
					lmu[tt + 1] = lmu[i];
					return 0;
				}
			} else {
				if (dmu_0_count == (uint32_t)((tt - (lmu[i] >> 1) - 1) / 2) + 1) {
					for (j = 0; j <= (lmu[i] >> 1) + 1; j++)
						pmecc_desc.smu[tt + 1][j] = pmecc_desc.smu[i][j];
					lmu[tt + 1] = lmu[i];
					return 0;
				}
			}

			/* copy polynom */
			for (j = 0; j <= (lmu[i] >> 1); j++)
				pmecc_desc.smu[i + 1][j] = pmecc_desc.smu[i][j];

			/* copy previous polynom order to the next */
			lmu[i + 1] = lmu[i];
		} else {
			/* find largest delta with dmu != 0 */
			ro = 0;
			largest = -1;
			for (j = 0; j < i; j++) {
				if (dmu[j]) {
					if (delta[j] > largest) {
						largest = delta[j];
						ro = j;
					}
				}
			}

			/* compute difference */
			diff = (mu[i] - mu[ro]);

			/* Compute degree of the new smu polynomial */
			if ((lmu[i] >> 1) > ((lmu[ro] >> 1) + diff))
				lmu[i + 1] = lmu[i];
			else
				lmu[i + 1] = ((lmu[ro] >> 1) + diff) * 2;

			/* Init smu[i+1] with 0 */
			for (k = 0; k < (2 * PMECC_NB_ERROR_MAX + 1); k++)
				pmecc_desc.smu[i+1][k] = 0;

			/* Compute smu[i+1] */
			for (k = 0; k <= (lmu[ro] >> 1); k++) {
				if (pmecc_desc.smu[ro][k] && dmu[i])
					pmecc_desc.smu[i + 1][k + diff] = pmecc_desc.alpha_to[(pmecc_desc.index_of[dmu[i]] +
							(pmecc_desc.nn - pmecc_desc.index_of[dmu[ro]]) +
							pmecc_desc.index_of[pmecc_desc.smu[ro][k]]) % pmecc_desc.nn];
			}
			for (k = 0; k <= (lmu[i] >> 1); k++)
				pmecc_desc.smu[i+1][k] ^= pmecc_desc.smu[i][k];
		}

		/*************************************************/
		/*      End Compute Sigma (Mu+1)                 */
		/*      And L(mu)                                */
		/*************************************************/
		/* In either case compute delta */
		delta[i + 1] = (mu[i + 1] * 2 - lmu[i + 1]) >> 1;

		/* Do not compute discrepancy for the last iteration */
		if (i < tt) {
			for (k = 0 ; k <= (lmu[i + 1] >> 1); k++) {
				if (k == 0)
					dmu[i + 1] = si[2 * (i - 1) + 3];
				/* check if one operand of the multiplier is null, its index is -1 */
				else if (pmecc_desc.smu[i+1][k] && si[2 * (i - 1) + 3 - k])
					dmu[i + 1] = pmecc_desc.alpha_to[(pmecc_desc.index_of[pmecc_desc.smu[i + 1][k]] +
							pmecc_desc.index_of[si[2 * (i - 1) + 3 - k]]) % pmecc_desc.nn] ^ dmu[i + 1];
			}
		}
	}
	return 0;
}

/**
 * \brief Init the PMECC Error Location peripheral and start the error
 *        location processing
 * \param sector_size_in_bits Size of the sector in bits.
 * \return Number of errors
 */
static int32_t error_location (uint32_t sector_size_in_bits)
{
	uint32_t alphax;
	uint32_t *sigma;
	uint32_t error_number;
	uint32_t nbr_of_roots;

	/* Disable PMECC Error Location IP */
	HSMC->HSMC_ELDIS |= 0xFFFFFFFF;
	error_number = 0;
	alphax = 0;

	sigma = (uint32_t*)&HSMC->HSMC_SIGMA0;

	for (alphax = 0; alphax <= (uint32_t)(pmecc_desc.lmu[pmecc_desc.tt + 1] >> 1); alphax++) {
		*sigma++ = pmecc_desc.smu[pmecc_desc.tt + 1][alphax];
		error_number++;
	}

	/* Enable error location process */
	HSMC->HSMC_ELCFG |= ((error_number - 1) << 16);
	HSMC->HSMC_ELEN = sector_size_in_bits;

	while ((HSMC->HSMC_ELISR & HSMC_ELISR_DONE) == 0);

	nbr_of_roots = (HSMC->HSMC_ELISR & HSMC_ELISR_ERR_CNT_Msk) >> 8;
	/* Number of roots == degree of smu hence <= tt */
	if (nbr_of_roots == (uint32_t)(pmecc_desc.lmu[pmecc_desc.tt + 1] >> 1))
		return (error_number - 1);

	/* Number of roots not match the degree of smu ==> unable to correct error */
	return -1;
}

/**
 * \brief Correct errors indicated in the PMECCEL error location registers.
 * \param sector_base_address Base address of the sector.
 * \param extra_bytes Number of extra bytes of the sector.(encoded Spare Area, only for the last sector)
 * \param error_nbr Number of error to correct
 * \return Number of errors
 */
static uint32_t error_correction(uint32_t sector_base_address, uint32_t extra_bytes, uint32_t error_nbr)
{
	uint32_t *error_pos;
	uint32_t byte_pos;
	uint32_t bit_pos;
	uint32_t sector_size;
	uint32_t ecc_size;
	uint32_t ecc_end_addr;

	error_pos = (uint32_t*)&HSMC->HSMC_ERRLOC0;

	sector_size = 512 * (((HSMC->HSMC_PMECCFG & HSMC_PMECCFG_SECTORSZ) >> 4) + 1);

	/* Get number of ECC bytes */
	ecc_end_addr = HSMC->HSMC_PMECCEADDR;
	ecc_size = (ecc_end_addr - HSMC->HSMC_PMECCSADDR) + 1;

	while (error_nbr) {
		byte_pos = (*error_pos - 1) / 8;
		bit_pos = (*error_pos - 1) % 8;

		/* If error is located in the data area(not in ECC) */
		if ( byte_pos < (sector_size + extra_bytes)) {
			uint8_t *data_ptr = NULL;

			/* If the error position is before ECC area */
			if ( byte_pos < sector_size + HSMC->HSMC_PMECCSADDR) {
				data_ptr = (uint8_t*)(sector_base_address + byte_pos);
			} else {
				data_ptr = (uint8_t*)(sector_base_address + byte_pos + ecc_size);
			}

			trace_info("Correct error bit @[#Byte %u,Bit# %u]\n\r",
					(unsigned)byte_pos, (unsigned)bit_pos);

			if (*data_ptr & (1 << bit_pos))
				*data_ptr &= (0xFF ^ (1 << bit_pos));
			else
				*data_ptr |= (1 << bit_pos);
		}
		error_pos++;
		error_nbr--;
	}
	return 0;
}

/**
 * \brief Configure the PMECC peripheral
 * \param pPmeccDescriptor Pointer to a PmeccDescriptor instance.
 */
static void _pmecc_configure(void)
{
	/* Disable ECC module */
	HSMC->HSMC_PMECCTRL |= HSMC_PMECCTRL_DISABLE;

	/* Reset the ECC module */
	HSMC->HSMC_PMECCTRL = HSMC_PMECCTRL_RST;
	HSMC->HSMC_PMECCFG = pmecc_desc.err_bit_nbr_capability |
		pmecc_desc.sector_size |
		pmecc_desc.page_size |
		pmecc_desc.nand_wr |
		pmecc_desc.spare_ena |
		pmecc_desc.mode_auto;
	HSMC->HSMC_PMECCSAREA = pmecc_desc.spare_size - 1;
	HSMC->HSMC_PMECCSADDR = pmecc_desc.ecc_start_address;
	HSMC->HSMC_PMECCEADDR = pmecc_desc.ecc_end_address - 1;

	/* Disable all interrupts */
	HSMC->HSMC_PMECCIDR = 0xFF;

	/* Enable ECC module */
	HSMC->HSMC_PMECCTRL |= HSMC_PMECCTRL_ENABLE;
}


/*----------------------------------------------------------------------------
 *        Export functions
 *----------------------------------------------------------------------------*/

/**
 * \brief This function is able to build Galois Field.
 * \param mm degree of the remainders.
 * \param index_of Pointer to a buffer for index_of table.
 * \param alpha_to Pointer to a buffer for alpha_to table.
 */
void build_gf(uint32_t mm, int32_t* index_of, int32_t* alpha_to)
{
	uint32_t i;
	uint32_t mask;
	uint32_t nn;
	uint32_t p[15];

	nn = (1 << mm) - 1;
	/* set default value */
	for (i = 1; i < mm; i++)
		p[i] = 0;

	/*  1 + X^mm */
	p[0]  = 1;
	p[mm] = 1;

	/*  others  */
	if (mm == 3)
		p[1] = 1;
	else if (mm == 4)
		p[1] = 1;
	else if (mm == 5)
		p[2] = 1;
	else if (mm == 6)
		p[1] = 1;
	else if (mm == 7)
		p[3] = 1;
	else if (mm == 8)
		p[2] = p[3] = p[4] = 1;
	else if (mm == 9)
		p[4] = 1;
	else if (mm == 10)
		p[3] = 1;
	else if (mm == 11)
		p[2] = 1;
	else if (mm == 12)
		p[1] = p[4] = p[6] = 1;
	else if (mm == 13)
		p[1] = p[3] = p[4] = 1;
	else if (mm == 14)
		p[1] = p[6] = p[10] = 1;
	else if (mm == 15)
		p[1] = 1;

	/*-- First of All */
	/*-- build alpha ^ mm it will help to generate the field (primitiv) */
	alpha_to[mm] = 0;
	for (i = 0; i < mm; i++)
		if (p[i])
			alpha_to[mm] |= 1 << i;

	/* Secondly */
	/* Build elements from 0 to mm - 1 */
	/* very easy because degree is less than mm so it is */
	/* just a logical shift ! (only the remainder) */
	mask = 1;
	for (i = 0; i < mm; i++) {
		alpha_to[i] = mask;
		index_of[alpha_to[i]] = i;
		mask <<= 1;
	}

	index_of[alpha_to[mm]] = mm;

	/* use a mask to select the MSB bit of the */
	/* LFSR ! */
	mask >>= 1; /* previous value moust be decremented */

	/* then finish the building */
	for (i = mm + 1; i <= nn; i++) {
		/* check if the msb bit of the lfsr is set */
		if (alpha_to[i-1] & mask)
			/* feedback loop is set */
			alpha_to[i] = alpha_to[mm] ^ ((alpha_to[i-1] ^ mask) << 1);
		else
			/*  only shift is enabled */
			alpha_to[i] = alpha_to[i-1] << 1;
		/*  lookup table */
		//index_of[alpha_to[i]] = i ;
		index_of[alpha_to[i]] = i%nn ;
	}
	/* of course index of 0 is undefined in a multiplicative field */
	index_of[0] = -1;
}

/**
 * \brief Initialize the PMECC peripheral
 * \param sector_size 0 for 512, 1 for 1024.
 * \param ecc_errors_per_sector Coded value of ECC bit number correction(2,4,8,12,24).
 * \param page_data_size Data area size in byte.
 * \param page_spare_size Spare area size in byte.
 * \param ecc_offset_in_spare offset of the first ecc byte in spare zone.
 * \param spare_protected 1: The spare area is protected with the last sector of data.
 *                       0: The spare area is skipped in read or write mode.
 * \return 0 if successful; otherwise returns 1.
 */
uint8_t pmecc_initialize(uint8_t sector_size , uint8_t ecc_errors_per_sector,
		uint32_t page_data_size, uint32_t page_spare_size,
		uint16_t ecc_offset_in_spare, uint8_t spare_protected)
{
	uint8_t nb_sectors_per_page = 0;

	if (ecc_errors_per_sector == 0xFF) {
		/* ONFI 2.2 : a value of 0xff indaicate we must apply a correction on sector > 512 bytes,
		   so we set at the maximum allowed by PMECC 24 bits on 1024 sectors. */
		ecc_errors_per_sector = 24;
		sector_size = 1;  /* 1 for 1024 bytes per sector */
	}

	/* Number of Sectors in one Page */
	switch (sector_size) {
	/* 512 bytes per sector */
	case 0:
		pmecc_desc.sector_size = 0;
		nb_sectors_per_page = page_data_size / 512;
		pmecc_desc.mm = 13;
		pmecc_get_gf_512_tables(&pmecc_desc.alpha_to, &pmecc_desc.index_of);
		break;

	/* 1024 bytes per sector */
	case 1:
		pmecc_desc.sector_size = HSMC_PMECCFG_SECTORSZ;
		nb_sectors_per_page = page_data_size / 1024;
		pmecc_desc.mm = 14;
		pmecc_get_gf_1024_tables(&pmecc_desc.alpha_to, &pmecc_desc.index_of);
		break;
	}

	switch (nb_sectors_per_page) {
	case 1:
		pmecc_desc.page_size = HSMC_PMECCFG_PAGESIZE_PAGESIZE_1SEC;
		break;
	case 2:
		pmecc_desc.page_size = HSMC_PMECCFG_PAGESIZE_PAGESIZE_2SEC;
		break;
	case 4:
		pmecc_desc.page_size = HSMC_PMECCFG_PAGESIZE_PAGESIZE_4SEC;
		break;
	case 8:
		pmecc_desc.page_size = HSMC_PMECCFG_PAGESIZE_PAGESIZE_8SEC;
		break;
	default :
		pmecc_desc.page_size = HSMC_PMECCFG_PAGESIZE_PAGESIZE_1SEC;
		break;
	}

	pmecc_desc.nn = (1 << pmecc_desc.mm) - 1;

	/* Coded value of ECC bit number correction (0 (2 bits), 1 (4 bits), 2 (8 bits), 3 (12 bits), 4 (24 bits), 5 (NU)) */
	switch (ecc_errors_per_sector) {
	case 2:
		pmecc_desc.err_bit_nbr_capability = HSMC_PMECCFG_BCH_ERR_BCH_ERR2;
		break;
	case 4:
		pmecc_desc.err_bit_nbr_capability = HSMC_PMECCFG_BCH_ERR_BCH_ERR4;
		break;
	case 8:
		pmecc_desc.err_bit_nbr_capability = HSMC_PMECCFG_BCH_ERR_BCH_ERR8;
		break;
	case 12:
		pmecc_desc.err_bit_nbr_capability = HSMC_PMECCFG_BCH_ERR_BCH_ERR12;
		break;
	case 24:
		pmecc_desc.err_bit_nbr_capability = HSMC_PMECCFG_BCH_ERR_BCH_ERR24;
		break;
	default:
		pmecc_desc.err_bit_nbr_capability = HSMC_PMECCFG_BCH_ERR_BCH_ERR2;
		ecc_errors_per_sector = 2;
		break;
	}

	/* Real value of ECC bit number correction (2, 4, 8, 12, 24) */
	pmecc_desc.tt = ecc_errors_per_sector;
	if (((pmecc_desc.mm * ecc_errors_per_sector ) % 8 ) == 0) {
		pmecc_desc.ecc_size_byte = ((pmecc_desc.mm * ecc_errors_per_sector ) / 8) * nb_sectors_per_page;
	} else  {
		pmecc_desc.ecc_size_byte = (((pmecc_desc.mm * ecc_errors_per_sector ) / 8 ) + 1 ) * nb_sectors_per_page;
	}
	if (ecc_offset_in_spare <= 2) {
		pmecc_desc.ecc_start_address = PMECC_ECC_DEFAULT_START_ADDR;
	} else {
		pmecc_desc.ecc_start_address = ecc_offset_in_spare;
	}
	pmecc_desc.ecc_end_address = pmecc_desc.ecc_start_address + pmecc_desc.ecc_size_byte;
	if (pmecc_desc.ecc_end_address > page_spare_size) {
		return 1;
	}
	pmecc_desc.spare_size = pmecc_desc.ecc_end_address;

	//pmecc_desc.nand_wr = PMECC_CFG_NANDWR;  /* NAND write access */
	pmecc_desc.nand_wr = 0;  /* NAND Read access */
	if (spare_protected) {
		pmecc_desc.spare_ena = HSMC_PMECCFG_SPAREEN;
	} else {
		pmecc_desc.spare_ena = 0;
	}
	/* PMECC_CFG_AUTO indicates that the spare is error protected. In this case, the ECC computation takes into account the whole spare area
	   minus the ECC area in the ECC computation operation */
	pmecc_desc.mode_auto = 0;
	/* At 133 Mhz, this field must be programmed with 2,
	   indicating that the setup time is 3 clock cycles.*/
	pmecc_desc.clk_ctrl = 2;
	pmecc_desc.interrupt = 0;
	_pmecc_configure();
	return 0;
}

/**
 * \brief Return PMECC page size.
 */
uint32_t pmecc_get_page_size(void)
{
	return pmecc_desc.page_size;
}

/**
 * \brief Return PMECC ecc size.
 */
uint32_t pmecc_get_ecc_bytes(void)
{
	return pmecc_desc.ecc_size_byte;
}

/**
 * \brief Return PMECC ecc start address.
 */
uint32_t pmecc_get_ecc_start_address(void)
{
	return pmecc_desc.ecc_start_address;
}

/**
 * \brief Return PMECC ecc end address.
 */
uint32_t pmecc_get_ecc_end_address(void)
{
	return pmecc_desc.ecc_end_address;
}


typedef uint32_t (*pmecc_correction_algo_t)(Smc *, struct _pmecc_descriptor *, uint32_t, uint32_t);

/**
 * \brief Launch error detection functions and correct corrupted bits.
 * \param pmecc_status Value of the PMECC status register.
 * \param page_buffer Base address of the buffer containing the page to be corrected.
 * \return 0 if all errors have been corrected, 1 if too many errors detected
 */
uint32_t pmecc_correction(uint32_t pmecc_status, uint32_t page_buffer)
{
	uint32_t sector_number = 0;
	uint32_t sector_base_address;
	volatile int32_t error_nbr;

	/* Set the sector size (512 or 1024 bytes) */
	HSMC->HSMC_ELCFG = pmecc_desc.sector_size >> 4;

	while (sector_number < (uint32_t)((1 << ((HSMC->HSMC_PMECCFG & HSMC_PMECCFG_PAGESIZE_Msk) >> 8)))) {
		error_nbr = 0;
		if (pmecc_status & 0x1) {
			sector_base_address = page_buffer + (sector_number * ((pmecc_desc.sector_size >> 4) + 1) * 512);
			gen_syn(sector_number);
			substitute();
			get_sigma();
			error_nbr = error_location((((pmecc_desc.sector_size >> 4) + 1) * 512 * 8) +
					(pmecc_desc.tt * (13 + (pmecc_desc.sector_size >> 4)))); /* number of bits of the sector + ecc */

			if (error_nbr == -1)
				return 1;
			else
				error_correction(sector_base_address, 0, error_nbr); /* Extra byte is 0 */
		}
		sector_number++;
		pmecc_status = pmecc_status >> 1;
	}
	return 0;
}

/**
 * \brief Disable pmecc.
 */
void pmecc_disable(void)
{
	/* Disable ECC module */
	HSMC->HSMC_PMECCTRL |= HSMC_PMECCTRL_DISABLE;
}
