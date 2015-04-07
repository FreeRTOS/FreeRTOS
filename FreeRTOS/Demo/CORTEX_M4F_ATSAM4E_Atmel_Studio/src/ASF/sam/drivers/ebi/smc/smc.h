/**
 * \file
 *
 * \brief Static Memory Controller (SMC) driver for SAM.
 *
 * Copyright (c) 2011-2013 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */

#ifndef SMC_H_INCLUDED
#define SMC_H_INCLUDED

#include "compiler.h"

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

#if ((SAM3S) || (SAM3U) || (SAM3XA) || (SAM4S) || (SAM4E))
void smc_set_setup_timing(Smc *p_smc, uint32_t ul_cs, uint32_t ul_setup_timing);
void smc_set_pulse_timing(Smc *p_smc, uint32_t ul_cs, uint32_t ul_pulse_timing);
void smc_set_cycle_timing(Smc *p_smc, uint32_t ul_cs, uint32_t ul_cycle_timing);
void smc_set_mode(Smc *p_smc, uint32_t ul_cs, uint32_t ul_mode);
uint32_t smc_get_mode(Smc *p_smc, uint32_t ul_cs);
void smc_enable_writeprotect(Smc *p_smc, uint32_t ul_enable);
uint32_t smc_get_writeprotect_status(Smc *p_smc);
#endif	/* ((SAM3S) || (SAM3U) || (SAM3XA)) */

#if ((SAM3U) || (SAM3XA))
/* NFCADDR_CMD : NFC Address Command */
#define NFCADDR_CMD_CMD1      (0xFFu <<  2) /* Command Register Value for Cycle 1 */
#define NFCADDR_CMD_CMD2      (0xFFu << 10) /* Command Register Value for Cycle 2 */
#define NFCADDR_CMD_VCMD2     (0x1u << 18)  /* Valid Cycle 2 Command */
#define NFCADDR_CMD_ACYCLE    (0x7u << 19)  /* Number of Address required for the current command */
#define   NFCADDR_CMD_ACYCLE_NONE    (0x0u << 19) /* No address cycle */
#define   NFCADDR_CMD_ACYCLE_ONE     (0x1u << 19) /* One address cycle */
#define   NFCADDR_CMD_ACYCLE_TWO     (0x2u << 19) /* Two address cycles */
#define   NFCADDR_CMD_ACYCLE_THREE   (0x3u << 19) /* Three address cycles */
#define   NFCADDR_CMD_ACYCLE_FOUR    (0x4u << 19) /* Four address cycles */
#define   NFCADDR_CMD_ACYCLE_FIVE    (0x5u << 19) /* Five address cycles */
#define NFCADDR_CMD_CSID_Pos 22
#define NFCADDR_CMD_CSID_Msk (0x7u << NFCADDR_CMD_CSID_Pos) /* Chip Select Identifier */
#define NFCADDR_CMD_CSID(value) ((NFCADDR_CMD_CSID_Msk & ((value) << NFCADDR_CMD_CSID_Pos)))
#define NFCADDR_CMD_NFCEN     (0x1u << 25)  /* NFC Enable */
#define NFCADDR_CMD_NFC_READ     (0x0u << 26)  /* NFC Write Enable */
#define NFCADDR_CMD_NFC_WIRTE    (0x1u << 26)  /* NFC Write Enable */
#define NFCADDR_CMD_NFCCMD    (0x1u << 27)  /* NFC Command Enable */

#define NFC_BUSY_FLAG    0x8000000
#define ECC_STATUS_MASK   0x07

void smc_set_nand_timing(Smc * p_smc, uint32_t ul_cs,
		uint32_t ul_nand_timing);
void smc_nfc_init(Smc *p_smc, uint32_t ul_config);
void smc_nfc_set_page_size(Smc *p_smc, uint32_t ul_page_size);
void smc_nfc_enable_spare_read(Smc *p_smc);
void smc_nfc_disable_spare_read(Smc *p_smc);
void smc_nfc_enable_spare_write(Smc *p_smc);
void smc_nfc_disable_spare_write(Smc *p_smc);
void smc_nfc_enable(Smc *p_smc);
void smc_nfc_disable(Smc *p_smc);
uint32_t smc_nfc_get_status(Smc * p_smc);
void smc_nfc_enable_interrupt(Smc *p_smc, uint32_t ul_sources);
void smc_nfc_disable_interrupt(Smc *p_smc, uint32_t ul_sources);
uint32_t smc_nfc_get_interrupt_mask(Smc *p_smc);
void smc_nfc_set_address0(Smc *p_smc, uint8_t uc_address0);
void smc_nfc_set_bank(Smc *p_smc, uint32_t ul_bank);
void smc_nfc_send_command(Smc *p_smc, uint32_t ul_cmd, uint32_t ul_address_cycle, uint32_t ul_cycle0);
void smc_ecc_init(Smc *p_smc, uint32_t ul_type, uint32_t ul_pagesize);
uint32_t smc_ecc_get_status(Smc *p_smc, uint32_t ul_parity_number);
void smc_ecc_get_value(Smc *p_smc, uint32_t *p_ecc);
#endif  /* ((SAM3U) || (SAM3XA)) */

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond

#endif /* SMC_H_INCLUDED */
