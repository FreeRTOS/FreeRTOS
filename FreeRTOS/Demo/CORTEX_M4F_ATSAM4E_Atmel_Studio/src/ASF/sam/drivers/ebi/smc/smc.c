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

#include "smc.h"
#include "board.h"

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

/**
 * \defgroup sam_drivers_smc_group Static Memory Controller (SMC)
 *
 * Driver for the Static Memory Controller. It provides functions for configuring
 * and using the on-chip SMC.
 *
 * @{
 */

#if ((SAM3S) || (SAM3U) || (SAM3XA) || (SAM4S) || (SAM4E))
#define SMC_WPKEY_VALUE (0x534D43)
/**
 * \brief Configure the SMC Setup timing for the specified Chip Select.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_cs Chip Select number to be set.
 * \param ul_setup_timing Setup timing for NWE, NCS, NRD.
 */
void smc_set_setup_timing(Smc *p_smc, uint32_t ul_cs,
		uint32_t ul_setup_timing)
{
	p_smc->SMC_CS_NUMBER[ul_cs].SMC_SETUP = ul_setup_timing;
}

/**
 * \brief Configure the SMC pulse timing for the specified Chip Select.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_cs Chip Select number to be set.
 * \param ul_pulse_timing Pulse timing for NWE,NCS,NRD.
 */
void smc_set_pulse_timing(Smc *p_smc, uint32_t ul_cs,
		uint32_t ul_pulse_timing)
{
	p_smc->SMC_CS_NUMBER[ul_cs].SMC_PULSE = ul_pulse_timing;
}

/**
 * \brief Configure the SMC cycle timing for the specified Chip Select.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_cs Chip Select number to be set.
 * \param ul_cycle_timing Cycle timing for NWE and NRD.
 */
void smc_set_cycle_timing(Smc *p_smc, uint32_t ul_cs,
		uint32_t ul_cycle_timing)
{
	p_smc->SMC_CS_NUMBER[ul_cs].SMC_CYCLE = ul_cycle_timing;
}

/**
 * \brief Configure the SMC mode for the specified Chip Select.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_cs Chip select number to be set.
 * \param ul_mode SMC mode.
 */
void smc_set_mode(Smc *p_smc, uint32_t ul_cs, uint32_t ul_mode)
{
	p_smc->SMC_CS_NUMBER[ul_cs].SMC_MODE = ul_mode;
}

/**
 * \brief Get the SMC mode of the specified Chip Select.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_cs Chip select number to be set.
 *
 * \return SMC mode.
 */
uint32_t smc_get_mode(Smc *p_smc, uint32_t ul_cs)
{
	return p_smc->SMC_CS_NUMBER[ul_cs].SMC_MODE;
}

/**
 * \brief Set write protection of SMC registers.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_enable 1 to enable, 0 to disable.
 */
void smc_enable_writeprotect(Smc *p_smc, uint32_t ul_enable)
{
#if (SAM3S || SAM4S || SAM4E)
	if (ul_enable)
		p_smc->SMC_WPMR =
				SMC_WPMR_WPKEY(SMC_WPKEY_VALUE) | SMC_WPMR_WPEN;
	else
		p_smc->SMC_WPMR = SMC_WPMR_WPKEY(SMC_WPKEY_VALUE);
#else
	if (ul_enable)
		p_smc->SMC_WPCR =
				SMC_WPCR_WP_KEY(SMC_WPKEY_VALUE) |
				SMC_WPCR_WP_EN;
	else
		p_smc->SMC_WPCR = SMC_WPCR_WP_KEY(SMC_WPKEY_VALUE);
#endif
}

/**
 * \brief Get the status of SMC write protection register.
 *
 * \param p_smc Pointer to an SMC instance.
 *
 * \return Write protect status.
 */
uint32_t smc_get_writeprotect_status(Smc *p_smc)
{
	return p_smc->SMC_WPSR;
}
#endif /* ((SAM3S) || (SAM3U) || (SAM3XA)) */

#if ((SAM3U) || (SAM3XA))
/**
 * \brief Configure the SMC nand timing for the specified Chip Select.
 * \param p_smc Pointer to an SMC instance.
 * \param ul_cs Chip Select number to be set.
 * \param ul_nand_timing nand timing for related signal.
 */
void smc_set_nand_timing(Smc *p_smc, uint32_t ul_cs,
		uint32_t ul_nand_timing)
{
	p_smc->SMC_CS_NUMBER[ul_cs].SMC_TIMINGS= ul_nand_timing;
}

/**
 * \brief Initialize NFC configuration.
 * \param p_smc Pointer to an SMC instance.
 * \param ul_config SMC NFC Configuration.
 */
void smc_nfc_init(Smc *p_smc, uint32_t ul_config)
{
	p_smc->SMC_CFG = ul_config;
}

/**
 * \brief Set NFC page size.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_page_size Use pattern defined in the device header file.
 */
void smc_nfc_set_page_size(Smc *p_smc, uint32_t ul_page_size)
{
	p_smc->SMC_CFG &= (~SMC_CFG_PAGESIZE_Msk);
	p_smc->SMC_CFG |= ul_page_size;
}

/**
 * \brief Enable NFC controller to read both main and spare area in read mode.
 *
 * \param p_smc Pointer to an SMC instance.
 */
void smc_nfc_enable_spare_read(Smc *p_smc)
{
	p_smc->SMC_CFG |= SMC_CFG_RSPARE;
}

/**
 * \brief Prevent NFC controller from reading the spare area in read mode.
 *
 * \param p_smc Pointer to an SMC instance.
 */
void smc_nfc_disable_spare_read(Smc *p_smc)
{
	p_smc->SMC_CFG &= (~SMC_CFG_RSPARE);
}

/**
 * \brief Enable NFC controller to write both main and spare area in write mode.
 *
 * \param p_smc Pointer to an SMC instance.
 */
void smc_nfc_enable_spare_write(Smc *p_smc)
{
	p_smc->SMC_CFG |= SMC_CFG_WSPARE;
}

/**
 * \brief Prevent NFC controller from writing the spare area in read mode.
 *
 * \param p_smc Pointer to an SMC instance.
 */
void smc_nfc_disable_spare_write(Smc *p_smc)
{
	p_smc->SMC_CFG &= (~SMC_CFG_WSPARE);
}

/**
 * \brief Enable NFC controller.
 *
 * \param p_smc Pointer to an SMC instance.
 */
void smc_nfc_enable(Smc *p_smc)
{
	p_smc->SMC_CTRL = SMC_CTRL_NFCEN;
}

/**
 * \brief Disable NFC controller.
 *
 * \param p_smc Pointer to an SMC instance.
 */
void smc_nfc_disable(Smc *p_smc)
{
	p_smc->SMC_CTRL = SMC_CTRL_NFCDIS;
}

/**
 * \brief Get the NFC Status.
 *
 * \param p_smc Pointer to an SMC instance.
 *
 * \return Returns the current status register of SMC NFC Status Register.
 * This resets the internal value of the status register, so further
 * read may yield different values.
 */
uint32_t smc_nfc_get_status(Smc *p_smc)
{
	return p_smc->SMC_SR;
}

/**
 * \brief Enable SMC interrupts.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_sources Interrupt source bitmap.
 */
void smc_nfc_enable_interrupt(Smc *p_smc, uint32_t ul_sources)
{
	p_smc->SMC_IER = ul_sources;
}

/**
 * \brief Disable SMC interrupts.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_sources Interrupt source bitmap.
 */
void smc_nfc_disable_interrupt(Smc *p_smc, uint32_t ul_sources)
{
	p_smc->SMC_IDR = ul_sources;
}

/**
 * \brief Get the interrupt mask.
 *
 * \param p_smc Pointer to an SMC instance.
 *
 * \return Interrupt mask bitmap.
 */
uint32_t smc_nfc_get_interrupt_mask(Smc *p_smc)
{
	return p_smc->SMC_IMR;
}

/**
 * \brief Set flash cycle 0 address.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param uc_address0 Address cycle 0 in 5 address cycles.
 */
void smc_nfc_set_address0(Smc *p_smc, uint8_t uc_address0)
{
	p_smc->SMC_ADDR = uc_address0;
}

/**
 * \brief Set NFC sram bank.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_bank NFC sram bank.
 */
void smc_nfc_set_bank(Smc *p_smc, uint32_t ul_bank)
{
	p_smc->SMC_BANK = SMC_BANK_BANK(ul_bank);
}

/**
 * \brief Use the HOST nandflash controller to send a command.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_cmd Command to send.
 * \param ul_address_cycle Address cycle when command access is decoded.
 * \param ul_cycle0 Address at first cycle.
 */
void smc_nfc_send_command(Smc *p_smc, uint32_t ul_cmd,
		uint32_t ul_address_cycle, uint32_t ul_cycle0)
{
	volatile uint32_t *p_command_address;

	/* Wait until host controller is not busy. */
	while (((*((volatile uint32_t *)(BOARD_NF_DATA_ADDR + NFCADDR_CMD_NFCCMD)))
			& NFC_BUSY_FLAG) == NFC_BUSY_FLAG) {
	}
	/* Send the command plus the ADDR_CYCLE. */
	p_command_address = (volatile uint32_t *)(ul_cmd + BOARD_NF_DATA_ADDR);
	p_smc->SMC_ADDR = ul_cycle0;
	*p_command_address = ul_address_cycle;
	while (!((p_smc->SMC_SR & SMC_SR_CMDDONE) == SMC_SR_CMDDONE)) {
	}
}

/**
 * \brief Initialize ECC mode.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_type Type of correction, use pattern defined in the device header file.
 * \param ul_pagesize Page size of NAND Flash device, use pattern defined in
 * the device header file.
 */
void smc_ecc_init(Smc *p_smc, uint32_t ul_type, uint32_t ul_pagesize)
{
	/* Software Reset ECC. */
	p_smc->SMC_ECC_CTRL = SMC_ECC_CTRL_SWRST;
	p_smc->SMC_ECC_MD = ul_type | ul_pagesize;
}

/**
 * \brief Get ECC status by giving ecc number.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param ul_parity_number ECC parity number from 0 to 15.
 *
 * \return ECC status by giving ECC number.
 */
uint32_t smc_ecc_get_status(Smc *p_smc, uint32_t ul_parity_number)
{
	uint32_t status;

	if (ul_parity_number < 8) {
		status = p_smc->SMC_ECC_SR1;
	} else {
		status = p_smc->SMC_ECC_SR2;
		ul_parity_number -= 8;
	}

	return ((status >> (ul_parity_number * 4)) & ECC_STATUS_MASK);
}

/**
 * \brief Get all ECC parity registers value.
 *
 * \param p_smc Pointer to an SMC instance.
 * \param p_ecc Pointer to a parity buffer.
 */
void smc_ecc_get_value(Smc *p_smc, uint32_t *p_ecc)
{
	p_ecc[0] = p_smc->SMC_ECC_PR0;
	p_ecc[1] = p_smc->SMC_ECC_PR1;
	p_ecc[2] = p_smc->SMC_ECC_PR2;
	p_ecc[3] = p_smc->SMC_ECC_PR3;
	p_ecc[4] = p_smc->SMC_ECC_PR4;
	p_ecc[5] = p_smc->SMC_ECC_PR5;
	p_ecc[6] = p_smc->SMC_ECC_PR6;
	p_ecc[7] = p_smc->SMC_ECC_PR7;
	p_ecc[8] = p_smc->SMC_ECC_PR8;
	p_ecc[9] = p_smc->SMC_ECC_PR9;
	p_ecc[10] = p_smc->SMC_ECC_PR10;
	p_ecc[11] = p_smc->SMC_ECC_PR11;
	p_ecc[12] = p_smc->SMC_ECC_PR12;
	p_ecc[13] = p_smc->SMC_ECC_PR13;
	p_ecc[14] = p_smc->SMC_ECC_PR14;
	p_ecc[15] = p_smc->SMC_ECC_PR15;
}
#endif /* ((SAM3U) || (SAM3XA)) */

//@}

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond
