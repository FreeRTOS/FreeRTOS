/**
 * \file
 *
 * \brief FlashCALW driver for SAM4L.
 *
 * Copyright (c) 2012-2013 Atmel Corporation. All rights reserved.
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

#include "flashcalw.h"
#include "sysclk.h"

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

/**
 * \defgroup group_sam_drivers_flashcalw FLASHCALW - FLASH Controller Double-Word
 *
 * See \ref sam_flashcalw_quickstart.
 *
 * FLASHCALW interfaces a flash block with the 32-bit internal HSB bus.
 *
 * \{
 */

/*! \name Flash Properties
 */
//! @{

/*! \brief Gets the size of the whole flash array.
 *
 * \return The size of the whole flash array in Bytes.
 */
uint32_t flashcalw_get_flash_size(void)
{
	const uint16_t flash_size[(FLASHCALW_FPR_FSZ_Msk >>
	FLASHCALW_FPR_FSZ_Pos) + 1] = {
		4,
		8,
		16,
		32,
		48,
		64,
		96,
		128,
		192,
		256,
		384,
		512,
		768,
		1024,
		2048,
	};
	return ((uint32_t)flash_size[(HFLASHC->FLASHCALW_FPR &
	       FLASHCALW_FPR_FSZ_Msk) >> FLASHCALW_FPR_FSZ_Pos] << 10);
}

/*! \brief Gets the total number of pages in the flash array.
 *
 * \return The total number of pages in the flash array.
 */
uint32_t flashcalw_get_page_count(void)
{
	return flashcalw_get_flash_size() / FLASH_PAGE_SIZE;
}

/*! \brief Gets the number of pages in each flash region.
 *
 * \return The number of pages in each flash region.
 */
uint32_t flashcalw_get_page_count_per_region(void)
{
	return flashcalw_get_page_count() / FLASH_NB_OF_REGIONS;
}

/*! \brief Gets the region number of a page.
 *
 * \param page_number The page number:
 *   \arg \c 0 to <tt>(flashcalw_get_page_count() - 1)</tt>: a page number
 * within the flash array;
 *   \arg <tt>< 0</tt>: the current page number.
 *
 * \return The region number of the specified page.
 */
uint32_t flashcalw_get_page_region(int32_t page_number)
{
	return ((page_number >= 0) ? page_number
			: (int32_t)flashcalw_get_page_number())
			/ flashcalw_get_page_count_per_region();
}

/*! \brief Gets the number of the first page of a region.
 *
 * \param region The region number: \c 0 to <tt>(FLASHCALW_REGIONS - 1)</tt>.
 *
 * \return The number of the first page of the specified region.
 */
uint32_t flashcalw_get_region_first_page_number(uint32_t region)
{
	return region * flashcalw_get_page_count_per_region();
}


//! @}

/*! \name FLASHC Control
 */
//! @{

/*! \brief Gets the number of wait states of flash read accesses.
 *
 * \return The number of wait states of flash read accesses.
 */
uint32_t flashcalw_get_wait_state(void)
{
	return (HFLASHC->FLASHCALW_FCR & FLASHCALW_FCR_FWS ? 1 : 0);
}

/*! \brief Sets the number of wait states of flash read accesses.
 *
 * \param wait_state The number of wait states of flash read accesses: \c 0 to
 *                   \c 1.
 */
void flashcalw_set_wait_state(uint32_t wait_state)
{
	HFLASHC->FLASHCALW_FCR = (HFLASHC->FLASHCALW_FCR & ~FLASHCALW_FCR_FWS)
			| (wait_state ? FLASHCALW_FCR_FWS_1 :
			FLASHCALW_FCR_FWS_0);
}

#define FLASH_FWS_0_MAX_FREQ           CHIP_FREQ_FWS_0
#define FLASH_FWS_1_MAX_FREQ           CHIP_FREQ_FWS_1
#define FLASH_HSEN_FWS_0_MAX_FREQ      CHIP_FREQ_FLASH_HSEN_FWS_0
#define FLASH_HSEN_FWS_1_MAX_FREQ      CHIP_FREQ_FLASH_HSEN_FWS_1

/*! \brief Depending on the CPU frequency, on the Power Scaling mode and on the
 * Fast Wakeup mode, set the wait states of flash read accesses and enable or
 * disable the High speed read mode.
 *
 * \param cpu_f_hz The CPU frequency
 * \param ps_value Power Scaling mode value (0, 1)
 * \param is_fwu_enabled (boolean), Is fast wakeup mode enabled or not
 */
void flashcalw_set_flash_waitstate_and_readmode(uint32_t cpu_f_hz,
		uint32_t ps_value, bool is_fwu_enabled)
{
#ifdef CONFIG_FLASH_READ_MODE_HIGH_SPEED_ENABLE
	UNUSED(ps_value);
	UNUSED(is_fwu_enabled);
	
	if (cpu_f_hz > FLASH_FREQ_PS2_FWS_0_MAX_FREQ) { /* > 24MHz */
		/* Set a wait-state. */
		flashcalw_set_wait_state(1);
	} else {
		/* No wait-state. */
		flashcalw_set_wait_state(0);
	}

	/* Enable the high-speed read mode. */
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_HSEN, -1);
#else
	if (ps_value == 0) {
		if (cpu_f_hz > FLASH_FREQ_PS0_FWS_0_MAX_FREQ) {
			// > 18MHz
			if (cpu_f_hz <= FLASH_FREQ_PS0_FWS_1_MAX_FREQ) {
				// <= 36MHz
				/* Set a wait-state, disable the high-speed read
				 * mode. */
				flashcalw_set_wait_state(1);
				flashcalw_issue_command(
						FLASHCALW_FCMD_CMD_HSDIS, -1);
			} else {
				// > 36 MHz
				/* Set a wait-state, enable the high-speed read
				mode. */
				flashcalw_set_wait_state(1);
				flashcalw_issue_command(FLASHCALW_FCMD_CMD_HSEN,
						-1);
			}
		} else { // <= 18MHz
			if((is_fwu_enabled == true) &&
				(cpu_f_hz <= FLASH_FREQ_PS1_FWS_1_FWU_MAX_FREQ))
			{
				// <= 12MHz
				/* Set a wait-state, disable the high-speed read
				mode. */
				flashcalw_set_wait_state(1);
				flashcalw_issue_command(
						FLASHCALW_FCMD_CMD_HSDIS, -1);
			} else {
				/* No wait-state, disable the high-speed read
				mode */
				flashcalw_set_wait_state(0);
				flashcalw_issue_command(
					FLASHCALW_FCMD_CMD_HSDIS, -1);
			}
		}
	} else { /* ps_value == 1 */
		if (cpu_f_hz > FLASH_FREQ_PS0_FWS_0_MAX_FREQ) { /* > 8MHz */
			/* Set a wait-state. */
			flashcalw_set_wait_state(1);
		} else {
			/* No wait-state. */
			flashcalw_set_wait_state(0);
		}

		/* Disable the high-speed read mode. */
		flashcalw_issue_command(FLASHCALW_FCMD_CMD_HSDIS, -1);
	}
#endif
}

/*! \brief Tells whether the Flash Ready interrupt is enabled.
 *
 * \return Whether the Flash Ready interrupt is enabled.
 */
bool flashcalw_is_ready_int_enabled(void)
{
	return ((HFLASHC->FLASHCALW_FCR & FLASHCALW_FCR_FRDY) != 0);
}

/*! \brief Enables or disables the Flash Ready interrupt.
 *
 * \param enable Whether to enable the Flash Ready interrupt: \c true or
 *               \c false.
 */
void flashcalw_enable_ready_int(bool enable)
{
	HFLASHC->FLASHCALW_FCR
		&= ((enable &
			FLASHCALW_FCR_FRDY) | (~FLASHCALW_FCR_FRDY));
}

/*! \brief Tells whether the Lock Error interrupt is enabled.
 *
 * \return Whether the Lock Error interrupt is enabled.
 */
bool flashcalw_is_lock_error_int_enabled(void)
{
	return ((HFLASHC->FLASHCALW_FCR & FLASHCALW_FCR_LOCKE) != 0);
}

/*! \brief Enables or disables the Lock Error interrupt.
 *
 * \param enable Whether to enable the Lock Error interrupt: \c true or
 *               \c false.
 */
void flashcalw_enable_lock_error_int(bool enable)
{
	HFLASHC->FLASHCALW_FCR
		&= ((enable &
			FLASHCALW_FCR_LOCKE) | (~FLASHCALW_FCR_LOCKE));
}

/*! \brief Tells whether the Programming Error interrupt is enabled.
 *
 * \return Whether the Programming Error interrupt is enabled.
 */
bool flashcalw_is_prog_error_int_enabled(void)
{
	return ((HFLASHC->FLASHCALW_FCR & FLASHCALW_FCR_PROGE) != 0);
}

/*! \brief Enables or disables the Programming Error interrupt.
 *
 * \param enable Whether to enable the Programming Error interrupt: \c true or
 *               \c false.
 */
void flashcalw_enable_prog_error_int(bool enable)
{
	HFLASHC->FLASHCALW_FCR &= ((enable &
			FLASHCALW_FCR_PROGE) | (~FLASHCALW_FCR_PROGE));
}


//! @}

/*! \name FLASHCALW Status
 */
//! @{

/*! \brief Tells whether the FLASHCALW is ready to run a new command.
 *
 * \return Whether the FLASHCALW is ready to run a new command.
 */
bool flashcalw_is_ready(void)
{
	return ((HFLASHC->FLASHCALW_FSR & FLASHCALW_FSR_FRDY) != 0);
}

/*! \brief Waits actively until the FLASHCALW is ready to run a new command.
 *
 * This is the default function assigned to \ref flashcalw_wait_until_ready.
 */
void flashcalw_default_wait_until_ready(void)
{
	while (!flashcalw_is_ready()) {
	}
}

/**
 * \brief Pointer to the function used by the driver when it needs to wait until
 * the FLASHCALW is ready to run a new command.
 *
 * The default function is \ref flashcalw_default_wait_until_ready.
 * The user may change this pointer to use another implementation.
 */
void(*volatile flashcalw_wait_until_ready) (void)
	= flashcalw_default_wait_until_ready;

/**
 * \internal
 * \brief Gets the error status of the FLASHCALW.
 *
 * \return The error status of the FLASHCALW built up from
 *         \c FLASHCALW_FSR_LOCKE and \c FLASHCALW_FSR_PROGE.
 *
 * \warning This hardware error status is cleared by all functions reading the
 *          Flash Status Register (FSR). This function is therefore not part of
 *          the driver's API which instead presents \ref flashcalw_is_lock_error
 *          and \ref flashcalw_is_programming_error.
 */
static uint32_t flashcalw_get_error_status(void)
{
	return HFLASHC->FLASHCALW_FSR &
	       (FLASHCALW_FSR_LOCKE | FLASHCALW_FSR_PROGE);
}

/**
 * \internal
 * \brief Sticky error status of the FLASHCALW.
 *
 * This variable is updated by functions that issue FLASHCALW commands. It
 * contains the cumulated FLASHCALW error status of all the FLASHCALW commands
 * issued by a function.
 */
static uint32_t flashcalw_error_status = 0;

/*! \brief Tells whether a Lock Error has occurred during the last function
 *         called that issued one or more FLASHCALW commands.
 *
 * \return Whether a Lock Error has occurred during the last function called
 *         that issued one or more FLASHCALW commands.
 */
bool flashcalw_is_lock_error(void)
{
	return ((flashcalw_error_status & FLASHCALW_FSR_LOCKE) != 0);
}

/*! \brief Tells whether a Programming Error has occurred during the last
 *         function called that issued one or more FLASHCALW commands.
 *
 * \return Whether a Programming Error has occurred during the last function
 *         called that issued one or more FLASHCALW commands.
 */
bool flashcalw_is_programming_error(void)
{
	return ((flashcalw_error_status & FLASHCALW_FSR_PROGE) != 0);
}

//! @}

/*! \name FLASHCALW Command Control
 */
//! @{

/*! \brief Gets the last issued FLASHCALW command.
 *
 * \return The last issued FLASHCALW command.
 */
uint32_t flashcalw_get_command(void)
{
	return (HFLASHC->FLASHCALW_FCMD & FLASHCALW_FCMD_CMD_Msk);
}

/*! \brief Gets the current FLASHCALW page number.
 *
 * \return The current FLASHCALW page number.
 */
uint32_t flashcalw_get_page_number(void)
{
	return ((HFLASHC->FLASHCALW_FCMD & FLASHCALW_FCMD_PAGEN_Msk)
			>> FLASHCALW_FCMD_PAGEN_Pos);
}


/*! \brief Issues a FLASHCALW command.
 *
 * \param command The command: \c FLASHCALW_FCMD_CMD_x.
 * \param page_number The page number to apply the command to:
 *   \arg \c 0 to <tt>(flashcalw_get_page_count() - 1)</tt>: a page number
 *        within the flash array;
 *   \arg <tt>< 0</tt>: use this to apply the command to the current page number
 *        or if the command does not apply to any page number;
 *   \arg this argument may have other meanings according to the command. See
 *        the FLASHCALW chapter of the MCU datasheet.
 *
 * \warning A Lock Error is issued if the command violates the protection
 *          mechanism.
 *
 * \warning A Programming Error is issued if the command is invalid.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
void flashcalw_issue_command(uint32_t command, int page_number)
{
	uint32_t tempo;

	flashcalw_wait_until_ready();
	tempo = HFLASHC->FLASHCALW_FCMD;
	/* Clear the command bitfield. */
	tempo &= ~FLASHCALW_FCMD_CMD_Msk;
	if (page_number >= 0) {
		tempo = (FLASHCALW_FCMD_KEY_KEY
				| FLASHCALW_FCMD_PAGEN(page_number) | command);
	} else {
		tempo |= (FLASHCALW_FCMD_KEY_KEY | command);
	}

	HFLASHC->FLASHCALW_FCMD = tempo;
	flashcalw_error_status = flashcalw_get_error_status();
	flashcalw_wait_until_ready();
}


//! @}

/*! \name FLASHCALW Global Commands
 */
//! @{

/*! \brief Issues a No Operation command to the FLASHCALW.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
void flashcalw_no_operation(void)
{
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_NOP, -1);
}

/*! \brief Issues an Erase All command to the FLASHCALW.
 *
 * This command erases all bits in the flash array, the general-purpose fuse
 * bits and the Security bit. The User page is not erased.
 *
 * This command also ensures that all volatile memories, such as register file
 * and RAMs, are erased before the Security bit is erased, i.e. deactivated.
 *
 * \warning A Lock Error is issued if at least one region is locked or the
 *          bootloader protection is active.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note An erase operation can only set bits.
 */
void flashcalw_erase_all(void)
{
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_EA, -1);
}


//! @}

/*! \name FLASHCALW Protection Mechanisms
 */
//! @{

/*! \brief Tells whether the Security bit is active.
 *
 * \return Whether the Security bit is active.
 */
bool flashcalw_is_security_bit_active(void)
{
	return ((HFLASHC->FLASHCALW_FSR & FLASHCALW_FSR_SECURITY) != 0);
}

/*! \brief Activates the Security bit.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
void flashcalw_set_security_bit(void)
{
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_SSB, -1);
}

/*! \brief Tells whether the region of a page is locked.
 *
 * \param page_number The page number:
 *   \arg \c 0 to <tt>(flashcalw_get_page_count() - 1)</tt>: a page number
 *        within the flash array;
 *   \arg <tt>< 0</tt>: the current page number.
 *
 * \return Whether the region of the specified page is locked.
 */
bool flashcalw_is_page_region_locked(uint32_t page_number)
{
	return flashcalw_is_region_locked(flashcalw_get_page_region(page_number));
}

/*! \brief Tells whether a region is locked.
 *
 * \param region The region number: \c 0 to <tt>(FLASHCALW_REGIONS - 1)</tt>.
 *
 * \return Whether the specified region is locked.
 */
bool flashcalw_is_region_locked(uint32_t region)
{
	return ((HFLASHC->FLASHCALW_FSR & FLASHCALW_FSR_LOCK0
			<< (region & (FLASHCALW_REGIONS - 1))) != 0);
}

/*! \brief Locks or unlocks the region of a page.
 *
 * \param page_number The page number:
 *   \arg \c 0 to <tt>(flashcalw_get_page_count() - 1)</tt>: a page number
 *        within the flash array;
 *   \arg <tt>< 0</tt>: the current page number.
 * \param lock Whether to lock the region of the specified page: \c true or
 *             \c false.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
void flashcalw_lock_page_region(int page_number, bool lock)
{
	flashcalw_issue_command(
			(lock) ? FLASHCALW_FCMD_CMD_LP : FLASHCALW_FCMD_CMD_UP,
			page_number);
}

/*! \brief Locks or unlocks a region.
 *
 * \param region The region number: \c 0 to <tt>(FLASHCALW_REGIONS - 1)</tt>.
 * \param lock Whether to lock the specified region: \c true or \c false.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
void flashcalw_lock_region(uint32_t region, bool lock)
{
	flashcalw_lock_page_region(flashcalw_get_region_first_page_number(
			region), lock);
}

/*! \brief Locks or unlocks all regions.
 *
 * \param lock Whether to lock the regions: \c true or \c false.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
void flashcalw_lock_all_regions(bool lock)
{
	uint32_t error_status = 0;
	uint32_t region = FLASHCALW_REGIONS;

	while (region) {
		flashcalw_lock_region(--region, lock);
		error_status |= flashcalw_error_status;
	}
	flashcalw_error_status = error_status;
}


//! @}

/*! \name Access to General-Purpose Fuses
 */
//! @{


/*! \brief Reads a general-purpose fuse bit.
 *
 * \param gp_fuse_bit The general-purpose fuse bit: \c 0 to \c 63.
 *
 * \return The value of the specified general-purpose fuse bit.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
bool flashcalw_read_gp_fuse_bit(uint32_t gp_fuse_bit)
{
	return ((flashcalw_read_all_gp_fuses() & 1ULL << (gp_fuse_bit & 0x3F))
		!= 0);
}

/*! \brief Reads a general-purpose fuse bit-field.
 *
 * \param pos The bit-position of the general-purpose fuse bit-field: \c 0 to
 *            \c 63.
 * \param width The bit-width of the general-purpose fuse bit-field: \c 0 to
 *              \c 64.
 *
 * \return The value of the specified general-purpose fuse bit-field.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
uint64_t flashcalw_read_gp_fuse_bitfield(uint32_t pos, uint32_t width)
{
	return flashcalw_read_all_gp_fuses() >> (pos & 0x3F)
		& ((1ULL << Min(width, 64)) - 1);
}

/*! \brief Reads a general-purpose fuse byte.
 *
 * \param gp_fuse_byte The general-purpose fuse byte: \c 0 to \c 7.
 *
 * \return The value of the specified general-purpose fuse byte.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
uint8_t flashcalw_read_gp_fuse_byte(uint32_t gp_fuse_byte)
{
	return flashcalw_read_all_gp_fuses() >> ((gp_fuse_byte & 0x07) << 3);
}

/*! \brief Reads all general-purpose fuses.
 *
 * \return The value of all general-purpose fuses as a word.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
uint64_t flashcalw_read_all_gp_fuses(void)
{
	return HFLASHC->FLASHCALW_FGPFRLO |
		(uint64_t)HFLASHC->FLASHCALW_FGPFRHI << 32;
}

/*! \brief Erases a general-purpose fuse bit.
 *
 * \param gp_fuse_bit The general-purpose fuse bit: \c 0 to \c 63.
 * \param check Whether to check erase: \c true or \c false.
 *
 * \return Whether the erase succeeded or always \c true if erase check was not
 *         requested.
 *
 * \warning A Lock Error is issued if the Security bit is active and the command
 *  is applied to BOOTPROT.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note An erase operation can only set bits.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
bool flashcalw_erase_gp_fuse_bit(uint32_t gp_fuse_bit, bool check)
{
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_EGPB, gp_fuse_bit & 0x3F);
	return (check) ? flashcalw_read_gp_fuse_bit(gp_fuse_bit) : true;
}

/*! \brief Erases a general-purpose fuse bit-field.
 *
 * \param pos The bit-position of the general-purpose fuse bit-field: \c 0 to
 *            \c 63.
 * \param width The bit-width of the general-purpose fuse bit-field: \c 0 to
 *              \c 64.
 * \param check Whether to check erase: \c true or \c false.
 *
 * \return Whether the erase succeeded or always \c true if erase check was not
 *         requested.
 *
 * \warning A Lock Error is issued if the Security bit is active and the command
 *  is applied to BOOTPROT.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note An erase operation can only set bits.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
bool flashcalw_erase_gp_fuse_bitfield(uint32_t pos, uint32_t width, bool check)
{
	uint32_t error_status = 0;
	uint32_t gp_fuse_bit;

	pos &= 0x3F;
	width = Min(width, 64);

	for (gp_fuse_bit = pos; gp_fuse_bit < pos + width; gp_fuse_bit++) {
		flashcalw_erase_gp_fuse_bit(gp_fuse_bit, false);
		error_status |= flashcalw_error_status;
	}
	flashcalw_error_status = error_status;
	return (check) ? (flashcalw_read_gp_fuse_bitfield(pos, width)
		== (1ULL << width) - 1) : true;
}

/*! \brief Erases a general-purpose fuse byte.
 *
 * \param gp_fuse_byte The general-purpose fuse byte: \c 0 to \c 7.
 * \param check Whether to check erase: \c true or \c false.
 *
 * \return Whether the erase succeeded or always \c true if erase check was not
 *         requested.
 *
 * \warning A Lock Error is issued if the Security bit is active.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note An erase operation can only set bits.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
bool flashcalw_erase_gp_fuse_byte(uint32_t gp_fuse_byte, bool check)
{
	uint32_t error_status;
	uint32_t current_gp_fuse_byte;
	uint64_t value = flashcalw_read_all_gp_fuses();

	flashcalw_erase_all_gp_fuses(false);
	error_status = flashcalw_error_status;
	for (current_gp_fuse_byte = 0; current_gp_fuse_byte < 8;
			current_gp_fuse_byte++, value >>= 8) {
		if (current_gp_fuse_byte != gp_fuse_byte) {
			flashcalw_write_gp_fuse_byte(current_gp_fuse_byte,
					value);
			error_status |= flashcalw_error_status;
		}
	}
	flashcalw_error_status = error_status;
	return (check) ? (flashcalw_read_gp_fuse_byte(gp_fuse_byte) == 0xFF)
		: true;
}

/*! \brief Erases all general-purpose fuses.
 *
 * \param check Whether to check erase: \c true or \c false.
 *
 * \return Whether the erase succeeded or always \c true if erase check was not
 *         requested.
 *
 * \warning A Lock Error is issued if the Security bit is active.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note An erase operation can only set bits.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
bool flashcalw_erase_all_gp_fuses(bool check)
{
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_EAGPF, -1);
	return (check) ? (flashcalw_read_all_gp_fuses() ==
		0xFFFFFFFFFFFFFFFFULL) : true;
}

/*! \brief Writes a general-purpose fuse bit.
 *
 * \param gp_fuse_bit The general-purpose fuse bit: \c 0 to \c 63.
 * \param value The value of the specified general-purpose fuse bit.
 *
 * \warning A Lock Error is issued if the Security bit is active and the command
 * is applied to BOOTPROT.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note A write operation can only clear bits; in other words, an erase
 *  operation must first be done if some bits need to be set to 1.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
void flashcalw_write_gp_fuse_bit(uint32_t gp_fuse_bit, bool value)
{
	if (!value) {
		flashcalw_issue_command(FLASHCALW_FCMD_CMD_WGPB, gp_fuse_bit
				& 0x3F);
	}
}

/*! \brief Writes a general-purpose fuse bit-field.
 *
 * \param pos The bit-position of the general-purpose fuse bit-field: \c 0 to
 *            \c 63.
 * \param width The bit-width of the general-purpose fuse bit-field: \c 0 to
 *              \c 64.
 * \param value The value of the specified general-purpose fuse bit-field.
 *
 * \warning A Lock Error is issued if the Security bit is active and the command
 * is applied to BOOTPROT.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note A write operation can only clear bits; in other words, an erase
 *  operation must first be done if some bits need to be set to 1.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
void flashcalw_write_gp_fuse_bitfield(uint32_t pos, uint32_t width,
		uint64_t value)
{
	uint32_t error_status = 0;
	uint32_t gp_fuse_bit;

	pos &= 0x3F;
	width = Min(width, 64);

	for (gp_fuse_bit = pos; gp_fuse_bit < pos + width;
			gp_fuse_bit++, value >>= 1) {
		flashcalw_write_gp_fuse_bit(gp_fuse_bit, value & 0x01);
		error_status |= flashcalw_error_status;
	}
	flashcalw_error_status = error_status;
}

/*! \brief Writes a general-purpose fuse byte.
 *
 * \param gp_fuse_byte The general-purpose fuse byte: \c 0 to \c 7.
 * \param value The value of the specified general-purpose fuse byte.
 *
 * \warning A Lock Error is issued if the Security bit is active.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note A write operation can only clear bits; in other words, an erase
 *  operation must first be done if some bits need to be set to 1.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
void flashcalw_write_gp_fuse_byte(uint32_t gp_fuse_byte, uint8_t value)
{
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_PGPFB, (gp_fuse_byte & 0x07)
			| value << 3);
}

/*! \brief Writes all general-purpose fuses.
 *
 * \param value The value of all general-purpose fuses as a word.
 *
 * \warning A Lock Error is issued if the Security bit is active.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note A write operation can only clear bits; in other words, an erase
 *  operation must first be done if some bits need to be set to 1.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
void flashcalw_write_all_gp_fuses(uint64_t value)
{
	uint32_t error_status = 0;
	uint32_t gp_fuse_byte;

	for (gp_fuse_byte = 0; gp_fuse_byte < 8; gp_fuse_byte++, value >>= 8) {
		flashcalw_write_gp_fuse_byte(gp_fuse_byte, value);
		error_status |= flashcalw_error_status;
	}
	flashcalw_error_status = error_status;
}

/*! \brief Sets a general-purpose fuse bit with the appropriate erase and write
 *         operations.
 *
 * \param gp_fuse_bit The general-purpose fuse bit: \c 0 to \c 63.
 * \param value The value of the specified general-purpose fuse bit.
 *
 * \warning A Lock Error is issued if the Security bit is active and the command
 * is applied to BOOTPROT.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
void flashcalw_set_gp_fuse_bit(uint32_t gp_fuse_bit, bool value)
{
	if (value) {
		flashcalw_erase_gp_fuse_bit(gp_fuse_bit, false);
	} else {
		flashcalw_write_gp_fuse_bit(gp_fuse_bit, false);
	}
}

/*! \brief Sets a general-purpose fuse bit-field with the appropriate erase and
 *         write operations.
 *
 * \param pos The bit-position of the general-purpose fuse bit-field: \c 0 to
 *            \c 63.
 * \param width The bit-width of the general-purpose fuse bit-field: \c 0 to
 *              \c 64.
 * \param value The value of the specified general-purpose fuse bit-field.
 *
 * \warning A Lock Error is issued if the Security bit is active and the command
 * is applied to BOOTPROT.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
void flashcalw_set_gp_fuse_bitfield(uint32_t pos, uint32_t width,
		uint64_t value)
{
	uint32_t error_status = 0;
	uint32_t gp_fuse_bit;

	pos &= 0x3F;
	width = Min(width, 64);

	for (gp_fuse_bit = pos; gp_fuse_bit < pos + width;
			gp_fuse_bit++, value >>= 1) {
		flashcalw_set_gp_fuse_bit(gp_fuse_bit, value & 0x01);
		error_status |= flashcalw_error_status;
	}
	flashcalw_error_status = error_status;
}

/*! \brief Sets a general-purpose fuse byte with the appropriate erase and write
 *         operations.
 *
 * \param gp_fuse_byte The general-purpose fuse byte: \c 0 to \c 7.
 * \param value The value of the specified general-purpose fuse byte.
 *
 * \warning A Lock Error is issued if the Security bit is active.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
void flashcalw_set_gp_fuse_byte(uint32_t gp_fuse_byte, uint8_t value)
{
	uint32_t error_status;

	switch (value) {
	case 0xFF:
		flashcalw_erase_gp_fuse_byte(gp_fuse_byte, false);
		break;

	case 0x00:
		flashcalw_write_gp_fuse_byte(gp_fuse_byte, 0x00);
		break;

	default:
		flashcalw_erase_gp_fuse_byte(gp_fuse_byte, false);
		error_status = flashcalw_error_status;
		flashcalw_write_gp_fuse_byte(gp_fuse_byte, value);
		flashcalw_error_status |= error_status;
		break;
	}
}

/*! \brief Sets all general-purpose fuses with the appropriate erase and write
 *         operations.
 *
 * \param value The value of all general-purpose fuses as a word.
 *
 * \warning A Lock Error is issued if the Security bit is active.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note The actual number of general-purpose fuse bits implemented by hardware
 *       is given by \c FLASH_GPF_NUM. The other bits among the 64 are
 *       fixed at 1 by hardware.
 */
void flashcalw_set_all_gp_fuses(uint64_t value)
{
	uint32_t error_status;

	switch (value) {
	case 0xFFFFFFFFFFFFFFFFULL:
		flashcalw_erase_all_gp_fuses(false);
		break;

	case 0x0000000000000000ULL:
		flashcalw_write_all_gp_fuses(0x0000000000000000ULL);
		break;

	default:
		flashcalw_erase_all_gp_fuses(false);
		error_status = flashcalw_error_status;
		flashcalw_write_all_gp_fuses(value);
		flashcalw_error_status |= error_status;
		break;
	}
}


//! @}

/*! \name Access to Flash Pages
 */
//! @{


/*! \brief Clears the page buffer.
 *
 * This command resets all bits in the page buffer to one. Write accesses to the
 * page buffer can only change page buffer bits from one to zero.
 *
 * \warning The page buffer is not automatically reset after a page write.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
void flashcalw_clear_page_buffer(void)
{
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_CPB, -1);
}

/*! \brief Tells whether the page to which the last Quick Page Read or Quick
 *         Page Read User Page command was applied was erased.
 *
 * \return Whether the page to which the last Quick Page Read or Quick Page Read
 *         User Page command was applied was erased.
 */
bool flashcalw_is_page_erased(void)
{
	return ((HFLASHC->FLASHCALW_FSR & FLASHCALW_FSR_QPRR) != 0);
}

/*! \brief Applies the Quick Page Read command to a page.
 *
 * \param page_number The page number:
 *   \arg \c 0 to <tt>(flashcalw_get_page_count() - 1)</tt>: a page number
 *        within the flash array;
 *   \arg <tt>< 0</tt>: the current page number.
 *
 * \return Whether the specified page is erased.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
bool flashcalw_quick_page_read(int page_number)
{
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_QPR, page_number);
	return flashcalw_is_page_erased();
}

/*! \brief Erases a page.
 *
 * \param page_number The page number:
 *   \arg \c 0 to <tt>(flashcalw_get_page_count() - 1)</tt>: a page number
 *        within the flash array;
 *   \arg <tt>< 0</tt>: the current page number.
 * \param check Whether to check erase: \c true or \c false.
 *
 * \return Whether the erase succeeded or always \c true if erase check was not
 *         requested.
 *
 * \warning A Lock Error is issued if the command is applied to a page belonging
 *          to a locked region or to the bootloader protected area.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note An erase operation can only set bits.
 */
bool flashcalw_erase_page(int page_number, bool check)
{
	bool page_erased = true;

	flashcalw_issue_command(FLASHCALW_FCMD_CMD_EP, page_number);

	if (check) {
		uint32_t error_status = flashcalw_error_status;
		page_erased = flashcalw_quick_page_read(-1);
		flashcalw_error_status |= error_status;
	}

	return page_erased;
}

/*! \brief Erases all pages within the flash array.
 *
 * \param check Whether to check erase: \c true or \c false.
 *
 * \return Whether the erase succeeded or always \c true if erase check was not
 *         requested.
 *
 * \warning A Lock Error is issued if at least one region is locked or the
 *          bootloader protection is active.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note An erase operation can only set bits.
 */
bool flashcalw_erase_all_pages(bool check)
{
	bool all_pages_erased = true;
	uint32_t error_status = 0;
	uint32_t page_number = flashcalw_get_page_count();

	while (page_number) {
		all_pages_erased &= flashcalw_erase_page(--page_number, check);
		error_status |= flashcalw_error_status;
	}

	flashcalw_error_status = error_status;
	return all_pages_erased;
}

/*! \brief Writes a page from the page buffer.
 *
 * \param page_number The page number:
 *   \arg \c 0 to <tt>(flashcalw_get_page_count() - 1)</tt>: a page number
 *        within the flash array;
 *   \arg <tt>< 0</tt>: the current page number.
 *
 * \warning A Lock Error is issued if the command is applied to a page belonging
 *          to a locked region or to the bootloader protected area.
 *
 * \warning The page buffer is not automatically reset after a page write.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note A write operation can only clear bits; in other words, an erase
 *  operation must first be done if some bits need to be set to 1.
 */
void flashcalw_write_page(int page_number)
{
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_WP, page_number);
}

/*! \brief Issues a Quick Page Read User Page command to the FLASHCALW.
 *
 * \return Whether the User page is erased.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
bool flashcalw_quick_user_page_read(void)
{
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_QPRUP, -1);
	return flashcalw_is_page_erased();
}

/*! \brief Erases the User page.
 *
 * \param check Whether to check erase: \c true or \c false.
 *
 * \return Whether the erase succeeded or always \c true if erase check was not
 *         requested.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note An erase operation can only set bits.
 */
bool flashcalw_erase_user_page(bool check)
{
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_EUP, -1);
	return (check) ? flashcalw_quick_user_page_read() : true;
}

/*! \brief Writes the User page from the page buffer.
 *
 * \warning The page buffer is not automatically reset after a page write.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 *
 * \note A write operation can only clear bits; in other words, an erase
 *  operation must first be done if some bits need to be set to 1.
 */
void flashcalw_write_user_page(void)
{
	flashcalw_issue_command(FLASHCALW_FCMD_CMD_WUP, -1);
}

/*! \brief Copies \a nbytes bytes to the flash destination pointed to by \a dst
 *         from the repeated \a src source byte.
 *
 * All pointer and size alignments are supported.
 *
 * \param dst Pointer to flash destination.
 * \param src Source byte.
 * \param nbytes Number of bytes to set.
 * \param erase Whether to erase before writing: \c true or \c false.
 *
 * \return The value of \a dst.
 *
 * \warning This function may be called with \a erase set to \c false only if
 *          the destination consists only of erased words, i.e. this function
 *          cannot be used to write only one bit of a previously written word.
 *          E.g., if \c 0x00000001 then \c 0xFFFFFFFE are written to a word, the
 *          resulting value in flash may be different from \c 0x00000000.
 *
 * \warning A Lock Error is issued if the command is applied to pages belonging
 *          to a locked region or to the bootloader protected area.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
volatile void *flashcalw_memset8(volatile void *dst, uint8_t src, size_t nbytes,
		bool erase)
{
	return flashcalw_memset16(dst, src | (uint16_t)src << 8, nbytes, erase);
}

/*! \brief Copies \a nbytes bytes to the flash destination pointed to by \a dst
 *         from the repeated \a src big-endian source half-word.
 *
 * All pointer and size alignments are supported.
 *
 * \param dst Pointer to flash destination.
 * \param src Source half-word.
 * \param nbytes Number of bytes to set.
 * \param erase Whether to erase before writing: \c true or \c false.
 *
 * \return The value of \a dst.
 *
 * \warning This function may be called with \a erase set to \c false only if
 *          the destination consists only of erased words, i.e. this function
 *          can not be used to write only one bit of a previously written word.
 *          E.g., if \c 0x00000001 then \c 0xFFFFFFFE are written to a word, the
 *          resulting value in flash may be different from \c 0x00000000.
 *
 * \warning A Lock Error is issued if the command is applied to pages belonging
 *          to a locked region or to the bootloader protected area.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
volatile void *flashcalw_memset16(volatile void *dst, uint16_t src,
		size_t nbytes, bool erase)
{
	return flashcalw_memset32(dst, src | (uint32_t)src << 16, nbytes,
			erase);
}

/*! \brief Copies \a nbytes bytes to the flash destination pointed to by \a dst
 *         from the repeated \a src big-endian source word.
 *
 * All pointer and size alignments are supported.
 *
 * \param dst Pointer to flash destination.
 * \param src Source word.
 * \param nbytes Number of bytes to set.
 * \param erase Whether to erase before writing: \c true or \c false.
 *
 * \return The value of \a dst.
 *
 * \warning This function may be called with \a erase set to \c false only if
 *          the destination consists only of erased words, i.e. this function
 *          can not be used to write only one bit of a previously written word.
 *          E.g., if \c 0x00000001 then \c 0xFFFFFFFE are written to a word, the
 *          resulting value in flash may be different from \c 0x00000000.
 *
 * \warning A Lock Error is issued if the command is applied to pages belonging
 *          to a locked region or to the bootloader protected area.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
volatile void *flashcalw_memset32(volatile void *dst, uint32_t src,
		size_t nbytes, bool erase)
{
	return flashcalw_memset64(dst, src | (uint64_t)src << 32, nbytes,
			erase);
}

/*! \brief Copies \a nbytes bytes to the flash destination pointed to by \a dst
 *         from the repeated \a src big-endian source double-word.
 *
 * All pointer and size alignments are supported.
 *
 * \param dst Pointer to flash destination.
 * \param src Source double-word.
 * \param nbytes Number of bytes to set.
 * \param erase Whether to erase before writing: \c true or \c false.
 *
 * \return The value of \a dst.
 *
 * \warning This function may be called with \a erase set to \c false only if
 *          the destination consists only of erased words, i.e. this function
 *          can not be used to write only one bit of a previously written word.
 *          E.g., if \c 0x00000001 then \c 0xFFFFFFFE are written to a word, the
 *          resulting value in flash may be different from \c 0x00000000.
 *
 * \warning A Lock Error is issued if the command is applied to pages belonging
 *          to a locked region or to the bootloader protected area.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
volatile void *flashcalw_memset64(volatile void *dst, uint64_t src,
		size_t nbytes, bool erase)
{
	/* Use aggregated pointers to have several alignments available for a
	 * same address. */
	UnionCVPtr flash_array_end;
	UnionVPtr dest;
	Union64 source = {0};
	StructCVPtr dest_end;
	UnionCVPtr flash_page_source_end;
	bool incomplete_flash_page_end;
	Union64 flash_dword;
	UnionVPtr tmp;
	uint32_t error_status = 0;
	uint32_t i;

	/* Reformat arguments. */
	flash_array_end.u8ptr = ((uint8_t *)FLASH_ADDR)
			+ flashcalw_get_flash_size();
	dest.u8ptr = dst;
	for (i = (Get_align((uint32_t)dest.u8ptr, sizeof(uint64_t)) - 1)
			& (sizeof(uint64_t) - 1); src;
			i = (i - 1) & (sizeof(uint64_t) - 1)) {
		source.u8[i] = src;
		src >>= 8;
	}
	dest_end.u8ptr = dest.u8ptr + nbytes;

	/* If destination is outside flash, go to next flash page if any. */
	if (dest.u8ptr < (uint8_t *)FLASH_ADDR) {
		dest.u8ptr = (uint8_t *)FLASH_ADDR;
	} else if (flash_array_end.u8ptr <= dest.u8ptr &&
			dest.u8ptr < (uint8_t *)FLASH_USER_PAGE_ADDR) {
		dest.u8ptr = (uint8_t *)FLASH_USER_PAGE_ADDR;
	}

	/* If end of destination is outside flash, move it to the end of the
	 * previous flash page if any. */
	if (dest_end.u8ptr >
			(((uint8_t *)FLASH_USER_PAGE_ADDR) + FLASH_PAGE_SIZE)) {
		dest_end.u8ptr = (uint8_t *)FLASH_USER_PAGE_ADDR
				+ FLASH_PAGE_SIZE;
	} else if ((uint8_t *)FLASH_USER_PAGE_ADDR >= dest_end.u8ptr &&
			dest_end.u8ptr > flash_array_end.u8ptr) {
		dest_end.u8ptr = flash_array_end.u8ptr;
	}

	/* Align each end of destination pointer with its natural boundary. */
	dest_end.u16ptr = (uint16_t *)Align_down((uint32_t)dest_end.u8ptr,
			sizeof(uint16_t));
	dest_end.u32ptr = (uint32_t *)Align_down((uint32_t)dest_end.u16ptr,
			sizeof(uint32_t));
	dest_end.u64ptr = (uint64_t *)Align_down((uint32_t)dest_end.u32ptr,
			sizeof(uint64_t));

	/* While end of destination is not reached... */
	while (dest.u8ptr < dest_end.u8ptr) {
		/* Clear the page buffer in order to prepare data for a flash
		 * page write. */
		flashcalw_clear_page_buffer();
		error_status |= flashcalw_error_status;

		/* Determine where the source data will end in the current flash
		 * page. */
		flash_page_source_end.u64ptr
			= (uint64_t *)Min((uint32_t)dest_end.u64ptr,
				Align_down((uint32_t)dest.u8ptr,
				(uint32_t)FLASH_PAGE_SIZE) + FLASH_PAGE_SIZE);

		/* Determine if the current destination page has an incomplete
		 * end. */
		incomplete_flash_page_end
			= (Align_down((uint32_t)dest.u8ptr,
				(uint32_t)FLASH_PAGE_SIZE)
				>= Align_down((uint32_t)dest_end.u8ptr,
				(uint32_t)FLASH_PAGE_SIZE));

		/* Use a flash double-word buffer to manage unaligned accesses. */
		flash_dword.u64 = source.u64;

		/* If destination does not point to the beginning of the current
		 * flash page... */
		if (!Test_align((uint32_t)dest.u8ptr, FLASH_PAGE_SIZE)) {
			/* Fill the beginning of the page buffer with the
			 * current flash page data.
			 * This is required by the hardware, even if page erase
			 * is not requested, in order to be able to write
			 * successfully to erased parts of flash pages that have
			 * already been written to. */
			for (tmp.u8ptr = (uint8_t *)Align_down((uint32_t)dest.u8ptr,
							(uint32_t)FLASH_PAGE_SIZE);
					tmp.u64ptr < (uint64_t *)Align_down(
					(uint32_t)dest.u8ptr,
					sizeof(uint64_t));
					tmp.u64ptr++) {
				*tmp.u32ptr = *tmp.u32ptr;
				*(tmp.u32ptr + 1) = *(tmp.u32ptr + 1);
			}

			/* If destination is not 64-bit aligned... */
			if (!Test_align((uint32_t)dest.u8ptr,
					sizeof(uint64_t))) {
				/* Fill the beginning of the flash double-word
				 * buffer with the current flash page data.
				 * This is required by the hardware, even if
				 * page erase is not requested, in order to be
				 * able to write successfully to erased parts
				 * of flash pages that have already been written
				 * to. */
				for (i = 0; i < Get_align((uint32_t)dest.u8ptr,
						sizeof(uint64_t)); i++) {
					flash_dword.u8[i] = *tmp.u8ptr++;
				}

				/* Align the destination pointer with its 64-bit
				 * boundary. */
				dest.u64ptr = (uint64_t *)Align_down(
						(uint32_t)dest.u8ptr,
						sizeof(uint64_t));

				/* If the current destination double-word is not
				 * the last one... */
				if (dest.u64ptr < dest_end.u64ptr) {
					/* Write the flash double-word buffer to
					the page buffer and reinitialize it. */
					*dest.u32ptr++ = flash_dword.u32[0];
					*dest.u32ptr++ = flash_dword.u32[1];
					flash_dword.u64 = source.u64;
				}
			}
		}

		/* Write the source data to the page buffer with 64-bit
		 * alignment. */
		for (i = flash_page_source_end.u64ptr - dest.u64ptr; i; i--) {
			*dest.u32ptr++ = source.u32[0];
			*dest.u32ptr++ = source.u32[1];
		}

		/* If the current destination page has an incomplete end... */
		if (incomplete_flash_page_end) {
			/* This is required by the hardware, even if page erase
			 * is not requested, in order to be able to write
			 * successfully to erased parts of flash pages that have
			 * already been written to. */
			{
				tmp.u8ptr = (volatile uint8_t *)dest_end.u8ptr;

				/* If end of destination is not 64-bit aligned. */
				if (!Test_align((uint32_t)dest_end.u8ptr,
						sizeof(uint64_t))) {
					/* Fill the end of the flash double-word
					 * buffer with the current flash page
					 * data. */
					for (i = Get_align(
							(uint32_t)dest_end.u8ptr,
							sizeof(uint64_t));
							i < sizeof(uint64_t);
							i++) {
						flash_dword.u8[i] = *tmp.u8ptr++;
					}

					/* Write the flash double-word buffer to
					 * the page buffer. */
					*dest.u32ptr++ = flash_dword.u32[0];
					*dest.u32ptr++ = flash_dword.u32[1];
				}

				/* Fill the end of the page buffer with the
				current flash page data. */
				for (; !Test_align((uint32_t)tmp.u64ptr,
						FLASH_PAGE_SIZE); tmp.u64ptr++){
					*tmp.u32ptr = *tmp.u32ptr;
					*(tmp.u32ptr + 1) = *(tmp.u32ptr + 1);
				}
			}
		}

		/* If the current flash page is in the flash array... */
		if (dest.u8ptr <= (uint8_t *)FLASH_USER_PAGE_ADDR) {
			/* Erase the current page if requested and write it from
			 * the page buffer. */
			if (erase) {
				flashcalw_erase_page(-1, false);
				error_status |= flashcalw_error_status;
			}

			flashcalw_write_page(-1);
			error_status |= flashcalw_error_status;

			/* If the end of the flash array is reached, go to the
			 * User page. */
			if (dest.u8ptr >= flash_array_end.u8ptr) {
				dest.u8ptr = (uint8_t *)FLASH_USER_PAGE_ADDR;
			}
		} else {
			/* Erase the User page if requested and write it from
			 * the page buffer. */
			if (erase) {
				flashcalw_erase_user_page(false);
				error_status |= flashcalw_error_status;
			}

			flashcalw_write_user_page();
			error_status |= flashcalw_error_status;
		}
	}

	/* Update the FLASHC error status. */
	flashcalw_error_status = error_status;

	/* Return the initial destination pointer as the standard memset
	 * function does. */
	return dst;
}

/*! \brief Copies \a nbytes bytes to the flash destination pointed to by \a dst
 *         from the source pointed to by \a src.
 *
 * The destination areas that are not within the flash
 * array or the User page are caught by an Assert() operation.
 *
 * All pointer and size alignments are supported.
 *
 * \param dst Pointer to flash destination.
 * \param src Pointer to source data.
 * \param nbytes Number of bytes to copy.
 * \param erase Whether to erase before writing: \c true or \c false.
 *
 * \return The value of \a dst.
 *
 * \warning If copying takes place between areas that overlap, the behavior is
 *          undefined.
 *
 * \warning This function may be called with \a erase set to \c false only if
 *          the destination consists only of erased words, i.e. this function
 *          can not be used to write only one bit of a previously written word.
 *          E.g., if \c 0x00000001 then \c 0xFFFFFFFE are written to a word, the
 *          resulting value in flash may be different from \c 0x00000000.
 *
 * \warning A Lock Error is issued if the command is applied to pages belonging
 *          to a locked region or to the bootloader protected area.
 *
 * \note The FLASHCALW error status returned by \ref flashcalw_is_lock_error and
 *       \ref flashcalw_is_programming_error is updated.
 */
volatile void *flashcalw_memcpy(volatile void *dst, const void *src,
		size_t nbytes, bool erase)
{
	uint16_t page_pos;
	Union64 flash_dword;
	uint8_t i;
	bool b_user_page;
	uint32_t error_status = 0;
	volatile uint8_t *flash_add;
	volatile uint8_t *dest_add = (uint8_t *)dst;
	const uint8_t *src_buf = (const uint8_t *)src;

	/* Copy area must be in flash array or flash user page */
	Assert((((uint8_t *)dst >= (uint8_t *)FLASH_ADDR) &&
			(((uint8_t *)dst + nbytes)
			<= (((uint8_t *)FLASH_ADDR)
			+ flashcalw_get_flash_size()))) ||
			(((uint8_t *)dst >= (uint8_t *)FLASH_USER_PAGE_ADDR) &&
			(((uint8_t *)dst + nbytes)
			<= (((uint8_t *)FLASH_USER_PAGE_ADDR)
			+ FLASH_PAGE_SIZE))));

	b_user_page = (volatile uint8_t *)dst
			>= (uint8_t *)FLASH_USER_PAGE_ADDR;

	flash_add = (uint8_t *)((uint32_t)dest_add
			- ((uint32_t)dest_add % FLASH_PAGE_SIZE));

	while (nbytes) {
		/* Clear the page buffer in order to prepare data for a flash
		 * page write. */
		flashcalw_clear_page_buffer();
		error_status |= flashcalw_error_status;

		/* Loop in the page */
		for (page_pos = 0; page_pos < FLASH_PAGE_SIZE;
				page_pos += sizeof(uint64_t)) {
			/* Read the flash double-word buffer */
			flash_dword.u64 = *(volatile uint64_t *)flash_add;

			/* Update double-word if necessary */
			for (i = 0; i < sizeof(uint64_t); i++) {
				if (nbytes && (flash_add == dest_add)) {
					/* Update page with data source */
					flash_dword.u8[i] = *src_buf++;
					dest_add++;
					nbytes--;
				}

				flash_add++;
			}

			/* Write the flash double-word buffer to the page buffer */
			*(volatile uint64_t *)((uint32_t)flash_add
			- sizeof(uint64_t)) = flash_dword.u64;
		}

		/* Erase the current page if requested and write it from the
		 * page buffer. */
		if (erase) {
			(b_user_page) ? flashcalw_erase_user_page(false)
			: flashcalw_erase_page(-1, false);
			error_status |= flashcalw_error_status;
		}

		/* Write the page */
		(b_user_page) ? flashcalw_write_user_page()
		: flashcalw_write_page(-1);
		error_status |= flashcalw_error_status;
	}
	/* Update the FLASHC error status. */
	flashcalw_error_status = error_status;

	/* Return the initial destination pointer as the standard memcpy
	 * function does. */
	return dst;
}

/** @} */


/*! \name PicoCache interfaces
 */
//! @{

/**
 * \brief Enable PicoCache.
 */
void flashcalw_picocache_enable(void)
{
	sysclk_enable_peripheral_clock(HCACHE);
	HCACHE->HCACHE_CTRL = HCACHE_CTRL_CEN_YES;

	while (!(flashcalw_picocache_get_status() & HCACHE_SR_CSTS_EN)) {
	}
}

/**
 * \brief Disable PicoCache.
 */
void flashcalw_picocache_disable(void)
{
	HCACHE->HCACHE_MAINT0 = HCACHE_MAINT0_INVALL_YES;
	HCACHE->HCACHE_CTRL = HCACHE_CTRL_CEN_NO;

	while (flashcalw_picocache_get_status() != HCACHE_SR_CSTS_DIS) {
	}

	sysclk_disable_peripheral_clock(HCACHE);
}

/**
 * \brief Get PicoCache status.
 *
 * \return 1 If PicoCahe is enabled, else disabled.
 */
uint32_t flashcalw_picocache_get_status(void)
{
	return HCACHE->HCACHE_SR;
}

/**
 * \brief Invalid all PicoCache lines.
 */
void flashcalw_picocache_invalid_all(void)
{
	HCACHE->HCACHE_MAINT0 = HCACHE_MAINT0_INVALL_YES;
}

/**
 * \brief Invalid specific cache line.
 *
 * \param index Lines to be invalid.
 */
void flashcalw_picocache_invalid_line(uint32_t index)
{
	/* Disable the cache controller */
	HCACHE->HCACHE_CTRL = HCACHE_CTRL_CEN_NO;

	/* Wait for disable successfully */
	while (flashcalw_picocache_get_status() != HCACHE_SR_CSTS_DIS) {
	}

	/* Invalid the line */
	HCACHE->HCACHE_MAINT1 = index;

	/* Enable the cache again */
	HCACHE->HCACHE_CTRL = HCACHE_CTRL_CEN_YES;
}

/**
 * \brief Set PicoCache monitor mode.
 *
 * \param mode PicoCache mode, 0 for cycle, 1 for instruction hit and 2 for data
 *hit.
 */
void flashcalw_picocache_set_monitor_mode(uint32_t mode)
{
	HCACHE->HCACHE_MCFG = mode;
}

/**
 * \brief Enable PicoCache monitor.
 */
void flashcalw_picocache_enable_monitor(void)
{
	HCACHE->HCACHE_MEN = HCACHE_MEN_MENABLE_EN;
}

/**
 * \brief Disable PicoCache monitor.
 */
void flashcalw_picocache_disable_monitor(void)
{
	HCACHE->HCACHE_MEN = HCACHE_MEN_MENABLE_DIS;
}

/**
 * \brief Reset PicoCache monitor.
 */
void flashcalw_picocache_reset_monitor( void )
{
	HCACHE->HCACHE_MCTRL = HCACHE_MCTRL_SWRST_YES;
}

/**
 * \brief Get PicoCache monitor count number.
 *
 * \return Monitor counter number.
 */
uint32_t flashcalw_picocache_get_monitor_cnt( void )
{
	return HCACHE->HCACHE_MSR;
}

/**
 * \brief Get PicoCache version.
 *
 * \return PicoCache version.
 */
uint32_t flashcalw_picocache_get_version( void )
{
	return HCACHE->HCACHE_VERSION;
}

/** @} */

/**
 * \}
 */

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond
