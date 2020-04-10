/**
 * \file
 *
 * \brief NVMCTRL Basic driver implementation.
 *
 (c) 2018 Microchip Technology Inc. and its subsidiaries.

    Subject to your compliance with these terms,you may use this software and
    any derivatives exclusively with Microchip products.It is your responsibility
    to comply with third party license terms applicable to your use of third party
    software (including open source software) that may accompany Microchip software.

    THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS". NO WARRANTIES, WHETHER
    EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE, INCLUDING ANY IMPLIED
    WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY, AND FITNESS FOR A
    PARTICULAR PURPOSE.

    IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
    INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
    WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
    BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE. TO THE
    FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL CLAIMS IN
    ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF FEES, IF ANY,
    THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
 *
 */

/**
 * \defgroup doc_driver_nvmctrl_basic NVMCTRL Basic Driver
 * \ingroup doc_driver_nvmctrl
 *
 * \section doc_driver_nvmctrl_rev Revision History
 * - v0.0.0.1 Initial Commit
 *
 *@{
 */

#include "nvmctrl_basic.h"

/* clang-format off */
#if defined(__ICCAVR__)

#define _GET_LOCK_BITS() __AddrToZByteToSPMCR_LPM( (void __flash *) 0x0001, 0x09 )
#define _GET_LOW_FUSES() __AddrToZByteToSPMCR_LPM( (void __flash *) 0x0000, 0x09 )
#define _GET_HIGH_FUSES() __AddrToZByteToSPMCR_LPM( (void __flash *) 0x0003, 0x09 )
#define _GET_EXTENDED_FUSES() __AddrToZByteToSPMCR_LPM( (void __flash *) 0x0002, 0x09 )
#define _SET_LOCK_BITS(data) __DataToR0ByteToSPMCR_SPM( data, 0x09 )
#define _ENABLE_RWW_SECTION() __DataToR0ByteToSPMCR_SPM( 0x00, 0x11 )

#define _WAIT_FOR_SPM() while( SPMCSR & (1<<SPMEN) );

#ifndef CONFIG_MEMORY_MODEL_LARGE
  #define _LOAD_PROGRAM_MEMORY(addr) __load_program_memory( (const unsigned char __flash *) (addr) )
  #define _FILL_TEMP_WORD(addr,data) __AddrToZWordToR1R0ByteToSPMCR_SPM( (void __flash *) (addr), data, 0x01 )
  #define _PAGE_ERASE(addr) __AddrToZByteToSPMCR_SPM( (void __flash *) (addr), 0x03 )
  #define _PAGE_WRITE(addr) __AddrToZByteToSPMCR_SPM( (void __flash *) (addr), 0x05 )
#else
  #define _LOAD_PROGRAM_MEMORY(addr) __extended_load_program_memory( (const unsigned char __farflash *) (addr) )
  #define _FILL_TEMP_WORD(addr,data) __AddrToZ24WordToR1R0ByteToSPMCR_SPM( (void __farflash *) (addr), data, 0x01 )
  #define _PAGE_ERASE(addr) __AddrToZ24ByteToSPMCR_SPM( (void __farflash *) (addr), 0x03 )
  #define _PAGE_WRITE(addr) __AddrToZ24ByteToSPMCR_SPM( (void __farflash *) (addr), 0x05 )
#endif

#endif

#if defined(__GNUC__)

#define	_FLASH_WRITE_PAGE          boot_page_write
#define	_FLASH_ERASE_PAGE          boot_page_erase
#define _FLASH_ENABLE_RWW_SECTION  boot_rww_enable
#define _FLASH_WRITE_PAGEBUF       boot_page_fill
#define _FLASH_READ                pgm_read_byte_near
#define _FLASH_WAIT_SPM()          boot_spm_busy_wait()

#elif defined(__ICCAVR__)

#define	_FLASH_WRITE_PAGE          _PAGE_WRITE
#define	_FLASH_ERASE_PAGE          _PAGE_ERASE
#define _FLASH_ENABLE_RWW_SECTION  _ENABLE_RWW_SECTION
#define _FLASH_WRITE_PAGEBUF       _FILL_TEMP_WORD
#define _FLASH_READ                _LOAD_PROGRAM_MEMORY
#define _FLASH_WAIT_SPM()          _WAIT_FOR_SPM()

#else
#error Unsupported compiler.
#endif
/* clang-format on */

#define EEPROM_WRITE_ENABLE EEPE
#define EEPROM_Master_WRITE_ENABLE EEMPE

/**
 * \brief Initialize nvmctrl interface
 * \return Return value 0 if success
 */
int8_t FLASH_0_init()
{

	// EECR = 0 << EERE /* EEPROM Read Enable: disabled */
	//		 | 0 << EEPE /* EEPROM Write Enable: disabled */
	//		 | 0 << EEMPE /* EEPROM Master Write Enable: disabled */
	//		 | 0 << EERIE /* EEPROM Ready Interrupt Enable: disabled */
	//		 | 0 << EEPM0 /* EEPROM Programming mode 0: disabled */
	//		 | 0 << EEPM1; /* EEPROM Programming mode 1: disabled */

	// SPMCSR = 0 << SPMEN /* SPM Enable: disabled */
	//		 | 0 << PGERS /* Page Erase: disabled */
	//		 | 0 << PGWRT /* Page Write: disabled */
	//		 | 0 << BLBSET /* Boot Lock Bit Set: disabled */
	//		 | 0 << RWWSRE /* Read-While-Write Section Enable: disabled */
	//		 | 0 << SIGRD /* Signature Row Read: disabled */
	//		 | 0 << RWWSB /* Read-While-Write Busy: disabled */
	//		 | 0 << SPMIE; /* SPM Interrupt Enable: disabled */

	return 0;
}

/**
 * \brief Read a byte from eeprom
 *
 * \param[in] eeprom_adr The byte-address in eeprom to read from
 *
 * \return The read byte
 */
uint8_t FLASH_0_read_eeprom_byte(eeprom_adr_t eeprom_adr)
{

	// Wait until any EEPROM write has completed
	while (EECR & (1 << EEPROM_WRITE_ENABLE))
		;

	/* Set up address register */
	EEAR = eeprom_adr;
	/* Start eeprom read by writing EERE */
	EECR |= (1 << EERE);
	/* Return data from Data Register */
	return EEDR;
}

/**
 * \brief Write a byte to eeprom
 *
 * \param[in] eeprom_adr The byte-address in eeprom to write to
 * \param[in] data The byte to write
 *
 * \return Status of write operation
 */
nvmctrl_status_t FLASH_0_write_eeprom_byte(eeprom_adr_t eeprom_adr, uint8_t data)
{

	/* Wait for completion of previous write */
	while (EECR & (1 << EEPROM_WRITE_ENABLE))
		;
	/* Set up address and Data Registers */
	EEAR = eeprom_adr;
	EEDR = data;
	ENTER_CRITICAL(WRITE_BYTE);
	/* Write logical one to EEMPE/EEWPE */
	EECR |= (1 << EEPROM_Master_WRITE_ENABLE);
	/* Start eeprom write by setting EEPE/EEWE */
	EECR |= (1 << EEPROM_WRITE_ENABLE);
	EXIT_CRITICAL(WRITE_BYTE);

	return NVM_OK;
}

/**
 * \brief Read a block from eeprom
 *
 * \param[in] eeprom_adr The byte-address in eeprom to read from
 * \param[in] data Buffer to place read data into
 *
 * \return Nothing
 */
void FLASH_0_read_eeprom_block(eeprom_adr_t eeprom_adr, uint8_t *data, size_t size)
{

	uint8_t i;
	for (i = 0; i < size; i++) {
		*data++ = FLASH_0_read_eeprom_byte(eeprom_adr++);
	}
}

/**
 * \brief Write a block to eeprom
 *
 * \param[in] eeprom_adr The byte-address in eeprom to write to
 * \param[in] data The buffer to write
 *
 * \return Status of write operation
 */
nvmctrl_status_t FLASH_0_write_eeprom_block(eeprom_adr_t eeprom_adr, uint8_t *data, size_t size)
{

	uint8_t i;
	for (i = 0; i < size; i++) {
		FLASH_0_write_eeprom_byte(eeprom_adr++, *data++);
	}
	return NVM_OK;
}

/**
 * \brief Check if the EEPROM can accept data to be read or written
 *
 * \return The status of EEPROM busy check
 * \retval false The EEPROM can not receive data to be read or written
 * \retval true The EEPROM can receive data to be read or written
 */
bool FLASH_0_is_eeprom_ready()
{

	return (EECR & (1 << EEPROM_WRITE_ENABLE));
}

/**
 * \brief Read a byte from flash
 *
 * \param[in] flash_adr The byte-address in flash to read from
 *
 * \return The read byte
 */
uint8_t FLASH_0_read_flash_byte(flash_adr_t flash_adr)
{

	return _FLASH_READ(flash_adr);
}

/**
 * \brief Write a byte to flash
 *
 * \param[in] flash_adr The byte-address in flash to write to
 * \param[in] page_buffer A buffer in memory the size of a flash page, used as a scratchpad
 * \param[in] data The byte to write
 *
 * \return Status of the operation
 */
nvmctrl_status_t FLASH_0_write_flash_byte(flash_adr_t flash_adr, uint8_t *ram_buffer, uint8_t data)
{

	uint8_t  i;
	uint16_t write_adr = (flash_adr & ~(SPM_PAGESIZE - 1));

	for (i = 0; i < SPM_PAGESIZE; i++) {
		if (i == flash_adr % SPM_PAGESIZE)
			ram_buffer[i] = data;
		else
			ram_buffer[i] = FLASH_0_read_flash_byte(write_adr + i);
	}

	// Write new byte into correct location in ram_buffer
	ram_buffer[flash_adr % SPM_PAGESIZE] = data;
	FLASH_0_erase_flash_page(write_adr);
	FLASH_0_write_flash_page(write_adr, ram_buffer);
	return NVM_OK;
}

/**
 * \brief Erase a page in flash
 *
 * \param[in] flash_adr The byte-address in flash to erase. Must point to start-of-page.
 *
 * \return Status of the operation
 */
nvmctrl_status_t FLASH_0_erase_flash_page(flash_adr_t flash_adr)
{

	_FLASH_ERASE_PAGE(flash_adr);
	_FLASH_WAIT_SPM();
	_FLASH_ENABLE_RWW_SECTION();
	return NVM_OK;
}

/**
 * \brief Write a page in flash.
 *
 * \param[in] flash_adr The byte-address of the flash page to write to. Must point to start-of-page.
 * \param[in] data The data to write to the flash page
 *
 * \return Status of the operation
 */
nvmctrl_status_t FLASH_0_write_flash_page(flash_adr_t flash_adr, uint8_t *data)
{

	uint8_t i;

	for (i = 0; i < SPM_PAGESIZE; i += 2) {
		// Set up little-endian word.
		uint16_t w = *data++;
		w += (*data++) << 8;

		_FLASH_WRITE_PAGEBUF(flash_adr + i, w);
	}
	_FLASH_WRITE_PAGE(flash_adr);
	_FLASH_WAIT_SPM();
	_FLASH_ENABLE_RWW_SECTION();

	return NVM_OK;
}

/**
 * \brief Writes a buffer to flash.
 * The flash does not need to be erased beforehand.
 * The flash address to write to does not need to be aligned to any specific boundary.
 *
 * \param[in] flash_adr The byte-address of the flash to write to
 * \param[in] data The data to write to the flash
 * \param[in] size The size of the data (in bytes) to write to the flash
 * \param[in] page_buffer A buffer in memory the size of a flash page, used as a scratch pad
 *
 * \return Status of the operation
 */
nvmctrl_status_t FLASH_0_write_flash_block(flash_adr_t flash_adr, uint8_t *data, size_t size, uint8_t *ram_buffer)
{

	// Get address of the start of first page to modify
	uint16_t write_adr    = flash_adr & ~(SPM_PAGESIZE - 1);
	uint8_t  start_offset = flash_adr % SPM_PAGESIZE;
	uint8_t  i;

	// Step 1:
	// Fill page buffer with contents of first flash page to be written up
	// to the first flash address to be replaced by the new contents
	for (i = 0; i < start_offset; i++) {
		ram_buffer[i] = FLASH_0_read_flash_byte(write_adr++);
	}

	// Step 2:
	// Write all of the new flash contents to the page buffer, writing the
	// page buffer to flash every time the buffer contains a complete flash
	// page.
	while (size > 0) {
		ram_buffer[i++] = *data++;
		write_adr++;
		size--;
		if ((write_adr % SPM_PAGESIZE) == 0) {
			// Erase and write the flash page
			FLASH_0_erase_flash_page(write_adr - SPM_PAGESIZE);
			FLASH_0_write_flash_page(write_adr - SPM_PAGESIZE, ram_buffer);
			i = 0;
		}
	}

	// Step 3:
	// After step 2, the page buffer may be partially full with the last
	// part of the new data to write to flash. The remainder of the flash page
	// shall be unaltered. Fill up the remainder
	// of the page buffer with the original contents of the flash page, and do a
	// final flash page write.
	while (1) {
		ram_buffer[i++] = FLASH_0_read_flash_byte(write_adr++);
		if ((write_adr % SPM_PAGESIZE) == 0) {
			// Erase and write the last flash page
			FLASH_0_erase_flash_page(write_adr - SPM_PAGESIZE);
			FLASH_0_write_flash_page(write_adr - SPM_PAGESIZE, ram_buffer);
			return NVM_OK;
		}
	}
}

/**
 * \brief Writes a byte stream to flash.
 * The erase granularity of the flash (i.e. one page) will cause this operation
 * to erase an entire page at a time. To avoid corrupting other flash contents,
 * make sure that the memory range in flash being streamed to is starting on a page
 * boundary, and that enough flash pages are available to hold all data being written.
 *
 * The function will perform flash page operations such as erase and write
 * as appropriate, typically when the last byte in a page is written. If
 * the last byte written is not at the last address of a page, the "finalize"
 * parameter can be set to force a page write after this byte.
 *
 * This function is intended used in devices where RAM resources are too limited
 * to afford a buffer needed by the write and erase page functions, and where
 * performance needs and code size concerns leaves the byte write and block
 * write functions too expensive.
 *
 * \param[in] flash_adr The byte-address of the flash to write to
 * \param[in] data The data byte to write to the flash
 * \param[in] finalize Set to true for the final write to the buffer
 *
 * \return Status of the operation
 */
nvmctrl_status_t FLASH_0_write_flash_stream(flash_adr_t flash_adr, uint8_t data, bool finalize)
{

	bool            final_adr_in_page = ((flash_adr & (SPM_PAGESIZE - 1)) == (SPM_PAGESIZE - 1));
	static uint16_t word_to_write;

	// Write the new byte value to the correct address in the page buffer
	if (flash_adr & 0x1) {
		word_to_write += data << 8;
		_FLASH_WRITE_PAGEBUF(flash_adr, word_to_write);
	} else {
		word_to_write = data;
	}

	if (final_adr_in_page || finalize) {
		// Erase page
		_FLASH_ERASE_PAGE(flash_adr);
		_FLASH_WAIT_SPM();

		// Write page
		_FLASH_WRITE_PAGE(flash_adr);
		_FLASH_WAIT_SPM();
		_FLASH_ENABLE_RWW_SECTION();
	}

	return NVM_OK;
}
