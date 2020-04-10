/**
 * \file
 *
 * \brief NVMCTRL basic driver example
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

#include <string.h>
#include <atmel_start.h>
#include <nvmctrl_basic_example.h>
#include <nvmctrl_basic.h>

// Some devices, e.g. tiny817, does not define SPM_PAGESIZE in its header file.
// For these devices, the rambuf variable is not used by the NVMCTL driver.
// Just give SPM_PAGESIZE a value here so that this example function compiles
// and executes correctly.
#ifndef SPM_PAGESIZE
#define SPM_PAGESIZE 1
#endif

#define TEST_ADDRESS 3072
#define TEST_SIZE 64

static uint8_t                   rambuf[SPM_PAGESIZE];
static uint8_t                   wdata[] = {0, 1, 2, 3};
static uint8_t                   rdata[4];
static volatile nvmctrl_status_t status;
static volatile uint8_t          rb;

/*
NOTE:
Depending on the compiler and device used, the flash programming
routines may have to be placed in a separate segment. This segment is called:
* For GCC: .bootloader. Segment must be given a location in linker
           file or Toolchain->AVR/GNU Linker->Memory Settings in STUDIO.
* For IAR: BOOTLOADER_SEGMENT. Segment must be added to linker file.

Refer to driver documentation for more details.
*/

uint8_t FLASH_0_test_nvmctrl_basic(void)
{
	uint16_t i;

	//  Test EEPROM write
	FLASH_0_write_eeprom_byte(0, wdata[1]);
	rdata[1] = FLASH_0_read_eeprom_byte(0);
	if (rdata[1] != wdata[1])
		return 0; // Error

	FLASH_0_write_eeprom_block(0, wdata, 4);
	FLASH_0_read_eeprom_block(0, rdata, 4);
	if (memcmp(wdata, rdata, 4) != 0)
		return 0; // Error

	// Test flash write
	status = FLASH_0_write_flash_byte(TEST_ADDRESS + 0, rambuf, 1);
	rb     = FLASH_0_read_flash_byte(TEST_ADDRESS + 0);
	if (rb != 1)
		return 0; // Error
	status = FLASH_0_write_flash_byte(TEST_ADDRESS + 1, rambuf, 2);
	rb     = FLASH_0_read_flash_byte(TEST_ADDRESS + 1);
	if (rb != 2)
		return 0; // Error
	status = FLASH_0_write_flash_byte(TEST_ADDRESS + 2, rambuf, 3);
	rb     = FLASH_0_read_flash_byte(TEST_ADDRESS + 2);
	if (rb != 3)
		return 0; // Error

	for (i = 0; i < 2 * TEST_SIZE; i++)
		// Init two pages in flash, starting at address TEST_ADDRESS-ONE_PAGE.
		status = FLASH_0_write_flash_byte(TEST_ADDRESS - TEST_SIZE + i, rambuf, i);

	rb = FLASH_0_read_flash_byte(TEST_ADDRESS - TEST_SIZE);
	if (rb != 0)
		return 0; // Error
	rb = FLASH_0_read_flash_byte(TEST_ADDRESS - 2);
	if (rb != TEST_SIZE - 2)
		return 0; // Error
	rb = FLASH_0_read_flash_byte(TEST_ADDRESS - 1);
	if (rb != TEST_SIZE - 1)
		return 0; // Error
	rb = FLASH_0_read_flash_byte(TEST_ADDRESS);
	if (rb != TEST_SIZE)
		return 0; // Error
	rb = FLASH_0_read_flash_byte(TEST_ADDRESS + 1);
	if (rb != TEST_SIZE + 1)
		return 0; // Error

	FLASH_0_write_flash_block(TEST_ADDRESS - 2, wdata, 4, rambuf);

	rb = FLASH_0_read_flash_byte(TEST_ADDRESS - TEST_SIZE);
	if (rb != 0)
		return 0; // Error
	rb = FLASH_0_read_flash_byte(TEST_ADDRESS - 2);
	if (rb != wdata[0])
		return 0; // Error
	rb = FLASH_0_read_flash_byte(TEST_ADDRESS - 1);
	if (rb != wdata[1])
		return 0; // Error
	rb = FLASH_0_read_flash_byte(TEST_ADDRESS);
	if (rb != wdata[2])
		return 0; // Error
	rb = FLASH_0_read_flash_byte(TEST_ADDRESS + 1);
	if (rb != wdata[3])
		return 0; // Error

	// If we get here, everything was OK
	return 1;
}
