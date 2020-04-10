/**
 * \file
 *
 * \brief SPI basic driver example.
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

#include <stdio.h>
#include <string.h>
#include <atmel_start.h>
#include <spi_basic_example.h>
#include <spi_basic.h>
#include <atomic.h>

static uint8_t buffer[16] = "data";

static void drive_slave_select_low(void);
static void drive_slave_select_high(void);

static void drive_slave_select_low()
{
	// Control GPIO to drive SS_bar low
}

static void drive_slave_select_high()
{
	// Control GPIO to drive SS_bar high
}

uint8_t SPI_0_test_spi_basic(void)
{

	// Register callback function releasing SS when transfer is complete
	SPI_0_register_callback(drive_slave_select_high);

	// SPI Basic driver is in IRQ-mode, enable global interrupts.
	ENABLE_INTERRUPTS();

	// Test driver, assume that the SPI MISO and MOSI pins have been looped back

	drive_slave_select_low();
	SPI_0_exchange_block(buffer, sizeof(buffer));

	while (SPI_0_status_busy())
		; // Wait for the transfer to complete

	// Check that the correct data was received
	if (strncmp((char *)buffer, "data", strlen("data")))
		return 0; // ERROR: Wrong data received

	// If we get here, everything was OK
	return 1;
}
