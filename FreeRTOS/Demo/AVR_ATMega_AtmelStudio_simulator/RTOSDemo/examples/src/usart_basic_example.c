/**
 * \file
 *
 * \brief USART basic driver example.
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
#include <usart_basic_example.h>
#include <usart_basic.h>
#include <atomic.h>

static uint8_t rx[16];

uint8_t USART_0_test_usart_basic(void)
{
	uint8_t i;

	// If USART Basic driver is in IRQ-mode, enable global interrupts.
	ENABLE_INTERRUPTS();

	// Test driver functions, assumes that the USART RX and
	// TX pins have been loopbacked, or that USART hardware
	// is configured in loopback mode

	// Test printf() support
	printf("hello");

	// Check that "hello" was received on loopback RX.
	// Initialize rx buffer so strncmp() check will work
	memset(rx, 0, sizeof(rx));
	for (i = 0; i < strlen("hello"); i++) {
		rx[i] = USART_0_read(); // Blocks until character is available
	}

	// Compare received and expected data
	if (strncmp("hello", (char *)rx, strlen("hello")) != 0)
		return 0; // Error: Mismatch

	// If we get here, everything was OK
	printf("ok");

	return 1;
}
