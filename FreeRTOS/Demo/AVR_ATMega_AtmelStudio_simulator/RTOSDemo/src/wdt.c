/**
 * \file
 *
 * \brief WDT related functionality implementation.
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
 * \addtogroup doc_driver_wdt
 *
 * \section doc_driver_wdt_rev Revision History
 * - v0.0.0.1 Initial Commit
 *
 *@{
 */

#include <wdt.h>

/**
 * \brief Initialize Watchdog Timer
 *
 * \return 0
 */
int8_t WDT_0_init()
{

	MCUSR &= ~(1 << WDRF);
	protected_write_io((void *)&WDTCSR,
	                   (1 << WDCE) | (1 << WDE),
	                   (0x00 /* Oscillator Cycles 2K */) | (0 << WDE /* Watch Dog Enable: disabled */)
	                       | (0 << WDIE /* Watchdog Timeout Interrupt Enable: disabled */));

	return 0;
}
