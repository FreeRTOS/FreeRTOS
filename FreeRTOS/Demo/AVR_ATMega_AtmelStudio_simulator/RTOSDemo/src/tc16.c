/**
 * \file
 *
 * \brief TC16 related functionality implementation.
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
 */

/**
 * \addtogroup doc_driver_tc16
 *
 * \section doc_driver_tc16_rev Revision History
 * - v0.0.0.1 Initial Commit
 *
 *@{
 */
#include <tc16.h>
#include <utils.h>

/**
 * \brief Initialize TIMER_1 interface
 *
 * \return Initialization status.
 */
int8_t TIMER_1_init()
{

	/* Enable TC1 */
	PRR0 &= ~(1 << PRTIM1);

	// TCCR1A = (0 << COM1A1) | (0 << COM1A0) /* Normal port operation, OCA disconnected */
	//		 | (0 << COM1B1) | (0 << COM1B0) /* Normal port operation, OCB disconnected */
	//		 | (0 << WGM11) | (0 << WGM10); /* TC16 Mode 0 Normal */

	// TCCR1B = (0 << WGM13) | (0 << WGM12) /* TC16 Mode 0 Normal */
	//		 | 0 << ICNC1 /* Input Capture Noise Canceler: disabled */
	//		 | 0 << ICES1 /* Input Capture Edge Select: disabled */
	//		 | (0 << CS12) | (0 << CS11) | (0 << CS10); /* No clock source (Timer/Counter stopped) */

	// ICR1 = 0x0; /* Input capture value, used as top counter value in some modes: 0x0 */

	// OCR1A = 0x0; /* Output compare A: 0x0 */

	// OCR1B = 0x0; /* Output compare B: 0x0 */

	// GTCCR = 0 << TSM /* Timer/Counter Synchronization Mode: disabled */
	//		 | 0 << PSRASY /* Prescaler Reset Timer/Counter2: disabled */
	//		 | 0 << PSRSYNC; /* Prescaler Reset: disabled */

	// TIMSK1 = 0 << OCIE1B /* Output Compare B Match Interrupt Enable: disabled */
	//		 | 0 << OCIE1A /* Output Compare A Match Interrupt Enable: disabled */
	//		 | 0 << ICIE1 /* Input Capture Interrupt Enable: disabled */
	//		 | 0 << TOIE1; /* Overflow Interrupt Enable: disabled */

	return 0;
}
