/**
 * \file
 *
 * \brief TC8 related functionality implementation.
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
 * \addtogroup doc_driver_tc8
 *
 * \section doc_driver_tc8_rev Revision History
 * - v0.0.0.1 Initial Commit
 *
 *@{
 */
#include <tc8.h>
#include <utils.h>

/**
 * \brief Initialize PWM_0 interface
 *
 * \return Initialization status.
 */
int8_t PWM_0_init()
{

	/* Enable TC0 */
	PRR0 &= ~(1 << PRTIM0);

	TCCR0A = (0 << COM0A1) | (0 << COM0A0)   /* Normal port operation, OCA disconnected */
	         | (0 << COM0B1) | (0 << COM0B0) /* Normal port operation, OCB disconnected */
	         | (0 << WGM01) | (1 << WGM00);  /* TC8 Mode 1 Phase Correct */

	// TCCR0B = 0 /* TC8 Mode 1 Phase Correct */
	//		 | (0 << CS02) | (0 << CS01) | (0 << CS00); /* No clock source (Timer/Counter stopped) */

	// TIMSK0 = 0 << OCIE0B /* Output Compare B Match Interrupt Enable: disabled */
	//		 | 0 << OCIE0A /* Output Compare A Match Interrupt Enable: disabled */
	//		 | 0 << TOIE0; /* Overflow Interrupt Enable: disabled */

	// OCR0A = 0x0; /* Output compare A: 0x0 */

	// OCR0B = 0x0; /* Output compare B: 0x0 */

	return 0;
}

/**
 * \brief Initialize TIMER_0 interface
 *
 * \return Initialization status.
 */
int8_t TIMER_0_init()
{

	/* Enable TC2 */
	PRR0 &= ~(1 << PRTIM2);

	// TCCR2A = (0 << COM2A1) | (0 << COM2A0) /* Normal port operation, OCA disconnected */
	//		 | (0 << COM2B1) | (0 << COM2B0) /* Normal port operation, OCB disconnected */
	//		 | (0 << WGM21) | (0 << WGM20); /* TC8 Mode 0 Normal */

	// TCCR2B = 0 /* TC8 Mode 0 Normal */
	//		 | (0 << CS22) | (0 << CS21) | (0 << CS20); /* No clock source (Timer/Counter stopped) */

	// TIMSK2 = 0 << OCIE2B /* Output Compare B Match Interrupt Enable: disabled */
	//		 | 0 << OCIE2A /* Output Compare A Match Interrupt Enable: disabled */
	//		 | 0 << TOIE2; /* Overflow Interrupt Enable: disabled */

	// OCR2A = 0x0; /* Output compare A: 0x0 */

	// OCR2B = 0x0; /* Output compare B: 0x0 */

	// GTCCR = 0 << TSM /* Timer/Counter Synchronization Mode: disabled */
	//		 | 0 << PSRASY /* Prescaler Reset Timer/Counter2: disabled */
	//		 | 0 << PSRSYNC; /* Prescaler Reset: disabled */

	return 0;
}
