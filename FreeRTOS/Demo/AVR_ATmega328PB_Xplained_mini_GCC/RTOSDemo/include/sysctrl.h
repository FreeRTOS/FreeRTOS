

/**
 * \file
 *
 * \brief Sysctrl covers power management (PM), system clock (SYSCLK) and system reset functionality
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
 */

/**
 * \defgroup doc_driver_system_sysctrl System Control (PM, SYSCLK, SYSRST)
 * \ingroup doc_driver_system
 *
 * \section doc_driver_sysctrl_rev Revision History
 * - v0.0.0.1 Initial Commit
 *
 *@{
 */

#ifndef SYSCTRL_H_INCLUDED
#define SYSCTRL_H_INCLUDED

#include <compiler.h>
#include <atomic.h>
#include <protected_io.h>
#ifdef __cplusplus
extern "C" {
#endif

#if defined(__ICCAVR__) || defined(__DOXYGEN__)
#include <intrinsics.h>
//! Macro for issuing the sleep instruction.
#define sleep_enter() __sleep()

/**
 * \brief Enable sleep
 */
static inline void sleep_enable(void)
{
	SMCR |= (1 << SE);
}

/**
 * \brief Disable sleep
 */
static inline void sleep_disable(void)
{
	SMCR &= ~(1 << SE);
}

#elif defined(__GNUC__)
#include <avr/sleep.h>
#define sleep_enter() sleep_cpu()

#else
#error Unsupported compiler.
#endif

/**
 * \brief Set sleep mode to use when entering sleep state
 *
 * \param mode Sleep mode
 */
static inline void sleep_set_mode(uint8_t mode)
{
	SMCR = mode | (SMCR & ~((1 << SM0) | (1 << SM1) | (1 << SM2)));
}

/*
 * \brief Initialize sysctrl interface
 *
 * \param[in] hw The pointer to hardware instance
 *
 * \return Initialization status.
 */
static inline int8_t sysctrl_init()
{
	/* Set up system clock prescaler according to configuration */
	protected_write_io((void *)&CLKPR, 1 << CLKPCE, (0 << CLKPS3) | (0 << CLKPS2) | (0 << CLKPS1) | (0 << CLKPS0));

	SMCR = (0 << SM2) | (0 << SM1) | (0 << SM0) | // Idle
	       (0 << SE);

	MCUCR = (0 << PUD);

	return 0;
}

#ifdef __cplusplus
}
#endif
#endif /* SYSCTRL_H_INCLUDED */
