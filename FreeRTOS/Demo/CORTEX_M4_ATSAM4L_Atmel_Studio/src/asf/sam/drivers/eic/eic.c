/**
 * \file
 *
 * \brief EIC driver for SAM
 *
 * Copyright (c) 2012 Atmel Corporation. All rights reserved.
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

#include "eic.h"
#include "sysclk.h"
#include "sleepmgr.h"

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

/**
 * \defgroup sam_drivers_eic_group External Interrupt Controller(EIC)
 *
 * See \ref sam_eic_quickstart.
 *
 * EIC allows pins to be configured as external interrupts.
 *
 * @{
 */


/**
 * \internal
 * \brief EIC callback function pointer array
 */
eic_callback_t eic_callback_pointer[EIC_NUMBER_OF_LINES];

/**
 * \brief Write the EIC hardware with specified configuration value.
 *
 * \param eic Base address of the EIC module
 * \param eic_line_conf Configuration parameters of the EIC module
 * (see \ref eic_line_config)
 * \param line_number Number of line to config
 */
void eic_line_set_config(Eic *eic, uint8_t line_number,
	struct eic_line_config *eic_line_conf)
{
		/* Set up mode level */
		eic->EIC_MODE = (eic_line_conf->eic_mode == EIC_MODE_LEVEL_TRIGGERED)
				? (eic->EIC_MODE | (1 << line_number))
				: (eic->EIC_MODE & ~(1 << line_number));
		/* Set up edge type */
		eic->EIC_EDGE = (eic_line_conf->eic_edge == EIC_EDGE_RISING_EDGE)
				? (eic->EIC_EDGE | (1 << line_number))
				: (eic->EIC_EDGE & ~(1 << line_number));
		/* Set up level */
		eic->EIC_LEVEL = (eic_line_conf->eic_level == EIC_LEVEL_HIGH_LEVEL)
				? (eic->EIC_LEVEL | (1 << line_number))
				: (eic->EIC_LEVEL & ~(1 << line_number));
		/* Set up if filter is used */
		eic->EIC_FILTER = (eic_line_conf->eic_filter == EIC_FILTER_ENABLED)
				? (eic->EIC_FILTER | (1 << line_number))
				: (eic->EIC_FILTER & ~(1 << line_number));
		/* Set up which mode is used : asynchronous mode/ synchronous mode */
		eic->EIC_ASYNC = (eic_line_conf->eic_async == EIC_ASYNCH_MODE)
				? (eic->EIC_ASYNC | (1 << line_number))
				: (eic->EIC_ASYNC & ~(1 << line_number));

}

/**
 * \brief Disable the EIC module
 *
 * \param eic Base address of the EIC module
 */
void eic_disable(Eic *eic)
{
	sysclk_disable_peripheral_clock(eic);
	sleepmgr_unlock_mode(SLEEPMGR_BACKUP);
}

/**
 * \brief Enable the EIC module
 *
 * \param eic Base address of the EIC module
 */
void eic_enable(Eic *eic)
{
	sysclk_enable_peripheral_clock(eic);
	sleepmgr_lock_mode(SLEEPMGR_BACKUP);
}

/**
 * \brief Set callback for given EIC line
 *
 * \param eic Base address of the EIC module
 * \param line_number Number of line.
 * \param callback callback function pointer.
 * \param irq_line  interrupt line.
 * \param irq_level interrupt level.
 */
void eic_line_set_callback(Eic *eic, uint8_t line_number,
	eic_callback_t callback, uint8_t irq_line, uint8_t irq_level)
{
	eic_callback_pointer[line_number] = callback;
	irq_register_handler((IRQn_Type)irq_line, irq_level);
	eic_line_enable_interrupt(eic, line_number);
}

/**
 * \internal
 * \brief Common EIC line interrupt handler
 *
 * The optional callback used by the interrupt handler is set by the
 * eic_line_set_callback() function.
 *
 * \param line_number EIC linel number to handle interrupt for
 */
static void eic_line_interrupt(uint8_t line_number)
{
	if (eic_callback_pointer[line_number]) {
		eic_callback_pointer[line_number]();
	} else {
		Assert(false); /* Catch unexpected interrupt */
	}
}

/**
 * \brief Interrupt handler for EIC NMI.
 */
void NMI_Handler(void)
{
	eic_line_interrupt(0);
}

/**
 * \brief Interrupt handler for EIC line 1.
 */
void EIC_1_Handler(void)
{
	eic_line_interrupt(1);
}

/**
 * \brief Interrupt handler for EIC line 2.
 */
void EIC_2_Handler(void)
{
	eic_line_interrupt(2);
}

/**
 * \brief Interrupt handler for EIC line 3.
 */
void EIC_3_Handler(void)
{
	eic_line_interrupt(3);
}

/**
 * \brief Interrupt handler for EIC line 4.
 */
void EIC_4_Handler(void)
{
	eic_line_interrupt(4);
}

/**
 * \brief Interrupt handler for EIC line 5.
 */
void EIC_5_Handler(void)
{
	eic_line_interrupt(5);
}

/**
 * \brief Interrupt handler for EIC line 6.
 */
void EIC_6_Handler(void)
{
	eic_line_interrupt(6);
}

/**
 * \brief Interrupt handler for EIC line 7.
 */
void EIC_7_Handler(void)
{
	eic_line_interrupt(7);
}

/**
 * \brief Interrupt handler for EIC line 8.
 */
void EIC_8_Handler(void)
{
	eic_line_interrupt(8);
}

//@}

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond
