/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _PIO_H
#define _PIO_H

#define IRQ_PIO_HANDLERS_SIZE 16

/*------------------------------------------------------------------------------
 *         Global Types
 *------------------------------------------------------------------------------*/

#include "chip.h"

struct _pin
{
	uint8_t group;      /*< The IO group containing the pins you want to use. */
	uint32_t mask;      /*< Bitmask indicating which pin(s) to configure. */
	uint8_t type;       /*< Pin type */
	uint32_t attribute; /*< Pin config attribute. */
};

typedef void(*pio_handler_t)(uint32_t, uint32_t, void*);

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#if defined(CONFIG_HAVE_PIO4)
#include "peripherals/pio4.h"
#endif

#ifdef __cplusplus
extern "C" {
#endif

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

/**
 * \brief Configures a list of Pin instances.
 *
 * \details Each of them can either hold a single pin or a group of
 * pins, depending on the mask value; all pins are configured by this
 * function. The size of the array must also be provided and is easily
 * computed using ARRAY_SIZE whenever its length is not known in
 * advance.
 *
 * \param list  Pointer to a list of Pin instances.
 * \param size  Size of the Pin list (calculated using ARRAY_SIZE).
 *
 * \return 1 if the pins have been configured properly; otherwise 0.
 */
extern uint8_t pio_configure(const struct _pin *list, uint32_t size);

/**
 * \brief Sets a high output level on all the PIOs defined in the
 * given Pin instance.
 *
 * \details This has no immediate effects on PIOs that are not output,
 * but the PIO controller will memorize the value they are changed to
 * outputs.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */
extern void pio_set(const struct _pin *pin);

/**
 * \brief Sets a low output level on all the PIOs defined in the given
 * Pin instance.
 *
 * \details This has no immediate effects on PIOs that are not output,
 * but the PIO controller will memorize the value they are changed to
 * outputs.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */
extern void pio_clear(const struct _pin *pin);

/**
 * \brief Returns 1 if one or more PIO of the given Pin instance currently have
 * a high level; otherwise returns 0. This method returns the actual value that
 * is being read on the pin. To return the supposed output value of a pin, use
 * \ref pio_get_output_date_status() instead.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 *
 * \return 1 if the Pin instance contains at least one PIO that currently has
 * a high level; otherwise 0.
 */
extern uint8_t pio_get(const struct _pin *pin);

/**
 * \brief Returns 1 if one or more PIO of the given Pin are configured to output a
 * high level (even if they are not output).
 * To get the actual value of the pin, use pio_get() instead.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 *
 * \return 1 if the Pin instance contains at least one PIO that is configured
 * to output a high level; otherwise 0.
 */
extern uint8_t pio_get_output_data_status(const struct _pin *pin);

/**
 * \brief Configures Glitch or Debouncing filter for input.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 * \param cuttoff  Cutt off frequency for debounce filter.
 */
extern void pio_set_debounce_filter(const struct _pin *pin, uint32_t cuttoff);

/**
 * \brief Enable write protect.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */
extern void pio_enable_write_protect(const struct _pin *pin);

/**
 * \brief Disable write protect.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */
extern void pio_disable_write_protect(const struct _pin *pin);

/**
 * \brief Get write protect violation information.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */
extern uint32_t pio_get_write_protect_violation_info(const struct _pin * pin);

/**
 * \brief Configure all pio outputs low
 *
 * \param group PIO group number
 * \param mask  Bitmask of one or more pin(s) to configure.
 */
extern void pio_output_low(uint32_t group, uint32_t mask);

extern void pio_add_handler_to_group(uint32_t group, uint32_t mask,
				     pio_handler_t handler, void* user_arg);

extern void pio_reset_all_it(void);

/**
 * \brief Generate an interrupt on status change for a PIO or a group
 * of PIO.

 * \details The provided interrupt handler will be called with the
 * triggering pin as its parameter (enabling different pin instances
 * to share the same handler).
 *
 * \param pin  Pointer to a _pin instance.
 */
extern void pio_configure_it(const struct _pin * pin);


/**
 * Enables the given interrupt source if it has been configured. The status
 * register of the corresponding PIO controller is cleared prior to enabling
 * the interrupt.
 * \param pin  Interrupt source to enable.
 */
extern void pio_enable_it(const struct _pin * pin);

/**
 * Disables a given interrupt source, with no added side effects.
 *
 * \param pin  Interrupt source to disable.
 */
extern void pio_disable_it(const struct _pin * pin);

#ifdef __cplusplus
}
#endif
#endif /* _PIO_H */
