/**
 * \file
 *
 * \brief Parallel Input/Output (PIO) interrupt handler for SAM.
 *
 * Copyright (c) 2011-2015 Atmel Corporation. All rights reserved.
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
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

#include "pio.h"
#include "pio_handler.h"

/**
 * Maximum number of interrupt sources that can be defined. This
 * constant can be increased, but the current value is the smallest possible one
 * that will be compatible with all existing projects.
 */
#define MAX_INTERRUPT_SOURCES       7

/**
 * Describes a PIO interrupt source, including the PIO instance triggering the
 * interrupt and the associated interrupt handler.
 */
struct s_interrupt_source {
	uint32_t id;
	uint32_t mask;
	uint32_t attr;

	/* Interrupt handler. */
	void (*handler) (const uint32_t, const uint32_t);
};


/* List of interrupt sources. */
static struct s_interrupt_source gs_interrupt_sources[MAX_INTERRUPT_SOURCES];

/* Number of currently defined interrupt sources. */
static uint32_t gs_ul_nb_sources = 0;

#if (SAM3S || SAM4S || SAM4E)
/* PIO Capture handler */
static void (*pio_capture_handler)(Pio *) = NULL;
extern uint32_t pio_capture_enable_flag;
#endif

/**
 * \brief Process an interrupt request on the given PIO controller.
 *
 * \param p_pio PIO controller base address.
 * \param ul_id PIO controller ID.
 */
void pio_handler_process(Pio *p_pio, uint32_t ul_id)
{
	uint32_t status;
	uint32_t i;

	/* Read PIO controller status */
	status = pio_get_interrupt_status(p_pio);
	status &= pio_get_interrupt_mask(p_pio);

	/* Check pending events */
	if (status != 0) {
		/* Find triggering source */
		i = 0;
		while (status != 0) {
			/* Source is configured on the same controller */
			if (gs_interrupt_sources[i].id == ul_id) {
				/* Source has PIOs whose statuses have changed */
				if ((status & gs_interrupt_sources[i].mask) != 0) {
					gs_interrupt_sources[i].handler(gs_interrupt_sources[i].id,
							gs_interrupt_sources[i].mask);
					status &= ~(gs_interrupt_sources[i].mask);
				}
			}
			i++;
			if (i >= MAX_INTERRUPT_SOURCES) {
				break;
			}
		}
	}

	/* Check capture events */
#if (SAM3S || SAM4S || SAM4E)
	if (pio_capture_enable_flag) {
		if (pio_capture_handler) {
			pio_capture_handler(p_pio);
		}
	}
#endif
}

/**
 * \brief Set an interrupt handler for the provided pins.
 * The provided handler will be called with the triggering pin as its parameter
 * as soon as an interrupt is detected.
 *
 * \param p_pio PIO controller base address.
 * \param ul_id PIO ID.
 * \param ul_mask Pins (bit mask) to configure.
 * \param ul_attr Pins attribute to configure.
 * \param p_handler Interrupt handler function pointer.
 *
 * \return 0 if successful, 1 if the maximum number of sources has been defined.
 */
uint32_t pio_handler_set(Pio *p_pio, uint32_t ul_id, uint32_t ul_mask,
		uint32_t ul_attr, void (*p_handler) (uint32_t, uint32_t))
{
	struct s_interrupt_source *pSource;

	if (gs_ul_nb_sources >= MAX_INTERRUPT_SOURCES)
		return 1;

	/* Define new source */
	pSource = &(gs_interrupt_sources[gs_ul_nb_sources]);
	pSource->id = ul_id;
	pSource->mask = ul_mask;
	pSource->attr = ul_attr;
	pSource->handler = p_handler;
	gs_ul_nb_sources++;

	/* Configure interrupt mode */
	pio_configure_interrupt(p_pio, ul_mask, ul_attr);

	return 0;
}

#if (SAM3S || SAM4S || SAM4E)
/**
 * \brief Set a capture interrupt handler for all PIO.
 *
 * The handler will be called with the triggering PIO as its parameter
 * as soon as an interrupt is detected.
 *
 * \param p_handler Interrupt handler function pointer.
 *
 */
void pio_capture_handler_set(void (*p_handler)(Pio *))
{
	pio_capture_handler = p_handler;
}
#endif

#ifdef ID_PIOA
/**
 * \brief Set an interrupt handler for the specified pin.
 * The provided handler will be called with the triggering pin as its parameter
 * as soon as an interrupt is detected.
 *
 * \param ul_pin Pin index to configure.
 * \param ul_flag Pin flag.
 * \param p_handler Interrupt handler function pointer.
 *
 * \return 0 if successful, 1 if the maximum number of sources has been defined.
 */
uint32_t pio_handler_set_pin(uint32_t ul_pin, uint32_t ul_flag,
		void (*p_handler) (uint32_t, uint32_t))
{
	Pio *p_pio = pio_get_pin_group(ul_pin);
	uint32_t group_id =  pio_get_pin_group_id(ul_pin);
	uint32_t group_mask = pio_get_pin_group_mask(ul_pin);

	return pio_handler_set(p_pio, group_id, group_mask, ul_flag, p_handler);
}

/**
 * \brief Parallel IO Controller A interrupt handler.
 * Redefined PIOA interrupt handler for NVIC interrupt table.
 */
void PIOA_Handler(void)
{
	pio_handler_process(PIOA, ID_PIOA);
}
#endif

#ifdef ID_PIOB
/**
 * \brief Parallel IO Controller B interrupt handler
 * Redefined PIOB interrupt handler for NVIC interrupt table.
 */
void PIOB_Handler(void)
{
    pio_handler_process(PIOB, ID_PIOB);
}
#endif

#ifdef ID_PIOC
/**
 * \brief Parallel IO Controller C interrupt handler.
 * Redefined PIOC interrupt handler for NVIC interrupt table.
 */
void PIOC_Handler(void)
{
	pio_handler_process(PIOC, ID_PIOC);
}
#endif

#ifdef ID_PIOD
/**
 * \brief Parallel IO Controller D interrupt handler.
 * Redefined PIOD interrupt handler for NVIC interrupt table.
 */
void PIOD_Handler(void)
{
	pio_handler_process(PIOD, ID_PIOD);
}
#endif

#ifdef ID_PIOE
/**
 * \brief Parallel IO Controller E interrupt handler.
 * Redefined PIOE interrupt handler for NVIC interrupt table.
 */
void PIOE_Handler(void)
{
	pio_handler_process(PIOE, ID_PIOE);
}
#endif

#ifdef ID_PIOF
/**
 * \brief Parallel IO Controller F interrupt handler.
 * Redefined PIOF interrupt handler for NVIC interrupt table.
 */
void PIOF_Handler(void)
{
	pio_handler_process(PIOF, ID_PIOF);
}
#endif

/**
 * \brief Initialize PIO interrupt management logic.
 *
 * \param p_pio PIO controller base address.
 * \param ul_irqn NVIC line number.
 * \param ul_priority PIO controller interrupts priority.
 */
void pio_handler_set_priority(Pio *p_pio, IRQn_Type ul_irqn, uint32_t ul_priority)
{
	uint32_t bitmask = 0;

	bitmask = pio_get_interrupt_mask(p_pio);
	pio_disable_interrupt(p_pio, 0xFFFFFFFF);
	pio_get_interrupt_status(p_pio);
	NVIC_DisableIRQ(ul_irqn);
	NVIC_ClearPendingIRQ(ul_irqn);
	NVIC_SetPriority(ul_irqn, ul_priority);
	NVIC_EnableIRQ(ul_irqn);
	pio_enable_interrupt(p_pio, bitmask);
}
