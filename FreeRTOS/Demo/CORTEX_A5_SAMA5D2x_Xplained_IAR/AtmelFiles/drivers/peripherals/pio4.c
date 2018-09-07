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

/** \addtogroup pio_module Working with PIO
 * \section Purpose
 * The PIO driver provides the Interface for configuration the Parallel Input/Output
 *  Controller (PIO).
 *
 * \section Usage
 * <ul>
 * <li>  Initialize the PIO with the desired period using pio_configure().
 * <li>  Set a high or low output level on the given PIO using pio_set() or pio_clear().
 * <li>  Get the level of the given PIOs using pio_get() or pio_get_output_date_status().
 * <li>  Configures Glitch or Debouncing filter for given input PIO using pio_set_debounce_filter().
 * <li>  Enable & disable write protect of the given PIOs using pio_enable_write_protect() or pio_disable_write_protect().
 * <li>  Get write protect violation information of given PIO using pio_get_write_protect_violation_info().
 * </li>
 * </ul>
 *
 * For more accurate information, please look at the PIT section of the Datasheet.
 *
 * Related files :\n
 * \ref pio.c\n
 * \ref pio3.h\n
*/
/*@{*/
/*@}*/

/**
 * \file
 *
 * Implementation of PIO V3 (Parallel Input/Output) controller.
 *
 */
/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "peripherals/pio.h"
#include "peripherals/pmc.h"
#include "peripherals/aic.h"
#include "peripherals/matrix.h"

#include "trace.h"
#include "compiler.h"

#include <stdint.h>
#include <string.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local types
 *----------------------------------------------------------------------------*/

struct _bitfield_pio_cfgr_func {
	uint32_t
	func            : 3,
	rfu3_7          : 5,
	dir             : 1,
	puen            : 1,
	pden            : 1,
	rfu11           : 1,
	ifen            : 1,
	ifscen          : 1,
	opd             : 1,
	schmitt         : 1,
	drvstr          : 2,
	rfu18_23        : 6,
	evtsel          : 3,
	rfu27_28        : 2,
	pcfs            : 1,
	icfs            : 1,
	tampen          : 1;
};

union _pio_cfg {
	struct _bitfield_pio_cfgr_func bitfield;
	uint32_t uint32_value;
};

/*----------------------------------------------------------------------------
 *        Local functions declarations
 *----------------------------------------------------------------------------*/

#ifdef ID_PIOA
static void _pioa_handler(void);
#endif
#ifdef ID_PIOB
static void _piob_handler(void);
#endif
#ifdef ID_PIOC
static void _pioc_handler(void);
#endif
#ifdef ID_PIOD
static void _piod_handler(void);
#endif

/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/
struct _handler {
	uint32_t mask;
	pio_handler_t handler;
	void *user_arg;
};
static struct _handler _handlers[IRQ_PIO_HANDLERS_SIZE];

static const aic_handler_t _generic_handlers[PIO_GROUP_LENGTH] = {
#ifdef ID_PIOA
	_pioa_handler,
#endif
#ifdef ID_PIOB
	_piob_handler,
#endif
#ifdef ID_PIOC
	_pioc_handler,
#endif
#ifdef ID_PIOD
	_piod_handler,
#endif
};

/*----------------------------------------------------------------------------
 *        Local functions definitions
 *----------------------------------------------------------------------------*/

static void _handler_push(void (*handler)(uint32_t, uint32_t, void*),
		uint32_t mask, void* user_arg)
{
	static int i = 0;
	_handlers[i].mask = mask;
	_handlers[i].handler = handler;
	_handlers[i].user_arg = user_arg;
	++i;
	assert(i < ARRAY_SIZE(_handlers));
}

#ifdef ID_PIOA
static void _pioa_handler(void)
{
	uint32_t status = 0;
	unsigned int i = 0;
	if (matrix_is_peripheral_secured(MATRIX1, ID_PIOA))
		status = PIOA->PIO_PIO_[PIO_GROUP_A].S_PIO_ISR;
	else
		status = PIOA->PIO_IO_GROUP[PIO_GROUP_A].PIO_ISR;

	for (i = 0; i < ARRAY_SIZE(_handlers); ++i) {
		if (_handlers[i].mask & status) {
			_handlers[i].handler(PIO_GROUP_A, status,
					_handlers[i].user_arg);
		}
	}
}
#endif
#ifdef ID_PIOB
static void _piob_handler(void)
{
	uint32_t status = 0;
	unsigned int i = 0;
	if (matrix_is_peripheral_secured(MATRIX1, ID_PIOB))
		status = PIOA->PIO_PIO_[PIO_GROUP_B].S_PIO_ISR;
	else
		status = PIOA->PIO_IO_GROUP[PIO_GROUP_B].PIO_ISR;

	for (i = 0; i < ARRAY_SIZE(_handlers); ++i) {
		if (_handlers[i].mask & status) {
			_handlers[i].handler(PIO_GROUP_B, status,
					_handlers[i].user_arg);
		}
	}

}
#endif
#ifdef ID_PIOC
static void _pioc_handler(void)
{
	uint32_t status = 0;
	unsigned int i = 0;
	if (matrix_is_peripheral_secured(MATRIX1, ID_PIOC))
		status = PIOA->PIO_PIO_[PIO_GROUP_C].S_PIO_ISR;
	else
		status = PIOA->PIO_IO_GROUP[PIO_GROUP_C].PIO_ISR;

	for (i = 0; i < ARRAY_SIZE(_handlers); ++i) {
		if (_handlers[i].mask & status) {
			_handlers[i].handler(PIO_GROUP_C, status,
					_handlers[i].user_arg);
		}
	}
}
#endif
#ifdef ID_PIOD
static void _piod_handler(void)
{
	uint32_t status = 0;
	unsigned int i = 0;
	if (matrix_is_peripheral_secured(MATRIX1, ID_PIOD))
		status = PIOA->PIO_PIO_[PIO_GROUP_D].S_PIO_ISR;
	else
		status = PIOA->PIO_IO_GROUP[PIO_GROUP_D].PIO_ISR;

	for (i = 0; i < ARRAY_SIZE(_handlers); ++i) {
		if (_handlers[i].mask & status) {
			_handlers[i].handler(PIO_GROUP_D, status,
					_handlers[i].user_arg);
		}
	}
}
#endif

static inline uint32_t _pio_group_to_id(int group)
{
	switch(group) {
	case PIO_GROUP_A:
		return ID_PIOA;
	case PIO_GROUP_B:
		return ID_PIOB;
	case PIO_GROUP_C:
		return ID_PIOC;
	case PIO_GROUP_D:
		return ID_PIOD;
	default:
		return (unsigned int)-1;
	};
}

static void* _pio_configure_pins(const struct _pin *pin, uint32_t periph_id)
{
	PioPio_* piogroup = &PIOA->PIO_PIO_[pin->group];
	if (!matrix_is_peripheral_secured(MATRIX1, periph_id)) {
		piogroup->S_PIO_SIONR = pin->mask;
		return (void*) &PIOA->PIO_IO_GROUP[pin->group];
	} else {
		piogroup->S_PIO_SIOSR = pin->mask;
		return (void*) piogroup;
	}
}

static void* _pio_retrive_group(const struct _pin *pin, uint32_t periph_id)
{
	if (!matrix_is_peripheral_secured(MATRIX1, periph_id)) {
		return (void*) &PIOA->PIO_IO_GROUP[pin->group];
	} else {
		return (void*) &PIOA->PIO_PIO_[pin->group];
	}
}
/*----------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Configures a list of Pin instances, each of which can either
 * hold a single pin or a group of pins, depending on the mask value;
 * all pins are configured by this function. The size of the array
 * must also be provided and is easily computed using ARRAY_SIZE
 * whenever its length is not known in advance.
 *
 * \param list  Pointer to a list of _pin instances.
 * \param size  Size of the _pin list (calculated using PIN_LISTSIZE).
 *
 * \return 1 if the pins have been configured properly; otherwise 0.
 */
uint8_t pio_configure(const struct _pin *pin_list, uint32_t size)
{
	union _pio_cfg cfg;
	PioIo_group* pioiog;

	/* Configure pins */
	while (size--)
	{
		/* Enable the PIO group if needed */
		uint32_t periph_id = _pio_group_to_id(pin_list->group);

		assert(pin_list->group < PIO_GROUP_LENGTH);
		cfg.uint32_value = 0;
		pioiog = (PioIo_group*) _pio_configure_pins(pin_list, periph_id);

		if ( pin_list->attribute != PIO_DEFAULT) {
			cfg.bitfield.puen = (pin_list->attribute & PIO_PULLUP)? 1:0;
			cfg.bitfield.pden = (pin_list->attribute & PIO_PULLDOWN)? 1:0;
			cfg.bitfield.ifen = (pin_list->attribute & PIO_DEGLITCH)? 1:0;
			cfg.bitfield.ifscen = (pin_list->attribute & PIO_DEBOUNCE)? 1:0;
			cfg.bitfield.opd = (pin_list->attribute & PIO_OPENDRAIN)? 1:0;
			cfg.bitfield.schmitt =(pin_list->attribute & PIO_TRIGGER_DIS)? 1:0;

			switch (pin_list->attribute & PIO_DRVSTR_Msk) {
			case PIO_DRVSTR_HI:
				cfg.bitfield.drvstr = PIO_CFGR_DRVSTR_HI >> PIO_CFGR_DRVSTR_Pos;
				break;
			case PIO_DRVSTR_ME:
				cfg.bitfield.drvstr = PIO_CFGR_DRVSTR_ME >> PIO_CFGR_DRVSTR_Pos;
				break;
			case PIO_DRVSTR_LO:
			default:
				cfg.bitfield.drvstr = PIO_CFGR_DRVSTR_LO >> PIO_CFGR_DRVSTR_Pos;
				break;
			}

			switch (pin_list->attribute & PIO_EVTSEL_Msk) {
			case PIO_IT_HIGH_LEVEL:
				cfg.bitfield.evtsel = PIO_CFGR_EVTSEL_HIGH >> PIO_CFGR_EVTSEL_Pos;
				break;
			case PIO_IT_LOW_LEVEL:
				cfg.bitfield.evtsel = PIO_CFGR_EVTSEL_LOW >> PIO_CFGR_EVTSEL_Pos;
				break;
			case PIO_IT_BOTH_EDGE:
				cfg.bitfield.evtsel = PIO_CFGR_EVTSEL_BOTH >> PIO_CFGR_EVTSEL_Pos;
				break;
			case PIO_IT_RISE_EDGE:
				cfg.bitfield.evtsel = PIO_CFGR_EVTSEL_RISING >> PIO_CFGR_EVTSEL_Pos;
				break;
			case PIO_IT_FALL_EDGE:
			default:
				cfg.bitfield.evtsel = PIO_CFGR_EVTSEL_FALLING >> PIO_CFGR_EVTSEL_Pos;
				break;
			}
		}

		switch (pin_list->type){

		case PIO_PERIPH_A:
			cfg.bitfield.func = PIO_CFGR_FUNC_PERIPH_A >> PIO_CFGR_FUNC_Pos;
			break;
		case PIO_PERIPH_B:
			cfg.bitfield.func = PIO_CFGR_FUNC_PERIPH_B >> PIO_CFGR_FUNC_Pos;
			break;
		case PIO_PERIPH_C:
			cfg.bitfield.func = PIO_CFGR_FUNC_PERIPH_C >> PIO_CFGR_FUNC_Pos;
			break;
		case PIO_PERIPH_D:
			cfg.bitfield.func = PIO_CFGR_FUNC_PERIPH_D >> PIO_CFGR_FUNC_Pos;
			break;
		case PIO_PERIPH_E:
			cfg.bitfield.func = PIO_CFGR_FUNC_PERIPH_E >> PIO_CFGR_FUNC_Pos;
			break;
		case PIO_PERIPH_F:
			cfg.bitfield.func = PIO_CFGR_FUNC_PERIPH_F >> PIO_CFGR_FUNC_Pos;
			break;
		case PIO_GENERIC:
		case PIO_INPUT:
			cfg.bitfield.dir = 0;
			break;

		case PIO_OUTPUT_0:
			cfg.bitfield.dir = 1;
			pio_clear(pin_list);
			break;

		case PIO_OUTPUT_1:
			cfg.bitfield.dir = 1;
			pio_set(pin_list);
			break;

		default:
		case PIO_PERIPH_G:
			return 0;
		}

		pioiog->PIO_MSKR = pin_list->mask;
		pioiog->PIO_CFGR = cfg.uint32_value;
		pmc_enable_peripheral(periph_id);

		++pin_list;
	}
	return 1;
}

/**
 * \brief Sets a high output level on all the PIOs defined in the
 * given Pin instance. This has no immediate effects on PIOs that are
 * not output, but the PIO controller will memorize the value they are
 * changed to outputs.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */
void pio_set(const struct _pin *pin)
{
	assert(pin->group < PIO_GROUP_LENGTH);
	uint32_t periph_id = _pio_group_to_id(pin->group);
	PioIo_group* pioiog = (PioIo_group*) _pio_retrive_group(pin, periph_id);
	pioiog->PIO_SODR = pin->mask;
}

/**
 * \brief Sets a low output level on all the PIOs defined in the given
 * Pin instance. This has no immediate effects on PIOs that are not
 * output, but the PIO controller will memorize the value they are
 * changed to outputs.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */
void pio_clear(const struct _pin *pin)
{
	assert(pin->group < PIO_GROUP_LENGTH);
	uint32_t periph_id = _pio_group_to_id(pin->group);
	PioIo_group* pioiog = (PioIo_group*) _pio_retrive_group(pin, periph_id);
	pioiog->PIO_CODR = pin->mask;
}

/**
 * \brief Returns 1 if one or more PIO of the given Pin instance currently have
 * a high level; otherwise returns 0. This method returns the actual value that
 * is being read on the pin. To return the supposed output value of a pin, use
 * pio_get_output_date_status() instead.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 *
 * \return 1 if the Pin instance contains at least one PIO that currently has
 * a high level; otherwise 0.
 */
uint8_t pio_get(const struct _pin *pin)
{
	assert(pin->group < PIO_GROUP_LENGTH);
	uint32_t reg ;
	uint32_t periph_id = _pio_group_to_id(pin->group);
	PioIo_group* pioiog = (PioIo_group*) _pio_retrive_group(pin, periph_id);

	if ((pin->type == PIO_OUTPUT_0) || (pin->type == PIO_OUTPUT_1)) {
		reg = pioiog->PIO_ODSR ;
	}
	else {
		reg = pioiog->PIO_PDSR ;
	}
	if ( (reg & pin->mask) == 0 ) {
		return 0 ;
	}
	else {
		return 1 ;
	}
}

/**
 * \brief Returns 1 if one or more PIO of the given Pin are configured
 * to output a high level (even if they are not output). To get the
 * actual value of the pin, use pio_get() instead.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 *
 * \return 1 if the Pin instance contains at least one PIO that is configured
 * to output a high level; otherwise 0.
 */
uint8_t pio_get_output_data_status(const struct _pin *pin)
{
	assert(pin->group < PIO_GROUP_LENGTH);
	uint32_t periph_id = _pio_group_to_id(pin->group);
	PioIo_group* pioiog = (PioIo_group*) _pio_retrive_group(pin, periph_id);

	if ((pioiog->PIO_ODSR & pin->mask) == 0) {
		return 0;
	}
	else {
		return 1;
	}
}

/**
 * \brief Configures Glitch or Debouncing filter for input.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 * \param cuttoff  Cutt off frequency for debounce filter.
 */
void pio_set_debounce_filter(const struct _pin *pin, uint32_t cuttoff)
{
	assert(pin->group < PIO_GROUP_LENGTH);
	if (cuttoff == 0) {
	   PIOA->S_PIO_SCDR = 0;
	}
	else {
		/* the lowest 14 bits work */
		PIOA->S_PIO_SCDR =
			((pmc_get_slow_clock()/(2*(cuttoff))) - 1) & 0x3FFF;
	}
}

/**
 * \brief Enable write protect.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */
void pio_enable_write_protect(const struct _pin *pin)
{
	assert(pin->group < PIO_GROUP_LENGTH);
	PIOA->PIO_WPMR = (PIO_WPMR_WPKEY_VALID | PIO_WPMR_WPEN_EN  );
}

/**
 * \brief Disable write protect.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */
void pio_disable_write_protect(const struct _pin *pin)
{
	assert(pin->group < PIO_GROUP_LENGTH);
	PIOA->PIO_WPMR = (PIO_WPMR_WPKEY_VALID | PIO_WPMR_WPEN_DIS );
}

/**
 * \brief Get write protect violation information.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */
uint32_t pio_get_write_protect_violation_info(const struct _pin * pin)
{
	assert(pin->group < PIO_GROUP_LENGTH);
	return PIOA->PIO_WPSR;
}

void pio_add_handler_to_group(uint32_t group, uint32_t mask,
			      pio_handler_t handler, void* user_arg)
{
	trace_debug("Enter in pio_add_handler_to_group()\n\r");
	assert(group <
	       (sizeof(_generic_handlers)/sizeof(_generic_handlers[0])));
	_handler_push(handler, mask, user_arg);
	uint32_t id = _pio_group_to_id(group);
	aic_set_source_vector(id,
			(aic_handler_t)_generic_handlers[group]);
	aic_enable(id);
}

void pio_reset_all_it(void)
{
	int i = 0;
	for (i = 0; i < PIO_GROUP_LENGTH; ++i) {
		PIOA->PIO_IO_GROUP[i].PIO_ISR;
		PIOA->PIO_IO_GROUP[i].PIO_IDR = ~0UL;
	}
}

/**
 * Configures a PIO or a group of PIO to generate an interrupt on status
 * change. The provided interrupt handler will be called with the triggering
 * pin as its parameter (enabling different pin instances to share the same
 * handler).
 * \param pin  Pointer to a _pin instance.
 */
void pio_configure_it(const struct _pin *pin)
{
	trace_debug("Enter in pio_configure_it()\n\r");
	assert(pin != NULL);
}

/**
 * Enables the given interrupt source if it has been configured. The status
 * register of the corresponding PIO controller is cleared prior to enabling
 * the interrupt.
 * \param pin  Interrupt source to enable.
 */
void pio_enable_it(const struct _pin *pin)
{
	trace_debug("pio_enable_it() \n\r");
	assert(pin != NULL);
	uint32_t periph_id = _pio_group_to_id(pin->group);
	PioIo_group* pioiog = (PioIo_group*) _pio_retrive_group(pin, periph_id);

	pioiog->PIO_ISR;
	/* Configure interrupt enable register */
	pioiog->PIO_IER = pin->mask;	/* enable interrupt register */
}

/**
 * Disables a given interrupt source, with no added side effects.
 *
 * \param pin  Interrupt source to disable.
 */
void pio_disable_it(const struct _pin *pin)
{
	trace_debug("pio_enable_it()\n\r");
	assert(pin != NULL);
	uint32_t periph_id = _pio_group_to_id(pin->group);
	PioIo_group* pioiog = (PioIo_group*) _pio_retrive_group(pin, periph_id);
	pioiog->PIO_IDR = pin->mask;
}
