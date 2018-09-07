/**
 * \file
 *
 * \brief SAM D20 Serial Peripheral Interface Driver
 *
 * Copyright (C) 2012-2013 Atmel Corporation. All rights reserved.
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
#include "sercom.h"

#define SHIFT 32

#if !defined(__DOXYGEN__)
/**
 * \internal Configuration structure to save current gclk status.
 */
struct _sercom_conf {
	/* Status of gclk generator initialization. */
	bool generator_is_set;
	/* Sercom gclk generator used. */
	enum gclk_generator generator_source;
};

static struct _sercom_conf _sercom_config;

/**
 * \internal Calculate synchronous baudrate value (SPI/UART)
 */
enum status_code _sercom_get_sync_baud_val(
		const uint32_t baudrate,
		const uint32_t external_clock,
		uint16_t *const baudvalue)
{
	/* Baud value variable */
	uint16_t baud_calculated = 0;

	/* Check if baudrate is outside of valid range. */
	if (baudrate > (external_clock / 2)) {
		/* Return with error code */
		return STATUS_ERR_BAUDRATE_UNAVAILABLE;
	}

	/* Calculate BAUD value from clock frequency and baudrate */
	baud_calculated = (external_clock / (2 * baudrate)) - 1;

	/* Check if BAUD value is more than 255, which is maximum
	 * for synchronous mode */
	if (baud_calculated > 0xFF) {
		/* Return with an error code */
		return STATUS_ERR_BAUDRATE_UNAVAILABLE;
	} else {
		*baudvalue = baud_calculated;
		return STATUS_OK;
	}
}

/**
 * \internal Calculate asynchronous baudrate value (UART)
*/
enum status_code _sercom_get_async_baud_val(
		const uint32_t baudrate,
		const uint32_t peripheral_clock,
		uint16_t *const baudval)
{
	/* Temporary variables  */
	uint64_t ratio = 0;
	uint64_t scale = 0;
	uint64_t baud_calculated = 0;

	/* Check if the baudrate is outside of valid range */
	if ((baudrate * 16) >= peripheral_clock) {
		/* Return with error code */
		return STATUS_ERR_BAUDRATE_UNAVAILABLE;
	}

	/* Calculate the BAUD value */
	ratio = ((16 * (uint64_t)baudrate) << SHIFT) / peripheral_clock;
	scale = ((uint64_t)1 << SHIFT) - ratio;
	baud_calculated = (65536 * scale) >> SHIFT;

	*baudval = baud_calculated;

	return STATUS_OK;
}
#endif

/**
 * \brief Set GCLK channel to generator.
 *
 * This will set the appropriate GCLK channel to the requested GCLK generator.
 * This will set the generator for all SERCOM instances, and the user will thus
 * only be able to set the same generator that has previously been set, if any.
 *
 * After the generator has been set the first time, the generator can be changed
 * using the \c force_change flag.
 *
 * \param[in]  generator_source The generator to use for SERCOM.
 * \param[in]  force_change     Force change the generator.
 *
 * \return Status code indicating the GCLK generator change operation.
 * \retval STATUS_OK                       If the generator update request was
 *                                         successful.
 * \retval STATUS_ERR_ALREADY_INITIALIZED  If a generator was already configured
 *                                         and the new configuration was not
 *                                         forced.
 */
enum status_code sercom_set_gclk_generator(
		const enum gclk_generator generator_source,
		const bool force_change)
{
	/* Check if valid option. */
	if (!_sercom_config.generator_is_set || force_change) {
		/* Create and fill a GCLK configuration structure for the new config. */
		struct system_gclk_chan_config gclk_chan_conf;
		system_gclk_chan_get_config_defaults(&gclk_chan_conf);
		gclk_chan_conf.source_generator = generator_source;
		system_gclk_chan_set_config(SERCOM_GCLK_ID, &gclk_chan_conf);
		system_gclk_chan_enable(SERCOM_GCLK_ID);

		/* Save config. */
		_sercom_config.generator_source = generator_source;
		_sercom_config.generator_is_set = true;

		return STATUS_OK;
	} else if (generator_source == _sercom_config.generator_source) {
		/* Return status OK if same config. */
		return STATUS_OK;
	}

	/* Return invalid config to already initialized GCLK. */
	return STATUS_ERR_ALREADY_INITIALIZED;
}

/** \internal
 * Creates a switch statement case entry to convert a SERCOM instance and pad
 * index to the default SERCOM pad MUX setting.
 */
#define _SERCOM_PAD_DEFAULTS_CASE(n, pad) \
		case (uintptr_t)SERCOM##n: \
			switch (pad) { \
				case 0: \
					return SERCOM##n##_PAD0_DEFAULT; \
				case 1: \
					return SERCOM##n##_PAD1_DEFAULT; \
				case 2: \
					return SERCOM##n##_PAD2_DEFAULT; \
				case 3: \
					return SERCOM##n##_PAD3_DEFAULT; \
			} \
			break;

/**
 * \internal Gets the default PAD pinout for a given SERCOM.
 *
 * Returns the PINMUX settings for the given SERCOM and pad. This is used
 * for default configuration of pins.
 *
 * \param[in]  sercom_module   Pointer to the SERCOM module
 * \param[in]  pad             PAD to get default pinout for
 *
 * \returns The default PINMUX for the given SERCOM instance and PAD
 *
 */
uint32_t _sercom_get_default_pad(
		Sercom *const sercom_module,
		const uint8_t pad)
{
	switch ((uintptr_t)sercom_module) {
		/* Auto-generate a lookup table for the default SERCOM pad defaults */
		MREPEAT(SERCOM_INST_NUM, _SERCOM_PAD_DEFAULTS_CASE, pad)
	}

	Assert(false);
	return 0;
}
