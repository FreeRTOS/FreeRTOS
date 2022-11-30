/**
 * \file
 *
 * \brief SAM D20 SERCOM USART Driver
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
#include "usart.h"
#include <pinmux.h>
#if USART_CALLBACK_MODE == true
#  include "usart_interrupt.h"
#endif

/**
 * \internal Checks a USART config against current set config
 *
 * This function will check that the config does not alter the
 * configuration of the module. If the new config changes any
 * setting, the initialization will be discarded.
 *
 * \param[in]  module  Pointer to the software instance struct
 * \param[in]  config  Pointer to the configuration struct
 *
 * \return The status of the configuration
 * \retval STATUS_ERR_INVALID_ARG       If invalid argument(s) were provided.
 * \retval STATUS_ERR_DENIED            If configuration was different from previous
 * \retval STATUS_OK                    If the configuration was written
 */
static enum status_code _usart_check_config(
		struct usart_module *const module,
		const struct usart_config *const config)
{
		/* Sanity check arguments */
	Assert(module);
	Assert(module->hw);

	SercomUsart *const usart_hw = &(module->hw->USART);
	Sercom *const hw = (module->hw);

	uint32_t pad0 = config->pinmux_pad0;
	uint32_t pad1 = config->pinmux_pad1;
	uint32_t pad2 = config->pinmux_pad2;
	uint32_t pad3 = config->pinmux_pad3;

	/* SERCOM PAD0 */
	if (pad0 == PINMUX_DEFAULT) {
		pad0 = _sercom_get_default_pad(hw, 0);
	}
	if ((pad0 != PINMUX_UNUSED) && ((pad0 & 0xFFFF)!=
			system_pinmux_pin_get_mux_position(pad0 >> 16))) {
		return STATUS_ERR_DENIED;
	}

	/* SERCOM PAD1 */
	if (pad1 == PINMUX_DEFAULT) {
		pad1 = _sercom_get_default_pad(hw, 1);
	}
	if ((pad1 != PINMUX_UNUSED) && ((pad1 & 0xFFFF) !=
			system_pinmux_pin_get_mux_position(pad1 >> 16))) {
		return STATUS_ERR_DENIED;
	}

	/* SERCOM PAD2 */
	if (pad2 == PINMUX_DEFAULT) {
		pad2 = _sercom_get_default_pad(hw, 2);
	}
	if ((pad2 != PINMUX_UNUSED) && ((pad2 & 0xFFFF) !=
			system_pinmux_pin_get_mux_position(pad2 >> 16))) {
		return STATUS_ERR_DENIED;
	}

	/* SERCOM PAD3 */
	if (pad3 == PINMUX_DEFAULT) {
		pad3 = _sercom_get_default_pad(hw, 3);
	}
	if ((pad3 != PINMUX_UNUSED) && ((pad3 & 0xFFFF) !=
			system_pinmux_pin_get_mux_position(pad3 >> 16))) {
		return STATUS_ERR_DENIED;
	}

	/* Find baud value and compare it */
	uint16_t baud  = 0;
	enum status_code status_code = STATUS_OK;

	switch (config->transfer_mode)
	{
	case USART_TRANSFER_SYNCHRONOUSLY:
		if (!config->use_external_clock) {
			status_code = _sercom_get_sync_baud_val(config->baudrate,
					system_gclk_chan_get_hz(SERCOM_GCLK_ID), &baud);
		}

		break;

	case USART_TRANSFER_ASYNCHRONOUSLY:
		if (config->use_external_clock) {
			status_code =
					_sercom_get_async_baud_val(config->baudrate,
						config->ext_clock_freq, &baud);
		} else {
			status_code =
					_sercom_get_async_baud_val(config->baudrate,
						system_gclk_chan_get_hz(SERCOM_GCLK_ID), &baud);
		}

		break;
	}

	if (status_code != STATUS_OK) {
		/* Baud rate calculation error, return status code */
		return STATUS_ERR_DENIED;
	}

	if (usart_hw->BAUD.reg != baud) {
		return STATUS_ERR_DENIED;
	}

	uint32_t ctrla = 0;
	uint32_t ctrlb = 0;

	/* Check sample mode, data order, internal muxing, and clock polarity */
	ctrla = (uint32_t)config->data_order |
		(uint32_t)config->mux_setting |
		(uint32_t)config->transfer_mode |
		SERCOM_USART_CTRLA_MODE(0) |
		(config->clock_polarity_inverted << SERCOM_USART_CTRLA_CPOL_Pos);

	/* set enable bit */
	ctrla |= (SERCOM_USART_CTRLA_ENABLE);

	if (config->use_external_clock == false) {
		ctrla |= SERCOM_USART_CTRLA_MODE_USART_INT_CLK;
	}
	else {
		ctrla |= SERCOM_USART_CTRLA_MODE_USART_EXT_CLK;
	}

	/* Check stopbits and character size */
	ctrlb = (uint32_t)config->stopbits | (uint32_t)config->character_size |
			(config->receiver_enable << SERCOM_USART_CTRLB_RXEN_Pos) |
			(config->transmitter_enable << SERCOM_USART_CTRLB_TXEN_Pos);

	/* Check parity mode bits */
	if (config->parity != USART_PARITY_NONE) {
		ctrla |= SERCOM_USART_CTRLA_FORM(1);
		ctrlb |= config->parity;
	} else {
		ctrla |= SERCOM_USART_CTRLA_FORM(0);
	}

	if (usart_hw->CTRLA.reg == ctrla && usart_hw->CTRLB.reg == ctrlb) {
		module->character_size = config->character_size;
		return STATUS_OK;
	} else {
		module->hw = NULL;
		return STATUS_ERR_DENIED;
	}
}

/**
 * \internal
 * Set Configuration of the USART module
 */
static enum status_code _usart_set_config(
		struct usart_module *const module,
		const struct usart_config *const config)
{
	/* Sanity check arguments */
	Assert(module);
	Assert(module->hw);

	/* Get a pointer to the hardware module instance */
	SercomUsart *const usart_hw = &(module->hw->USART);

	/* Index for generic clock */
	uint32_t sercom_index = _sercom_get_sercom_inst_index(module->hw);
	uint32_t gclk_index   = sercom_index + SERCOM0_GCLK_ID_CORE;

	/* Cache new register values to minimize the number of register writes */
	uint32_t ctrla = 0;
	uint32_t ctrlb = 0;
	uint16_t baud  = 0;

	/* Set data order, internal muxing, and clock polarity */
	ctrla = (uint32_t)config->data_order |
		(uint32_t)config->mux_setting |
		(config->clock_polarity_inverted << SERCOM_USART_CTRLA_CPOL_Pos);

	enum status_code status_code = STATUS_OK;

	/* Get baud value from mode and clock */
	switch (config->transfer_mode)
	{
		case USART_TRANSFER_SYNCHRONOUSLY:
			if (!config->use_external_clock) {
				status_code = _sercom_get_sync_baud_val(config->baudrate,
						system_gclk_chan_get_hz(gclk_index), &baud);
			}

			break;

		case USART_TRANSFER_ASYNCHRONOUSLY:
			if (config->use_external_clock) {
				status_code =
						_sercom_get_async_baud_val(config->baudrate,
							config->ext_clock_freq, &baud);
			} else {
				status_code =
						_sercom_get_async_baud_val(config->baudrate,
							system_gclk_chan_get_hz(gclk_index), &baud);
			}

			break;
	}

	/* Check if calculating the baud rate failed */
	if (status_code != STATUS_OK) {
		/* Abort */
		return status_code;
	}

	/* Wait until synchronization is complete */
	_usart_wait_for_sync(module);

	/*Set baud val */
	usart_hw->BAUD.reg = baud;

	/* Set sample mode */
	ctrla |= config->transfer_mode;

	if (config->use_external_clock == false) {
		ctrla |= SERCOM_USART_CTRLA_MODE_USART_INT_CLK;
	}
	else {
		ctrla |= SERCOM_USART_CTRLA_MODE_USART_EXT_CLK;
	}

	/* Set stopbits, character size and enable transceivers */
	ctrlb = (uint32_t)config->stopbits | (uint32_t)config->character_size |
			(config->receiver_enable << SERCOM_USART_CTRLB_RXEN_Pos) |
			(config->transmitter_enable << SERCOM_USART_CTRLB_TXEN_Pos);

	/* Set parity mode */
	if (config->parity != USART_PARITY_NONE) {
		ctrla |= SERCOM_USART_CTRLA_FORM(1);
		ctrlb |= config->parity;
	} else {
		ctrla |= SERCOM_USART_CTRLA_FORM(0);
	}

	/* Set run mode during device sleep */
	if (config->run_in_standby) {
		/* Enable in sleep mode */
		ctrla |= SERCOM_USART_CTRLA_RUNSTDBY;
	}

	/* Wait until synchronization is complete */
	_usart_wait_for_sync(module);

	/* Write configuration to CTRLB */
	usart_hw->CTRLB.reg = ctrlb;

	/* Wait until synchronization is complete */
	_usart_wait_for_sync(module);

	/* Write configuration to CTRLA */
	usart_hw->CTRLA.reg = ctrla;

	return STATUS_OK;
}

/**
 * \brief Initializes the device
 *
 * Initializes the USART device based on the setting specified in the
 * configuration struct.
 *
 * \param[out] module  Pointer to USART device
 * \param[in]  hw      Pointer to USART hardware instance
 * \param[in]  config  Pointer to configuration struct
 *
 * \return Status of the initialization
 *
 * \retval STATUS_OK                       The initialization was successful
 * \retval STATUS_BUSY                     The USART module is busy
 *                                         resetting
 * \retval STATUS_ERR_DENIED               The USART have not been disabled in
 *                                         advance of initialization
 * \retval STATUS_ERR_INVALID_ARG          The configuration struct contains
 *                                         invalid configuration
 * \retval STATUS_ERR_ALREADY_INITIALIZED  The SERCOM instance has already been
 *                                         initialized with different clock
 *                                         configuration
 * \retval STATUS_ERR_BAUD_UNAVAILABLE     The BAUD rate given by the
 *                                         configuration
 *                                         struct cannot be reached with
 *                                         the current clock configuration
 */
enum status_code usart_init(
		struct usart_module *const module,
		Sercom *const hw,
		const struct usart_config *const config)
{
	/* Sanity check arguments */
	Assert(module);
	Assert(hw);
	Assert(config);

	enum status_code status_code = STATUS_OK;

	/* Assign module pointer to software instance struct */
	module->hw = hw;

	/* Get a pointer to the hardware module instance */
	SercomUsart *const usart_hw = &(module->hw->USART);

	uint32_t sercom_index = _sercom_get_sercom_inst_index(module->hw);
	uint32_t pm_index     = sercom_index + PM_APBCMASK_SERCOM0_Pos;
	uint32_t gclk_index   = sercom_index + SERCOM0_GCLK_ID_CORE;

	if (usart_hw->CTRLA.reg & SERCOM_USART_CTRLA_SWRST) {
		/* The module is busy resetting itself */
		return STATUS_BUSY;
	}

	if (usart_hw->CTRLA.reg & SERCOM_USART_CTRLA_ENABLE) {
		/* Check if the new setting are the same as the old */
		return _usart_check_config(module, config);
	}

	/* Turn on module in PM */
	system_apb_clock_set_mask(SYSTEM_CLOCK_APB_APBC, 1 << pm_index);

	/* Set up the GCLK for the module */
	struct system_gclk_chan_config gclk_chan_conf;
	system_gclk_chan_get_config_defaults(&gclk_chan_conf);
	gclk_chan_conf.source_generator = config->generator_source;
	system_gclk_chan_set_config(gclk_index, &gclk_chan_conf);
	system_gclk_chan_enable(gclk_index);
	sercom_set_gclk_generator(config->generator_source, false);

	/* Set character size */
	module->character_size = config->character_size;

	/* Set transmitter and receiver status */
	module->receiver_enabled = config->receiver_enable;
	module->transmitter_enabled = config->transmitter_enable;

	/* Configure Pins */
	struct system_pinmux_config pin_conf;
	system_pinmux_get_config_defaults(&pin_conf);
	pin_conf.direction = SYSTEM_PINMUX_PIN_DIR_INPUT;

	/* Set configuration according to the config struct */
	status_code = _usart_set_config(module, config);
	if(status_code != STATUS_OK) {
		return status_code;
	}

	uint32_t pad0 = config->pinmux_pad0;
	uint32_t pad1 = config->pinmux_pad1;
	uint32_t pad2 = config->pinmux_pad2;
	uint32_t pad3 = config->pinmux_pad3;

	/* SERCOM PAD0 */
	if (pad0 == PINMUX_DEFAULT) {
		pad0 = _sercom_get_default_pad(hw, 0);
	}
	if (pad0 != PINMUX_UNUSED) {
		pin_conf.mux_position = pad0 & 0xFFFF;
		system_pinmux_pin_set_config(pad0 >> 16, &pin_conf);
	}

	/* SERCOM PAD1 */
	if (pad1 == PINMUX_DEFAULT) {
		pad1 = _sercom_get_default_pad(hw, 1);
	}
	if (pad1 != PINMUX_UNUSED) {
		pin_conf.mux_position = pad1 & 0xFFFF;
		system_pinmux_pin_set_config(pad1 >> 16, &pin_conf);
	}

	/* SERCOM PAD2 */
	if (pad2 == PINMUX_DEFAULT) {
		pad2 = _sercom_get_default_pad(hw, 2);
	}
	if (pad2 != PINMUX_UNUSED) {
		pin_conf.mux_position = pad2 & 0xFFFF;
		system_pinmux_pin_set_config(pad2 >> 16, &pin_conf);
	}

	/* SERCOM PAD3 */
	if (pad3 == PINMUX_DEFAULT) {
		pad3 = _sercom_get_default_pad(hw, 3);
	}
	if (pad3 != PINMUX_UNUSED) {
		pin_conf.mux_position = pad3 & 0xFFFF;
		system_pinmux_pin_set_config(pad3 >> 16, &pin_conf);
	}
#if USART_CALLBACK_MODE == true
	/* Initialize parameters */
	for (uint32_t i = 0; i < USART_CALLBACK_N; i++) {
		module->callback[i]            = NULL;
	}

	module->tx_buffer_ptr              = NULL;
	module->rx_buffer_ptr              = NULL;
	module->remaining_tx_buffer_length = 0x0000;
	module->remaining_rx_buffer_length = 0x0000;
	module->callback_reg_mask          = 0x00;
	module->callback_enable_mask       = 0x00;
	module->rx_status                  = STATUS_OK;
	module->tx_status                  = STATUS_OK;

	/* Set interrupt handler and register USART software module struct in
	 * look-up table */
	uint8_t instance_index = _sercom_get_sercom_inst_index(module->hw);
	_sercom_set_handler(instance_index, _usart_interrupt_handler);
	_sercom_instances[instance_index] = module;
#endif
	return status_code;
}

/**
 * \brief Transmit a character via the USART
 *
 * This blocking function will transmit a single character via the
 * USART.
 *
 * \param[in]  module   Pointer to the software instance struct
 * \param[in]  tx_data  Data to transfer
 *
 * \return Status of the operation
 * \retval STATUS_OK         If the operation was completed
 * \retval STATUS_BUSY       If the operation was not completed, due to the USART
 *                           module being busy.
 * \retval STATUS_ERR_DENIED If the transmitter is not enabled
 */
enum status_code usart_write_wait(
		struct usart_module *const module,
		const uint16_t tx_data)
{
	/* Sanity check arguments */
	Assert(module);
	Assert(module->hw);

	/* Get a pointer to the hardware module instance */
	SercomUsart *const usart_hw = &(module->hw->USART);

	/* Check that the transmitter is enabled */
	if (!(module->transmitter_enabled)) {
		return STATUS_ERR_DENIED;
	}

#if USART_CALLBACK_MODE == true
	/* Check if the USART is busy doing asynchronous operation. */
	if (module->remaining_tx_buffer_length > 0) {
		return STATUS_BUSY;
	}

#else
	/* Check if USART is ready for new data */
	if (!(usart_hw->INTFLAG.reg & SERCOM_USART_INTFLAG_DRE)) {
		/* Return error code */
		return STATUS_BUSY;
	}
#endif

	/* Wait until synchronization is complete */
	_usart_wait_for_sync(module);

	/* Write data to USART module */
	usart_hw->DATA.reg = tx_data;

	while (!(usart_hw->INTFLAG.reg & SERCOM_USART_INTFLAG_TXC)) {
		/* Wait until data is sent */
	}

	return STATUS_OK;
}

/**
 * \brief Receive a character via the USART
 *
 * This blocking function will receive a character via the USART.
 *
 * \param[in]   module   Pointer to the software instance struct
 * \param[out]  rx_data  Pointer to received data
 *
 * \return Status of the operation
 * \retval STATUS_OK                If the operation was completed
 * \retval STATUS_BUSY              If the operation was not completed,
 *                                  due to the USART module being busy
 * \retval STATUS_ERR_BAD_FORMAT    If the operation was not completed,
 *                                  due to configuration mismatch between USART
 *                                  and the sender
 * \retval STATUS_ERR_BAD_OVERFLOW  If the operation was not completed,
 *                                  due to the baud rate being too low or the
 *                                  system frequency being too high
 * \retval STATUS_ERR_BAD_DATA      If the operation was not completed, due to
 *                                  data being corrupted
 * \retval STATUS_ERR_DENIED        If the receiver is not enabled
 */
enum status_code usart_read_wait(
		struct usart_module *const module,
		uint16_t *const rx_data)
{
	/* Sanity check arguments */
	Assert(module);
	Assert(module->hw);

	/* Error variable */
	uint8_t error_code;

	/* Get a pointer to the hardware module instance */
	SercomUsart *const usart_hw = &(module->hw->USART);

	/* Check that the receiver is enabled */
	if (!(module->receiver_enabled)) {
		return STATUS_ERR_DENIED;
	}

#if USART_CALLBACK_MODE == true
	/* Check if the USART is busy doing asynchronous operation. */
	if (module->remaining_rx_buffer_length > 0) {
		return STATUS_BUSY;
	}

#else
	/* Check if USART has new data */
	if (!(usart_hw->INTFLAG.reg & SERCOM_USART_INTFLAG_RXC)) {
		/* Return error code */
		return STATUS_BUSY;
	}
#endif

	/* Wait until synchronization is complete */
	_usart_wait_for_sync(module);

	/* Read out the status code and mask away all but the 3 LSBs*/
	error_code = (uint8_t)(usart_hw->STATUS.reg & SERCOM_USART_STATUS_MASK);

	/* Check if an error has occurred during the receiving */
	if (error_code) {
		/* Check which error occurred */
		if (error_code & SERCOM_USART_STATUS_FERR) {
			/* Clear flag by writing a 1 to it and
			 * return with an error code */
			usart_hw->STATUS.reg = SERCOM_USART_STATUS_FERR;

			return STATUS_ERR_BAD_FORMAT;
		} else if (error_code & SERCOM_USART_STATUS_BUFOVF) {
			/* Clear flag by writing a 1 to it and
			 * return with an error code */
			usart_hw->STATUS.reg = SERCOM_USART_STATUS_BUFOVF;

			return STATUS_ERR_OVERFLOW;
		} else if (error_code & SERCOM_USART_STATUS_PERR) {
			/* Clear flag by writing a 1 to it and
			 * return with an error code */
			usart_hw->STATUS.reg = SERCOM_USART_STATUS_PERR;

			return STATUS_ERR_BAD_DATA;
		}
	}

	/* Read data from USART module */
	*rx_data = usart_hw->DATA.reg;

	return STATUS_OK;
}

/**
 * \brief Transmit a buffer of characters via the USART
 *
 * This blocking function will transmit a block of \c length characters
 * via the USART
 *
 * \note Using this function in combination with the interrupt (\c _job) functions is
 *       not recommended as it has no functionality to check if there is an
 *       ongoing interrupt driven operation running or not.
 *
 * \param[in]  module   Pointer to USART software instance struct
 * \param[in]  tx_data  Pointer to data to transmit
 * \param[in]  length   Number of characters to transmit
 *
 * \return Status of the operation
 * \retval STATUS_OK              If operation was completed
 * \retval STATUS_ERR_INVALID_ARG If operation was not completed, due to invalid
 *                                arguments
 * \retval STATUS_ERR_TIMEOUT     If operation was not completed, due to USART
 *                                module timing out
 * \retval STATUS_ERR_DENIED      If the transmitter is not enabled
 */
enum status_code usart_write_buffer_wait(
		struct usart_module *const module,
		const uint8_t *tx_data,
		uint16_t length)
{
	/* Sanity check arguments */
	Assert(module);
	Assert(module->hw);

	/* Check if the buffer length is valid */
	if (length == 0) {
		return STATUS_ERR_INVALID_ARG;
	}

	/* Check that the transmitter is enabled */
	if (!(module->transmitter_enabled)) {
		return STATUS_ERR_DENIED;
	}

	/* Get a pointer to the hardware module instance */
	SercomUsart *const usart_hw = &(module->hw->USART);

	/* Wait until synchronization is complete */
	_usart_wait_for_sync(module);

	uint16_t tx_pos = 0;

	/* Blocks while buffer is being transferred */
	while (length--) {
		/* Wait for the USART to be ready for new data and abort
		* operation if it doesn't get ready within the timeout*/
		for (uint32_t i = 0; i <= USART_TIMEOUT; i++) {
			if (usart_hw->INTFLAG.reg & SERCOM_USART_INTFLAG_DRE) {
				break;
			} else if (i == USART_TIMEOUT) {
				return STATUS_ERR_TIMEOUT;
			}
		}

		/* Data to send is at least 8 bits long */
		uint16_t data_to_send = tx_data[tx_pos++];

		/* Check if the character size exceeds 8 bit */
		if (module->character_size == USART_CHARACTER_SIZE_9BIT) {
			data_to_send |= (tx_data[tx_pos++] << 8);
		}

		/* Send the data through the USART module */
		usart_write_wait(module, data_to_send);
	}

	/* Wait until Transmit is complete or timeout */
	for (uint32_t i = 0; i <= USART_TIMEOUT; i++) {
		if (usart_hw->INTFLAG.reg & SERCOM_USART_INTFLAG_TXC) {
			break;
		} else if (i == USART_TIMEOUT) {
			return STATUS_ERR_TIMEOUT;
		}
	}

	return STATUS_OK;
}

/**
 * \brief Receive a buffer of \c length characters via the USART
 *
 * This blocking function will receive a block of \c length characters
 * via the USART.
 *
 * \note Using this function in combination with the interrupt (\c *_job)
 *       functions is not recommended as it has no functionality to check if
 *       there is an ongoing interrupt driven operation running or not.
 *
 * \param[in]  module   Pointer to USART software instance struct
 * \param[out] rx_data  Pointer to receive buffer
 * \param[in]  length   Number of characters to receive
 *
 * \return Status of the operation.
 * \retval STATUS_OK                If operation was completed
 * \retval STATUS_ERR_INVALID_ARG   If operation was not completed, due to an
 *                                  invalid argument being supplied
 * \retval STATUS_ERR_TIMEOUT       If operation was not completed, due
 *                                  to USART module timing out
 * \retval STATUS_ERR_BAD_FORMAT    If the operation was not completed,
 *                                  due to a configuration mismatch
 *                                  between USART and the sender
 * \retval STATUS_ERR_BAD_OVERFLOW  If the operation was not completed,
 *                                  due to the baud rate being too low or the
 *                                  system frequency being too high
 * \retval STATUS_ERR_BAD_DATA      If the operation was not completed, due
 *                                  to data being corrupted
 * \retval STATUS_ERR_DENIED        If the receiver is not enabled
 */
enum status_code usart_read_buffer_wait(
		struct usart_module *const module,
		uint8_t *rx_data,
		uint16_t length)
{
	/* Sanity check arguments */
	Assert(module);
	Assert(module->hw);

	/* Check if the buffer length is valid */
	if (length == 0) {
		return STATUS_ERR_INVALID_ARG;
	}

	/* Check that the receiver is enabled */
	if (!(module->receiver_enabled)) {
		return STATUS_ERR_DENIED;
	}

	/* Get a pointer to the hardware module instance */
	SercomUsart *const usart_hw = &(module->hw->USART);

	uint16_t rx_pos = 0;

	/* Blocks while buffer is being received */
	while (length--) {
		/* Wait for the USART to have new data and abort operation if it
		 * doesn't get ready within the timeout*/
		for (uint32_t i = 0; i <= USART_TIMEOUT; i++) {
			if (usart_hw->INTFLAG.reg & SERCOM_USART_INTFLAG_RXC) {
				break;
			} else if (i == USART_TIMEOUT) {
				return STATUS_ERR_TIMEOUT;
			}
		}

		enum status_code retval;
		uint16_t received_data = 0;

		retval = usart_read_wait(module, &received_data);

		if (retval != STATUS_OK) {
			/* Overflow, abort */
			return retval;
		}

		/* Read value will be at least 8-bits long */
		rx_data[rx_pos++] = received_data;

		/* If 9-bit data, write next received byte to the buffer */
		if (module->character_size == USART_CHARACTER_SIZE_9BIT) {
			rx_data[rx_pos++] = (received_data >> 8);
		}
	}

	return STATUS_OK;
}
