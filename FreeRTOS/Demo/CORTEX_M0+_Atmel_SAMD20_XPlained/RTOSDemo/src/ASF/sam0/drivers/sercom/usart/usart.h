/**
 *
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
#ifndef USART_H_INCLUDED
#define USART_H_INCLUDED

/**
 * \defgroup asfdoc_samd20_sercom_usart_group SAM D20 Serial USART Driver (SERCOM USART)
 *
 * This driver for SAM D20 devices provides an interface for the configuration
 * and management of the SERCOM module in its USART mode to transfer or receive
 * USART data frames. The following driver API modes are covered by this
 * manual:
 *
 *  - Polled APIs
 * \if USART_CALLBACK_MODE
 *  - Callback APIs
 * \endif
 *
 * The following peripherals are used by this module:
 *
 * - SERCOM (Serial Communication Interface)
 *
 * The outline of this documentation is as follows:
 * - \ref asfdoc_samd20_sercom_usart_prerequisites
 * - \ref asfdoc_samd20_sercom_usart_overview
 * - \ref asfdoc_samd20_sercom_usart_special_considerations
 * - \ref asfdoc_samd20_sercom_usart_extra_info
 * - \ref asfdoc_samd20_sercom_usart_examples
 * - \ref asfdoc_samd20_sercom_usart_api_overview
 *
 * \section asfdoc_samd20_sercom_usart_prerequisites Prerequisites
 *
 * To use the USART you need to have a GCLK generator enabled and running
 * that can be used as the SERCOM clock source. This can either be configured
 * in conf_clocks.h or by using the system clock driver.
 *
 * \section asfdoc_samd20_sercom_usart_overview Module Overview
 *
 * This driver will use one (or more) SERCOM interfaces on the system
 * and configure it to run as a USART interface in either synchronous
 * or asynchronous mode.
 *
 * \subsection asfdoc_samd20_sercom_usart_overview_frame_format Frame Format
 *
 * Communication is based on frames, where the frame format can be customized
 * to accommodate a wide range of standards. A frame consists of a start bit,
 * a number of data bits, an optional parity bit for error detection as well
 * as a configurable length stop bit(s) - see
 * \ref asfdoc_samd20_sercom_usart_frame_diagram "the figure below".
 * \ref asfdoc_samd20_sercom_usart_frame_params "The table below" shows the
 * available parameters you can change in a frame.
 *
 * \anchor asfdoc_samd20_sercom_usart_frame_params
 * <table>
 *  <caption>USART Frame Parameters</caption>
 *  <tr>
 *      <th>Parameter</th>
 *      <th>Options</th>
 *  </tr>
 *  <tr>
 *      <td>Start bit</td>
 *      <td>1</td>
 *  </tr>
 *  <tr>
 *      <td>Data bits</td>
 *      <td>5, 6, 7, 8, 9</td>
 *  </tr>
 *  <tr>
 *      <td>Parity bit</td>
 *      <td>None, Even, Odd</td>
 *  </tr>
 *  <tr>
 *      <td>Stop bits</td>
 *      <td>1, 2</td>
 *  </tr>
 * </table>
 *
 * \anchor asfdoc_samd20_sercom_usart_frame_diagram
 * \image html usart_frame.svg "USART Frame overview" width=100%
 *
 * \subsection asfdoc_samd20_sercom_usart_overview_sync Synchronous mode
 *
 * In synchronous mode a dedicated clock line is provided; either by the USART
 * itself if in master mode, or by an external master if in slave mode.
 * Maximum transmission speed is the same as the GCLK clocking the USART
 * peripheral when in slave mode, and the GCLK divided by two if in
 * master mode. In synchronous mode the interface needs three lines to
 * communicate:
 * - TX (Transmit pin)
 * - RX (Receive pin)
 * - XCK (Clock pin)
 *
 * \subsubsection asfdoc_samd20_sercom_usart_overview_sync_sampling Data sampling
 * In synchronous mode the data is sampled on either the rising or falling edge
 * of the clock signal. This is configured by setting the clock polarity in the
 * configuration struct.
 *
 * \subsection asfdoc_samd20_sercom_usart_overview_async Asynchronous mode
 *
 * In asynchronous mode no dedicated clock line is used, and the communication
 * is based on matching the clock speed on the transmitter and receiver. The
 * clock is generated from the internal SERCOM baudrate generator, and the
 * frames are synchronized by using the frame start bits. Maximum transmission
 * speed is limited to the SERCOM GCLK divided by 16.
 * In asynchronous mode the interface only needs two lines to communicate:
 * - TX (Transmit pin)
 * - RX (Receive pin)
 *
 * \subsubsection asfdoc_samd20_sercom_usart_overview_async_clock_matching Transmitter/receiver clock matching
 *
 * For successful transmit and receive using the asynchronous mode the receiver
 * and transmitter clocks needs to be closely matched. When receiving a frame
 * that does not match the selected baud rate closely enough the receiver will
 * be unable to synchronize the frame(s), and garbage transmissions will
 * result.
 *
 * \subsection asfdoc_samd20_sercom_usart_parity Parity
 * Parity can be enabled to detect if a transmission was in error. This is done by
 * counting the number of "1" bits in the frame. When using Even parity the
 * parity bit will be set if the total number of "1"s in the frame are an even
 * number. If using Odd parity the parity bit will be set if the total number
 * of "1"s are Odd.
 *
 * When receiving a character the receiver will count the number of "1"s in the
 * frame and give an error if the received frame and parity bit disagree.
 *
 * \subsection asfdoc_samd20_sercom_usart_overview_pin_configuration GPIO configuration
 *
 * the SERCOM module have four internal PADS where the RX pin can be placed at all
 * the PADS, and the TX and XCK pins have two predefined positions that can be changed.
 * The PADS can then be routed to an external GPIO pin using the normal pin
 * multiplexing scheme on the SAM D20.
 *
 * For SERCOM pad multiplexer position documentation, see
 * \ref asfdoc_samd20_sercom_usart_mux_settings.
 *
 * \section asfdoc_samd20_sercom_usart_special_considerations Special Considerations
 *
 * \if USART_CALLBACK_MODE
 * Never execute large portions of code in the callbacks. These
 * are run from the interrupt routine, and thus having long callbacks will
 * keep the processor in the interrupt handler for an equally long time.
 * A common way to handle this is to use global flags signaling the
 * main application that an interrupt event has happened, and only do the
 * minimal needed processing in the callback.
 * \else
 * No special considerations.
 * \endif
 *
 * \section asfdoc_samd20_sercom_usart_extra_info Extra Information
 *
 * For extra information see \ref asfdoc_samd20_sercom_usart_extra. This includes:
 * - \ref asfdoc_samd20_sercom_usart_extra_acronyms
 * - \ref asfdoc_samd20_sercom_usart_extra_dependencies
 * - \ref asfdoc_samd20_sercom_usart_extra_errata
 * - \ref asfdoc_samd20_sercom_usart_extra_history
 *
 * \section asfdoc_samd20_sercom_usart_examples Examples
 *
 * For a list of examples related to this driver, see
 * \ref asfdoc_samd20_sercom_usart_exqsg.
 *
 * \section asfdoc_samd20_sercom_usart_api_overview API Overview
 * @{
 */

#include <sercom.h>
#include <pinmux.h>

#if USART_CALLBACK_MODE == true
#  include <sercom_interrupt.h>
#endif

#ifdef __cplusplus
extern "C" {
#endif

#ifndef PINMUX_DEFAULT
#  define PINMUX_DEFAULT 0
#endif

#ifndef PINMUX_UNUSED
#  define PINMUX_UNUSED 0xFFFFFFFF
#endif

#ifndef USART_TIMEOUT
#  define USART_TIMEOUT 0xFFFF
#endif

#if USART_CALLBACK_MODE == true
/**
 * \brief USART Callback enum
 *
 * Callbacks for the Asynchronous USART driver
 */
/* TODO: Add support for RX started interrupt. */
enum usart_callback {
	/** Callback for buffer transmitted */
	USART_CALLBACK_BUFFER_TRANSMITTED,
	/** Callback for buffer received */
	USART_CALLBACK_BUFFER_RECEIVED,
	/** Callback for error */
	USART_CALLBACK_ERROR,
#  if !defined(__DOXYGEN__)
	/** Number of available callbacks. */
	USART_CALLBACK_N,
#  endif
};
#endif

/**
 * \brief USART Data Order enum
 *
 * The data order decides which of MSB or LSB is shifted out first when data is
 * transferred
 */
enum usart_dataorder {
	/** The MSB will be shifted out first during transmission,
	 *  and shifted in first during reception */
	USART_DATAORDER_MSB = 0,
	/** The LSB will be shifted out first during transmission,
	 *  and shifted in first during reception */
	USART_DATAORDER_LSB = SERCOM_USART_CTRLA_DORD,
};

/**
 * \brief USART Transfer mode enum
 *
 * Select USART transfer mode
 */
enum usart_transfer_mode {
	/** Transfer of data is done synchronously */
	USART_TRANSFER_SYNCHRONOUSLY = (SERCOM_USART_CTRLA_CMODE),
	/** Transfer of data is done asynchronously */
	USART_TRANSFER_ASYNCHRONOUSLY = 0
};

/**
 * \brief USART Parity enum
 *
 * Select parity USART parity mode
 */
enum usart_parity {
	/** For odd parity checking, the parity bit will be set if number of
	 *  ones being transferred is even */
	USART_PARITY_ODD  = SERCOM_USART_CTRLB_PMODE,

	/** For even parity checking, the parity bit will be set if number of
	 *  ones being received is odd */
	USART_PARITY_EVEN = 0,

	/** No parity checking will be executed, and there will be no parity bit
	 *  in the received frame */
	USART_PARITY_NONE = 0xFF,
};

/**
 * \brief USART signal mux settings
 *
 * Set the functionality of the SERCOM pins.
 */
enum usart_signal_mux_settings {
	/** See \ref asfdoc_samd20_sercom_usart_mux_setting_a */
	USART_RX_0_TX_0_XCK_1 = (SERCOM_USART_CTRLA_RXPO(0)),
	/** See \ref asfdoc_samd20_sercom_usart_mux_setting_b */
	USART_RX_0_TX_2_XCK_3 = (SERCOM_USART_CTRLA_RXPO(0) | SERCOM_USART_CTRLA_TXPO),
	/** See \ref asfdoc_samd20_sercom_usart_mux_setting_c */
	USART_RX_1_TX_0_XCK_1 = (SERCOM_USART_CTRLA_RXPO(1)),
	/** See \ref asfdoc_samd20_sercom_usart_mux_setting_d */
	USART_RX_1_TX_2_XCK_3 = (SERCOM_USART_CTRLA_RXPO(1) | SERCOM_USART_CTRLA_TXPO),
	/** See \ref asfdoc_samd20_sercom_usart_mux_setting_e */
	USART_RX_2_TX_0_XCK_1 = (SERCOM_USART_CTRLA_RXPO(2)),
	/** See \ref asfdoc_samd20_sercom_usart_mux_setting_f */
	USART_RX_2_TX_2_XCK_3 = (SERCOM_USART_CTRLA_RXPO(2) | SERCOM_USART_CTRLA_TXPO),
	/** See \ref asfdoc_samd20_sercom_usart_mux_setting_g */
	USART_RX_3_TX_0_XCK_1 = (SERCOM_USART_CTRLA_RXPO(3)),
	/** See \ref asfdoc_samd20_sercom_usart_mux_setting_h */
	USART_RX_3_TX_2_XCK_3 = (SERCOM_USART_CTRLA_RXPO(3) | SERCOM_USART_CTRLA_TXPO),
};

/**
 * \brief USART Stop Bits enum
 *
 * Number of stop bits for a frame.
 */
enum usart_stopbits {
	/** Each transferred frame contains 1 stop bit */
	USART_STOPBITS_1 = 0,
	/** Each transferred frame contains 2 stop bits */
	USART_STOPBITS_2 = SERCOM_USART_CTRLB_SBMODE,
};

/**
 * \brief USART Character Size
 *
 * Number of bits for the character sent in a frame.
 */
enum usart_character_size {
	/** The char being sent in a frame is 5 bits long */
	USART_CHARACTER_SIZE_5BIT = SERCOM_USART_CTRLB_CHSIZE(5),
	/** The char being sent in a frame is 6 bits long */
	USART_CHARACTER_SIZE_6BIT = SERCOM_USART_CTRLB_CHSIZE(6),
	/** The char being sent in a frame is 7 bits long */
	USART_CHARACTER_SIZE_7BIT = SERCOM_USART_CTRLB_CHSIZE(7),
	/** The char being sent in a frame is 8 bits long */
	USART_CHARACTER_SIZE_8BIT = SERCOM_USART_CTRLB_CHSIZE(0),
	/** The char being sent in a frame is 9 bits long */
	USART_CHARACTER_SIZE_9BIT = SERCOM_USART_CTRLB_CHSIZE(1),
};


/**
 * \brief USART Transceiver
 *
 * Select Receiver or Transmitter
 */
enum usart_transceiver_type {
	/** The parameter is for the Receiver */
	USART_TRANSCEIVER_RX,
	/** The parameter is for the Transmitter */
	USART_TRANSCEIVER_TX,
};

/**
 * \brief USART configuration struct
 *
 * Configuration options for USART
 */
struct usart_config {
	/** USART bit order (MSB or LSB first) */
	enum usart_dataorder data_order;
	/** USART in asynchronous or synchronous mode */
	enum usart_transfer_mode transfer_mode;
	/** USART parity */
	enum usart_parity parity;
	/** Number of stop bits */
	enum usart_stopbits stopbits;
	/** USART character size */
	enum usart_character_size character_size;
	/** USART pin out */
	enum usart_signal_mux_settings mux_setting;
	/** USART baud rate */
	uint32_t baudrate;
	/** Enable receiver */
	bool receiver_enable;
	/** Enable transmitter */
	bool transmitter_enable;

	/** USART Clock Polarity.
	 * If true, data changes on falling XCK edge and
	 * is sampled at rising edge.
	 * If false, data changes on rising XCK edge and
	 * is sampled at falling edge.
	 * */
	bool clock_polarity_inverted;

	/** States whether to use the external clock applied to the XCK pin.
	 * In synchronous mode the shift register will act directly on the XCK clock.
	 * In asynchronous mode the XCK will be the input to the USART hardware module.
	 */
	bool use_external_clock;
	/** External clock frequency in synchronous mode.
	 * This must be set if \c use_external_clock is true. */
	uint32_t ext_clock_freq;
	/** If true the USART will be kept running in Standby sleep mode */
	bool run_in_standby;
	/** GCLK generator source */
	enum gclk_generator generator_source;
	/** PAD0 pinmux */
	uint32_t pinmux_pad0;
	/** PAD1 pinmux */
	uint32_t pinmux_pad1;
	/** PAD2 pinmux */
	uint32_t pinmux_pad2;
	/** PAD3 pinmux */
	uint32_t pinmux_pad3;
};

#if USART_CALLBACK_MODE == true
/* Forward Declaration for the device instance */
struct usart_module;

/* Type of the callback functions */
typedef void (*usart_callback_t)(const struct usart_module *const module);
#endif

/**
 * \brief SERCOM USART driver software device instance structure.
 *
 * SERCOM USART driver software instance structure, used to retain software
 * state information of an associated hardware module instance.
 *
 * \note The fields of this structure should not be altered by the user
 *       application; they are reserved for module-internal use only.
 */
struct usart_module {
#if !defined(__DOXYGEN__)
	/** Pointer to the hardware instance */
	Sercom *hw;
	/** Character size of the data being transferred */
	enum usart_character_size character_size;
	/** Receiver enabled */
	bool receiver_enabled;
	/** Transmitter enabled */
	bool transmitter_enabled;
#  if USART_CALLBACK_MODE == true
	/** Array to store callback function pointers in */
	usart_callback_t callback[USART_CALLBACK_N];
	/** Buffer pointer to where the next received character will be put */
	volatile uint8_t *rx_buffer_ptr;

	/** Buffer pointer to where the next character will be transmitted from
	**/
	volatile uint8_t *tx_buffer_ptr;
	/** Remaining characters to receive */
	volatile uint16_t remaining_rx_buffer_length;
	/** Remaining characters to transmit */
	volatile uint16_t remaining_tx_buffer_length;
	/** Bit mask for callbacks registered */
	uint8_t callback_reg_mask;
	/** Bit mask for callbacks enabled */
	uint8_t callback_enable_mask;
	/** Holds the status of the ongoing or last read operation */
	volatile enum status_code rx_status;
	/** Holds the status of the ongoing or last write operation */
	volatile enum status_code tx_status;
#  endif
#endif
};

#if !defined (__DOXYGEN__)
/**
 * \internal
 * Waits until synchronization is complete
 */
static inline void _usart_wait_for_sync(
		const struct usart_module *const module)
{
	/* Get a pointer to the hardware module instance */
	SercomUsart *const usart_hw = &(module->hw->USART);

	while (usart_hw->STATUS.reg & SERCOM_USART_STATUS_SYNCBUSY) {
		/* Wait until the synchronization is complete */
	}
}
#endif

/**
 * \brief Check if peripheral is busy syncing registers across clock domains
 *
 * Return peripheral synchronization status. If doing a non-blocking
 * implementation this function can be used to check the sync state and hold of
 * any new actions until sync is complete. If this functions is not run; the
 * functions will block until the sync has completed.
 *
 * \param[in]  module  Pointer to peripheral module
 *
 * \return Peripheral sync status
 *
 * \retval true   Peripheral is busy syncing
 * \retval false  Peripheral is not busy syncing and can be read/written without
 *                stalling the bus.
 */
static inline bool usart_is_syncing(
		const struct usart_module *const module)
{
	/* Sanity check arguments */
	Assert(module);
	Assert(module->hw);

	SercomUsart *const usart_hw = &(module->hw->USART);

	if(usart_hw->STATUS.reg & SERCOM_USART_STATUS_SYNCBUSY) {
		return true;
	} else {
		return false;
	}
}

/**
 * \brief Initializes the device to predefined defaults
 *
 * Initialize the USART device to predefined defaults:
 * - 8-bit asynchronous USART
 * - No parity
 * - 1 stop bit
 * - 9600 baud
 * - Transmitter enabled
 * - Receiver enabled
 * - GCLK generator 0 as clock source
 * - Default pin configuration
 *
 * The configuration struct will be updated with the default
 * configuration.
 *
 * \param[in,out] config  Pointer to configuration struct
 */
static inline void usart_get_config_defaults(
		struct usart_config *const config)
{
	/* Sanity check arguments */
	Assert(config);

	/* Set default config in the config struct */
	config->data_order       = USART_DATAORDER_LSB;
	config->transfer_mode    = USART_TRANSFER_ASYNCHRONOUSLY;
	config->parity           = USART_PARITY_NONE;
	config->stopbits         = USART_STOPBITS_1;
	config->character_size   = USART_CHARACTER_SIZE_8BIT;
	config->baudrate         = 9600;
	config->receiver_enable  = true;
	config->transmitter_enable = true;
	config->clock_polarity_inverted = false;
	config->use_external_clock = false;
	config->ext_clock_freq   = 0;
	config->mux_setting      = USART_RX_1_TX_2_XCK_3;
	config->run_in_standby   = false;
	config->generator_source = GCLK_GENERATOR_0;
	config->pinmux_pad0      = PINMUX_DEFAULT;
	config->pinmux_pad1      = PINMUX_DEFAULT;
	config->pinmux_pad2      = PINMUX_DEFAULT;
	config->pinmux_pad3      = PINMUX_DEFAULT;
}

enum status_code usart_init(
		struct usart_module *const module,
		Sercom *const hw,
		const struct usart_config *const config);

/**
 * \brief Enable the module
 *
 * Enables the USART module
 *
 * \param[in]  module  Pointer to USART software instance struct
 */
static inline void usart_enable(
		const struct usart_module *const module)
{
	/* Sanity check arguments */
	Assert(module);
	Assert(module->hw);

	/* Get a pointer to the hardware module instance */
	SercomUsart *const usart_hw = &(module->hw->USART);

#if USART_CALLBACK_MODE == true
	/* Enable Global interrupt for module */
	system_interrupt_enable(_sercom_get_interrupt_vector(module->hw));
#endif

	/* Wait until synchronization is complete */
	_usart_wait_for_sync(module);

	/* Enable USART module */
	usart_hw->CTRLA.reg |= SERCOM_USART_CTRLA_ENABLE;
}

/**
 * \brief Disable module
 *
 * Disables the USART module
 *
 * \param[in]  module  Pointer to USART software instance struct
 */
static inline void usart_disable(
		const struct usart_module *const module)
{
	/* Sanity check arguments */
	Assert(module);
	Assert(module->hw);

	/* Get a pointer to the hardware module instance */
	SercomUsart *const usart_hw = &(module->hw->USART);

	/* Disable Global interrupt for module */
	system_interrupt_disable(_sercom_get_interrupt_vector(module->hw));

	/* Wait until synchronization is complete */
	_usart_wait_for_sync(module);

	/* Disable USART module */
	usart_hw->CTRLA.reg &= ~SERCOM_USART_CTRLA_ENABLE;
}

/**
 * \brief Resets the USART module
 *
 * Disables and resets the USART module.
 *
 * \param[in]  module  Pointer to the USART software instance struct
 */
static inline void usart_reset(
		const struct usart_module *const module)
{
	/* Sanity check arguments */
	Assert(module);
	Assert(module->hw);

	/* Get a pointer to the hardware module instance */
	SercomUsart *const usart_hw = &(module->hw->USART);

	usart_disable(module);

	/* Wait until synchronization is complete */
	_usart_wait_for_sync(module);

	/* Reset module */
	usart_hw->CTRLA.reg = SERCOM_USART_CTRLA_SWRST;
}

/**
 * \name Writing and reading
 * @{
 */
enum status_code usart_write_wait(
		struct usart_module *const module,
		const uint16_t tx_data);

enum status_code usart_read_wait(
		struct usart_module *const module,
		uint16_t *const rx_data);

enum status_code usart_write_buffer_wait(
		struct usart_module *const module,
		const uint8_t *tx_data,
		uint16_t length);

enum status_code usart_read_buffer_wait(
		struct usart_module *const module,
		uint8_t *rx_data,
		uint16_t length);
/** @} */

/**
 * \name Enabling/Disabling receiver and transmitter
 * @{
 */

/**
 * \brief Enable Transceiver
 *
 * Enable the given transceiver. Either RX or TX.
 *
 * \param[in]  module            Pointer to USART software instance struct
 * \param[in]  transceiver_type  Transceiver type.
 */
static inline void usart_enable_transceiver(
		struct usart_module *const module,
		enum usart_transceiver_type transceiver_type)
{
	/* Sanity check arguments */
	Assert(module);
	Assert(module->hw);

	/* Get a pointer to the hardware module instance */
	SercomUsart *const usart_hw = &(module->hw->USART);

	/* Wait until synchronization is complete */
	_usart_wait_for_sync(module);

	switch (transceiver_type) {
		case USART_TRANSCEIVER_RX:
			/* Enable RX */
			usart_hw->CTRLB.reg |= SERCOM_USART_CTRLB_RXEN;
			module->receiver_enabled = true;
			break;

		case USART_TRANSCEIVER_TX:
			/* Enable TX */
			usart_hw->CTRLB.reg |= SERCOM_USART_CTRLB_TXEN;
			module->transmitter_enabled = true;
			break;
	}
}

/**
 * \brief Disable Transceiver
 *
 * Disable the given transceiver (RX or TX).
 *
 * \param[in]  module            Pointer to USART software instance struct
 * \param[in]  transceiver_type  Transceiver type.
 */
static inline void usart_disable_transceiver(
		struct usart_module *const module,
		enum usart_transceiver_type transceiver_type)
{
	/* Sanity check arguments */
	Assert(module);
	Assert(module->hw);

	/* Get a pointer to the hardware module instance */
	SercomUsart *const usart_hw = &(module->hw->USART);

	/* Wait until synchronization is complete */
	_usart_wait_for_sync(module);

	switch (transceiver_type) {
		case USART_TRANSCEIVER_RX:
			/* Disable RX */
			usart_hw->CTRLB.reg &= ~SERCOM_USART_CTRLB_RXEN;
			module->receiver_enabled = false;
			break;

		case USART_TRANSCEIVER_TX:
			/* Disable TX */
			usart_hw->CTRLB.reg &= ~SERCOM_USART_CTRLB_TXEN;
			module->transmitter_enabled = false;
			break;
	}
}

/** @} */

#ifdef __cplusplus
}
#endif

/** @} */

/**
* \page asfdoc_samd20_sercom_usart_extra Extra Information for SERCOM USART Driver
*
* \section asfdoc_samd20_sercom_usart_extra_acronyms Acronyms
*
* Below is a table listing the acronyms used in this module, along with their
* intended meanings.
*
* <table>
* <tr>
* <th>Acronym</th>
* <th>Description</th>
* </tr>
* <tr>
* <td>SERCOM</td>
* <td>Serial Communication Interface</td>
* </tr>
* <tr>
* <td>USART</td>
* <td>Universal Synchronous and Asynchronous Serial Receiver and Transmitter</td>
* </tr>
* <tr>
* <td>LSB</td>
* <td>Least Significant Bit</td>
* </tr>
* <tr>
* <td>MSB</td>
* <td>Most Significant Bit</td>
* </tr>
* </table>
*
*
* \section asfdoc_samd20_sercom_usart_extra_dependencies Dependencies
* This driver has the following dependencies:
*
* - \ref asfdoc_samd20_system_pinmux_group "System Pin Multiplexer Driver"
* - \ref asfdoc_samd20_system_clock_group "System clock configuration"
*
*
* \section asfdoc_samd20_sercom_usart_extra_errata Errata
* There are no errata related to this driver.
*
*
* \section asfdoc_samd20_sercom_usart_extra_history Module History
* An overview of the module history is presented in the table below, with
* details on the enhancements and fixes made to the module since its first
* release. The current version of this corresponds to the newest version in
* the table.
*
 * <table>
 *	<tr>
 *		<th>Changelog</th>
 *	</tr>
 *	<tr>
 *		<td>\li Added new \c transmitter_enable and \c receiver_enable boolean
 *              values to \c struct usart_config.
 *          \li Altered \c usart_write_* and usart_read_* functions to abort with
 *              an error code if the relevant transceiver is not enabled.
 *          \li Fixed \c usart_write_buffer_wait() and \c usart_read_buffer_wait()
 *              not aborting correctly when a timeout condition occurs.</td>
 *	</tr>
 *	<tr>
 *		<td>Initial Release</td>
 *	</tr>
 * </table>
*/

/**
 * \page asfdoc_samd20_sercom_usart_exqsg Examples for SERCOM USART Driver
 *
 * This is a list of the available Quick Start guides (QSGs) and example
 * applications for \ref asfdoc_samd20_sercom_usart_group. QSGs are simple examples with
 * step-by-step instructions to configure and use this driver in a selection of
 * use cases. Note that QSGs can be compiled as a standalone application or be
 * added to the user application.
 *
 * - \subpage asfdoc_samd20_sercom_usart_basic_use_case
 * \if USART_CALLBACK_MODE
 * - \subpage asfdoc_samd20_sercom_usart_callback_use_case
 * \endif
 */

/**
 * \page asfdoc_samd20_sercom_usart_mux_settings SERCOM USART MUX Settings
 *
 * The different options for functionality of the SERCOM pads.
 *
 * \section asfdoc_samd20_sercom_usart_mux_setting_a MUX Setting A
 *
 * Enum: \ref USART_RX_0_TX_0_XCK_1
 *
 * <table>
 *   <tr>
 *      <th> Function </th>
 *      <th> RX </th>
 *      <th> TX </th>
 *      <th> XCK </th>
 *   </tr>
 *   <tr>
 *      <td> PAD0 </td>
 *      <td> x </td>
 *      <td> x </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD1 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td> x </td>
 *   </tr>
 *   <tr>
 *      <td> PAD2 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD3 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 * </table>
 *
 * \section asfdoc_samd20_sercom_usart_mux_setting_b MUX Setting B
 *
 * Enum: \ref USART_RX_0_TX_2_XCK_3
 *
 * <table>
 *   <tr>
 *      <th> Function </th>
 *      <th> RX </th>
 *      <th> TX </th>
 *      <th> XCK </th>
 *   </tr>
 *   <tr>
 *      <td> PAD0 </td>
 *      <td> x </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD1 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD2 </td>
 *      <td>  </td>
 *      <td> x </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD3 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td> x </td>
 *   </tr>
 * </table>
 *
 * \section asfdoc_samd20_sercom_usart_mux_setting_c MUX Setting C
 *
 * Enum: \ref USART_RX_1_TX_0_XCK_1
 *
 * <table>
 *   <tr>
 *      <th> Function </th>
 *      <th> RX </th>
 *      <th> TX </th>
 *      <th> XCK </th>
 *   </tr>
 *   <tr>
 *      <td> PAD0 </td>
 *      <td>  </td>
 *      <td> x </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD1 </td>
 *      <td> x </td>
 *      <td>  </td>
 *      <td> x </td>
 *   </tr>
 *   <tr>
 *      <td> PAD2 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD3 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 * </table>
 *
 * \section asfdoc_samd20_sercom_usart_mux_setting_d MUX Setting D
 *
 * Enum: \ref USART_RX_1_TX_2_XCK_3
 *
 * <table>
 *   <tr>
 *      <th> Function </th>
 *      <th> RX </th>
 *      <th> TX </th>
 *      <th> XCK </th>
 *   </tr>
 *   <tr>
 *      <td> PAD0 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD1 </td>
 *      <td> x </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD2 </td>
 *      <td>  </td>
 *      <td> x </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD3 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td> x </td>
 *   </tr>
 * </table>
 *
 * \section asfdoc_samd20_sercom_usart_mux_setting_e MUX Setting E
 *
 * Enum: \ref USART_RX_2_TX_0_XCK_1
 *
 * <table>
 *   <tr>
 *      <th> Function </th>
 *      <th> RX </th>
 *      <th> TX </th>
 *      <th> XCK </th>
 *   </tr>
 *   <tr>
 *      <td> PAD0 </td>
 *      <td>  </td>
 *      <td> x </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD1 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td> x </td>
 *   </tr>
 *   <tr>
 *      <td> PAD2 </td>
 *      <td> x </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD3 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 * </table>
 *
 * \section asfdoc_samd20_sercom_usart_mux_setting_f MUX Setting F
 *
 * Enum: \ref USART_RX_2_TX_2_XCK_3
 *
 * <table>
 *   <tr>
 *      <th> Function </th>
 *      <th> RX </th>
 *      <th> TX </th>
 *      <th> XCK </th>
 *   </tr>
 *   <tr>
 *      <td> PAD0 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD1 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD2 </td>
 *      <td> x </td>
 *      <td> x </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD3 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td> x </td>
 *   </tr>
 * </table>
 *
 * \section asfdoc_samd20_sercom_usart_mux_setting_g MUX Setting G
 *
 * Enum: \ref USART_RX_3_TX_0_XCK_1
 *
 * <table>
 *   <tr>
 *      <th> Function </th>
 *      <th> RX </th>
 *      <th> TX </th>
 *      <th> XCK </th>
 *   </tr>
 *   <tr>
 *      <td> PAD0 </td>
 *      <td>  </td>
 *      <td> x </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD1 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td> x </td>
 *   </tr>
 *   <tr>
 *      <td> PAD2 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD3 </td>
 *      <td> x </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 * </table>
 *
 * \section asfdoc_samd20_sercom_usart_mux_setting_h MUX Setting H
 *
 * Enum: \ref USART_RX_3_TX_2_XCK_3
 *
 * <table>
 *   <tr>
 *      <th> Function </th>
 *      <th> RX </th>
 *      <th> TX </th>
 *      <th> XCK </th>
 *   </tr>
 *   <tr>
 *      <td> PAD0 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD1 </td>
 *      <td>  </td>
 *      <td>  </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD2 </td>
 *      <td>  </td>
 *      <td> x </td>
 *      <td>  </td>
 *   </tr>
 *   <tr>
 *      <td> PAD3 </td>
 *      <td> x </td>
 *      <td>  </td>
 *      <td> x </td>
 *   </tr>
 * </table>
 *
 * \page asfdoc_samd20_sercom_usart_document_revision_history Document Revision History
 *
 * <table>
 *	<tr>
 *		<th>Doc. Rev.</td>
 *		<th>Date</td>
 *		<th>Comments</td>
 *	</tr>
 *	<tr>
 *		<td>B</td>
 *		<td>06/2013</td>
 *		<td>Corrected documentation typos.</td>
 *	</tr>
 *	<tr>
 *		<td>A</td>
 *		<td>06/2013</td>
 *		<td>Initial release</td>
 *	</tr>
 * </table>
 */
#endif /* USART_H_INCLUDED */
