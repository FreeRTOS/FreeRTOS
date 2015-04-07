/**
 * \file
 *
 * \brief Universal Synchronous Asynchronous Receiver Transmitter (USART) driver for SAM.
 *
 * Copyright (c) 2011-2012 Atmel Corporation. All rights reserved.
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

#include "compiler.h"

/**
 * \defgroup usart_group Universal Synchronous Asynchronous Receiver Transmitter (USART)
 *
 * See \ref sam_usart_quickstart.
 *
 * This is a low-level driver implementation for the SAM Universal
 * Synchronous/Asynchronous Receiver/Transmitter.
 *
 * @{
 */

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

/** Clock phase. */
#define SPI_CPHA	(1 << 0)

/** Clock polarity. */
#define SPI_CPOL	(1 << 1)

/** SPI mode definition. */
#define SPI_MODE_0	(SPI_CPHA)
#define SPI_MODE_1	0
#define SPI_MODE_2	(SPI_CPOL | SPI_CPHA)
#define SPI_MODE_3	(SPI_CPOL)

//! Input parameters when initializing RS232 and similar modes.
typedef struct {
	//! Set baud rate of the USART (unused in slave modes).
	uint32_t baudrate;
	
	//! Number of bits, which should be one of the following: US_MR_CHRL_5_BIT,
	//! US_MR_CHRL_6_BIT, US_MR_CHRL_7_BIT, US_MR_CHRL_8_BIT or US_MR_MODE9.
	uint32_t char_length;
	
	//! Parity type, which should be one of the following: US_MR_PAR_EVEN, US_MR_PAR_ODD,
	//! US_MR_PAR_SPACE, US_MR_PAR_MARK, US_MR_PAR_NO or US_MR_PAR_MULTIDROP.
	uint32_t parity_type;

	//! Number of stop bits between two characters: US_MR_NBSTOP_1_BIT,
	//! US_MR_NBSTOP_1_5_BIT, US_MR_NBSTOP_2_BIT.
	//! \note US_MR_NBSTOP_1_5_BIT is supported in asynchronous modes only.
	uint32_t stop_bits;

	//! Run the channel in test mode, which should be one of following: US_MR_CHMODE_NORMAL,
	//! US_MR_CHMODE_AUTOMATIC, US_MR_CHMODE_LOCAL_LOOPBACK, US_MR_CHMODE_REMOTE_LOOPBACK
	uint32_t channel_mode;

	//! Filter of IrDA mode, useless in other modes. 
	uint32_t irda_filter;
} sam_usart_opt_t;

//! Input parameters when initializing ISO7816 mode.
typedef struct {
	//! Set the frequency of the ISO7816 clock.
	uint32_t iso7816_hz;
	
	//! The number of ISO7816 clock ticks in every bit period (1 to 2047, 0 = disable clock).
	//! Baudrate rate = iso7816_hz / fidi_ratio
	uint32_t fidi_ratio;

	//! How to calculate the parity bit: US_MR_PAR_EVEN for normal mode or
	//! US_MR_PAR_ODD for inverse mode.
	uint32_t parity_type;

	//! Inhibit Non Acknowledge:
	//!   - 0: the NACK is generated;
	//!   - 1: the NACK is not generated.
	//!
	//! \note This bit will be used only in ISO7816 mode, protocol T = 0 receiver.
	uint32_t inhibit_nack;

	//! Disable successive NACKs.
	//!  - 0: NACK is sent on the ISO line as soon as a parity error occurs in the received character.
	//! Successive parity errors are counted up to the value in the max_iterations field.
	//! These parity errors generate a NACK on the ISO line. As soon as this value is reached,
	//! No additional NACK is sent on the ISO line. The ITERATION flag is asserted.
	uint32_t dis_suc_nack;

	//! Max number of repetitions (0 to 7).
	uint32_t max_iterations;

	//! Bit order in transmitted characters:
	//!   - 0: LSB first;
	//!   - 1: MSB first.
	uint32_t bit_order;
	
	//! Which protocol is used:
	//!   - 0: T = 0;
	//!   - 1: T = 1.
	uint32_t protocol_type;
} usart_iso7816_opt_t;

//! Input parameters when initializing SPI mode.
typedef struct {
	//! Set the frequency of the SPI clock (unused in slave mode).
	uint32_t baudrate;

	//! Number of bits, which should be one of the following: US_MR_CHRL_5_BIT,
	//! US_MR_CHRL_6_BIT, US_MR_CHRL_7_BIT, US_MR_CHRL_8_BIT or US_MR_MODE9.
	uint32_t char_length;

	//! Which SPI mode to use, which should be one of the following:
	//! SPI_MODE_0, SPI_MODE_1, SPI_MODE_2, SPI_MODE_3.
	uint32_t spi_mode;

	//! Run the channel in test mode, which should be one of following: US_MR_CHMODE_NORMAL,
	//! US_MR_CHMODE_AUTOMATIC, US_MR_CHMODE_LOCAL_LOOPBACK, US_MR_CHMODE_REMOTE_LOOPBACK
	uint32_t channel_mode;
} usart_spi_opt_t;

void usart_reset(Usart *p_usart);
uint32_t usart_init_rs232(Usart *p_usart, const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck);
uint32_t usart_init_hw_handshaking(Usart *p_usart, const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck);
#if (SAM3S || SAM4S || SAM3U)
uint32_t usart_init_modem(Usart *p_usart, const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck);
#endif
uint32_t usart_init_sync_master(Usart *p_usart, const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck);
uint32_t usart_init_sync_slave(Usart *p_usart, const sam_usart_opt_t *p_usart_opt);
uint32_t usart_init_rs485(Usart *p_usart, const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck);
uint32_t usart_init_irda(Usart *p_usart, const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck);
uint32_t usart_init_iso7816(Usart *p_usart, const usart_iso7816_opt_t *p_usart_opt, uint32_t ul_mck);
uint32_t usart_init_spi_master(Usart *p_usart, const usart_spi_opt_t *p_usart_opt, uint32_t ul_mck);
uint32_t usart_init_spi_slave(Usart *p_usart, const usart_spi_opt_t *p_usart_opt);
#if SAM3XA
uint32_t usart_init_lin_master(Usart *p_usart, const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck);
uint32_t usart_init_lin_slave(Usart *p_usart, const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck);
void usart_lin_abort_tx(Usart *p_usart);
void usart_lin_send_wakeup_signal(Usart *p_usart);
void usart_lin_set_node_action(Usart *p_usart, uint8_t uc_action);
void usart_lin_disable_parity(Usart *p_usart);
void usart_lin_enable_parity(Usart *p_usart);
void usart_lin_disable_checksum(Usart *p_usart);
void usart_lin_enable_checksum(Usart *p_usart);
void usart_lin_set_checksum_type(Usart *p_usart, uint8_t uc_type);
void usart_lin_set_data_len_mode(Usart *p_usart, uint8_t uc_mode);
void usart_lin_disable_frame_slot(Usart *p_usart);
void usart_lin_enable_frame_slot(Usart *p_usart);
void usart_lin_set_wakeup_signal_type(Usart *p_usart, uint8_t uc_type);
void usart_lin_set_response_data_len(Usart *p_usart, uint8_t uc_len);
void usart_lin_disable_pdc_mode(Usart *p_usart);
void usart_lin_enable_pdc_mode(Usart *p_usart);
void usart_lin_set_tx_identifier(Usart *p_usart, uint8_t uc_id);
uint8_t usart_lin_read_identifier(Usart *p_usart);
#endif
void usart_enable_tx(Usart *p_usart);
void usart_disable_tx(Usart *p_usart);
void usart_reset_tx(Usart *p_usart);
void usart_set_tx_timeguard(Usart *p_usart, uint32_t timeguard);
void usart_enable_rx(Usart *p_usart);
void usart_disable_rx(Usart *p_usart);
void usart_reset_rx(Usart *p_usart);
void usart_set_rx_timeout(Usart *p_usart, uint32_t timeout);
void usart_enable_interrupt(Usart *p_usart,uint32_t ul_sources);
void usart_disable_interrupt(Usart *p_usart,uint32_t ul_sources);
uint32_t usart_get_interrupt_mask(Usart *p_usart);
uint32_t usart_get_status(Usart *p_usart);
void usart_reset_status(Usart *p_usart);
void usart_start_tx_break(Usart *p_usart);
void usart_stop_tx_break(Usart *p_usart);
void usart_start_rx_timeout(Usart *p_usart);
uint32_t usart_send_address(Usart *p_usart, uint32_t ul_addr);
void usart_reset_iterations(Usart *p_usart);
void usart_reset_nack(Usart *p_usart);
void usart_restart_rx_timeout(Usart *p_usart);
#if (SAM3S || SAM4S || SAM3U)
void usart_drive_DTR_pin_low(Usart *p_usart);
void usart_drive_DTR_pin_high(Usart *p_usart);
#endif
void usart_drive_RTS_pin_low(Usart *p_usart);
void usart_drive_RTS_pin_high(Usart *p_usart);
void usart_spi_force_chip_select(Usart *p_usart);
void usart_spi_release_chip_select(Usart *p_usart);
uint32_t usart_is_tx_ready(Usart *p_usart);
uint32_t usart_is_tx_empty(Usart *p_usart);
uint32_t usart_is_rx_ready(Usart *p_usart);
uint32_t usart_is_rx_buf_end(Usart *p_usart);
uint32_t usart_is_tx_buf_end(Usart *p_usart);
uint32_t usart_is_rx_buf_full(Usart *p_usart);
uint32_t usart_is_tx_buf_empty(Usart *p_usart);
uint32_t usart_write(Usart *p_usart, uint32_t c);
uint32_t usart_putchar(Usart *p_usart, uint32_t c);
void usart_write_line(Usart *p_usart, const char *string);
uint32_t usart_read(Usart *p_usart, uint32_t *c);
uint32_t usart_getchar(Usart *p_usart, uint32_t *c);
#if (SAM3XA || SAM3U)
uint32_t * usart_get_tx_access(Usart *p_usart);
uint32_t * usart_get_rx_access(Usart *p_usart);
#endif
Pdc *usart_get_pdc_base(Usart *p_usart);
void usart_enable_writeprotect(Usart *p_usart);
void usart_disable_writeprotect(Usart *p_usart);
uint32_t usart_get_writeprotect_status(Usart *p_usart);
uint8_t usart_get_error_number(Usart *p_usart);
#if (SAM3S || SAM4S || SAM3U || SAM3XA)
void usart_man_set_tx_pre_len(Usart *p_usart, uint8_t uc_len);
void usart_man_set_tx_pre_pattern(Usart *p_usart, uint8_t uc_pattern);
void usart_man_set_tx_polarity(Usart *p_usart, uint8_t uc_polarity);
void usart_man_set_rx_pre_len(Usart *p_usart, uint8_t uc_len);
void usart_man_set_rx_pre_pattern(Usart *p_usart, uint8_t uc_pattern);
void usart_man_set_rx_polarity(Usart *p_usart, uint8_t uc_polarity);
void usart_man_enable_drift_compensation(Usart *p_usart);
void usart_man_disable_drift_compensation(Usart *p_usart);
#endif

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond

//! @}

/**
 * \page sam_usart_quickstart Quick start guide for the SAM USART module
 *
 * This is the quick start guide for the \ref usart_group "USART module", with
 * step-by-step instructions on how to configure and use the driver in a
 * selection of use cases.
 *
 * The use cases contain several code fragments. The code fragments in the
 * steps for setup can be copied into a custom initialization function, while
 * the steps for usage can be copied into, e.g., the main application function.
 *
 * \note Some SAM devices contain both USART and UART modules, with the latter
 *       being a subset in functionality of the former but physically separate
 *       peripherals. UART modules are compatible with the USART driver, but
 *       only for the functions and modes supported by the base UART driver.
 *
 * \section usart_basic_use_case Basic use case
 * \section usart_use_cases USART use cases
 * - \ref usart_basic_use_case
 * - \subpage usart_use_case_1
 * - \subpage usart_use_case_2
 *
 * \section usart_basic_use_case Basic use case - transmit a character
 * In this use case, the USART module is configured for:
 * - Using USART0
 * - Baudrate: 9600
 * - Character length: 8 bit
 * - Parity mode: Disabled
 * - Stop bit: None
 * - RS232 mode
 *
 * \section usart_basic_use_case_setup Setup steps
 *
 * \subsection usart_basic_use_case_setup_prereq Prerequisites
 * -# \ref sysclk_group "System Clock Management (sysclock)"
 * -# \ref pio_group "Parallel Input/Output Controller (pio)"
 * -# \ref pmc_group "Power Management Controller (pmc)"
 *
 * \subsection usart_basic_use_case_setup_code Example code
 * The following configuration must be added to the project (typically to a 
 * conf_usart.h file, but it can also be added to your main application file.)
 * \code
 *    #define USART_SERIAL                 USART0
 *    #define USART_SERIAL_ID              ID_USART0
 *    #define USART_SERIAL_PIO             PINS_USART_PIO
 *    #define USART_SERIAL_TYPE            PINS_USART_TYPE
 *    #define USART_SERIAL_PINS            PINS_USART_PINS
 *    #define USART_SERIAL_MASK            PINS_USART_MASK
 *    #define USART_SERIAL_BAUDRATE        9600
 *    #define USART_SERIAL_CHAR_LENGTH     US_MR_CHRL_8_BIT
 *    #define USART_SERIAL_PARITY          US_MR_PAR_NO
 *    #define USART_SERIAL_STOP_BIT        US_MR_NBSTOP_1_BIT
 * \endcode
 *
 * Add to application initialization:
 * \code
 *    sysclk_init();
 *
 *    pio_configure(USART_SERIAL_PIO, USART_SERIAL_TYPE,
 *                  USART_SERIAL_MASK, USART_SERIAL_ATTR);
 *    
 *    const sam_usart_opt_t usart_console_settings = {
 *        USART_SERIAL_BAUDRATE,
 *        USART_SERIAL_CHAR_LENGTH,
 *        USART_SERIAL_PARITY,
 *        USART_SERIAL_STOP_BIT,
 *        US_MR_CHMODE_NORMAL
 *    };
 *    
 *    pmc_enable_periph_clk(USART_SERIAL_ID);
 *   
 *    usart_init_rs232(USART_SERIAL, &usart_console_settings, sysclk_get_main_hz());
 *    usart_enable_tx(USART_SERIAL);
 *    usart_enable_rx(USART_SERIAL);
 * \endcode
 *
 * \subsection usart_basic_use_case_setup_flow Workflow
 * -# Initialize system clock:
 *   \code
 *   sysclk_init();
 *   \endcode
 * -# Configure the USART Tx and Rx pins as Outputs and Inputs respectively:
 *   \code
 *   pio_configure(PINS_UART_PIO, PINS_UART_TYPE, PINS_UART_MASK,
 *                 PINS_UART_ATTR);
 *   \endcode
 * -# Create USART options struct:
 *   \code
 *   const sam_usart_opt_t usart_console_settings = {
 *        USART_SERIAL_BAUDRATE,
 *        USART_SERIAL_CHAR_LENGTH,
 *        USART_SERIAL_PARITY,
 *        USART_SERIAL_STOP_BIT,
 *        US_MR_CHMODE_NORMAL
 *   };
 *   \endcode
 * -# Enable the clock to the USART module:
 *   \code
 *   pmc_enable_periph_clk(USART_SERIAL_ID);
 *   \endcode
 * -# Initialize the USART module in RS232 mode:
 *   \code
 *   usart_init_rs232(USART_SERIAL, &usart_console_settings, sysclk_get_main_hz());
 *   \endcode
 * -# Enable the Rx and Tx modes of the USART module:
 *   \code
 *   usart_enable_tx(USART_SERIAL);
 *   usart_enable_rx(USART_SERIAL);
 *   \endcode
 *
 * \section usart_basic_use_case_usage Usage steps
 *
 * \subsection usart_basic_use_case_usage_code Example code
 * Add to application C-file:
 * \code
 * usart_putchar(USART_SERIAL, 'a');
 * \endcode
 *
 * \subsection usart_basic_use_case_usage_flow Workflow
 * -# Send an 'a' character via USART
 *   \code usart_putchar(USART_SERIAL, 'a'); \endcode
 */

/**
 * \page usart_use_case_1 USART receive character and echo back
 *
 * In this use case, the USART module is configured for:
 * - Using USART0
 * - Baudrate: 9600
 * - Character length: 8 bit
 * - Parity mode: Disabled
 * - Stop bit: None
 * - RS232 mode
 *
 * The use case waits for a received character on the configured USART and
 * echoes the character back to the same USART.
 *
 * \section usart_use_case_1_setup Setup steps
 *
 * \subsection usart_use_case_1_setup_prereq Prerequisites
 * -# \ref sysclk_group "System Clock Management (sysclock)"
 * -# \ref pio_group "Parallel Input/Output Controller (pio)"
 * -# \ref pmc_group "Power Management Controller (pmc)"
 *
 * \subsection usart_use_case_1_setup_code Example code
 * The following configuration must be added to the project (typically to a 
 * conf_usart.h file, but it can also be added to your main application file.):
 * \code
 *    #define USART_SERIAL                 USART0
 *    #define USART_SERIAL_ID              ID_USART0
 *    #define USART_SERIAL_PIO             PINS_USART_PIO
 *    #define USART_SERIAL_TYPE            PINS_USART_TYPE
 *    #define USART_SERIAL_PINS            PINS_USART_PINS
 *    #define USART_SERIAL_MASK            PINS_USART_MASK
 *    #define USART_SERIAL_BAUDRATE        9600
 *    #define USART_SERIAL_CHAR_LENGTH     US_MR_CHRL_8_BIT
 *    #define USART_SERIAL_PARITY          US_MR_PAR_NO
 *    #define USART_SERIAL_STOP_BIT        US_MR_NBSTOP_1_BIT
 * \endcode
 *
 * A variable for the received byte must be added:
 * \code
 *    uint32_t received_byte;
 * \endcode
 *
 * Add to application initialization:
 * \code
 *    sysclk_init();
 *
 *    pio_configure(USART_SERIAL_PIO, USART_SERIAL_TYPE,
 *                  USART_SERIAL_MASK, USART_SERIAL_ATTR);
 *    
 *    const sam_usart_opt_t usart_console_settings = {
 *        USART_SERIAL_BAUDRATE,
 *        USART_SERIAL_CHAR_LENGTH,
 *        USART_SERIAL_PARITY,
 *        USART_SERIAL_STOP_BIT,
 *        US_MR_CHMODE_NORMAL
 *    };
 *    
 *    pmc_enable_periph_clk(USART_SERIAL_ID);
 *   
 *    usart_init_rs232(USART_SERIAL, &usart_console_settings, sysclk_get_main_hz());
 *    usart_enable_tx(USART_SERIAL);
 *    usart_enable_rx(USART_SERIAL);
 * \endcode
 *
 * \subsection usart_use_case_1_setup_flow Workflow
 * -# Initialize system clock:
 *   \code
 *   sysclk_init();
 *   \endcode
 * -# Configure the USART Tx and Rx pins as Outputs and Inputs respectively:
 *   \code
 *    pio_configure(USART_SERIAL_PIO, USART_SERIAL_TYPE,
 *                  USART_SERIAL_MASK, USART_SERIAL_ATTR);
 *   \endcode
 * -# Create USART options struct:
 *   \code
 *   const sam_usart_opt_t usart_console_settings = {
 *        USART_SERIAL_BAUDRATE,
 *        USART_SERIAL_CHAR_LENGTH,
 *        USART_SERIAL_PARITY,
 *        USART_SERIAL_STOP_BIT,
 *        US_MR_CHMODE_NORMAL
 *   };
 *   \endcode
 * -# Enable the clock to the USART module:
 *   \code pmc_enable_periph_clk(USART_SERIAL_ID); \endcode
 * -# Initialize the USART module in RS232 mode:
 *   \code usart_init_rs232(USART_SERIAL, &usart_console_settings, sysclk_get_main_hz()); \endcode
 * -# Enable the Rx and Tx modes of the USART module:
 *   \code
 *   usart_enable_tx(USART_SERIAL);
 *   usart_enable_rx(USART_SERIAL);
 *   \endcode
 *
 * \section usart_use_case_1_usage Usage steps
 *
 * \subsection usart_use_case_1_usage_code Example code
 * Add to, e.g., main loop in application C-file:
 * \code
 * received_byte = usart_getchar(USART_SERIAL);
 * usart_putchar(USART_SERIAL, received_byte);
 * \endcode
 *
 * \subsection usart_use_case_1_usage_flow Workflow
 * -# Wait for reception of a character:
 *   \code usart_getchar(USART_SERIAL, &received_byte); \endcode
 * -# Echo the character back:
 *   \code usart_putchar(USART_SERIAL, received_byte); \endcode
 */

/**
 * \page usart_use_case_2 USART receive character and echo back via interrupts
 *
 * In this use case, the USART module is configured for:
 * - Using USART0
 * - Baudrate: 9600
 * - Character length: 8 bit
 * - Parity mode: Disabled
 * - Stop bit: None
 * - RS232 mode
 *
 * The use case waits for a received character on the configured USART and
 * echoes the character back to the same USART. The character reception is
 * performed via an interrupt handler, rather than the polling method used
 * in \ref usart_use_case_1.
 *
 * \section usart_use_case_2_setup Setup steps
 *
 * \subsection usart_use_case_2_setup_prereq Prerequisites
 * -# \ref sysclk_group "System Clock Management (sysclock)"
 * -# \ref pio_group "Parallel Input/Output Controller (pio)"
 * -# \ref pmc_group "Power Management Controller (pmc)"
 *
 * \subsection usart_use_case_2_setup_code Example code
 * The following configuration must be added to the project (typically to a 
 * conf_usart.h file, but it can also be added to your main application file.):
 * \code
 *    #define USART_SERIAL                 USART0
 *    #define USART_SERIAL_ID              ID_USART0
 *    #define USART_SERIAL_ISR_HANDLER     USART0_Handler
 *    #define USART_SERIAL_PIO             PINS_USART_PIO
 *    #define USART_SERIAL_TYPE            PINS_USART_TYPE
 *    #define USART_SERIAL_PINS            PINS_USART_PINS
 *    #define USART_SERIAL_MASK            PINS_USART_MASK
 *    #define USART_SERIAL_BAUDRATE        9600
 *    #define USART_SERIAL_CHAR_LENGTH     US_MR_CHRL_8_BIT
 *    #define USART_SERIAL_PARITY          US_MR_PAR_NO
 *    #define USART_SERIAL_STOP_BIT        US_MR_NBSTOP_1_BIT
 * \endcode
 *
 * A variable for the received byte must be added:
 * \code
 *    uint32_t received_byte;
 * \endcode
 *
 * Add to application initialization:
 * \code
 *    sysclk_init();
 *
 *    pio_configure(USART_SERIAL_PIO, USART_SERIAL_TYPE,
 *                  USART_SERIAL_MASK, USART_SERIAL_ATTR);
 *    
 *    const sam_usart_opt_t usart_console_settings = {
 *        USART_SERIAL_BAUDRATE,
 *        USART_SERIAL_CHAR_LENGTH,
 *        USART_SERIAL_PARITY,
 *        USART_SERIAL_STOP_BIT,
 *        US_MR_CHMODE_NORMAL
 *    };
 *    
 *    pmc_enable_periph_clk(USART_SERIAL_ID);
 *   
 *    usart_init_rs232(USART_SERIAL, &usart_console_settings, sysclk_get_main_hz());
 *    usart_enable_tx(USART_SERIAL);
 *    usart_enable_rx(USART_SERIAL);
 * 
 *    usart_enable_interrupt(USART_SERIAL, US_IER_RXRDY);
 *    NVIC_EnableIRQ(USART_SERIAL_IRQ);
 * \endcode
 *
 * \subsection usart_use_case_2_setup_flow Workflow
 * -# Initialize system clock:
 *   \code
 *   sysclk_init();
 *   \endcode
 * -# Configure the USART Tx and Rx pins as Outputs and Inputs respectively:
 *   \code
 *    pio_configure(USART_SERIAL_PIO, USART_SERIAL_TYPE,
 *                  USART_SERIAL_MASK, USART_SERIAL_ATTR);
 *   \endcode
 * -# Create USART options struct:
 *   \code
 *   const sam_usart_opt_t usart_console_settings = {
 *        USART_SERIAL_BAUDRATE,
 *        USART_SERIAL_CHAR_LENGTH,
 *        USART_SERIAL_PARITY,
 *        USART_SERIAL_STOP_BIT,
 *        US_MR_CHMODE_NORMAL
 *   };
 *   \endcode
 * -# Enable the clock to the USART module:
 *   \code pmc_enable_periph_clk(USART_SERIAL_ID); \endcode
 * -# Initialize the USART module in RS232 mode:
 *   \code usart_init_rs232(USART_SERIAL, &usart_console_settings, sysclk_get_main_hz()); \endcode
 * -# Enable the Rx and Tx modes of the USART module:
 *   \code
 *   usart_enable_tx(USART_SERIAL);
 *   usart_enable_rx(USART_SERIAL);
 *   \endcode
 * -# Enable the USART character reception interrupt, and general interrupts for the USART module.
 *   \code
 *   usart_enable_interrupt(USART_SERIAL, US_IER_RXRDY);
 *   NVIC_EnableIRQ(USART_SERIAL_IRQ);
 *   \endcode
 * \section usart_use_case_2_usage Usage steps
 *
 * \subsection usart_use_case_2_usage_code Example code
 * Add to your main application C-file the USART interrupt handler:
 * \code
 * void USART_SERIAL_ISR_HANDLER(void)
 * {
 *    uint32_t dw_status = usart_get_status(USART_SERIAL);
 * 
 *    if (dw_status & US_CSR_RXRDY) {
 *        uint32_t received_byte;
 * 
 *        usart_read(USART_SERIAL, &received_byte);
 *        usart_write(USART_SERIAL, received_byte);
 *    }
 * }
 * \endcode
 *
 * \subsection usart_use_case_2_usage_flow Workflow
 * -# When the USART ISR fires, retrieve the USART module interrupt flags:
 *   \code uint32_t dw_status = usart_get_status(USART_SERIAL); \endcode
 * -# Check if the USART Receive Character interrupt has fired:
 *   \code if (dw_status & US_CSR_RXRDY) \endcode
 * -# If a character has been received, fetch it into a temporary variable:
 *   \code usart_read(USART_SERIAL, &received_byte); \endcode
 * -# Echo the character back:
 *   \code usart_write(USART_SERIAL, received_byte); \endcode
 */

#endif /* USART_H_INCLUDED */
