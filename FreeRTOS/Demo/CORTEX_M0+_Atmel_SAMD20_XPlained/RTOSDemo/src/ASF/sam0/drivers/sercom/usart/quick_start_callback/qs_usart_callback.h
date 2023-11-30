/**
 * \file
 *
 * \brief SAM D20 USART Interface Driver
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

/**
 * \page asfdoc_samd20_sercom_usart_callback_use_case Quick Start Guide for SERCOM USART - Callback
 *
 * This quick start will echo back characters typed into the terminal, using
 * asynchronous TX and RX callbacks from the USART peripheral. In this use case
 * the USART will be configured with the following settings:
 * - Asynchronous mode
 * - 9600 Baudrate
 * - 8-bits, No Parity and 1 Stop Bit
 * - TX and RX enabled and connected to the Xplained PRO Embedded Debugger virtual COM port
 *
 * \section asfdoc_samd20_sercom_usart_callback_use_case_setup Setup
 *
 * \subsection asfdoc_samd20_sercom_usart_callback_use_case_prereq Prerequisites
 * There are no special setup requirements for this use-case.
 *
 * \subsection asfdoc_samd20_usart_callback_use_case_setup_code Code
 * Add to the main application source file, outside of any functions:
 * \snippet qs_usart_callback.c module_inst
 * \snippet qs_usart_callback.c rx_buffer_var
 *
 * Copy-paste the following callback function code to your user application:
 * \snippet qs_usart_callback.c callback_funcs
 *
 * Copy-paste the following setup code to your user application:
 * \snippet qs_usart_callback.c setup
 *
 * Add to user application initialization (typically the start of \c main()):
 * \snippet qs_usart_callback.c setup_init
 *
 * \subsection asfdoc_samd20_usart_callback_use_case_setup_flow Workflow
 * -# Create a module software instance structure for the USART module to store
 *    the USART driver state while it is in use.
 *    \note This should never go out of scope as long as the module is in use.
 *          In most cases, this should be global.
 *
 *    \snippet qs_usart_callback.c module_inst
 * -# Configure the USART module.
 *  -# Create a USART module configuration struct, which can be filled out to
 *     adjust the configuration of a physical USART peripheral.
 *     \snippet qs_usart_callback.c setup_config
 *  -# Initialize the USART configuration struct with the module's default values.
 *     \note This should always be performed before using the configuration
 *           struct to ensure that all values are initialized to known default
 *           settings.
 *
 *     \snippet qs_usart_callback.c setup_config_defaults
 *  -# Alter the USART settings to configure the physical pinout, baud rate and
 *     other relevant parameters.
 *     \snippet qs_usart_callback.c setup_change_config
 *  -# Configure the USART module with the desired settings, retrying while the
 *     driver is busy until the configuration is stressfully set.
 *     \snippet qs_usart_callback.c setup_set_config
 *  -# Enable the USART module.
 *     \snippet qs_usart_callback.c setup_enable
 * -# Configure the USART callbacks.
 *  -# Register the TX and RX callback functions with the driver.
 *     \snippet qs_usart_callback.c setup_register_callbacks
 *  -# Enable the TX and RX callbacks so that they will be called by the driver
 *     when appropriate.
 *     \snippet qs_usart_callback.c setup_enable_callbacks
 *
 * \section asfdoc_samd20_usart_callback_use_case_main Use Case
 *
 * \subsection asfdoc_samd20_usart_callback_use_case_main_code Code
 * Copy-paste the following code to your user application:
 * \snippet qs_usart_callback.c main
 *
 * \subsection asfdoc_samd20_usart_callback_use_case_main_flow Workflow
 * -# Enable global interrupts, so that the callbacks can be fired.
 *  \snippet qs_usart_callback.c enable_global_interrupts
 * -# Send a string to the USART to show the demo is running, blocking until
 *    all characters have been sent.
 *  \snippet qs_usart_callback.c main_send_string
 * -# Enter an infinite loop to continuously echo received values on the USART.
 *  \snippet qs_usart_callback.c main_loop
 * -# Perform an asynchronous read of the USART, which will fire the registered
 *    callback when characters are received.
 *  \snippet qs_usart_callback.c main_read
 */

#include <asf.h>
#include <conf_clocks.h>

