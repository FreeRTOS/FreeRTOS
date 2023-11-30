/**
 * \file
 *
 * \brief SAM D20 GPIO Port Driver Quick Start
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
 * \page asfdoc_samd20_port_basic_use_case Quick Start Guide for PORT - Basic
 *
 * In this use case, the PORT module is configured for:
 *  \li One pin in input mode, with pull-up enabled
 *  \li One pin in output mode
 *
 * This use case sets up the PORT to read the current state of a GPIO pin set as
 * an input, and mirrors the opposite logical state on a pin configured as an
 * output.
 *
 * \section asfdoc_samd20_port_basic_use_case_setup Setup
 *
 * \subsection asfdoc_samd20_port_basic_use_case_setup_prereq Prerequisites
 * There are no special setup requirements for this use-case.
 *
 * \subsection asfdoc_samd20_port_basic_use_case_setup_code Code
 * Copy-paste the following setup code to your user application:
 * \snippet qs_port_basic.c setup
 *
 * Add to user application initialization (typically the start of \c main()):
 * \snippet qs_port_basic.c setup_init
 *
 * \subsection asfdoc_samd20_port_basic_use_case_setup_flow Workflow
 * -# Create a PORT module pin configuration struct, which can be filled out to
 *    adjust the configuration of a single port pin.
 *  \snippet qs_port_basic.c setup_1
 * -# Initialize the pin configuration struct with the module's default values.
 *    \note This should always be performed before using the configuration
 *          struct to ensure that all values are initialized to known default
 *          settings.
 *
 *  \snippet qs_port_basic.c setup_2
 * -# Adjust the configuration struct to request an input pin.
 *  \snippet qs_port_basic.c setup_3
 * -# Configure GPIO10 with the initialized pin configuration struct, to enable
 *    the input sampler on the pin.
 *  \snippet qs_port_basic.c setup_4
 * -# Adjust the configuration struct to request an output pin.
 *    \note The existing configuration struct may be re-used, as long as any
 *          values that have been altered from the default settings are taken
 *          into account by the user application.
 *
 *  \snippet qs_port_basic.c setup_5
 * -# Configure GPIO11 with the initialized pin configuration struct, to enable
 *    the output driver on the pin.
 *  \snippet qs_port_basic.c setup_6
 *
 * \section asfdoc_samd20_port_basic_use_case_use_main Use Case
 *
 * \subsection asfdoc_samd20_port_basic_use_case_code Code
 * Copy-paste the following code to your user application:
 * \snippet qs_port_basic.c main
 *
 * \subsection asfdoc_samd20_port_basic_use_case_flow Workflow
 * -# Read in the current input sampler state of GPIO10, which has been
 *    configured as an input in the use-case setup code.
 *  \snippet qs_port_basic.c main_1
 * -# Write the inverted pin level state to GPIO11, which has been configured as
 *    an output in the use-case setup code.
 *  \snippet qs_port_basic.c main_2
 */
