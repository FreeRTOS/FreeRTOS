/**
 * \file
 *
 * \brief SAM D20 System Clock Driver Quick Start
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
 */

/**
 * \page asfdoc_samd20_system_clock_basic_use_case Quick Start Guide for SYSTEM CLOCK - Basic
 *
 * In this case we apply the following configuration:
 * - RC8MHz (internal 8MHz RC oscillator)
 *  - Divide by 4, giving a frequency of 2MHz
 * - DFLL (Digital frequency locked loop)
 *  - Open loop mode
 *  - 48MHz frequency
 * - CPU clock
 *  - Use the DFLL, configured to 48MHz
 *
 * \section asfdoc_samd20_system_clock_basic_use_case_setup Setup
 *
 * \subsection asfdoc_samd20_system_clock_basic_use_case_setup_prereq Prerequisites
 * There are no special setup requirements for this use-case.
 *
 * \subsection asfdoc_samd20_system_clock_basic_use_case_setup_code Code
 * Copy-paste the following setup code to your application:
 * \snippet qs_clock_source.c setup
 *
 * \subsection asfdoc_samd20_system_clock_basic_use_case_setup_flow Workflow
 * -# Create a EXTOSC32K module configuration struct, which can be filled
 *    out to adjust the configuration of the external 32KHz oscillator channel.
 *  \snippet qs_clock_source.c config_extosc32k_config
 *
 * -# Initialize the oscillator configuration struct with the module's default
 *    values.
 *    \note This should always be performed before using the configuration
 *          struct to ensure that all values are initialized to known default
 *          settings.
 *
 *  \snippet qs_clock_source.c config_extosc32k_get_defaults
 *
 * -# Alter the EXTOSC32K module configuration struct to require a start-up time
 *    of 4096 clock cycles.
 *  \snippet qs_clock_source.c config_extosc32k_change_defaults
 *
 * -# Write the new configuration to the EXTOSC32K module.
 *  \snippet qs_clock_source.c config_extosc32k_set_config
 *
 * -# Create a DFLL module configuration struct, which can be filled
 *    out to adjust the configuration of the external 32KHz oscillator channel.
 *  \snippet qs_clock_source.c config_dfll_config
 *
 * -# Initialize the DFLL oscillator configuration struct with the module's
 *    default values.
 *    \note This should always be performed before using the configuration
 *          struct to ensure that all values are initialized to known default
 *          settings.
 *
 *  \snippet qs_clock_source.c config_dfll_get_defaults
 *
 * -# Write the new configuration to the DFLL module.
 *  \snippet qs_clock_source.c config_extosc32k_set_config


 * \section asfdoc_samd20_system_clock_basic_use_case_use_main Use Case
 *
 * \subsection asfdoc_samd20_system_clock_basic_use_case_code Code
 *
 * Copy-paste the following code to your user application:
 * \snippet qs_clock_source.c main
 *
 * \subsection asfdoc_samd20_system_clock_basic_use_case_flow Workflow
 * -# Configure the external 32KHz oscillator source using the previously
 *    defined setup function.
 * \snippet qs_clock_source.c config_extosc32k_main
 *
 * -# Enable the configured external 32KHz oscillator source.
 * \snippet qs_clock_source.c enable_extosc32k_main
 *
 * -# Configure the DFLL oscillator source using the previously defined setup
 *    function.
 * \snippet qs_clock_source.c config_dfll_main
 *
 * -# Enable the configured DFLL oscillator source.
 * \snippet qs_clock_source.c enable_dfll_main
 *
 * -# Switch the system clock source to the DFLL, by reconfiguring the main
 *    clock generator.
 * \snippet qs_clock_source.c set_sys_clk_src
 */
