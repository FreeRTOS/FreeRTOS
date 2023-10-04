/**
 * \file
 *
 * \brief SAM D20 Generic Clock Driver Quick Start
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
 * \page asfdoc_samd20_system_gclk_basic_use_case Quick Start Guide for SYSTEM CLOCK - GCLK Configuration
 *
 * In this use case, the GCLK module is configured for:
 *  \li One generator attached to the internal 8MHz RC oscillator clock source
 *  \li Generator output equal to input frequency divided by a factor of 128
 *  \li One channel (connected to the TC0 module) enabled with the enabled generator selected
 *
 * This use case configures a clock channel to output a clock for a peripheral
 * within the device, by first setting up a clock generator from a master clock
 * source, and then linking the generator to the desired channel. This clock
 * can then be used to clock a module within the device.
 *
 * \section asfdoc_samd20_system_gclk_basic_use_case_setup Setup
 *
 * \subsection asfdoc_samd20_system_gclk_basic_use_case_setup_prereq Prerequisites
 * There are no special setup requirements for this use-case.
 *
 * \subsection asfdoc_samd20_system_gclk_basic_use_case_setup_code Code
 * Copy-paste the following setup code to your user application:
 * \snippet qs_gclk_basic.c setup
 *
 * Add to user application initialization (typically the start of \c main()):
 * \snippet qs_gclk_basic.c setup_init
 *
 * \subsection asfdoc_samd20_system_gclk_basic_use_case_setup_flow Workflow
 * -# Create a GCLK generator configuration struct, which can be filled out to
 *    adjust the configuration of a single clock generator.
 *  \snippet qs_gclk_basic.c setup_1
 * -# Initialize the generator configuration struct with the module's default
 *    values.
 *    \note This should always be performed before using the configuration
 *          struct to ensure that all values are initialized to known default
 *          settings.
 *
 *  \snippet qs_gclk_basic.c setup_2
 * -# Adjust the configuration struct to request that the master clock source
 *    channel 0 be used as the source of the generator, and set the generator
 *    output prescaler to divide the input clock by a factor of 128.
 *  \snippet qs_gclk_basic.c setup_3
 * -# Configure the generator using the configuration structure.
 *    \note The existing configuration struct may be re-used, as long as any
 *          values that have been altered from the default settings are taken
 *          into account by the user application.
 *
 *  \snippet qs_gclk_basic.c setup_4
 * -# Enable the generator once it has been properly configured, to begin clock
 *    generation.
 *  \snippet qs_gclk_basic.c setup_5
 *
 * -# Create a GCLK channel configuration struct, which can be filled out to
 *    adjust the configuration of a single generic clock channel.
 *  \snippet qs_gclk_basic.c setup_6
 * -# Initialize the channel configuration struct with the module's default
 *    values.
 *    \note This should always be performed before using the configuration
 *          struct to ensure that all values are initialized to known default
 *          settings.
 *
 *  \snippet qs_gclk_basic.c setup_7
 * -# Adjust the configuration struct to request that the previously configured
 *    and enabled clock generator be used as the clock source for the channel.
 *  \snippet qs_gclk_basic.c setup_8
 * -# Configure the channel using the configuration structure.
 *    \note The existing configuration struct may be re-used, as long as any
 *          values that have been altered from the default settings are taken
 *          into account by the user application.
 *
 *  \snippet qs_gclk_basic.c setup_9
 * -# Enable the channel once it has been properly configured, to output the
 *    clock to the channel's peripheral module consumers.
 *  \snippet qs_gclk_basic.c setup_10
 *
 * \section asfdoc_samd20_system_gclk_basic_use_case_main Use Case
 *
 * \subsection asfdoc_samd20_system_gclk_basic_use_case_code Code
 * Copy-paste the following code to your user application:
 * \snippet qs_gclk_basic.c main
 *
 * \subsection asfdoc_samd20_system_gclk_basic_use_case_flow Workflow
 * -# As the clock is generated asynchronously to the system core, no special
 *    extra application code is required.
 */
