/**
 * \file
 *
 * \brief SAM D20 External Interrupt Driver Quick Start
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
 * \page asfdoc_samd20_system_interrupt_critsec_use_case Quick Start Guide for SYSTEM INTERRUPT - Critical Section Use Case
 *
 * In this case we perform a critical piece of code, disabling all interrupts
 * while a global shared flag is read. During the critical section, no interrupts
 * may occur.
 *
 * \section asfdoc_samd20_system_interrupt_critsec_use_case_setup Setup
 *
 * \subsection asfdoc_samd20_system_interrupt_critsec_use_case_setup_prereq Prerequisites
 * There are no special setup requirements for this use-case.
 *
 * \section asfdoc_samd20_system_interrupt_critsec_use_case_use_main Use Case
 *
 * \subsection asfdoc_samd20_system_interrupt_critsec_use_case_code Code
 * Copy-paste the following code to your user application:
 * \snippet qs_system_interrupt.c main_1
 *
 * \subsection asfdoc_samd20_system_interrupt_critsec_use_case_flow Workflow
 * -# Enter a critical section to disable global interrupts.
 *  \note Critical sections <i>may</i> be nested if desired; if nested, global
 *        interrupts will only be re-enabled once the outer-most critical
 *        section has completed.
 *
 *  \snippet qs_system_interrupt.c critical_section_start
 *
 * -# Check a global shared flag and perform a response. This code may be any
 *    critical code that requires exclusive access to all resources without the
 *    possibility of interruption.
 *  \snippet qs_system_interrupt.c do_critical_code
 *
 * -# Exit the critical section to re-enable global interrupts.
 *  \snippet qs_system_interrupt.c critical_section_end
 */

/**
 * \page asfdoc_samd20_system_interrupt_enablemodint_use_case Quick Start Guide for SYSTEM INTERRUPT - Enable Module Interrupt Use Case
 *
 * In this case we enable interrupt handling for a specific module, as well as
 * enable interrupts globally for the device.
 *
 * \section asfdoc_samd20_system_interrupt_enablemodint_use_case_setup Setup
 *
 * \subsection asfdoc_samd20_system_interrupt_enablemodint_use_case_setup_prereq Prerequisites
 * There are no special setup requirements for this use-case.
 *
 * \section asfdoc_samd20_system_interrupt_enablemodint_use_case_use_main Use Case
 *
 * \subsection asfdoc_samd20_system_interrupt_enablemodint_use_case_code Code
 * Copy-paste the following code to your user application:
 * \snippet qs_system_interrupt.c main_2
 *
 * \subsection asfdoc_samd20_system_interrupt_enablemodint_use_case_flow Workflow
 * -# Enable interrupt handling for the device's RTC peripheral.
 *  \snippet qs_system_interrupt.c module_int_enable
 *
 * -# Enable global interrupts, so that any enabled and active interrupt sources
 *    can trigger their respective handler functions.
 *  \snippet qs_system_interrupt.c global_int_enable
 */
