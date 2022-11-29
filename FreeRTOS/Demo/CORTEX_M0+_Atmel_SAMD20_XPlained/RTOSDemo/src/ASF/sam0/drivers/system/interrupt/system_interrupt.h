/**
 * \file
 *
 * \brief SAM D20 System Interrupt Driver
 *
 * Copyright (C) 2013 Atmel Corporation. All rights reserved.
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
#ifndef SYSTEM_INTERRUPT_H_INCLUDED
#define SYSTEM_INTERRUPT_H_INCLUDED

/**
 * \defgroup asfdoc_samd20_system_interrupt_group SAM D20 System Interrupt Driver (SYSTEM INTERRUPT)
 *
 * This driver for SAM D20 devices provides an interface for the configuration
 * and management of internal software and hardware interrupts/exceptions.
 *
 * The following peripherals are used by this module:
 *
 *  - NVIC (Nested Vector Interrupt Controller)
 *
 * The outline of this documentation is as follows:
 *  - \ref asfdoc_samd20_system_interrupt_prerequisites
 *  - \ref asfdoc_samd20_system_interrupt_module_overview
 *  - \ref asfdoc_samd20_system_interrupt_special_considerations
 *  - \ref asfdoc_samd20_system_interrupt_extra_info
 *  - \ref asfdoc_samd20_system_interrupt_examples
 *  - \ref asfdoc_samd20_system_interrupt_api_overview
 *
 *
 * \section asfdoc_samd20_system_interrupt_prerequisites Prerequisites
 *
 * There are no prerequisites for this module.
 *
 *
 * \section asfdoc_samd20_system_interrupt_module_overview Module Overview
 *
 * The Cortex M0+ core contains an interrupt an exception vector table, which
 * can be used to configure the device's interrupt handlers; individual
 * interrupts and exceptions can be enabled and disabled, as well as configured
 * with a variable priority.
 *
 * This driver provides a set of wrappers around the core interrupt functions,
 * to expose a simple API for the management of global and individual interrupts
 * within the device.
 *
 * \subsection asfdoc_samd20_system_interrupt_module_overview_criticalsec Critical Sections
 * In some applications it is important to ensure that no interrupts may be
 * executed by the system whilst a critical portion of code is being run; for
 * example, a buffer may be copied from one context to another - during which
 * interrupts must be disabled to avoid corruption of the source buffer contents
 * until the copy has completed. This driver provides a basic API to enter and
 * exit nested critical sections, so that global interrupts can be kept disabled
 * for as long as necessary to complete a critical application code section.
 *
 * \subsection asfdoc_samd20_system_interrupt_module_overview_softints Software Interrupts
 * For some applications, it may be desirable to raise a module or core
 * interrupt via software. For this reason, a set of APIs to set an interrupt or
 * exception as pending are provided to the user application.
 *
 * \section asfdoc_samd20_system_interrupt_special_considerations Special Considerations
 *
 * Interrupts from peripherals in the SAM D20 devices are on a per-module basis;
 * an interrupt raised from any source within a module will cause a single,
 * module-common handler to execute. It is the user application or driver's
 * responsibility to de-multiplex the module-common interrupt to determine the
 * exact interrupt cause.
 *
 * \section asfdoc_samd20_system_interrupt_extra_info Extra Information
 *
 * For extra information see \ref asfdoc_samd20_system_interrupt_extra. This includes:
 *  - \ref asfdoc_samd20_system_interrupt_extra_acronyms
 *  - \ref asfdoc_samd20_system_interrupt_extra_dependencies
 *  - \ref asfdoc_samd20_system_interrupt_extra_errata
 *  - \ref asfdoc_samd20_system_interrupt_extra_history
 *
 *
 * \section asfdoc_samd20_system_interrupt_examples Examples
 *
 * For a list of examples related to this driver, see
 * \ref asfdoc_samd20_system_interrupt_exqsg.
 *
 * \section asfdoc_samd20_system_interrupt_api_overview API Overview
 * @{
 */

#include <compiler.h>
#include <core_cm0plus.h>

#if !defined(__DOXYGEN__)
/* Generates a interrupt vector table enum list entry for a given module type
   and index (e.g. "SYSTEM_INTERRUPT_MODULE_TC0 = TC0_IRQn,"). */
#  define _MODULE_IRQn(n, module) \
		SYSTEM_INTERRUPT_MODULE_##module##n = module##n##_IRQn,

/* Generates interrupt vector table enum list entries for all instances of a
   given module type on the selected device. */
#  define _SYSTEM_INTERRUPT_MODULES(name) \
		MREPEAT(name##_INST_NUM, _MODULE_IRQn, name)


#  define _SYSTEM_INTERRUPT_IPSR_MASK              0x0000003f
#  define _SYSTEM_INTERRUPT_PRIORITY_MASK          0x00000007

#  define _SYSTEM_INTERRUPT_EXTERNAL_VECTOR_START  0

#  define _SYSTEM_INTERRUPT_SYSTICK_PRI_POS        29
#endif

/**
 * \brief Table of possible system interrupt/exception vector numbers.
 *
 * Table of all possible interrupt and exception vector indexes within the
 * device.
 */
enum system_interrupt_vector {
	/** Interrupt vector index for a NMI interrupt. */
	SYSTEM_INTERRUPT_NON_MASKABLE      = NonMaskableInt_IRQn,
	/** Interrupt vector index for a Hard Fault memory access exception. */
	SYSTEM_INTERRUPT_HARD_FAULT        = HardFault_IRQn,
	/** Interrupt vector index for a Supervisor Call exception. */
	SYSTEM_INTERRUPT_SV_CALL           = SVCall_IRQn,
	/** Interrupt vector index for a Pending Supervisor interrupt. */
	SYSTEM_INTERRUPT_PENDING_SV        = PendSV_IRQn,
	/** Interrupt vector index for a System Tick interrupt. */
	SYSTEM_INTERRUPT_SYSTICK           = SysTick_IRQn,

	/** Interrupt vector index for a Power Manager peripheral interrupt. */
	SYSTEM_INTERRUPT_MODULE_PM         = PM_IRQn,
	/** Interrupt vector index for a System Control peripheral interrupt. */
	SYSTEM_INTERRUPT_MODULE_SYSCTRL    = SYSCTRL_IRQn,
	/** Interrupt vector index for a Watch Dog peripheral interrupt. */
	SYSTEM_INTERRUPT_MODULE_WDT        = WDT_IRQn,
	/** Interrupt vector index for a Real Time Clock peripheral interrupt. */
	SYSTEM_INTERRUPT_MODULE_RTC        = RTC_IRQn,
	/** Interrupt vector index for an External Interrupt peripheral interrupt. */
	SYSTEM_INTERRUPT_MODULE_EIC        = EIC_IRQn,
	/** Interrupt vector index for a Non Volatile Memory Controller interrupt. */
	SYSTEM_INTERRUPT_MODULE_NVMCTRL    = NVMCTRL_IRQn,
	/** Interrupt vector index for an Event System interrupt. */
	SYSTEM_INTERRUPT_MODULE_EVSYS      = EVSYS_IRQn,
#if defined(__DOXYGEN__)
	/** Interrupt vector index for a SERCOM peripheral interrupt.
	 *
	 *  Each specific device may contain several SERCOM peripherals; each module
	 *  instance will have its own entry in the table, with the instance number
	 *  substituted for "n" in the entry name (e.g.
	 *  \c SYSTEM_INTERRUPT_MODULE_SERCOM0).
	 */
	SYSTEM_INTERRUPT_MODULE_SERCOMn    = SERCOMn_IRQn,
	/** Interrupt vector index for a Timer/Counter peripheral interrupt.
	 *
	 *  Each specific device may contain several TC peripherals; each module
	 *  instance will have its own entry in the table, with the instance number
	 *  substituted for "n" in the entry name (e.g.
	 *  \c SYSTEM_INTERRUPT_MODULE_TC0).
	 */
	SYSTEM_INTERRUPT_MODULE_TCn        = TCn_IRQn,
#else
	_SYSTEM_INTERRUPT_MODULES(SERCOM)
	_SYSTEM_INTERRUPT_MODULES(TC)
#endif
	/** Interrupt vector index for an Analog Comparator peripheral interrupt. */
	SYSTEM_INTERRUPT_MODULE_AC         = AC_IRQn,
	/** Interrupt vector index for an Analog-to-Digital peripheral interrupt. */
	SYSTEM_INTERRUPT_MODULE_ADC        = ADC_IRQn,
	/** Interrupt vector index for a Digital-to-Analog peripheral interrupt. */
	SYSTEM_INTERRUPT_MODULE_DAC        = DAC_IRQn,
};

/**
 * \brief Table of possible system interrupt/exception vector priorities.
 *
 * Table of all possible interrupt and exception vector priorities within the
 * device.
 */
enum system_interrupt_priority_level {
	/** Priority level 0, the highest possible interrupt priority. */
	SYSTEM_INTERRUPT_PRIORITY_LEVEL_0  = 0,
	/** Priority level 1. */
	SYSTEM_INTERRUPT_PRIORITY_LEVEL_1  = 1,
	/** Priority level 2. */
	SYSTEM_INTERRUPT_PRIORITY_LEVEL_2  = 2,
	/** Priority level 3, the lowest possible interrupt priority. */
	SYSTEM_INTERRUPT_PRIORITY_LEVEL_3  = 3,
};

/**
 * \name Critical Section Management
 * @{
 */

/**
 * \brief Enters a critical section
 *
 * Disables global interrupts. To support nested critical sections, an internal
 * count of the critical section nesting will be kept, so that global interrupts
 * are only re-enabled upon leaving the outermost nested critical section.
 *
 */
static inline void system_interrupt_enter_critical_section(void)
{
	cpu_irq_enter_critical();
}

/**
 * \brief Leaves a critical section
 *
 * Enables global interrupts. To support nested critical sections, an internal
 * count of the critical section nesting will be kept, so that global interrupts
 * are only re-enabled upon leaving the outermost nested critical section.
 *
 */
static inline void system_interrupt_leave_critical_section(void)
{
	cpu_irq_leave_critical();
}

/** @} */

/**
 * \name Interrupt Enabling/Disabling
 * @{
 */

/**
 * \brief Check if global interrupts are enabled
 *
 * Checks if global interrupts are currently enabled.
 *
 * \returns A boolean that identifies if the global interrupts are enabled or not.
 *
 * \retval true   Global interrupts are currently enabled
 * \retval false  Global interrupts are currently disabled
 *
 */
static inline bool system_interrupt_is_global_enabled(void)
{
	return cpu_irq_is_enabled();
}

/**
 * \brief Enables global interrupts
 *
 * Enables global interrupts in the device to fire any enabled interrupt handlers.
 */
static inline void system_interrupt_enable_global(void)
{
	cpu_irq_enable();
}

/**
 * \brief Disables global interrupts
 *
 * Disabled global interrupts in the device, preventing any enabled interrupt
 * handlers from executing.
 */
static inline void system_interrupt_disable_global(void)
{
	cpu_irq_disable();
}

/**
 * \brief Checks if an interrupt vector is enabled or not
 *
 * Checks if a specific interrupt vector is currently enabled.
 *
 * \param[in] vector  Interrupt vector number to check
 *
 * \returns A variable identifying if the requested interrupt vector is enabled
 *
 * \retval true   Specified interrupt vector is currently enabled
 * \retval false  Specified interrupt vector is currently disabled
 *
 */
static inline bool system_interrupt_is_enabled(
		const enum system_interrupt_vector vector)
{
	return (bool)((NVIC->ISER[0] >> (uint32_t)vector) & 0x00000001);
}

/**
 * \brief Enable interrupt vector
 *
 * Enables execution of the software handler for the requested interrupt vector.
 *
 * \param[in] vector Interrupt vector to enable
 */
static inline void system_interrupt_enable(
		const enum system_interrupt_vector vector)
{
	NVIC->ISER[0] = (uint32_t)(1 << ((uint32_t)vector & 0x0000001f));
}

/**
 * \brief Disable interrupt vector
 *
 * Disables execution of the software handler for the requested interrupt vector.
 *
 * \param[in] vector  Interrupt vector to disable
 */
static inline void system_interrupt_disable(
		const enum system_interrupt_vector vector)
{
	NVIC->ICER[0] = (uint32_t)(1 << ((uint32_t)vector & 0x0000001f));
}

/** @} */

/**
 * \name Interrupt State Management
 * @{
 */

/**
 * \brief Get active interrupt (if any)
 *
 * Return the vector number for the current executing software handler, if any.
 *
 * \return Interrupt number that is currently executing.
 */
static inline enum system_interrupt_vector system_interrupt_get_active(void)
{
	uint32_t IPSR = __get_IPSR();

	return (enum system_interrupt_vector)(IPSR & _SYSTEM_INTERRUPT_IPSR_MASK);
}

bool system_interrupt_is_pending(
		const enum system_interrupt_vector vector);

enum status_code system_interrupt_set_pending(
		const enum system_interrupt_vector vector);

enum status_code system_interrupt_clear_pending(
		const enum system_interrupt_vector vector);

/** @} */

/**
 * \name Interrupt Priority Management
 * @{
 */

enum status_code system_interrupt_set_priority(
		const enum system_interrupt_vector vector,
		const enum system_interrupt_priority_level priority_level);

enum system_interrupt_priority_level system_interrupt_get_priority(
		const enum system_interrupt_vector vector);

/** @} */

/** @} */

/**
 * \page asfdoc_samd20_system_interrupt_extra Extra Information for SYSTEM INTERRUPT Driver
 *
 * \section asfdoc_samd20_system_interrupt_extra_acronyms Acronyms
 * The table below presents the acronyms used in this module:
 *
 * <table>
 *	<tr>
 *		<th>Acronym</th>
 *		<th>Description</th>
 *	</tr>
 *	<tr>
 *		<td>ISR</td>
 *		<td>Interrupt Service Routine</td>
 *	</tr>
 * </table>
 *
 *
 * \section asfdoc_samd20_system_interrupt_extra_dependencies Dependencies
 * This driver has the following dependencies:
 *
 *  - None
 *
 *
 * \section asfdoc_samd20_system_interrupt_extra_errata Errata
 * There are no errata related to this driver.
 *
 *
 * \section asfdoc_samd20_system_interrupt_extra_history Module History
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
 *		<td>Initial Release</td>
 *	</tr>
 * </table>
 */

/**
 * \page asfdoc_samd20_system_interrupt_exqsg Examples for SYSTEM INTERRUPT Driver
 *
 * This is a list of the available Quick Start guides (QSGs) and example
 * applications for \ref asfdoc_samd20_system_interrupt_group. QSGs are simple examples with
 * step-by-step instructions to configure and use this driver in a selection of
 * use cases. Note that QSGs can be compiled as a standalone application or be
 * added to the user application.
 *
 *  - \subpage asfdoc_samd20_system_interrupt_critsec_use_case
 *  - \subpage asfdoc_samd20_system_interrupt_enablemodint_use_case
 *
 * \page asfdoc_samd20_system_interrupt_document_revision_history Document Revision History
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

#endif
