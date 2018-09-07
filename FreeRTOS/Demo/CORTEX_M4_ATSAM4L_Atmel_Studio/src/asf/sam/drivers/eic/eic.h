/**
 * \file
 *
 * \brief EIC driver for SAM
 *
 * Copyright (c) 2012 Atmel Corporation. All rights reserved.
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

#ifndef EIC_H_INCLUDED
#define EIC_H_INCLUDED

#include "compiler.h"

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

/** Number of available EIC lines, device dependent. */
#if SAM4L
#define EIC_NUMBER_OF_LINES                 9
#else
#error  'This device does not support EIC driver'
#endif

/** \name External Interrupt lines */
/* @{ */
#define EXT_NMI     0
#define EXT_INT1    1
#define EXT_INT2    2
#define EXT_INT3    3
#define EXT_INT4    4
#define EXT_INT5    5
#define EXT_INT6    6
#define EXT_INT7    7
#define EXT_INT8    8
/* @} */

/** \name Mode Trigger Options */
/* @{ */
#define EIC_MODE_EDGE_TRIGGERED   0
#define EIC_MODE_LEVEL_TRIGGERED  1
/* @{ */

/** \name Edge level Options */
/* @{ */
#define EIC_EDGE_FALLING_EDGE     0
#define EIC_EDGE_RISING_EDGE      1
/* @{ */

/** \name Level Options */
/* @{ */
#define EIC_LEVEL_LOW_LEVEL       0
#define EIC_LEVEL_HIGH_LEVEL      1
/* @{ */

/** \name Filter Options */
/* @{ */
#define EIC_FILTER_ENABLED        1
#define EIC_FILTER_DISABLED       0
/* @{ */

/** \name Synch Mode Options */
/* @{ */
#define EIC_SYNCH_MODE            0
#define EIC_ASYNCH_MODE           1
/* @{ */

/** Configuration parameters of the EIC module. */
struct eic_line_config {
	/** Mode : \ref EIC_MODE_EDGE_TRIGGERED or \ref EIC_MODE_LEVEL_TRIGGERED */
	uint8_t eic_mode;
	/** Edge : \ref EIC_EDGE_FALLING_EDGE or \ref EIC_EDGE_RISING_EDGE */
	uint8_t eic_edge;
	/** Level : \ref EIC_LEVEL_LOW_LEVEL or \ref EIC_LEVEL_HIGH_LEVEL */
	uint8_t eic_level;
	/** Filter: \ref EIC_FILTER_DISABLED or \ref EIC_FILTER_ENABLED */
	uint8_t eic_filter;
	/** Async: \ref EIC_ASYNCH_MODEmode or \ref EIC_SYNCH_MODE */
	uint8_t eic_async;
};

typedef void (*eic_callback_t)(void);

void eic_disable(Eic *eic);
void eic_enable(Eic *eic);

void eic_line_set_config(Eic *eic, uint8_t line_number,
	struct eic_line_config *eic_line_conf);

void eic_line_set_callback(Eic *eic, uint8_t line_number,
	eic_callback_t callback, uint8_t irq_line, uint8_t irq_level);

/**
 * \brief Enable the external interrupt on specified line.
 *
 * \param eic Base address of the EIC module
 * \param line_number The number of enabled line
 */
static inline void eic_line_enable(Eic *eic, uint8_t line_number)
{
	eic->EIC_EN = 1 << line_number;
}

/**
 * \brief Disable the external interrupt on specified line.
 *
 * \param eic Base address of the EIC module
 * \param line_number The number of disabled line
 */
static inline void eic_line_disable(Eic *eic, uint8_t line_number)
{
	eic->EIC_DIS = 1 << line_number;
}

/**
 * \brief Tells whether an EIC line is enabled.
 *
 * \param eic Base address of the EIC module
 * \param line_number Line number to test
 *
 * \return Whether an EIC line is enabled.
 */
static inline bool eic_line_is_enabled(Eic *eic, uint8_t line_number)
{
	return (eic->EIC_CTRL & (1 << line_number)) != 0;
}

/**
 * \brief Enables the external interrupt from specified pin propagate from
 * EIC to interrupt controller.
 *
 * \param eic Base address of the EIC (i.e. EIC).
 * \param line_number Line number to test
 */
static inline void eic_line_enable_interrupt(Eic *eic,
		uint8_t line_number)
{
	eic->EIC_IER = 1 << line_number;
}

/**
 * \brief Disables the external interrupt from specified pin propagate from
 * EIC to interrupt controller.
 *
 * \param eic Base address of the EIC (i.e. EIC).
 * \param line_number Line number to test
 */
static inline void eic_line_disable_interrupt(Eic *eic,
		uint8_t line_number)
{
	eic->EIC_IDR = 1 << line_number;
	eic->EIC_IMR;
}

/**
 * \brief Tells whether an EIC interrupt line is enabled.
 *
 * \param eic Base address of the EIC module
 * \param line_number Line number to test
 *
 * \return Whether an EIC interrupt line is enabled.
 */
static inline bool eic_line_interrupt_is_enabled(Eic *eic,
		uint8_t line_number)
{
	return (eic->EIC_IMR & (1 << line_number)) != 0;
}

/**
 * \brief Clear the interrupt flag of specified pin.
 *          Call this function once you've handled the interrupt.
 *
 * \param eic Base address of the EIC (i.e. EIC).
 * \param line_number Line number to test
 */
static inline void eic_line_clear_interrupt(Eic *eic,
		uint8_t line_number)
{
	eic->EIC_ICR = 1 << line_number;
	eic->EIC_ISR;
}

/**
 * \brief Tells whether an EIC interrupt line is pending.
 *
 * \param eic Base address of the EIC module
 * \param line_number Line number to test
 *
 * \return Whether an EIC interrupt line is pending.
 */
static inline bool eic_line_interrupt_is_pending(Eic *eic,
		uint8_t line_number)
{
	return (eic->EIC_ISR & (1 << line_number)) != 0;
}

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond

/**
 * \page sam_eic_quickstart Quickstart guide for SAM EIC driver
 *
 * This is the quickstart guide for the \ref eic_group "SAM EIC driver",
 * with step-by-step instructions on how to configure and use the driver in a
 * selection of use cases.
 *
 * The use cases contain several code fragments. The code fragments in the
 * steps for setup can be copied into a custom initialization function, while
 * the steps for usage can be copied into, e.g., the main application function.
 *
 * \section eic_basic_use_case Basic use case
 * In this basic use case, the EIC module and single line are configured for:
 * - Falling edge trigger and async mode
 * - Interrupt-based handling
 * - EIC_LINE_5 as input
 *
 * \subsection sam_eic_quickstart_prereq Prerequisites
 * -# \ref sysclk_group "System Clock Management (Sysclock)"
 *
 * \section eic_basic_use_case_setup Setup steps
 * \subsection eic_basic_use_case_setup_code Example code
 * Add to application C-file:
 * \code
 *   void eic_callback(void)
 *   {
 *       // Check if EIC push button line interrupt line is pending
 *       if (eic_line_interrupt_is_pending(EIC, GPIO_PUSH_BUTTON_EIC_LINE)) {
 *           eic_line_clear_interrupt(EIC, GPIO_PUSH_BUTTON_EIC_LINE);
 *           bToggle = 1;
 *       }
 *   }
 *   void eic_setup(void)
 *   {
 *       eic_enable(EIC);
 *
 *       eic_line_set_config(EIC, GPIO_PUSH_BUTTON_EIC_LINE, &eic_line_conf);
 *
 *       eic_line_set_callback(EIC, GPIO_PUSH_BUTTON_EIC_LINE, set_toggle_flag, EIC_5_IRQn, 1);
 *
 *       eic_line_enable(EIC, GPIO_PUSH_BUTTON_EIC_LINE);
 *   }
 * \endcode
 *
 * \subsection eic_basic_use_case_setup_flow Workflow
 * -# Define the interrupt callback function in the application:
 *   - \code
*   void eic_callback(void)
 *   {
 *       // Check if EIC push button line interrupt line is pending
 *       if (eic_line_interrupt_is_pending(EIC, GPIO_PUSH_BUTTON_EIC_LINE)) {
 *           eic_line_clear_interrupt(EIC, GPIO_PUSH_BUTTON_EIC_LINE);
 *           bToggle = 1;
 *       }
 *   }
 * \endcode
 * -# Enable EIC module:
 *   - \code eic_enable(EIC); \endcode
 *   - \note Including enable module clock and lock sleep mode.
 * -# Configure EIC line with specified mode:
 *   - \code aeic_line_set_config(EIC, GPIO_PUSH_BUTTON_EIC_LINE, &eic_line_conf); \endcode
 * -# Set the EIC callback function and enable EIC interrupt.
 *   - \code eic_line_set_callback(EIC, GPIO_PUSH_BUTTON_EIC_LINE, set_toggle_flag, EIC_5_IRQn, 1); \endcode
 * -# Enable EIC line:
 *   - \code eic_line_enable(EIC, GPIO_PUSH_BUTTON_EIC_LINE); \endcode
 */
#endif // EIC_H_INCLUDED
