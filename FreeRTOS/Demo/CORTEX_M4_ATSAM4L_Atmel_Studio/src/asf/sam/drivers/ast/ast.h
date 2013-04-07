/**
 * \file
 *
 * \brief AST driver for SAM.
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

#ifndef AST_H_INCLUDED
#define AST_H_INCLUDED

/**
 * \defgroup group_sam_drivers_ast AST - Asynchronous Timer
 *
 * Driver for the AST (Asynchronous Timer).
 * Provides functions for configuring and operating the AST in the calendar or
 * timer/counter modes.
 *
 * \{
 */

#include "compiler.h"

/// @cond 0 */
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond */

/** Timeout to prevent code hang in clock initialization */
#define AST_POLL_TIMEOUT 10000

/** \name Predefined PSEL Values
 */
/* @{ */

/**
 * The PSEL value to set the AST source clock (after the prescaler) to 1 Hz,
 * when using an external 32-kHz crystal.
 */
#define AST_PSEL_32KHZ_1HZ    14

/**
 * The PSEL value to set the AST source clock (after the prescaler)
 * to 1.76 Hz when using the internal RC oscillator (~ 115 kHz)
 */
#define AST_PSEL_RC_1_76HZ    15

/* @} */

/* Description for Calendar Field.*/
struct ast_calv {
	uint32_t sec   : 6;
	uint32_t min   : 6;
	uint32_t hour  : 5;
	uint32_t day   : 5;
	uint32_t month : 4;
	uint32_t year  : 6;
};

/* Input when initializing AST in calendar mode.*/
struct ast_calendar {
	union {
		uint32_t field;
		struct ast_calv FIELD;
	};
};

typedef enum ast_mode {
	AST_COUNTER_MODE  = 0,
	AST_CALENDAR_MODE = 1,
} ast_mode_t;

typedef enum ast_oscillator_type {
	AST_OSC_RC    = 0,
	AST_OSC_32KHZ = 1,
	AST_OSC_PB    = 2,
	AST_OSC_GCLK  = 3,
	AST_OSC_1KHZ  = 4,
} ast_oscillator_type_t;

#define AST_INTERRUPT_SOURCE_NUM    5
typedef enum ast_interrupt_source {
	AST_INTERRUPT_ALARM = 0,
	AST_INTERRUPT_PER,
	AST_INTERRUPT_OVF,
	AST_INTERRUPT_READY,
	AST_INTERRUPT_CLKREADY,
} ast_interrupt_source_t;

typedef enum ast_wakeup_source {
	AST_WAKEUP_ALARM = 0,
	AST_WAKEUP_PER,
	AST_WAKEUP_OVF,
} ast_wakeup_source_t;

typedef enum ast_event_source {
	AST_EVENT_ALARM = 0,
	AST_EVENT_PER,
	AST_EVENT_OVF,
} ast_event_source_t;

struct ast_config {
	/*
	 * Mode: Calendar mode:
	 * \ref AST_CALENDAR_MODE or
	 * \ref Counter mode: AST_COUNTER_MODE.
	 */
	ast_mode_t mode;
	/* Oscillator type */
	ast_oscillator_type_t osc_type;
	/* Prescaler Value. */
	uint8_t psel;
	/* Initial counter Value. */
	uint32_t counter;
	/* Initial calendar Value. */
	struct ast_calendar calendar;
};

typedef void (*ast_callback_t)(void);

bool ast_is_enabled(Ast *ast);

void ast_enable(Ast *ast);
void ast_disable(Ast *ast);

uint32_t ast_set_config(Ast *ast, struct ast_config *ast_conf);
void ast_set_callback(Ast *ast, ast_interrupt_source_t source,
		ast_callback_t callback, uint8_t irq_line, uint8_t irq_level);
uint32_t ast_configure_digital_tuner(Ast *ast, uint32_t input_freq,
		uint32_t tuned_freq);
void ast_init_digital_tuner(Ast *ast, bool add, uint8_t value,
		uint8_t exp);
void ast_disable_digital_tuner(Ast *ast);

void ast_write_calendar_value(Ast *ast, struct ast_calendar ast_calendar);
struct ast_calendar ast_read_calendar_value(Ast *ast);
void ast_write_counter_value(Ast *ast, uint32_t ast_counter);
void ast_enable_counter_clear_on_alarm(Ast *ast, uint8_t alarm_channel);
void ast_clear_prescalar(Ast *ast);

/**
 * \brief This function returns the AST current counter value.
 *
 * \param ast Base address of the AST.
 *
 * \return The AST current counter value.
 */
static inline uint32_t ast_read_counter_value(Ast *ast)
{
	return ast->AST_CV;
}

/**
 * \brief Check the busy status of AST clock
 *
 * \param ast Base address of the AST.
 *
 * \return 1 If AST clock is busy, else it will return 0.
 */
static inline bool ast_is_clkbusy(Ast *ast)
{
	return (ast->AST_SR & AST_SR_CLKBUSY) != 0;
}

/**
 * \brief Check the busy status of AST.
 *
 * \param ast Base address of the AST.
 *
 * \return 1 If AST is busy, else it will return 0.
 */
static inline bool ast_is_busy(Ast *ast)
{
	return (ast->AST_SR & AST_SR_BUSY) != 0;
}

/**
 * \brief Get status of AST.
 *
 * \param ast Base address of the AST (i.e. Ast).
 *
 * \return status of AST.
 */
static inline uint32_t ast_read_status(Ast *ast)
{
	return ast->AST_SR;
}

/**
 * \brief This function return the AST interrupts mask value.
 *
 * \param ast             Base address of the AST.
 *
 * \return Interrupt mask value
 */
static inline uint32_t ast_read_interrupt_mask(Ast *ast)
{
	return ast->AST_IMR;
}

void ast_write_alarm0_value(Ast *ast, uint32_t alarm_value);
void ast_write_periodic0_value(Ast *ast, uint32_t pir);

void ast_enable_interrupt(Ast *ast, ast_interrupt_source_t source);
void ast_disable_interrupt(Ast *ast, ast_interrupt_source_t source);
void ast_clear_interrupt_flag(Ast *ast, ast_interrupt_source_t source);

void ast_enable_wakeup(Ast *ast, ast_wakeup_source_t source);
void ast_disable_wakeup(Ast *ast, ast_wakeup_source_t source);

void ast_enable_event(Ast *ast, ast_event_source_t source);
void ast_disable_event(Ast *ast, ast_event_source_t source);

/// @cond 0 */
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond */

/**
 * \}
 */

/**
 * \page sam_ast_quick_start Quick Start Guide for the AST driver
 *
 * This is the quick start guide for the \ref group_sam_drivers_ast, with
 * step-by-step instructions on how to configure and use the driver for
 * a specific use case.The code examples can be copied into e.g the main
 * application loop or any other function that will need to control the
 * AST module.
 *
 * \section ast_qs_use_cases Use cases
 * - \ref ast_basic
 *
 * \section ast_basic AST basic usage
 *
 * This use case will demonstrate how to initialize the AST module to
 * calendar or counter mode.
 *
 *
 * \section ast_basic_setup Setup steps
 *
 * \subsection ast_basic_prereq Prerequisites
 *
 * This module requires the following service
 * - \ref clk_group
 *
 * \subsection ast_basic_setup_code
 *
 * Add this to the main loop or a setup function:
 * \code
 * osc_priv_enable_osc32();
 * \endcode
 *
 * \subsection ast_basic_setup_workflow
 *
 * -# Enable the AST module
 *  - \code ast_enable(AST); \endcode
 * -# Initialize the AST to counter mode
 *  - \code
 * struct ast_config ast_conf;
 * ast_conf.mode = AST_COUNTER_MODE;
 * ast_conf.osc_type = AST_OSC_32KHZ;
 * ast_conf.psel = AST_PSEL_32KHZ_1HZ;
 * ast_conf.counter = 0;
 * ast_set_config(AST, &ast_conf)
 * \endcode
 * -# Or initialize the AST to calendar mode
 *  - \code
 * struct ast_calendar calendar;
 * struct ast_config ast_conf;
 * calendar.FIELD.sec = 0;
 * calendar.FIELD.min = 15;
 * calendar.FIELD.hour = 12;
 * calendar.FIELD.day = 20;
 * calendar.FIELD.month = 9;
 * calendar.FIELD.year = 12;
 * struct ast_config ast_conf;
 * ast_conf.mode = AST_CALENDAR_MODE;
 * ast_conf.osc_type = AST_OSC_32KHZ;
 * ast_conf.psel = AST_PSEL_32KHZ_1HZ;
 * ast_conf.calendar = calendar;
 * ast_set_config(AST, &ast_conf)
 * \endcode
 *  - \note We need to set the clock after prescaler to 1HZ.
 *
 *
 * \section ast_basic_usage Usage steps
 *
 * \subsection ast_basic_usage_code
 *
 * We can get the calendar value by
 * \code
 * calendar = ast_read_calendar_value(AST);
 * \endcode
 * Or we can get the counter value by
 * \code
 * ast_counter = ast_read_counter_value(AST);
 * \endcode
 *
 * We can set the alarm interrupt by
 * \code
 * ast_write_alarm0_value(AST, calendar.field + 1);
 * ast_set_callback(AST, ast_interrupt_alarm, ast_alarm_callback,
 *    AST_ALARM_IRQn, 1);
 * \endcode
 * And we can set the periodic interrupt by
 * \code
 * ast_write_periodic0_value(AST, AST_PSEL_32KHZ_1HZ - 4);
 * ast_set_callback(AST, ast_interrupt_per, ast_per_callback,
 *    AST_PER_IRQn, 1);
 * \endcode
 */

#endif  /* AST_H_INCLUDED */
