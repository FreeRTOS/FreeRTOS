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

#include "ast.h"
#include "sysclk.h"
#include "sleepmgr.h"
#include "conf_ast.h"

/**
 * \internal
 * \brief AST callback function pointer array
 */
ast_callback_t ast_callback_pointer[AST_INTERRUPT_SOURCE_NUM];

/**
 * \brief Check the status of AST.
 *
 * \param ast Base address of the AST.
 *
 * \return true If AST is enabled, else it will return false.
 */
bool ast_is_enabled(Ast *ast)
{
	while (ast_is_busy(ast)) {
	}
	return ((ast->AST_CR & AST_CR_EN) != 0);
}

/**
 * \brief Enable the AST.
 *
 * \param ast Base address of the AST.
 */
void ast_enable(Ast *ast)
{
	sysclk_enable_peripheral_clock(ast);
	sleepmgr_lock_mode(SLEEPMGR_BACKUP);
}

/**
 * \brief Disable the AST. It also disables the AST module.
 *
 * \param ast Base address of the AST.
 */
void ast_disable(Ast *ast)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}
	/* Disable the AST */
	ast->AST_CR &= ~(AST_CR_EN);
	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}

	sysclk_disable_peripheral_clock(ast);
	sleepmgr_unlock_mode(SLEEPMGR_BACKUP);
}

/**
 * \brief This function enables the option to clear the counter on AST alarm.
 *
 * \param ast            Base address of the AST.
 * \param alarm_channel  AST Alarm Channel.
 */
void ast_enable_counter_clear_on_alarm(Ast *ast,
		uint8_t alarm_channel)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}
	/* Enable Clear Counter on Alarm */
	ast->AST_CR
		|= (alarm_channel ? 0 : AST_CR_CA0);
	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function clears the AST periodic prescalar counter to zero.
 *
 * \param ast            Base address of the AST.
 */
void ast_clear_prescalar(Ast *ast)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}
	/* Clear Counter on Alarm */
	ast->AST_CR |= AST_CR_PCLR;
	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function will initialize the AST module in
 * calendar or counter Mode. It then enables the AST module.
 *
 * \note  If you use the 32 KHz oscillator, it will enable this module.
 *
 * \param ast Base address of the AST.
 * \param ast_conf The AST configuration
 *
 * \return 1 if the initialization succeeds otherwise it will return 0.
 */
uint32_t ast_set_config(Ast *ast, struct ast_config *ast_conf)
{
	uint32_t time_out = AST_POLL_TIMEOUT;
	while (ast_is_clkbusy(ast)) {
		if (--time_out == 0) {
			return 0;
		}
	}
	ast->AST_CLOCK = ast_conf->osc_type << AST_CLOCK_CSSEL_Pos;
	time_out = AST_POLL_TIMEOUT;
	while (ast_is_clkbusy(ast)) {
		if (--time_out == 0) {
			return 0;
		}
	}
	ast->AST_CLOCK |= AST_CLOCK_CEN;
	time_out = AST_POLL_TIMEOUT;
	while (ast_is_clkbusy(ast)) {
		if (--time_out == 0) {
			return 0;
		}
	}
	/* Set the new AST configuration */
	if (ast_conf->mode == AST_CALENDAR_MODE) {
		ast->AST_CR = AST_CR_CAL | ast_conf->psel << AST_CR_PSEL_Pos;
	}

	if (ast_conf->mode == AST_COUNTER_MODE) {
		ast->AST_CR = ast_conf->psel << AST_CR_PSEL_Pos;
	}

	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}

	/* Set the calendar */
	if (ast_conf->mode == AST_CALENDAR_MODE) {
		ast_write_calendar_value(ast, ast_conf->calendar);
	}

	if (ast_conf->mode == AST_COUNTER_MODE) {
		ast_write_counter_value(ast, ast_conf->counter);
	}

	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}
	/* Enable the AST */
	ast->AST_CR |= AST_CR_EN;
	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}

	return 1;
}

/**
 * \brief Function to tune the AST prescalar frequency to the desired frequency
 *
 * \param ast         Base address of the AST.
 * \param input_freq  Prescaled AST Clock Frequency
 * \param tuned_freq  Desired AST frequency
 *
 * \retval 0 If invalid frequency is passed
 * \retval 1 If configuration succeeds
 *
 * \note Parameter Calculation:
 * Formula: \n
 * ADD=0 -> ft= fi(1 - (1/((div_ceil(256/value) * (2^exp)) + 1))) \n
 * ADD=1 -> ft= fi(1 + (1/((div_ceil(256/value) * (2^exp)) - 1))) \n
 * Specifications: \n
 * exp > 0, value > 1 \n
 * Let X = (2 ^ exp), Y = div_ceil(256 / value) \n
 * Tuned Frequency -> ft \n
 * Input Frequency -> fi \n
 *
 * IF ft < fi \n
 * ADD = 0 \n
 * Z = (ft / (fi - ft)) \n
 * ELSE IF ft > fi \n
 * ADD = 1 \n
 * Z = (ft / (ft - fi)) \n
 * ELSE \n
 * exit function -> Tuned Frequency = Input Frequency \n
 *
 * The equation can be reduced to (X * Y) = Z
 *
 * Frequency Limits \n
 * (1/((div_ceil(256/value) * (2^exp)) + 1)) should be min to get the lowest
 * possible output from Digital Tuner.\n
 * (1/((div_ceil(256/value) * (2^exp)) - 1)) should be min to get the highest
 * possible output from Digital Tuner.\n
 * For that, div_ceil(256/value) & (2^exp) should be minimum \n
 * min (EXP) = 1 (Note: EXP > 0) \n
 * min (div_ceil(256/value)) = 2 \n
 * max (Ft) = (4*fi)/3 \n
 * min (Ft) = (4*fi)/5 \n
 *
 * Using the above details, X & Y that will closely satisfy the equation is
 * found in this function.
 */
uint32_t ast_configure_digital_tuner(Ast *ast,
		uint32_t input_freq, uint32_t tuned_freq)
{
	bool add;
	uint8_t value;
	uint8_t exp;
	uint32_t x, y, z;
	uint32_t diff;
	if (tuned_freq < input_freq) {
		/* Check for Frequency Limit */
		if (tuned_freq < ((4 * input_freq) / 5)) {
			return 0;
		}

		/* Set the ADD to 0 when freq less than input freq */
		add = false;
		/* Calculate the frequency difference */
		diff = input_freq - tuned_freq;
	} else if (tuned_freq > input_freq) {
		/* Check for Frequency Limit */
		if (tuned_freq > ((4 * input_freq) / 3)) {
			return 0;
		}

		/* Set the ADD to 1 when freq greater than input freq */
		add = true;
		/* Calculate the frequency difference */
		diff = tuned_freq - input_freq;
	} else {
		/* required & input freq are equal */
		return 1;
	}

	z = (tuned_freq) / (diff);
	if ((tuned_freq % diff) > (diff / 2)) {
		z++;
	}

	/*
	 * Initialize with minimum possible values.
	 * exp value should be greater than zero, min(exp) = 1 -> min(x)= (2^1)
	 * = 2
	 * y should be greater than one -> div_ceil(256/value) where value- 0 to
	 * 255
	 * min(y) = div_ceil(256/255) = 2
	 */
	y = 2;
	x = 2;
	exp = 1;

	/*
	 * Keep exp constant and increase y value until it reaches its limit.
	 * Increment exp and follow the same steps until we found the closest
	 * possible match for the required frequency.
	 */
	do {
		if (y < 255) {
			y++;
		} else {
			x = x << 1;
			y = 2;
			exp++;
		}
	} while (z > (x * y));
	/* Decrement y value after exit from loop */
	y = y - 1;
	/* Find VALUE from y */
	value = div_ceil(256, y);
	/* Initialize the Digital Tuner using the required parameters */
	ast_init_digital_tuner(ast, add, value, exp);
	return 1;
}

/**
 * \brief This function will initialize the digital tuner of AST module.
 *
 * \param ast   Base address of the AST.
 * \param add   set to true if frequency has to be increased, false if it
 *              has to be decreased.
 * \param value Parameter used in the formula
 * \param exp   Parameter used in the formula
 *
 * \return 1 if the initialization succeeds otherwise it will return 0.
 */
void ast_init_digital_tuner(Ast *ast, bool add,
		uint8_t value, uint8_t exp)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}

	if (add) {
		ast->AST_DTR = AST_DTR_ADD | AST_DTR_VALUE(value) | AST_DTR_EXP(
				exp);
	} else {
		ast->AST_DTR = AST_DTR_VALUE(value) | AST_DTR_EXP(exp);
	}

	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function will disable the digital tuner of AST module.
 *
 * \param ast   Base address of the AST.
 */
void ast_disable_digital_tuner(Ast *ast)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}
	ast->AST_DTR &= ~(AST_DTR_VALUE_Msk);
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function sets the AST current calendar value.
 *
 * \param ast          Base address of the AST.
 * \param ast_calendar Startup date
 */
void ast_write_calendar_value(Ast *ast,
		struct ast_calendar calendar)
{
	/* Wait until we can write into the VAL register */
	while (ast_is_busy(ast)) {
	}
	/* Set the new val value */
	ast->AST_CALV = calendar.field;
	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function sets the AST current counter value.
 *
 * \param ast         Base address of the AST.
 * \param ast_counter Startup counter value
 */
void ast_write_counter_value(Ast *ast,
		uint32_t ast_counter)
{
	/* Wait until we can write into the VAL register */
	while (ast_is_busy(ast)) {
	}
	/* Set the new val value */
	ast->AST_CV = ast_counter;
	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function returns the AST current calendar value.
 *
 * \param ast Base address of the AST.
 *
 * \return The AST current calendar value.
 */
struct ast_calendar ast_read_calendar_value(Ast *ast)
{
	struct ast_calendar calendar;
	calendar.field = ast->AST_CALV;
	return calendar;
}

/**
 * \brief This function set the AST alarm0 value.
 *
 * \param ast         Base address of the AST.
 * \param alarm_value AST alarm0 value.
 */
void ast_write_alarm0_value(Ast *ast, uint32_t alarm_value)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}
	/* Set the new alarm0 compare value */
	ast->AST_AR0 = alarm_value;
	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function set the AST periodic0 value.
 *
 * \param ast Base address of the AST.
 * \param pir AST periodic0.
 */
void ast_write_periodic0_value(Ast *ast, uint32_t pir)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}
	/* Set the periodic prescaler value */
	ast->AST_PIR0 = pir;
	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function enables the AST interrupts
 *
 * \param ast             Base address of the AST.
 * \param source  AST Interrupts to be enabled
 */
void ast_enable_interrupt(Ast *ast, ast_interrupt_source_t source)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}

	switch (source) {
	case AST_INTERRUPT_ALARM:
		ast->AST_IER = AST_IER_ALARM0_1;
		break;

	case AST_INTERRUPT_PER:
		ast->AST_IER = AST_IER_PER0_1;
		break;

	case AST_INTERRUPT_OVF:
		ast->AST_IER = AST_IER_OVF_1;
		break;

	case AST_INTERRUPT_READY:
		ast->AST_IER = AST_IER_READY_1;
		break;

	case AST_INTERRUPT_CLKREADY:
		ast->AST_IER = AST_IER_CLKRDY_1;
		break;

	default:
		break;
	}

	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function disables the AST interrupts.
 *
 * \param ast              Base address of the AST.
 * \param source   AST Interrupts to be disabled
 */
void ast_disable_interrupt(Ast *ast, ast_interrupt_source_t source)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}

	switch (source) {
	case AST_INTERRUPT_ALARM:
		ast->AST_IDR = AST_IDR_ALARM0_1;
		break;

	case AST_INTERRUPT_PER:
		ast->AST_IDR = AST_IDR_PER0_1;
		break;

	case AST_INTERRUPT_OVF:
		ast->AST_IDR = AST_IDR_OVF_1;
		break;

	case AST_INTERRUPT_READY:
		ast->AST_IDR = AST_IDR_READY_1;
		break;

	case AST_INTERRUPT_CLKREADY:
		ast->AST_IDR = AST_IDR_CLKRDY_1;
		break;

	default:
		break;
	}

	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function clears the AST status flags.
 *
 * \param ast          Base address of the AST.
 * \param source  AST status flag to be cleared
 */
void ast_clear_interrupt_flag(Ast *ast, ast_interrupt_source_t source)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}

	switch (source) {
	case AST_INTERRUPT_ALARM:
		ast->AST_SCR = AST_SCR_ALARM0;
		break;

	case AST_INTERRUPT_PER:
		ast->AST_SCR = AST_SCR_PER0;
		break;

	case AST_INTERRUPT_OVF:
		ast->AST_SCR = AST_SCR_OVF;
		break;

	case AST_INTERRUPT_READY:
		ast->AST_SCR = AST_SCR_READY;
		break;

	case AST_INTERRUPT_CLKREADY:
		ast->AST_SCR = AST_SCR_CLKRDY;
		break;

	default:
		break;
	}

	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief Set callback for AST
 *
 * \param ast          Base address of the AST.
 * \param source AST interrupt source.
 * \param callback callback function pointer.
 * \param irq_line  interrupt line.
 * \param irq_level interrupt level.
 */
void ast_set_callback(Ast *ast, ast_interrupt_source_t source,
		ast_callback_t callback, uint8_t irq_line, uint8_t irq_level)
{
	ast_callback_pointer[source] = callback;
	NVIC_ClearPendingIRQ((IRQn_Type)irq_line);
	NVIC_SetPriority((IRQn_Type)irq_line, irq_level);
	NVIC_EnableIRQ((IRQn_Type)irq_line);
	ast_enable_interrupt(ast, source);
}

/**
 * \brief Interrupt handler for AST.
 */
void ast_interrupt_handler(void)
{
	uint32_t status, mask;

	status = ast_read_status(AST);
	mask = ast_read_interrupt_mask(AST);

	if ((status & AST_SR_ALARM0) && (mask & AST_IMR_ALARM0)) {
		ast_callback_pointer[AST_INTERRUPT_ALARM]();
	}

	if ((status & AST_SR_PER0) && (mask & AST_IMR_PER0)) {
		ast_callback_pointer[AST_INTERRUPT_PER]();
	}

	if ((status & AST_SR_OVF) && (mask & AST_IMR_OVF_1)) {
		ast_callback_pointer[AST_INTERRUPT_OVF]();
	}

	if ((status & AST_SR_READY) && (mask & AST_IMR_READY_1)) {
		ast_callback_pointer[AST_INTERRUPT_READY]();
	}

	if ((status & AST_SR_CLKRDY) && (mask & AST_IMR_CLKRDY_1)) {
		ast_callback_pointer[AST_INTERRUPT_CLKREADY]();
	}
}

/**
 * \brief Interrupt handler for AST periodic.
 */
#ifdef AST_PER_ENABLE
void AST_PER_Handler(void)
{
	ast_interrupt_handler();
}
#endif

/**
 * \brief Interrupt handler for AST alarm.
 */
#ifdef AST_ALARM_ENABLE
void AST_ALARM_Handler(void)
{
	ast_interrupt_handler();
}

#endif

/**
 * \brief Interrupt handler for AST periodic.
 */
#ifdef AST_OVF_ENABLE
void AST_OVF_Handler(void)
{
	ast_interrupt_handler();
}

#endif

/**
 * \brief Interrupt handler for AST alarm.
 */
#ifdef AST_READY_ENABLE
void AST_READY_Handler(void)
{
	ast_interrupt_handler();
}

#endif

/**
 * \brief Interrupt handler for AST periodic.
 */
#ifdef AST_CLKREADY_ENABLE
void AST_CLKREADY_Handler(void)
{
	ast_interrupt_handler();
}

#endif

/**
 * \brief This function enables the AST Asynchronous wake-up.
 *
 * \param ast          Base address of the AST.
 * \param source  AST wake-up flag to be enabled.
 */
void ast_enable_wakeup(Ast *ast, ast_wakeup_source_t source)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}

	switch (source) {
	case AST_WAKEUP_ALARM:
		ast->AST_WER |= AST_WER_ALARM0_1;
		break;

	case AST_WAKEUP_PER:
		ast->AST_WER |= AST_WER_PER0_1;
		break;

	case AST_WAKEUP_OVF:
		ast->AST_WER |= AST_WER_OVF_1;
		break;

	default:
		break;
	}

	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function disables the AST Asynchronous wake-up.
 * 8
 * \param ast          Base address of the AST.
 * \param source  AST wake-up flag to be disabled.
 */
void ast_disable_wakeup(Ast *ast, ast_wakeup_source_t source)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}

	switch (source) {
	case AST_WAKEUP_ALARM:
		ast->AST_WER &= ~AST_WER_ALARM0_1;
		break;

	case AST_WAKEUP_PER:
		ast->AST_WER &= ~AST_WER_PER0_1;
		break;

	case AST_WAKEUP_OVF:
		ast->AST_WER &= ~AST_WER_OVF_1;
		break;

	default:
		break;
	}

	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function enables the AST event.
 *
 * \param ast          Base address of the AST.
 * \param source  AST event flag to be enabled.
 */
void ast_enable_event(Ast *ast, ast_event_source_t source)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}

	switch (source) {
	case AST_EVENT_ALARM:
		ast->AST_EVE = AST_EVE_ALARM0;
		break;

	case AST_EVENT_PER:
		ast->AST_EVE = AST_EVE_PER0;
		break;

	case AST_EVENT_OVF:
		ast->AST_EVE = AST_EVE_OVF;
		break;

	default:
		break;
	}

	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}

/**
 * \brief This function disables the AST event.
 *
 * \param ast          Base address of the AST.
 * \param source  AST event flag to be disabled.
 */
void ast_disable_event(Ast *ast, ast_event_source_t source)
{
	/* Wait until the ast CTRL register is up-to-date */
	while (ast_is_busy(ast)) {
	}

	switch (source) {
	case AST_EVENT_ALARM:
		ast->AST_EVD = AST_EVD_ALARM0;
		break;

	case AST_EVENT_PER:
		ast->AST_EVD = AST_EVD_PER0;
		break;

	case AST_EVENT_OVF:
		ast->AST_EVD = AST_EVD_OVF;
		break;

	default:
		break;
	}

	/* Wait until write is done */
	while (ast_is_busy(ast)) {
	}
}
