/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/** \addtogroup aic_module
 *
 * \section Purpose
 * The Advanced Interrupt Controller (AIC) is an 8-level priority, individually
 * maskable, vectored interrupt controller, providing handling of up to thirty-two interrupt sources.
 *
 * \section Usage
 * <ul>
 * <li> Each interrupt source can be enabled or disabled by using the aic_enable() and aic_disable()</li>
 * </ul>
 *
 * For more accurate information, please look at the AIC section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref aic.c\n
 * \ref aic.h\n
 */
/*@{*/
/*@}*/

/**
* \file
*
* Implementation of Advanced Interrupt Controller (AIC) controller.
*
*/

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "peripherals/aic.h"
#include "peripherals/matrix.h"
#include "cortex-a/cp15.h"
#include "cortex-a/cp15_pmu.h"
#include "cortex-a/cpsr.h"

#include <stdint.h>
#include <assert.h>

/*------------------------------------------------------------------------------
 *         Local functions
 *------------------------------------------------------------------------------*/

/**
 * \brief Default interrupt handler.
 */
static void _aic_default_irq_handler(void)
{
	while (1);
}

/**
 * \brief Interrupt Init.
 */
static void _aic_initialize(Aic* aic)
{
	uint32_t i;

	/* Disable all interrupts */
	for (i = 1; i < ID_PERIPH_COUNT; i++)
	{
		aic->AIC_SSR = i;
		aic->AIC_IDCR = AIC_IDCR_INTD;
	}

	/* Clear All pending interrupts flags */
	for (i = 0; i < ID_PERIPH_COUNT; i++)
	{
		aic->AIC_SSR = i;
		aic->AIC_ICCR = AIC_ICCR_INTCLR;
	}

	/* Perform 8 IT acknowledge (write any value in EOICR) (VPy) */
	for (i = 0; i < 8; i++)
		aic->AIC_EOICR = 0;

	/* Assign default handler */
	for (i = 0; i < ID_PERIPH_COUNT; i++)
	{
		aic->AIC_SSR = i;
		aic->AIC_SVR = (uint32_t)_aic_default_irq_handler;
	}
	aic->AIC_SPU = (uint32_t)_aic_default_irq_handler;
}

/**
 * \brief Configures an interrupt in the AIC. The interrupt is identified by its
 * source (ID_xxx) and is configured to use the specified mode and
 * interrupt handler function. Mode is the value that will be put in AIC_SMRx
 * and the function address will be set in AIC_SVRx.
 * The interrupt is disabled before configuration, so it is useless
 * to do it before calling this function. When aic_configure returns, the
 * interrupt will always be disabled and cleared; it must be enabled by a
 * call to aic_enable().
 *
 * \param source  Interrupt source to configure.
 * \param mode  Triggering mode and priority of the interrupt.
 * \param handler  Interrupt handler function.
 */

static void _aic_configure_it(uint32_t source, uint8_t mode)
{
	AIC->AIC_SSR = source;
	/* Disable the interrupt first */
	AIC->AIC_IDCR = AIC_IDCR_INTD;
	/* Configure mode and handler */
	AIC->AIC_SMR = mode;
	/* Clear interrupt */
	AIC->AIC_ICCR = AIC_ICCR_INTCLR;
}

/**
 * \brief Enables interrupts coming from the given AIC and (unique) source (ID_xxx).
 *
 * \param aic  AIC instance.
 * \param source  Interrupt source to enable.
 */
static void _aic_enable_it(Aic * aic, uint32_t source)
{
	aic->AIC_SSR = AIC_SSR_INTSEL(source);
	aic->AIC_IECR = AIC_IECR_INTEN;
}

/**
 * \brief Disables interrupts coming from the given AIC and (unique) source (ID_xxx).
 *
 * \param aic  AIC instance.
 * \param source  Interrupt source to disable.
 */
static void _aic_disable_it(Aic * aic, uint32_t source)
{
	aic->AIC_SSR = AIC_SSR_INTSEL(source);
	aic->AIC_IDCR = AIC_IDCR_INTD;
}

/**
 * \brief Configure corresponding handler for the interrupts coming from the given (unique) source (ID_xxx).
 *
 * \param aic  AIC instance.
 * \param source  Interrupt source to configure.
 * \param handler handler for the interrupt.
 */
static void _aic_set_source_vector(Aic * aic, uint32_t source, void (*handler)(void))
{
	if (aic->AIC_WPMR & AIC_WPMR_WPEN) {
		aic_write_protection(aic, 1);
	}
	aic->AIC_SSR = AIC_SSR_INTSEL(source);
	aic->AIC_SVR = (uint32_t)handler;
}

/**
 * \brief Configure the spurious interrupt handler
 *
 * \param aic  AIC instance.
 * \param handler handler for the interrupt.
 */
static void _aic_set_spurious_vector(Aic * aic, void (*handler)(void))
{
	if (aic->AIC_WPMR & AIC_WPMR_WPEN) {
		aic_write_protection(aic, 1);
	}
	aic->AIC_SPU = (uint32_t)handler;
}

/**
 * \brief Clears interrupts coming from the given AIC and (unique) source (ID_xxx).
 *
 * \param aic  AIC instance.
 * \param source  Interrupt source to disable.
 */
static void _aic_clear_it(Aic * aic, uint32_t source)
{
	aic->AIC_SSR = AIC_SSR_INTSEL(source);
	aic->AIC_ICCR = AIC_ICCR_INTCLR;
}

/**
 * \brief Sets interrupts coming from the given AIC and (unique) source (ID_xxx).
 *
 * \param aic  AIC instance.
 * \param source  Interrupt source to disable.
 */
static void _aic_set_it(Aic * aic, uint32_t source)
{
	aic->AIC_SSR = AIC_SSR_INTSEL(source);
	aic->AIC_ISCR = AIC_ISCR_INTSET;
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Set the default handler for all interrupts
 */
void aic_initialize(void)
{
	/* Disable IRQ and FIQ at core level */
	v_arm_set_cpsr_bits(CPSR_MASK_IRQ | CPSR_MASK_FIQ);

	/* Set default vectors */
	_aic_initialize(AIC);
	_aic_initialize(SAIC);

	/* Redirect all interrupts to Non-secure AIC */
	SFR->SFR_AICREDIR = (SFR_AICREDIR_AICREDIRKEY(AICREDIR_KEY) ^ SFR->SFR_SN1) |
	                    SFR_AICREDIR_NSAIC;

	/* Enable IRQ and FIQ at core level */
	v_arm_clr_cpsr_bits(CPSR_MASK_IRQ | CPSR_MASK_FIQ);
}

/**
 * \brief Enables interrupts coming from the given (unique) source (ID_xxx).
 *
 * \param source  Interrupt source to enable.
 */
void aic_enable(uint32_t source)
{
	if (SFR->SFR_AICREDIR) {
		_aic_enable_it(AIC, source);
		return;
	}

	Matrix* matrix = get_peripheral_matrix(source);
	if (!matrix_is_peripheral_secured(matrix, source)) {
		_aic_enable_it(AIC, source);
	} else {
		_aic_enable_it(SAIC, source);
	}
}

/**
 * \brief Disables interrupts coming from the given (unique) source (ID_xxx).
 *
 * \param source  Interrupt source to disable.
 */
void aic_disable(uint32_t source)
{
	if (SFR->SFR_AICREDIR) {
		_aic_disable_it(AIC, source);
		return;
	}

	Matrix* matrix = get_peripheral_matrix(source);
	if (!matrix_is_peripheral_secured(matrix, source)) {
		_aic_disable_it(AIC, source);
	} else {
		_aic_disable_it(SAIC, source);
	}
}

/**
 * \brief Configure interrupts' source mode.
 *
 * \param source  Interrupt source to configure.
 * \param mode    mode combined of priority level and interrupt source type.
 */
void aic_configure(uint32_t source, uint8_t mode)
{
	if (SFR->SFR_AICREDIR) {
		_aic_configure_it(source, mode);
		return;
	}

	Matrix* matrix = get_peripheral_matrix(source);
	if (!matrix_is_peripheral_secured(matrix, source)) {
		_aic_configure_it(source, mode);
	} else {
		// Does not apply for SAIC
	}
}

/**
 * \brief Configure corresponding handler for the interrupts coming from the given (unique) source (ID_xxx).
 *
 * \param source  Interrupt source to configure.
 * \param handler handler for the interrupt.
 */
void aic_set_source_vector(uint32_t source, void (*handler)(void))
{
	Aic *aic = AIC;

	if (SFR->SFR_AICREDIR == 0) {
		Matrix* matrix = get_peripheral_matrix(source);
		if (matrix_is_peripheral_secured(matrix, source))
			aic = SAIC;
	}
	_aic_set_source_vector(aic, source, handler);
}

/**
 * \brief Configure the spurious interrupt handler
 *
 * \param handler handler for the interrupt.
 */
void aic_set_spurious_vector(void (*handler)(void))
{
	Aic *aic = AIC;

	if (SFR->SFR_AICREDIR == 0) {
		aic = SAIC;
	}

	_aic_set_spurious_vector(aic, handler);
}

/**
 * \brief Configure interrupts' source mode.
 *
 * \param source  Interrupt source to configure.
 * \param mode    mode combined of priority level and interrupt source type.
 */
void aic_set_or_clear(uint32_t source, uint8_t set)
{
	Aic *aic = AIC;

	if (SFR->SFR_AICREDIR == 0) {
		Matrix* matrix = get_peripheral_matrix(source);
		if (matrix_is_peripheral_secured(matrix, source))
			aic = SAIC;
	}

	if (set) {
		_aic_set_it(aic, source);
	} else {
		_aic_clear_it(aic, source);
	}
}

/**
 * \brief Indicate treatment completion for interrupts coming from the given AIC and (unique) source (ID_xxx).
 *
 * \param aic  AIC instance.
 */
void aic_end_interrupt(Aic * aic)
{
	aic->AIC_EOICR = AIC_EOICR_ENDIT;
}

/**
 * \brief Configuration of protection mode and general interrupt mask for debug.
 *
 * \param aic     AIC instance.
 * \param protect Enable/Disable protection mode.
 * \param mask    Enable/Disable mask IRQ and FIQ.
 *
 * \retval        0 - succeed.  1 - failed.
 */
uint32_t aic_debug_config(Aic * aic, uint8_t protect, uint8_t mask)
{
	uint32_t tmp;

	/* return in case the "Write Protection Mode" is enabled */
	if (aic->AIC_WPMR & AIC_WPMR_WPEN)
		return 1;

	tmp = protect ? (1 << 1) : (0 << 1);
	if (mask)
		tmp++;
	aic->AIC_DCR = tmp;
	return 0;
}

/**
 * \brief Enable/Disable AIC write protection mode.
 *
 * \param aic     AIC instance.
 * \param enable  Enable/Disable AIC write protection mode.
 */
void aic_write_protection(Aic * aic, uint32_t enable)
{
	if (enable) {
		aic->AIC_WPMR = AIC_WPMR_WPKEY_PASSWD | AIC_WPMR_WPEN;
	} else {
		aic->AIC_WPMR = AIC_WPMR_WPKEY_PASSWD;
	}
}

/**
 * \brief Get AIC Write Protection Status.
 *
 * \param aic     AIC instance.
 * \param pViolationSource pointer to address to store the violation source
 *
 * \retval        0 - No violation occured.  1 - violation occured.
 */
uint32_t aic_violation_occured(Aic * aic, uint32_t * pViolationSource)
{
	if (aic->AIC_WPSR & AIC_WPSR_WPVS) {
		*pViolationSource =
		    (aic->
		     AIC_WPSR & AIC_WPSR_WPVSRC_Msk) >> AIC_WPSR_WPVSRC_Pos;
	}
	return 0;
}
