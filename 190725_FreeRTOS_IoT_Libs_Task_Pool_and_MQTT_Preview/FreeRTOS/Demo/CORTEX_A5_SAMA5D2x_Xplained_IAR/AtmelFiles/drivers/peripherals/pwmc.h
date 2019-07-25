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

/**
 * \file
 *
 * \par Purpose
 *
 * Interface for configuration the Pulse Width Modulation Controller (PWM) peripheral.
 *
 * \par Usage
 *
 *    -# Configures PWM clocks A & B to run at the given frequencies using
 *       pwmc_configure_clocks().
 *    -# Configure PWMC channel using pwmc_configure_channel(), pwmc_set_period()
 *       and pwmc_set_duty_cycle().
 *    -# Enable & disable channel using pwmc_enable_channel() and pwmc_disable_channel().
 *    -# Enable & disable the period interrupt for the given PWM channel using
 *       pwmc_enable_channel_it() and pwmc_disable_channel_it().
 *
 */

#ifndef _PWMC_
#define _PWMC_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Configures PWM clocks
 * \param p_pwm  Pointer to a Pwm instance
 * \param mode  PWM clock source selection and divide factor.
 */
extern void pwmc_configure_clocks(Pwm * p_pwm, uint32_t mode);

/**
 * \brief Enables the given PWM channel.
 *
 * This does NOT enable the corresponding pin; this must be done in the user
 * code.
 *
 * \param p_pwm  Pointer to a Pwm instance
 * \param channel  Channel number.
 */
extern void pwmc_enable_channel(Pwm * p_pwm, uint8_t channel);

/**
 * \brief Disables the given PWM channel.
 *
 * Beware, the channel will be effectively disabled at the end of the current
 * period.
 * Applications may check whether the channel is disabled using the following
 * wait loop:
 * 	while ((PWM->PWM_SR & (1 << channel)) != 0) {};
 *
 * \param p_pwm  Pointer to a Pwm instance
 * \param channel  Channel number.
 */
extern void pwmc_disable_channel(Pwm * p_pwm, uint8_t channel);

/**
 * \brief Enables the selected interrupts sources on a PWMC peripheral.
 * \param p_pwm  Pointer to a Pwm instance
 * \param channel  Channel number.
 */
extern void pwmc_enable_channel_it(Pwm * p_pwm, uint8_t channel);

/**
 * \brief Disables the selected interrupts sources on a PWMC peripheral.
 * \param p_pwm  Pointer to a Pwm instance
 * \param channel  Channel number.
 */
extern void pwmc_disable_channel_it(Pwm * p_pwm, uint8_t channel);

/**
 * \brief Configures a PWM channel with the given parameters, basic configure
 * function.
 *
 * The PWM controller must have been clocked in the PMC prior to calling this
 * function.
 * Beware: this function disables the channel. It will wait until the channel is
 * effectively disabled.
 *
 * \param p_pwm  Pointer to a Pwm instance
 * \param channel  Channel number.
 * \param mode  Channel mode.
 */
extern void pwmc_configure_channel(Pwm * p_pwm, uint8_t channel, uint32_t mode);

/**
 * \brief Sets the period value used by a PWM channel.
 *
 * This function writes directly to the CPRD register if the channel is
 * disabled. Otherwise it sets the update register CPRDUPD.
 *
 * \param p_pwm  Pointer to a Pwm instance
 * \param channel  Channel number.
 * \param period  Period value.
 */
extern void pwmc_set_period(Pwm * p_pwm, uint8_t channel, uint16_t period);

/**
 * \brief Sets the duty cycle used by a PWM channel.
 * This function writes directly to the CDTY register if the channel is
 * disabled. Otherwise it sets the update register CDTYUPD.
 * Note that the duty cycle must always be inferior or equal to the channel
 * period.
 *
 * \param p_pwm  Pointer to a Pwm instance
 * \param channel  Channel number.
 * \param duty  Duty cycle value.
 */
extern void pwmc_set_duty_cycle(Pwm * p_pwm, uint8_t channel, uint16_t duty);

#ifdef __cplusplus
}
#endif
#endif				/* #ifndef _PWMC_ */
