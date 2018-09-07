/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

/** \addtogroup pwm_module Working with PWM
 * The PWM driver provides the interface to configure and use the PWM
 * peripheral.
 *
 * The PWM macrocell controls square output waveforms of 4 channels.
 * Characteristics of output waveforms such as period, duty-cycle can be configured.\n
 *
 * Before enabling the channels, they must have been configured first.
 * The main settings include:
 * <ul>
 * <li>Configuration of the clock generator.</li>
 * <li>Selection of the clock for each channel.</li>
 * <li>Configuration of output waveform characteristics, such as period, duty-cycle etc.</li>
 * </ul>
 *
 * After the channels is enabled, the user must use respective update registers
 * to change the wave characteristics to prevent unexpected output waveform.
 * i.e. PWM_CUPDx register should be used if user want to change duty-cycle
 * when the channel is enabled.
 *
 * For more accurate information, please look at the PWM section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref pwmc.c\n
 * \ref pwmc.h.\n
 */
/*@{*/
/*@}*/

/**
 * \file
 *
 * Implementation of the Pulse Width Modulation Controller (PWM) peripheral.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Configures PWM clocks  
 */
void PWMC_ConfigureClocks(Pwm* pPwm, uint32_t mode)
{
    pPwm->PWM_CLK= mode;
}

/**
 * \brief Enables the given PWM channel.
 *
 * This does NOT enable the corresponding pin;this must be done in the user code.
 *
 * \param channel  Channel number.
 */
void PWMC_EnableChannel(Pwm* pPwm,uint8_t channel)
{
    pPwm->PWM_ENA= 0x1ul<<channel;  
}

/**
 * \brief Disables the given PWM channel.
 *
 * Beware, channel will be effectively disabled at the end of the current period.
 * Application can check channel is disabled using the following wait loop:
 * while ((PWM->PWM_SR & (1 << channel)) != 0);
 *
 * \param channel  Channel number.
 */
void PWMC_DisableChannel(Pwm* pPwm,uint8_t channel)
{
    pPwm->PWM_DIS= 0x1ul<<channel;    
}

/**
 * \brief Enables the selected interrupts sources on a PWMC peripheral. 
 */
void PWMC_EnableChannelIt(Pwm* pPwm,uint8_t channel)
{
    pPwm->PWM_IER1= 0x1ul<<channel;  
}

/**
 * \brief Disables the selected interrupts sources on a PWMC peripheral. 
 */
void PWMC_DisableChannelIt(Pwm* pPwm,uint8_t channel)
{
   pPwm->PWM_IDR1 = 0x1ul<<channel;
}

/**
 * \brief Configures PWM a channel with the given parameters, basic configure function.
 *
 * The PWM controller must have been clocked in the PMC prior to calling this
 * function.
 * Beware: this function disables the channel. It waits until disable is effective.
 *
 * \param channel  Channel number.
 * \param prescaler  Channel prescaler.
 * \param alignment  Channel alignment.
 * \param polarity  Channel polarity.
 */
void PWMC_ConfigureChannel(Pwm* pPwm,uint8_t channel,uint32_t mode)
{
    pPwm->PWM_CH_NUM[channel].PWM_CMR= mode;
}

/**
 * \brief Sets the period value used by a PWM channel.
 *
 * This function writes directly to the CPRD register if the channel is disabled;
 * otherwise, it uses the update register CPRDUPD.
 *
 * \param channel Channel number.
 * \param period  Period value.
 */
void PWMC_SetPeriod( Pwm* pPwm, uint8_t channel, uint16_t period)
{
    /* If channel is disabled, write to CPRD */
    if ((pPwm->PWM_SR & (1 << channel)) == 0) {
        pPwm->PWM_CH_NUM[channel].PWM_CPRD = period;
    }
    /* Otherwise use update register */
    else {
        pPwm->PWM_CH_NUM[channel].PWM_CPRDUPD = period;
    }
}

/**
 * \brief Sets the duty cycle used by a PWM channel.
 * This function writes directly to the CDTY register if the channel is disabled;
 * otherwise it uses the update register CDTYUPD.
 * Note that the duty cycle must always be inferior or equal to the channel
 * period.
 *
 * \param channel  Channel number.
 * \param duty     Duty cycle value.
 */
void PWMC_SetDutyCycle( Pwm* pPwm, uint8_t channel, uint16_t duty)
{
    assert(duty <= pPwm->PWM_CH_NUM[channel].PWM_CPRD);

    /* If channel is disabled, write to CDTY */
    if ((pPwm->PWM_SR & (1 << channel)) == 0) {
        pPwm->PWM_CH_NUM[channel].PWM_CDTY = duty;
    }
    /* Otherwise use update register */
    else {
        pPwm->PWM_CH_NUM[channel].PWM_CDTYUPD = duty;
    }
}


