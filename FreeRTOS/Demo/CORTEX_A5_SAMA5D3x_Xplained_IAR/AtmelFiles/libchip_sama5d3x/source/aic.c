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

/** \addtogroup aic_module
 *
 * The Advanced Interrupt Controller (AIC) is an 8-level priority, individually 
 * maskable, vectored interrupt controller, providing handling of up to thirty-two interrupt sources. 
 *
 * \section Usage
 * <ul>
 * <li> Each interrupt source can be enabled or disabled by using the IRQ_EnableIT() and IRQ_DisableIT()</li>
 * <li> Configure the AIC interrupt to its requirements and special needs,such as priorty 
 * level, source type and configure the addresses of the corresponding handler for each interrupt source
 * could be setting by  IRQ_ConfigureIT(). </li>
 * <li> Start conversion by setting ADC_CR_START in ADC_CR. </li>
 * </ul>
 *
 * For more accurate information, please look at the AIC section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref aic.c\n
 * \ref irq.h\n
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

#include <stdint.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Configures an interrupt in the AIC. The interrupt is identified by its
 * source (ID_xxx) and is configured to use the specified mode and
 * interrupt handler function. Mode is the value that will be put in AIC_SMRx
 * and the function address will be set in AIC_SVRx.
 * The interrupt is disabled before configuration, so it is useless
 * to do it before calling this function. When AIC_ConfigureIT returns, the
 * interrupt will always be disabled and cleared; it must be enabled by a
 * call to AIC_EnableIT().
 *
 * \param source  Interrupt source to configure.
 * \param mode  Triggering mode and priority of the interrupt.
 * \param handler  Interrupt handler function.
 */
uint32_t IRQ_ConfigureIT(uint32_t source,
                     uint32_t mode,
                     void( *handler )( void ))
{
    uint32_t prevHandler;
    PMC->PMC_PCER1 = (1 << ( ID_IRQ - 32));
    AIC->AIC_SSR  = source;
    prevHandler = AIC->AIC_SVR;
    /* Disable the interrupt first */
    AIC->AIC_IDCR = AIC_IDCR_INTD;
    /* Configure mode and handler */
    AIC->AIC_SMR  = mode;
    AIC->AIC_SVR = (uint32_t) handler;
    /* Clear interrupt */
    AIC->AIC_ICCR = AIC_ICCR_INTCLR;
    return prevHandler;
}


/**
 * \brief Enables interrupts coming from the given (unique) source (ID_xxx).
 *
 * \param source  Interrupt source to enable.
 */
void IRQ_EnableIT(uint32_t source)
{
    AIC->AIC_SSR  = source;
    AIC->AIC_IECR = AIC_IECR_INTEN;
}

/**
 * \brief Disables interrupts coming from the given (unique) source (ID_xxx).
 *
 * \param source  Interrupt source to disable.
 */
void IRQ_DisableIT(uint32_t source)
{
    AIC->AIC_SSR  = source;
    AIC->AIC_IDCR = AIC_IDCR_INTD ;
}

