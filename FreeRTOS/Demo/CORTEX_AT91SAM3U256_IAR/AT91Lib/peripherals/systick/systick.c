/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "systick.h"

//------------------------------------------------------------------------------
/// Configures the SysTick in .
/// \param countEnable  Enable SysTick counting.
/// \param reloadValue  Value used for tick counter to reload.
/// \param handler      Interrupt handler function, 0 to disable interrupt.
//------------------------------------------------------------------------------
void SysTick_Configure(unsigned char countEnable,
                           unsigned int reloadValue,
                           void( *handler )( void ))
{
    unsigned int intEnable = handler ? AT91C_NVIC_STICKINT : 0;

    // Disable the SysTick & using core source
    AT91C_BASE_NVIC->NVIC_STICKCSR = AT91C_NVIC_STICKCLKSOURCE;

    // Reset the current value
    AT91C_BASE_NVIC->NVIC_STICKCVR &= ~AT91C_NVIC_STICKCURRENT;

    // Setup the reload value
    AT91C_BASE_NVIC->NVIC_STICKRVR = reloadValue;

    // Enable the SysTick
    AT91C_BASE_NVIC->NVIC_STICKCSR =  AT91C_NVIC_STICKCLKSOURCE
                                    | AT91C_NVIC_STICKENABLE
                                    | intEnable;

}

