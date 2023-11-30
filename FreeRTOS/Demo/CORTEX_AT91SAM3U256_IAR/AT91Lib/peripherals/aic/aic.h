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
/// \unit
///
/// !Purpose
/// 
/// Methods and definitions for configuring interrupts using the Advanced
/// Interrupt Controller (AIC).
/// 
/// !Usage
///
/// -# Configure an interrupt source using AIC_ConfigureIT
/// -# Enable or disable interrupt generation of a particular source with
///    AIC_EnableIT and AIC_DisableIT.
///
/// \note Most of the time, peripheral interrupts must be also configured
/// inside the peripheral itself.
//------------------------------------------------------------------------------

#ifndef AIC_H
#define AIC_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include <board.h>

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------

#ifndef AT91C_AIC_SRCTYPE_INT_HIGH_LEVEL
    /// Interrupt is internal and uses a logical 1 level.
    #define AT91C_AIC_SRCTYPE_INT_HIGH_LEVEL AT91C_AIC_SRCTYPE_INT_LEVEL_SENSITIVE
#endif

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

extern void AIC_ConfigureIT(unsigned int source,
                                   unsigned int mode,
                                   void (*handler)( void ));

extern void AIC_EnableIT(unsigned int source);

extern void AIC_DisableIT(unsigned int source);

#endif //#ifndef AIC_H

