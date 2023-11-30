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

#include "board.h"
#include "irq.h"
#include "exceptions.h"
#include <utility/trace.h>

/// The index of IRQ handler in the exception table
#define NVIC_IRQ_HANDLER_INDEX     16

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Configures an interrupt in the NVIC. The interrupt is identified by its
/// source (AT91C_ID_xxx) and is configured to a specified priority and
/// interrupt handler function. priority is the value that will be put in NVIC_IPRx
/// and the function address will be set in "ExceptionTable". The parameter priority
/// will include the preemptionPriority and the subPriority, where the subPriority
/// defined in the B[7:0] of the parameter "priority", and the preemptionPriority defined
/// in the B[15:8] of the parameter "priority". 
/// The interrupt is disabled before configuration, so it is useless
/// to do it before calling this function. When NVIC_ConfigureIT returns, the
/// interrupt will always be disabled and cleared; it must be enabled by a
/// call to NVIC_EnableIT().
/// \param source               Interrupt source to configure.
/// \param priority              Pre-emption priority (B[15:8] )+ subPriority (B[7:0])
/// \param handler              Interrupt handler function.
//------------------------------------------------------------------------------
void IRQ_ConfigureIT(
    unsigned int source,
    //unsigned int preemptionPriority,
    //unsigned int subPriority,
    unsigned int priority,
    IntFunc handler)
{
    unsigned int priGroup = __NVIC_PRIO_BITS;
    unsigned int nPre = 7 - priGroup;
    unsigned int nSub = priGroup + 1;
    unsigned int preemptionPriority;
    unsigned int subPriority;
    unsigned int IRQpriority;

    preemptionPriority = (priority & 0xff00) >> 8;
    subPriority = (priority & 0xff);

    // Disable the interrupt first
    NVIC_DisableIRQ((IRQn_Type)source);

    // Clear any pending status
    NVIC_ClearPendingIRQ((IRQn_Type)source);

    // Configure interrupt handler
    //if (handler == 0) handler = IrqHandlerNotUsed;
      //  GetExceptionTable()[NVIC_IRQ_HANDLER_INDEX + source] = handler;

    if (subPriority >= (0x01 << nSub))
      subPriority = (0x01 << nSub) - 1;
    if (preemptionPriority >= (0x01 << nPre))
      preemptionPriority = (0x01 << nPre) - 1;

    IRQpriority = (subPriority | (preemptionPriority << nSub));
    NVIC_SetPriority((IRQn_Type)source, IRQpriority);
}

//------------------------------------------------------------------------------
/// Enables interrupt coming from the given (unique) source (AT91C_ID_xxx).
/// \param source  Interrupt source to enable.
//------------------------------------------------------------------------------
void IRQ_EnableIT(unsigned int source)
{
    NVIC_EnableIRQ((IRQn_Type)source);
}

//------------------------------------------------------------------------------
/// Disables interrupt coming from the given (unique) source (AT91C_ID_xxx).
/// \param source  Interrupt source to disable.
//------------------------------------------------------------------------------
void IRQ_DisableIT(unsigned int source)
{
    NVIC_DisableIRQ((IRQn_Type)source);
}

//------------------------------------------------------------------------------
/// Set interrupt pending bit from the given (unique) source (AT91C_ID_xxx).
/// \param source  Interrupt source to set.
//------------------------------------------------------------------------------
void NVIC_SetPending(unsigned int source)
{
    NVIC_SetPendingIRQ((IRQn_Type)source);
}

//------------------------------------------------------------------------------
/// Clear interrupt pending bit from the given (unique) source (AT91C_ID_xxx).
/// \param source  Interrupt source to clear.
//------------------------------------------------------------------------------
void NVIC_ClrPending(unsigned int source)
{
    NVIC_ClearPendingIRQ((IRQn_Type)source);
}

#if !defined(USE_CMSIS_on)
//------------------------------------------------------------------------------
/// Use the Software Trigger Interrupt Register to pend an interrupt.
/// \param source Interrupt source to trigger.
//------------------------------------------------------------------------------
void NVIC_Swi(unsigned int source)
{
    AT91C_BASE_NVIC->NVIC_STIR = source;
}
#endif

