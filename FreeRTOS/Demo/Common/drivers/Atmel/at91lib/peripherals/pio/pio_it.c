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

/// Disable traces for this file
#ifndef NOTRACE
    #define NOTRACE
#endif

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "pio_it.h"
#include "pio.h"
#include <aic/aic.h>
#include <board.h>
#include <utility/assert.h>
#include <utility/trace.h>

//------------------------------------------------------------------------------
//         Local definitions
//------------------------------------------------------------------------------

/// Returns the current value of a register.
#define READ(peripheral, register)          (peripheral->register)
/// Modifies the current value of a register.
#define WRITE(peripheral, register, value)  (peripheral->register = value)

/// Maximum number of interrupt sources that can be defined.
#define MAX_INTERRUPT_SOURCES       7

//------------------------------------------------------------------------------
//         Local types
//------------------------------------------------------------------------------

/// Describes a PIO interrupt source, including the PIO instance triggering the
/// interrupt and the associated interrupt handler.
typedef struct _InterruptSource {

    /// Interrupt source pin.
    const Pin *pPin;

    /// Interrupt handler.
    void (*handler)(const Pin *);

} InterruptSource;

//------------------------------------------------------------------------------
//         Local variables
//------------------------------------------------------------------------------

/// List of interrupt sources.
static InterruptSource pSources[MAX_INTERRUPT_SOURCES];

/// Number of currently defined interrupt sources.
static unsigned int numSources;

//------------------------------------------------------------------------------
//         Local functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Handles all interrupts on the given PIO controller.
/// \param id  PIO controller ID.
/// \param pBase  PIO controller base address.
//------------------------------------------------------------------------------
void PioInterruptHandler(unsigned int id, AT91S_PIO *pBase)
{
    unsigned int status;
    unsigned int i;

    // Check PIO controller status
    status = pBase->PIO_ISR;
    status &= pBase->PIO_IMR;
    if (status != 0) {

        trace_LOG(trace_DEBUG, "-D- PIO interrupt on PIO controller #%d\n\r", id);

        // Check all sources
        i = 0;
        while (status != 0) {

            // There cannot be an unconfigured source enabled.
            SANITY_CHECK(i < numSources);

            // Source if configured on PIOA
            if (pSources[i].pPin->id == id) {

                // Source has PIOs which have changed
                if ((status & pSources[i].pPin->mask) != 0) {

                    trace_LOG(trace_DEBUG, "-D- Interrupt source #%d triggered\n\r", i);

                    pSources[i].handler(pSources[i].pPin);
                    status &= ~(pSources[i].pPin->mask);
                }
            }
            i++;
        }
    }
}

//------------------------------------------------------------------------------
/// Generic PIO interrupt handler. Single entry point for interrupts coming
/// from any PIO controller (PIO A, B, C ...). Dispatches the interrupt to
/// the user-configured handlers.
//------------------------------------------------------------------------------
void InterruptHandler()
{
#if defined(AT91C_ID_PIOA)
    // Treat PIOA interrupts
    PioInterruptHandler(AT91C_ID_PIOA, AT91C_BASE_PIOA);
#endif

#if defined(AT91C_ID_PIOB)
    // Treat PIOB interrupts
    PioInterruptHandler(AT91C_ID_PIOB, AT91C_BASE_PIOB);
#endif

#if defined(AT91C_ID_PIOC)
    // Treat PIOC interrupts
    PioInterruptHandler(AT91C_ID_PIOC, AT91C_BASE_PIOC);
#endif

#if defined(AT91C_ID_PIOD)
    // Treat PIOD interrupts
    PioInterruptHandler(AT91C_ID_PIOD, AT91C_BASE_PIOD);
#endif

#if defined(AT91C_ID_PIOE)
    // Treat PIOE interrupts
    PioInterruptHandler(AT91C_ID_PIOE, AT91C_BASE_PIOE);
#endif

#if defined(AT91C_ID_PIOABCD)
    // Treat PIOABCD interrupts
    #if !defined(AT91C_ID_PIOA)
        PioInterruptHandler(AT91C_ID_PIOABCD, AT91C_BASE_PIOA);
    #endif
    #if !defined(AT91C_ID_PIOB)
        PioInterruptHandler(AT91C_ID_PIOABCD, AT91C_BASE_PIOB);
    #endif
    #if !defined(AT91C_ID_PIOC)
        PioInterruptHandler(AT91C_ID_PIOABCD, AT91C_BASE_PIOC);
    #endif
    #if !defined(AT91C_ID_PIOD)
        PioInterruptHandler(AT91C_ID_PIOABCD, AT91C_BASE_PIOD);
    #endif
#endif

#if defined(AT91C_ID_PIOABCDE)
    // Treat PIOABCDE interrupts
    #if !defined(AT91C_ID_PIOA)
        PioInterruptHandler(AT91C_ID_PIOABCDE, AT91C_BASE_PIOA);
    #endif
    #if !defined(AT91C_ID_PIOB)
        PioInterruptHandler(AT91C_ID_PIOABCDE, AT91C_BASE_PIOB);
    #endif
    #if !defined(AT91C_ID_PIOC)
        PioInterruptHandler(AT91C_ID_PIOABCDE, AT91C_BASE_PIOC);
    #endif
    #if !defined(AT91C_ID_PIOD)
        PioInterruptHandler(AT91C_ID_PIOABCDE, AT91C_BASE_PIOD);
    #endif
    #if !defined(AT91C_ID_PIOE)
        PioInterruptHandler(AT91C_ID_PIOABCDE, AT91C_BASE_PIOE);
    #endif
#endif

#if defined(AT91C_ID_PIOCDE)
    // Treat PIOCDE interrupts
    #if !defined(AT91C_ID_PIOC)
        PioInterruptHandler(AT91C_ID_PIOCDE, AT91C_BASE_PIOC);
    #endif
    #if !defined(AT91C_ID_PIOD)
        PioInterruptHandler(AT91C_ID_PIOCDE, AT91C_BASE_PIOD);
    #endif
    #if !defined(AT91C_ID_PIOE)
        PioInterruptHandler(AT91C_ID_PIOCDE, AT91C_BASE_PIOE);
    #endif
#endif

}

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Initializes the PIO interrupt management logic.
/// \param priority  PIO controller interrupts priority.
//------------------------------------------------------------------------------
void PIO_InitializeInterrupts(unsigned int priority)
{
    trace_LOG(trace_DEBUG, "-D- PIO_Initialize()\n\r");

    SANITY_CHECK((priority & ~AT91C_AIC_PRIOR) == 0);

    // Reset sources
    numSources = 0;

#ifdef AT91C_ID_PIOA
    // Configure PIO interrupt sources
    trace_LOG(trace_DEBUG, "-D- PIO_Initialize: Configuring PIOA\n\r");
    AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_PIOA;
    AT91C_BASE_PIOA->PIO_ISR;
    AT91C_BASE_PIOA->PIO_IDR = 0xFFFFFFFF;
    AIC_ConfigureIT(AT91C_ID_PIOA, priority, InterruptHandler);
    AIC_EnableIT(AT91C_ID_PIOA);
#endif

#ifdef AT91C_ID_PIOB
    trace_LOG(trace_DEBUG, "-D- PIO_Initialize: Configuring PIOB\n\r");
    AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_PIOB;
    AT91C_BASE_PIOB->PIO_ISR;
    AT91C_BASE_PIOB->PIO_IDR = 0xFFFFFFFF;
    AIC_ConfigureIT(AT91C_ID_PIOB, priority, InterruptHandler);
    AIC_EnableIT(AT91C_ID_PIOB);
#endif

#ifdef AT91C_ID_PIOC
    trace_LOG(trace_DEBUG, "-D- PIO_Initialize: Configuring PIOC\n\r");
    AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_PIOC;
    AT91C_BASE_PIOC->PIO_ISR;
    AT91C_BASE_PIOC->PIO_IDR = 0xFFFFFFFF;
    AIC_ConfigureIT(AT91C_ID_PIOC, priority, InterruptHandler);
    AIC_EnableIT(AT91C_ID_PIOC);
#endif

#ifdef AT91C_ID_PIOD
    trace_LOG(trace_DEBUG, "-D- PIO_Initialize: Configuring PIOD\n\r");
    AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_PIOD;
    AT91C_BASE_PIOC->PIO_ISR;
    AT91C_BASE_PIOC->PIO_IDR = 0xFFFFFFFF;
    AIC_ConfigureIT(AT91C_ID_PIOD, priority, InterruptHandler);
    AIC_EnableIT(AT91C_ID_PIOD);
#endif

#ifdef AT91C_ID_PIOE
    trace_LOG(trace_DEBUG, "-D- PIO_Initialize: Configuring PIOE\n\r");
    AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_PIOE;
    AT91C_BASE_PIOC->PIO_ISR;
    AT91C_BASE_PIOC->PIO_IDR = 0xFFFFFFFF;
    AIC_ConfigureIT(AT91C_ID_PIOE, priority, InterruptHandler);
    AIC_EnableIT(AT91C_ID_PIOE);
#endif

#if defined(AT91C_ID_PIOABCD)
    // Treat PIOABCD interrupts
    #if !defined(AT91C_ID_PIOA) \
     && !defined(AT91C_ID_PIOB) \
     && !defined(AT91C_ID_PIOC) \
     && !defined(AT91C_ID_PIOD)

        trace_LOG(trace_DEBUG, "-D- PIO_Initialize: Configuring PIOABCD\n\r");
        AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_PIOABCD;
        AT91C_BASE_PIOA->PIO_ISR;
        AT91C_BASE_PIOA->PIO_IDR = 0xFFFFFFFF;
        AIC_ConfigureIT(AT91C_ID_PIOABCD, priority, InterruptHandler);
        AIC_EnableIT(AT91C_ID_PIOABCD);
    #endif
#endif

#if defined(AT91C_ID_PIOABCDE)
    // Treat PIOABCDE interrupts
    #if !defined(AT91C_ID_PIOA) \
     && !defined(AT91C_ID_PIOB) \
     && !defined(AT91C_ID_PIOC) \
     && !defined(AT91C_ID_PIOD) \
     && !defined(AT91C_ID_PIOE)

        trace_LOG(trace_DEBUG, "-D- PIO_Initialize: Configuring PIOABCDE\n\r");
        AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_PIOABCDE;
        AT91C_BASE_PIOA->PIO_ISR;
        AT91C_BASE_PIOA->PIO_IDR = 0xFFFFFFFF;
        AIC_ConfigureIT(AT91C_ID_PIOABCDE, priority, InterruptHandler);
        AIC_EnableIT(AT91C_ID_PIOABCDE);
    #endif
#endif

#if defined(AT91C_ID_PIOCDE)
    // Treat PIOCDE interrupts
    #if !defined(AT91C_ID_PIOC) \
     && !defined(AT91C_ID_PIOD) \
     && !defined(AT91C_ID_PIOE)

        trace_LOG(trace_DEBUG, "-D- PIO_Initialize: Configuring PIOC\n\r");
        AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_PIOCDE;
        AT91C_BASE_PIOC->PIO_ISR;
        AT91C_BASE_PIOC->PIO_IDR = 0xFFFFFFFF;
        AIC_ConfigureIT(AT91C_ID_PIOCDE, priority, InterruptHandler);
        AIC_EnableIT(AT91C_ID_PIOCDE);
    #endif
#endif
}

//------------------------------------------------------------------------------
/// Configures an interrupt source.
/// \param pPin  Interrupt source.
/// \param handler  Desired interrupt handler for the source.
//------------------------------------------------------------------------------
void PIO_ConfigureIt(const Pin *pPin, void (*handler)(const Pin *))
{
    InterruptSource *pSource;

    trace_LOG(trace_DEBUG, "-D- PIO_ConfigureIt()\n\r");

    SANITY_CHECK(pPin);
    ASSERT(numSources < MAX_INTERRUPT_SOURCES,
           "-F- PIO_ConfigureIt: Increase MAX_INTERRUPT_SOURCES\n\r");

    // Define new source
    trace_LOG(trace_DEBUG, "-D- PIO_ConfigureIt: Defining new source #%d.\n\r", numSources);

    pSource = &(pSources[numSources]);
    pSource->pPin = pPin;
    pSource->handler = handler;
    numSources++;
}

//------------------------------------------------------------------------------
/// Enables the given interrupt source if it has been configured.
/// \param pPin  Interrupt source to enable.
//------------------------------------------------------------------------------
void PIO_EnableIt(const Pin *pPin)
{
    trace_LOG(trace_DEBUG, "-D- PIO_EnableIt()\n\r");

    SANITY_CHECK(pPin);

#ifndef NOASSERT
    unsigned int i = 0;
    unsigned char found = 0;
    while ((i < numSources) && !found) {

        if (pSources[i].pPin == pPin) {

            found = 1;
        }
        i++;
    }
    ASSERT(found, "-F- PIO_EnableIt: Interrupt source has not been configured\n\r");
#endif

    pPin->pio->PIO_ISR;
    pPin->pio->PIO_IER = pPin->mask;
}

//------------------------------------------------------------------------------
/// Disables a given interrupt source.
/// \param pPin  Interrupt source to disable.
//------------------------------------------------------------------------------
void PIO_DisableIt(const Pin *pPin)
{
    SANITY_CHECK(pPin);

    trace_LOG(trace_DEBUG, "-D- PIO_DisableIt()\n\r");

    pPin->pio->PIO_IDR = pPin->mask;
}

