//*****************************************************************************
//
// adc.c - Driver for the ADC.
//
// Copyright (c) 2005-2020 Texas Instruments Incorporated.  All rights reserved.
// Software License Agreement
// 
//   Redistribution and use in source and binary forms, with or without
//   modification, are permitted provided that the following conditions
//   are met:
// 
//   Redistributions of source code must retain the above copyright
//   notice, this list of conditions and the following disclaimer.
// 
//   Redistributions in binary form must reproduce the above copyright
//   notice, this list of conditions and the following disclaimer in the
//   documentation and/or other materials provided with the  
//   distribution.
// 
//   Neither the name of Texas Instruments Incorporated nor the names of
//   its contributors may be used to endorse or promote products derived
//   from this software without specific prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// 
// This is part of revision 2.2.0.295 of the Tiva Peripheral Driver Library.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup adc_api
//! @{
//
//*****************************************************************************

#include <stdbool.h>
#include <stdint.h>
#include "inc/hw_adc.h"
#include "inc/hw_ints.h"
#include "inc/hw_memmap.h"
#include "inc/hw_types.h"
#include "inc/hw_sysctl.h"
#include "driverlib/adc.h"
#include "driverlib/debug.h"
#include "driverlib/interrupt.h"

//*****************************************************************************
//
// These defines are used by the ADC driver to simplify access to the ADC
// sequencer's registers.
//
//*****************************************************************************
#define ADC_SEQ                 (ADC_O_SSMUX0)
#define ADC_SEQ_STEP            (ADC_O_SSMUX1 - ADC_O_SSMUX0)
#define ADC_SSMUX               (ADC_O_SSMUX0 - ADC_O_SSMUX0)
#define ADC_SSEMUX              (ADC_O_SSEMUX0 - ADC_O_SSMUX0)
#define ADC_SSCTL               (ADC_O_SSCTL0 - ADC_O_SSMUX0)
#define ADC_SSFIFO              (ADC_O_SSFIFO0 - ADC_O_SSMUX0)
#define ADC_SSFSTAT             (ADC_O_SSFSTAT0 - ADC_O_SSMUX0)
#define ADC_SSOP                (ADC_O_SSOP0 - ADC_O_SSMUX0)
#define ADC_SSDC                (ADC_O_SSDC0 - ADC_O_SSMUX0)
#define ADC_SSTSH               (ADC_O_SSTSH0 - ADC_O_SSMUX0)

//*****************************************************************************
//
// The currently configured software oversampling factor for each of the ADC
// sequencers.
//
//*****************************************************************************
static uint8_t g_pui8OversampleFactor[2][3];

//*****************************************************************************
//
//! Returns the interrupt number for a given ADC base address and sequence
//! number.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! This function returns the interrupt number for the ADC module and sequence
//! number provided in the \e ui32Base and \e ui32SequenceNum parameters.
//!
//! \return Returns the ADC sequence interrupt number or 0 if the interrupt
//! does not exist.
//
//*****************************************************************************
static uint_fast8_t
_ADCIntNumberGet(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    uint_fast8_t ui8Int;

    //
    // Determine the interrupt to register based on the sequence number.
    //
    if(CLASS_IS_TM4C123)
    {
        ui8Int = ((ui32Base == ADC0_BASE) ?
                  (INT_ADC0SS0_TM4C123 + ui32SequenceNum) :
                  (INT_ADC1SS0_TM4C123 + ui32SequenceNum));
    }
    else if(CLASS_IS_TM4C129)
    {
        ui8Int = ((ui32Base == ADC0_BASE) ?
                  (INT_ADC0SS0_TM4C129 + ui32SequenceNum) :
                  (INT_ADC1SS0_TM4C129 + ui32SequenceNum));
    }
    else
    {
        ui8Int = 0;
    }

    return(ui8Int);
}

//*****************************************************************************
//
//! Registers an interrupt handler for an ADC interrupt.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//! \param pfnHandler is a pointer to the function to be called when the
//! ADC sample sequence interrupt occurs.
//!
//! This function sets the handler to be called when a sample sequence
//! interrupt occurs.  This function enables the global interrupt in the
//! interrupt controller; the sequence interrupt must be enabled with
//! ADCIntEnable().  It is the interrupt handler's responsibility to clear the
//! interrupt source via ADCIntClear().
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
void
ADCIntRegister(uint32_t ui32Base, uint32_t ui32SequenceNum,
               void (*pfnHandler)(void))
{
    uint_fast8_t ui8Int;

    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Determine the interrupt to register based on the sequence number.
    //
    ui8Int = _ADCIntNumberGet(ui32Base, ui32SequenceNum);
    ASSERT(ui8Int != 0);

    //
    // Register the interrupt handler.
    //
    IntRegister(ui8Int, pfnHandler);

    //
    // Enable the timer interrupt.
    //
    IntEnable(ui8Int);
}

//*****************************************************************************
//
//! Unregisters the interrupt handler for an ADC interrupt.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! This function unregisters the interrupt handler.  This function disables
//! the global interrupt in the interrupt controller; the sequence interrupt
//! must be disabled via ADCIntDisable().
//!
//! \sa IntRegister() for important information about registering interrupt
//! handlers.
//!
//! \return None.
//
//*****************************************************************************
void
ADCIntUnregister(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    uint_fast8_t ui8Int;

    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Determine the interrupt to unregister based on the sequence number.
    //
    ui8Int = _ADCIntNumberGet(ui32Base, ui32SequenceNum);
    ASSERT(ui8Int != 0);

    //
    // Disable the interrupt.
    //
    IntDisable(ui8Int);

    //
    // Unregister the interrupt handler.
    //
    IntUnregister(ui8Int);
}

//*****************************************************************************
//
//! Disables a sample sequence interrupt.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! This function disables the requested sample sequence interrupt.
//!
//! \return None.
//
//*****************************************************************************
void
ADCIntDisable(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Disable this sample sequence interrupt.
    //
    HWREG(ui32Base + ADC_O_IM) &= ~(1 << ui32SequenceNum);
}

//*****************************************************************************
//
//! Enables a sample sequence interrupt.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! This function enables the requested sample sequence interrupt.  Any
//! outstanding interrupts are cleared before enabling the sample sequence
//! interrupt.
//!
//! \return None.
//
//*****************************************************************************
void
ADCIntEnable(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Clear any outstanding interrupts on this sample sequence.
    //
    HWREG(ui32Base + ADC_O_ISC) = 1 << ui32SequenceNum;

    //
    // Enable this sample sequence interrupt.
    //
    HWREG(ui32Base + ADC_O_IM) |= 1 << ui32SequenceNum;
}

//*****************************************************************************
//
//! Gets the current interrupt status.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//! \param bMasked is false if the raw interrupt status is required and true if
//! the masked interrupt status is required.
//!
//! This function returns the interrupt status for the specified sample
//! sequence.  Either the raw interrupt status or the status of interrupts that
//! are allowed to reflect to the processor can be returned.
//!
//! \return The current raw or masked interrupt status.
//
//*****************************************************************************
uint32_t
ADCIntStatus(uint32_t ui32Base, uint32_t ui32SequenceNum, bool bMasked)
{
    uint32_t ui32Temp;

    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Return either the interrupt status or the raw interrupt status as
    // requested.
    //
    if(bMasked)
    {
        ui32Temp = HWREG(ui32Base + ADC_O_ISC) & (0x10001 << ui32SequenceNum);
    }
    else
    {
        ui32Temp = (HWREG(ui32Base + ADC_O_RIS) &
                    (0x10000 | (1 << ui32SequenceNum)));

        //
        // If the digital comparator status bit is set, reflect it to the
        // appropriate sequence bit.
        //
        if(ui32Temp & 0x10000)
        {
            ui32Temp |= 0xF0000;
            ui32Temp &= ~(0x10000 << ui32SequenceNum);
        }
    }

    //
    // Return the interrupt status
    //
    return(ui32Temp);
}

//*****************************************************************************
//
//! Clears sample sequence interrupt source.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! The specified sample sequence interrupt is cleared, so that it no longer
//! asserts.  This function must be called in the interrupt handler to keep
//! the interrupt from being triggered again immediately upon exit.
//!
//! \note Because there is a write buffer in the Cortex-M processor, it may
//! take several clock cycles before the interrupt source is actually cleared.
//! Therefore, it is recommended that the interrupt source be cleared early in
//! the interrupt handler (as opposed to the very last action) to avoid
//! returning from the interrupt handler before the interrupt source is
//! actually cleared.  Failure to do so may result in the interrupt handler
//! being immediately reentered (because the interrupt controller still sees
//! the interrupt source asserted).
//!
//! \return None.
//
//*****************************************************************************
void
ADCIntClear(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Clear the interrupt.
    //
    HWREG(ui32Base + ADC_O_ISC) = 1 << ui32SequenceNum;
}

//*****************************************************************************
//
//! Enables a sample sequence.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! Allows the specified sample sequence to be captured when its trigger is
//! detected.  A sample sequence must be configured before it is enabled.
//!
//! \return None.
//
//*****************************************************************************
void
ADCSequenceEnable(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Enable the specified sequence.
    //
    HWREG(ui32Base + ADC_O_ACTSS) |= 1 << ui32SequenceNum;
}

//*****************************************************************************
//
//! Disables a sample sequence.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! Prevents the specified sample sequence from being captured when its trigger
//! is detected.  A sample sequence must be disabled before it is configured.
//!
//! \return None.
//
//*****************************************************************************
void
ADCSequenceDisable(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Disable the specified sequences.
    //
    HWREG(ui32Base + ADC_O_ACTSS) &= ~(1 << ui32SequenceNum);
}

//*****************************************************************************
//
//! Configures the trigger source and priority of a sample sequence.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//! \param ui32Trigger is the trigger source that initiates the sample
//! sequence; must be one of the \b ADC_TRIGGER_* values.
//! \param ui32Priority is the relative priority of the sample sequence with
//! respect to the other sample sequences.
//!
//! This function configures the initiation criteria for a sample sequence.
//! Valid sample sequencers range from zero to three; sequencer zero captures
//! up to eight samples, sequencers one and two capture up to four samples,
//! and sequencer three captures a single sample.  The trigger condition and
//! priority (with respect to other sample sequencer execution) are set.
//!
//! The \e ui32Trigger parameter can take on the following values:
//!
//! - \b ADC_TRIGGER_PROCESSOR - A trigger generated by the processor, via the
//!                              ADCProcessorTrigger() function.
//! - \b ADC_TRIGGER_COMP0 - A trigger generated by the first analog
//!                          comparator; configured with ComparatorConfigure().
//! - \b ADC_TRIGGER_COMP1 - A trigger generated by the second analog
//!                          comparator; configured with ComparatorConfigure().
//! - \b ADC_TRIGGER_COMP2 - A trigger generated by the third analog
//!                          comparator; configured with ComparatorConfigure().
//! - \b ADC_TRIGGER_EXTERNAL - A trigger generated by an input from the Port
//!                             B4 pin.  Note that some microcontrollers can
//!                             select from any GPIO using the
//!                             GPIOADCTriggerEnable() function.
//! - \b ADC_TRIGGER_TIMER - A trigger generated by a timer; configured with
//!                          TimerControlTrigger().
//! - \b ADC_TRIGGER_PWM0 - A trigger generated by the first PWM generator;
//!                         configured with PWMGenIntTrigEnable().
//! - \b ADC_TRIGGER_PWM1 - A trigger generated by the second PWM generator;
//!                         configured with PWMGenIntTrigEnable().
//! - \b ADC_TRIGGER_PWM2 - A trigger generated by the third PWM generator;
//!                         configured with PWMGenIntTrigEnable().
//! - \b ADC_TRIGGER_PWM3 - A trigger generated by the fourth PWM generator;
//!                         configured with PWMGenIntTrigEnable().
//! - \b ADC_TRIGGER_ALWAYS - A trigger that is always asserted, causing the
//!                           sample sequence to capture repeatedly (so long as
//!                           there is not a higher priority source active).
//!
//! When \b ADC_TRIGGER_PWM0, \b ADC_TRIGGER_PWM1, \b ADC_TRIGGER_PWM2 or
//! \b ADC_TRIGGER_PWM3 is specified, one of the following should be ORed into
//! \e ui32Trigger to select the PWM module from which the triggers will be
//! routed for this sequence:
//!
//! - \b ADC_TRIGGER_PWM_MOD0 - Selects PWM module 0 as the source of the
//!                             PWM0 to PWM3 triggers for this sequence.
//! - \b ADC_TRIGGER_PWM_MOD1 - Selects PWM module 1 as the source of the
//!                             PWM0 to PWM3 triggers for this sequence.
//!
//! Note that not all trigger sources are available on all Tiva family
//! members; consult the data sheet for the device in question to determine the
//! availability of triggers.
//!
//! The \e ui32Priority parameter is a value between 0 and 3, where 0
//! represents the highest priority and 3 the lowest.  Note that when
//! programming the priority among a set of sample sequences, each must have
//! unique priority; it is up to the caller to guarantee the uniqueness of the
//! priorities.
//!
//! \return None.
//
//*****************************************************************************
void
ADCSequenceConfigure(uint32_t ui32Base, uint32_t ui32SequenceNum,
                     uint32_t ui32Trigger, uint32_t ui32Priority)
{
    uint32_t ui32Gen;

    //
    // Check the arugments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);
    ASSERT(((ui32Trigger & 0xF) == ADC_TRIGGER_PROCESSOR) ||
           ((ui32Trigger & 0xF) == ADC_TRIGGER_COMP0) ||
           ((ui32Trigger & 0xF) == ADC_TRIGGER_COMP1) ||
           ((ui32Trigger & 0xF) == ADC_TRIGGER_COMP2) ||
           ((ui32Trigger & 0xF) == ADC_TRIGGER_EXTERNAL) ||
           ((ui32Trigger & 0xF) == ADC_TRIGGER_TIMER) ||
           ((ui32Trigger & 0xF) == ADC_TRIGGER_PWM0) ||
           ((ui32Trigger & 0xF) == ADC_TRIGGER_PWM1) ||
           ((ui32Trigger & 0xF) == ADC_TRIGGER_PWM2) ||
           ((ui32Trigger & 0xF) == ADC_TRIGGER_PWM3) ||
           ((ui32Trigger & 0xF) == ADC_TRIGGER_ALWAYS) ||
           ((ui32Trigger & 0x30) == ADC_TRIGGER_PWM_MOD0) ||
           ((ui32Trigger & 0x30) == ADC_TRIGGER_PWM_MOD1));
    ASSERT(ui32Priority < 4);

    //
    // Compute the shift for the bits that control this sample sequence.
    //
    ui32SequenceNum *= 4;

    //
    // Set the trigger event for this sample sequence.
    //
    HWREG(ui32Base + ADC_O_EMUX) = ((HWREG(ui32Base + ADC_O_EMUX) &
                                     ~(0xf << ui32SequenceNum)) |
                                    ((ui32Trigger & 0xf) << ui32SequenceNum));

    //
    // Set the priority for this sample sequence.
    //
    HWREG(ui32Base + ADC_O_SSPRI) = ((HWREG(ui32Base + ADC_O_SSPRI) &
                                      ~(0xf << ui32SequenceNum)) |
                                     ((ui32Priority & 0x3) <<
                                      ui32SequenceNum));

    //
    // Set the source PWM module for this sequence's PWM triggers.
    //
    ui32Gen = ui32Trigger & 0x0f;
    if(ui32Gen >= ADC_TRIGGER_PWM0 && ui32Gen <= ADC_TRIGGER_PWM3)
    {
        //
        // Set the shift for the module and generator
        //
        ui32Gen = (ui32Gen - ADC_TRIGGER_PWM0) * 8;
        
        HWREG(ui32Base + ADC_O_TSSEL) = ((HWREG(ui32Base + ADC_O_TSSEL) &
                                         ~(0x30 << ui32Gen)) |
                                         ((ui32Trigger & 0x30) << ui32Gen));
    }
}

//*****************************************************************************
//
//! Configure a step of the sample sequencer.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//! \param ui32Step is the step to be configured.
//! \param ui32Config is the configuration of this step; is a logical OR
//! of \b ADC_CTL_TS, \b ADC_CTL_IE, \b ADC_CTL_END, \b ADC_CTL_D, one of the
//! input channel selects (\b ADC_CTL_CH0 through \b ADC_CTL_CH23), and one of
//! the digital comparator selects (\b ADC_CTL_CMP0 through \b ADC_CTL_CMP7).
//! On some parts the sample and hold time can be increased by including a 
//! logical OR of one of \b ADC_CTL_SHOLD_4, \b ADC_CTL_SHOLD_8,
//! \b ADC_CTL_SHOLD_16, \b ADC_CTL_SHOLD_32, \b ADC_CTL_SHOLD_64, 
//! \b ADC_CTL_SHOLD_128 or \b ADC_CTL_SHOLD_256. The default sample time is 4
//! ADC clocks.
//!
//! This function configures the ADC for one step of a sample sequence.  The
//! ADC can be configured for single-ended or differential operation (the
//! \b ADC_CTL_D bit selects differential operation when set), the channel to
//! be sampled can be chosen (the \b ADC_CTL_CH0 through \b ADC_CTL_CH23
//! values), and the internal temperature sensor can be selected (the
//! \b ADC_CTL_TS bit).  Additionally, this step can be defined as the last in
//! the sequence (the \b ADC_CTL_END bit) and it can be configured to cause an
//! interrupt when the step is complete (the \b ADC_CTL_IE bit).  If the
//! digital comparators are present on the device, this step may also be
//! configured to send the ADC sample to the selected comparator using
//! \b ADC_CTL_CMP0 through \b ADC_CTL_CMP7.  The configuration is used by the
//! ADC at the appropriate time when the trigger for this sequence occurs.
//!
//! \note If the Digital Comparator is present and enabled using the
//! \b ADC_CTL_CMP0 through \b ADC_CTL_CMP7 selects, the ADC sample is NOT
//! written into the ADC sequence data FIFO.
//!
//! The \e ui32Step parameter determines the order in which the samples are
//! captured by the ADC when the trigger occurs.  It can range from zero to
//! seven for the first sample sequencer, from zero to three for the second and
//! third sample sequencer, and can only be zero for the fourth sample
//! sequencer.
//!
//! Differential mode only works with adjacent channel pairs (for example, 0
//! and 1).  The channel select must be the number of the channel pair to
//! sample (for example, \b ADC_CTL_CH0 for 0 and 1, or \b ADC_CTL_CH1 for 2
//! and 3) or undefined results are returned by the ADC.  Additionally, if
//! differential mode is selected when the temperature sensor is being sampled,
//! undefined results are returned by the ADC.
//!
//! It is the responsibility of the caller to ensure that a valid configuration
//! is specified; this function does not check the validity of the specified
//! configuration.
//!
//! \return None.
//
//*****************************************************************************
void
ADCSequenceStepConfigure(uint32_t ui32Base, uint32_t ui32SequenceNum,
                         uint32_t ui32Step, uint32_t ui32Config)
{
    uint32_t ui32Temp;

    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);
    ASSERT(((ui32SequenceNum == 0) && (ui32Step < 8)) ||
           ((ui32SequenceNum == 1) && (ui32Step < 4)) ||
           ((ui32SequenceNum == 2) && (ui32Step < 4)) ||
           ((ui32SequenceNum == 3) && (ui32Step < 1)));

    //
    // Get the offset of the sequence to be configured.
    //
    ui32Base += ADC_SEQ + (ADC_SEQ_STEP * ui32SequenceNum);

    //
    // Compute the shift for the bits that control this step.
    //
    ui32Step *= 4;

    //
    // Set the analog mux value for this step.
    //
    HWREG(ui32Base + ADC_SSMUX) = ((HWREG(ui32Base + ADC_SSMUX) &
                                    ~(0x0000000f << ui32Step)) |
                                   ((ui32Config & 0x0f) << ui32Step));

    //
    // Set the upper bits of the analog mux value for this step.
    //
    HWREG(ui32Base + ADC_SSEMUX) = ((HWREG(ui32Base + ADC_SSEMUX) &
                                     ~(0x0000000f << ui32Step)) |
                                    (((ui32Config & 0xf00) >> 8) << ui32Step));

    //
    // Set the control value for this step.
    //
    HWREG(ui32Base + ADC_SSCTL) = ((HWREG(ui32Base + ADC_SSCTL) &
                                    ~(0x0000000f << ui32Step)) |
                                   (((ui32Config & 0xf0) >> 4) << ui32Step));

    //
    // Set the sample and hold time for this step.  This is not available on
    // all devices, however on devices that do not support this feature these
    // reserved bits are ignored on write access.
    //
    HWREG(ui32Base + ADC_SSTSH) = ((HWREG(ui32Base + ADC_SSTSH) &
                                    ~(0x0000000f << ui32Step)) |
                                (((ui32Config & 0xf00000) >> 20) << ui32Step));

    //
    // Enable digital comparator if specified in the ui32Config bit-fields.
    //
    if(ui32Config & 0x000F0000)
    {
        //
        // Program the comparator for the specified step.
        //
        ui32Temp = HWREG(ui32Base + ADC_SSDC);
        ui32Temp &= ~(0xF << ui32Step);
        ui32Temp |= (((ui32Config & 0x00070000) >> 16) << ui32Step);
        HWREG(ui32Base + ADC_SSDC) = ui32Temp;

        //
        // Enable the comparator.
        //
        HWREG(ui32Base + ADC_SSOP) |= (1 << ui32Step);
    }

    //
    // Disable digital comparator if not specified.
    //
    else
    {
        HWREG(ui32Base + ADC_SSOP) &= ~(1 << ui32Step);
    }
}

//*****************************************************************************
//
//! Determines if a sample sequence overflow occurred.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! This function determines if a sample sequence overflow has occurred.
//! Overflow happens if the captured samples are not read from the FIFO before
//! the next trigger occurs.
//!
//! \return Returns zero if there was not an overflow, and non-zero if there
//! was.
//
//*****************************************************************************
int32_t
ADCSequenceOverflow(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Determine if there was an overflow on this sequence.
    //
    return(HWREG(ui32Base + ADC_O_OSTAT) & (1 << ui32SequenceNum));
}

//*****************************************************************************
//
//! Clears the overflow condition on a sample sequence.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! This function clears an overflow condition on one of the sample sequences.
//! The overflow condition must be cleared in order to detect a subsequent
//! overflow condition (it otherwise causes no harm).
//!
//! \return None.
//
//*****************************************************************************
void
ADCSequenceOverflowClear(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Clear the overflow condition for this sequence.
    //
    HWREG(ui32Base + ADC_O_OSTAT) = 1 << ui32SequenceNum;
}

//*****************************************************************************
//
//! Determines if a sample sequence underflow occurred.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! This function determines if a sample sequence underflow has occurred.
//! Underflow happens if too many samples are read from the FIFO.
//!
//! \return Returns zero if there was not an underflow, and non-zero if there
//! was.
//
//*****************************************************************************
int32_t
ADCSequenceUnderflow(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Determine if there was an underflow on this sequence.
    //
    return(HWREG(ui32Base + ADC_O_USTAT) & (1 << ui32SequenceNum));
}

//*****************************************************************************
//
//! Clears the underflow condition on a sample sequence.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! This function clears an underflow condition on one of the sample
//! sequencers.  The underflow condition must be cleared in order to detect a
//! subsequent underflow condition (it otherwise causes no harm).
//!
//! \return None.
//
//*****************************************************************************
void
ADCSequenceUnderflowClear(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Clear the underflow condition for this sequence.
    //
    HWREG(ui32Base + ADC_O_USTAT) = 1 << ui32SequenceNum;
}

//*****************************************************************************
//
//! Gets the captured data for a sample sequence.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//! \param pui32Buffer is the address where the data is stored.
//!
//! This function copies data from the specified sample sequencer output FIFO
//! to a memory resident buffer.  The number of samples available in the
//! hardware FIFO are copied into the buffer, which is assumed to be large
//! enough to hold that many samples.  This function only returns the samples
//! that are presently available, which may not be the entire sample sequence
//! if it is in the process of being executed.
//!
//! \return Returns the number of samples copied to the buffer.
//
//*****************************************************************************
int32_t
ADCSequenceDataGet(uint32_t ui32Base, uint32_t ui32SequenceNum,
                   uint32_t *pui32Buffer)
{
    uint32_t ui32Count;

    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Get the offset of the sequence to be read.
    //
    ui32Base += ADC_SEQ + (ADC_SEQ_STEP * ui32SequenceNum);

    //
    // Read samples from the FIFO until it is empty.
    //
    ui32Count = 0;
    while(!(HWREG(ui32Base + ADC_SSFSTAT) & ADC_SSFSTAT0_EMPTY) &&
          (ui32Count < 8))
    {
        //
        // Read the FIFO and copy it to the destination.
        //
        *pui32Buffer++ = HWREG(ui32Base + ADC_SSFIFO);

        //
        // Increment the count of samples read.
        //
        ui32Count++;
    }

    //
    // Return the number of samples read.
    //
    return(ui32Count);
}

//*****************************************************************************
//
//! Causes a processor trigger for a sample sequence.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number, with
//! \b ADC_TRIGGER_WAIT or \b ADC_TRIGGER_SIGNAL optionally ORed into it.
//!
//! This function triggers a processor-initiated sample sequence if the sample
//! sequence trigger is configured to \b ADC_TRIGGER_PROCESSOR.  If
//! \b ADC_TRIGGER_WAIT is ORed into the sequence number, the
//! processor-initiated trigger is delayed until a later processor-initiated
//! trigger to a different ADC module that specifies \b ADC_TRIGGER_SIGNAL,
//! allowing multiple ADCs to start from a processor-initiated trigger in a
//! synchronous manner.
//!
//! \return None.
//
//*****************************************************************************
void
ADCProcessorTrigger(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Generate a processor trigger for this sample sequence.
    //
    HWREG(ui32Base + ADC_O_PSSI) |= ((ui32SequenceNum & 0xffff0000) |
                                     (1 << (ui32SequenceNum & 0xf)));
}

//*****************************************************************************
//
//! Configures the software oversampling factor of the ADC.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//! \param ui32Factor is the number of samples to be averaged.
//!
//! This function configures the software oversampling for the ADC, which can
//! be used to provide better resolution on the sampled data.  Oversampling is
//! accomplished by averaging multiple samples from the same analog input.
//! Three different oversampling rates are supported; 2x, 4x, and 8x.
//!
//! Oversampling is only supported on the sample sequencers that are more than
//! one sample in depth (that is, the fourth sample sequencer is not
//! supported).  Oversampling by 2x (for example) divides the depth of the
//! sample sequencer by two; so 2x oversampling on the first sample sequencer
//! can only provide four samples per trigger.  This also means that 8x
//! oversampling is only available on the first sample sequencer.
//!
//! \return None.
//
//*****************************************************************************
void
ADCSoftwareOversampleConfigure(uint32_t ui32Base, uint32_t ui32SequenceNum,
                               uint32_t ui32Factor)
{
    uint32_t ui32Value;
    uint32_t ui32ADCInst;

    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 3);
    ASSERT(((ui32Factor == 2) || (ui32Factor == 4) || (ui32Factor == 8)) &&
           ((ui32SequenceNum == 0) || (ui32Factor != 8)));

    //
    // Convert the oversampling factor to a shift factor.
    //
    for(ui32Value = 0, ui32Factor >>= 1; ui32Factor;
        ui32Value++, ui32Factor >>= 1)
    {
    }

    //
    // Evaluate the ADC Instance.
    //
    if(ui32Base == ADC0_BASE)
    {
        ui32ADCInst = 0;
    }
    else
    {
        ui32ADCInst = 1;
    }

    //
    // Save the shift factor.
    //
    g_pui8OversampleFactor[ui32ADCInst][ui32SequenceNum] = ui32Value;
}

//*****************************************************************************
//
//! Configures a step of the software oversampled sequencer.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//! \param ui32Step is the step to be configured.
//! \param ui32Config is the configuration of this step.
//!
//! This function configures a step of the sample sequencer when using the
//! software oversampling feature.  The number of steps available depends on
//! the oversampling factor set by ADCSoftwareOversampleConfigure().  The value
//! of \e ui32Config is the same as defined for ADCSequenceStepConfigure().
//!
//! \return None.
//
//*****************************************************************************
void
ADCSoftwareOversampleStepConfigure(uint32_t ui32Base, uint32_t ui32SequenceNum,
                                   uint32_t ui32Step, uint32_t ui32Config)
{
    uint32_t ui32ADCInst;

    //
    // Evaluate the ADC Instance.
    //
    if(ui32Base == ADC0_BASE)
    {
        ui32ADCInst = 0;
    }
    else
    {
        ui32ADCInst = 1;
    }

    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 3);
    ASSERT(((ui32SequenceNum == 0) &&
            (ui32Step < 
            (8 >> g_pui8OversampleFactor[ui32ADCInst][ui32SequenceNum]))) ||
           (ui32Step < 
           (4 >> g_pui8OversampleFactor[ui32ADCInst][ui32SequenceNum])));

    //
    // Get the offset of the sequence to be configured.
    //
    ui32Base += ADC_SEQ + (ADC_SEQ_STEP * ui32SequenceNum);

    //
    // Compute the shift for the bits that control this step.
    //
    ui32Step *= 4 << g_pui8OversampleFactor[ui32ADCInst][ui32SequenceNum];

    //
    // Loop through the hardware steps that make up this step of the software
    // oversampled sequence.
    //
    for(ui32SequenceNum = 
        (1 << g_pui8OversampleFactor[ui32ADCInst][ui32SequenceNum]);
        ui32SequenceNum; ui32SequenceNum--)
    {
        //
        // Set the analog mux value for this step.
        //
        HWREG(ui32Base + ADC_SSMUX) = ((HWREG(ui32Base + ADC_SSMUX) &
                                        ~(0x0000000f << ui32Step)) |
                                       ((ui32Config & 0x0f) << ui32Step));

        //
        // Set the upper bits of the analog mux value for this step.
        //
        HWREG(ui32Base + ADC_SSEMUX) = ((HWREG(ui32Base + ADC_SSEMUX) &
                                         ~(0x0000000f << ui32Step)) |
                                        (((ui32Config & 0xf00) >> 8) <<
                                         ui32Step));

        //
        // Set the control value for this step.
        //
        HWREG(ui32Base + ADC_SSCTL) = ((HWREG(ui32Base + ADC_SSCTL) &
                                        ~(0x0000000f << ui32Step)) |
                                       (((ui32Config & 0xf0) >> 4) <<
                                        ui32Step));
        if(ui32SequenceNum != 1)
        {
            HWREG(ui32Base + ADC_SSCTL) &= ~((ADC_SSCTL0_IE0 |
                                              ADC_SSCTL0_END0) << ui32Step);
        }

        //
        // Go to the next hardware step.
        //
        ui32Step += 4;
    }
}

//*****************************************************************************
//
//! Gets the captured data for a sample sequence using software oversampling.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//! \param pui32Buffer is the address where the data is stored.
//! \param ui32Count is the number of samples to be read.
//!
//! This function copies data from the specified sample sequence output FIFO to
//! a memory resident buffer with software oversampling applied.  The requested
//! number of samples are copied into the data buffer; if there are not enough
//! samples in the hardware FIFO to satisfy this many oversampled data items,
//! then incorrect results are returned.  It is the caller's responsibility to
//! read only the samples that are available and wait until enough data is
//! available, for example as a result of receiving an interrupt.
//!
//! \return None.
//
//*****************************************************************************
void
ADCSoftwareOversampleDataGet(uint32_t ui32Base, uint32_t ui32SequenceNum,
                             uint32_t *pui32Buffer, uint32_t ui32Count)
{
    uint32_t ui32Idx, ui32Accum;
    uint32_t ui32ADCInst;

    //
    // Evaluate the ADC Instance.
    //
    if(ui32Base == ADC0_BASE)
    {
        ui32ADCInst = 0;
    }
    else
    {
        ui32ADCInst = 1;
    }


    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 3);
    ASSERT(((ui32SequenceNum == 0) &&
            (ui32Count < 
            (8 >> g_pui8OversampleFactor[ui32ADCInst][ui32SequenceNum]))) ||
            (ui32Count < 
            (4 >> g_pui8OversampleFactor[ui32ADCInst][ui32SequenceNum])));

    //
    // Get the offset of the sequence to be read.
    //
    ui32Base += ADC_SEQ + (ADC_SEQ_STEP * ui32SequenceNum);

    //
    // Read the samples from the FIFO until it is empty.
    //
    while(ui32Count--)
    {
        //
        // Compute the sum of the samples.
        //
        ui32Accum = 0;
        for(ui32Idx = 1 << g_pui8OversampleFactor[ui32ADCInst][ui32SequenceNum];
            ui32Idx; ui32Idx--)
        {
            //
            // Read the FIFO and add it to the accumulator.
            //
            ui32Accum += HWREG(ui32Base + ADC_SSFIFO);
        }

        //
        // Write the averaged sample to the output buffer.
        //
        *pui32Buffer++ = 
            ui32Accum >> g_pui8OversampleFactor[ui32ADCInst][ui32SequenceNum];
    }
}

//*****************************************************************************
//
//! Configures the hardware oversampling factor of the ADC.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32Factor is the number of samples to be averaged.
//!
//! This function configures the hardware oversampling for the ADC, which can
//! be used to provide better resolution on the sampled data.  Oversampling is
//! accomplished by averaging multiple samples from the same analog input.  Six
//! different oversampling rates are supported; 2x, 4x, 8x, 16x, 32x, and 64x.
//! Specifying an oversampling factor of zero disables hardware
//! oversampling.
//!
//! Hardware oversampling applies uniformly to all sample sequencers.  It does
//! not reduce the depth of the sample sequencers like the software
//! oversampling APIs; each sample written into the sample sequencer FIFO is a
//! fully oversampled analog input reading.
//!
//! Enabling hardware averaging increases the precision of the ADC at the cost
//! of throughput.  For example, enabling 4x oversampling reduces the
//! throughput of a 250 k samples/second ADC to 62.5 k samples/second.
//!
//! \return None.
//
//*****************************************************************************
void
ADCHardwareOversampleConfigure(uint32_t ui32Base, uint32_t ui32Factor)
{
    uint32_t ui32Value;

    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(((ui32Factor == 0) || (ui32Factor == 2) || (ui32Factor == 4) ||
            (ui32Factor == 8) || (ui32Factor == 16) || (ui32Factor == 32) ||
            (ui32Factor == 64)));

    //
    // Convert the oversampling factor to a shift factor.
    //
    for(ui32Value = 0, ui32Factor >>= 1; ui32Factor;
        ui32Value++, ui32Factor >>= 1)
    {
    }

    //
    // Write the shift factor to the ADC to configure the hardware oversampler.
    //
    HWREG(ui32Base + ADC_O_SAC) = ui32Value;
}

//*****************************************************************************
//
//! Configures an ADC digital comparator.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32Comp is the index of the comparator to configure.
//! \param ui32Config is the configuration of the comparator.
//!
//! This function configures a comparator.  The \e ui32Config parameter is
//! the result of a logical OR operation between the \b ADC_COMP_TRIG_xxx, and
//! \b ADC_COMP_INT_xxx values.
//!
//! The \b ADC_COMP_TRIG_xxx term can take on the following values:
//!
//! - \b ADC_COMP_TRIG_NONE to never trigger PWM fault condition.
//! - \b ADC_COMP_TRIG_LOW_ALWAYS to always trigger PWM fault condition when
//! ADC output is in the low-band.
//! - \b ADC_COMP_TRIG_LOW_ONCE to trigger PWM fault condition once when ADC
//! output transitions into the low-band.
//! - \b ADC_COMP_TRIG_LOW_HALWAYS to always trigger PWM fault condition when
//! ADC output is in the low-band only if ADC output has been in the high-band
//! since the last trigger output.
//! - \b ADC_COMP_TRIG_LOW_HONCE to trigger PWM fault condition once when ADC
//! output transitions into low-band only if ADC output has been in the
//! high-band since the last trigger output.
//! - \b ADC_COMP_TRIG_MID_ALWAYS to always trigger PWM fault condition when
//! ADC output is in the mid-band.
//! - \b ADC_COMP_TRIG_MID_ONCE to trigger PWM fault condition once when ADC
//! output transitions into the mid-band.
//! - \b ADC_COMP_TRIG_HIGH_ALWAYS to always trigger PWM fault condition when
//! ADC output is in the high-band.
//! - \b ADC_COMP_TRIG_HIGH_ONCE to trigger PWM fault condition once when ADC
//! output transitions into the high-band.
//! - \b ADC_COMP_TRIG_HIGH_HALWAYS to always trigger PWM fault condition when
//! ADC output is in the high-band only if ADC output has been in the low-band
//! since the last trigger output.
//! - \b ADC_COMP_TRIG_HIGH_HONCE to trigger PWM fault condition once when ADC
//! output transitions into high-band only if ADC output has been in the
//! low-band since the last trigger output.
//!
//! The \b ADC_COMP_INT_xxx term can take on the following values:
//!
//! - \b ADC_COMP_INT_NONE to never generate ADC interrupt.
//! - \b ADC_COMP_INT_LOW_ALWAYS to always generate ADC interrupt when ADC
//! output is in the low-band.
//! - \b ADC_COMP_INT_LOW_ONCE to generate ADC interrupt once when ADC output
//! transitions into the low-band.
//! - \b ADC_COMP_INT_LOW_HALWAYS to always generate ADC interrupt when ADC
//! output is in the low-band only if ADC output has been in the high-band
//! since the last trigger output.
//! - \b ADC_COMP_INT_LOW_HONCE to generate ADC interrupt once when ADC output
//! transitions into low-band only if ADC output has been in the high-band
//! since the last trigger output.
//! - \b ADC_COMP_INT_MID_ALWAYS to always generate ADC interrupt when ADC
//! output is in the mid-band.
//! - \b ADC_COMP_INT_MID_ONCE to generate ADC interrupt once when ADC output
//! transitions into the mid-band.
//! - \b ADC_COMP_INT_HIGH_ALWAYS to always generate ADC interrupt when ADC
//! output is in the high-band.
//! - \b ADC_COMP_INT_HIGH_ONCE to generate ADC interrupt once when ADC output
//! transitions into the high-band.
//! - \b ADC_COMP_INT_HIGH_HALWAYS to always generate ADC interrupt when ADC
//! output is in the high-band only if ADC output has been in the low-band
//! since the last trigger output.
//! - \b ADC_COMP_INT_HIGH_HONCE to generate ADC interrupt once when ADC output
//! transitions into high-band only if ADC output has been in the low-band
//! since the last trigger output.
//!
//! \return None.
//
//*****************************************************************************
void
ADCComparatorConfigure(uint32_t ui32Base, uint32_t ui32Comp,
                       uint32_t ui32Config)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32Comp < 8);

    //
    // Save the new setting.
    //
    HWREG(ui32Base + ADC_O_DCCTL0 + (ui32Comp * 4)) = ui32Config;
}

//*****************************************************************************
//
//! Defines the ADC digital comparator regions.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32Comp is the index of the comparator to configure.
//! \param ui32LowRef is the reference point for the low/mid band threshold.
//! \param ui32HighRef is the reference point for the mid/high band threshold.
//!
//! The ADC digital comparator operation is based on three ADC value regions:
//! - \b low-band is defined as any ADC value less than or equal to the
//!   \e ui32LowRef value.
//! - \b mid-band is defined as any ADC value greater than the \e ui32LowRef
//!   value but less than or equal to the \e ui32HighRef value.
//! - \b high-band is defined as any ADC value greater than the \e ui32HighRef
//!   value.
//!
//! \return None.
//
//*****************************************************************************
void
ADCComparatorRegionSet(uint32_t ui32Base, uint32_t ui32Comp,
                       uint32_t ui32LowRef, uint32_t ui32HighRef)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32Comp < 8);
    ASSERT((ui32LowRef < 4096) && (ui32LowRef <= ui32HighRef));
    ASSERT(ui32HighRef < 4096);

    //
    // Save the new region settings.
    //
    HWREG(ui32Base + ADC_O_DCCMP0 + (ui32Comp * 4)) = ((ui32HighRef << 16) |
                                                       ui32LowRef);
}

//*****************************************************************************
//
//! Resets the current ADC digital comparator conditions.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32Comp is the index of the comparator.
//! \param bTrigger is the flag to indicate reset of Trigger conditions.
//! \param bInterrupt is the flag to indicate reset of Interrupt conditions.
//!
//! Because the digital comparator uses current and previous ADC values, this
//! function allows the comparator to be reset to its initial
//! value to prevent stale data from being used when a sequence is enabled.
//!
//! \return None.
//
//*****************************************************************************
void
ADCComparatorReset(uint32_t ui32Base, uint32_t ui32Comp, bool bTrigger,
                   bool bInterrupt)
{
    uint32_t ui32Temp;

    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32Comp < 8);

    //
    // Set the appropriate bits to reset the trigger and/or interrupt
    // comparator conditions.
    //
    ui32Temp = 0;
    if(bTrigger)
    {
        ui32Temp |= (1 << (16 + ui32Comp));
    }
    if(bInterrupt)
    {
        ui32Temp |= (1 << ui32Comp);
    }

    HWREG(ui32Base + ADC_O_DCRIC) = ui32Temp;
}

//*****************************************************************************
//
//! Disables a sample sequence comparator interrupt.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! This function disables the requested sample sequence comparator interrupt.
//!
//! \return None.
//
//*****************************************************************************
void
ADCComparatorIntDisable(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Disable this sample sequence comparator interrupt.
    //
    HWREG(ui32Base + ADC_O_IM) &= ~(0x10000 << ui32SequenceNum);
}

//*****************************************************************************
//
//! Enables a sample sequence comparator interrupt.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! This function enables the requested sample sequence comparator interrupt.
//!
//! \return None.
//
//*****************************************************************************
void
ADCComparatorIntEnable(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Enable this sample sequence interrupt.
    //
    HWREG(ui32Base + ADC_O_IM) |= 0x10000 << ui32SequenceNum;
}

//*****************************************************************************
//
//! Gets the current comparator interrupt status.
//!
//! \param ui32Base is the base address of the ADC module.
//!
//! This function returns the digital comparator interrupt status bits.  This
//! status is sequence agnostic.
//!
//! \return The current comparator interrupt status.
//
//*****************************************************************************
uint32_t
ADCComparatorIntStatus(uint32_t ui32Base)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));

    //
    // Return the digital comparator interrupt status.
    //
    return(HWREG(ui32Base + ADC_O_DCISC));
}

//*****************************************************************************
//
//! Clears sample sequence comparator interrupt source.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32Status is the bit-mapped interrupts status to clear.
//!
//! The specified interrupt status is cleared.
//!
//! \return None.
//
//*****************************************************************************
void
ADCComparatorIntClear(uint32_t ui32Base, uint32_t ui32Status)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));

    //
    // Clear the interrupt.
    //
    HWREG(ui32Base + ADC_O_DCISC) = ui32Status;
}

//*****************************************************************************
//
//! Disables ADC interrupt sources.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32IntFlags is the bit mask of the interrupt sources to disable.
//!
//! This function disables the indicated ADC interrupt sources.  Only the
//! sources that are enabled can be reflected to the processor interrupt;
//! disabled sources have no effect on the processor.
//!
//! The \e ui32IntFlags parameter is the logical OR of any of the following:
//!
//! - \b ADC_INT_SS0 - interrupt due to ADC sample sequence 0.
//! - \b ADC_INT_SS1 - interrupt due to ADC sample sequence 1.
//! - \b ADC_INT_SS2 - interrupt due to ADC sample sequence 2.
//! - \b ADC_INT_SS3 - interrupt due to ADC sample sequence 3.
//! - \b ADC_INT_DMA_SS0 - interrupt due to DMA on ADC sample sequence 0.
//! - \b ADC_INT_DMA_SS1 - interrupt due to DMA on ADC sample sequence 1.
//! - \b ADC_INT_DMA_SS2 - interrupt due to DMA on ADC sample sequence 2.
//! - \b ADC_INT_DMA_SS3 - interrupt due to DMA on ADC sample sequence 3.
//! - \b ADC_INT_DCON_SS0 - interrupt due to digital comparator on ADC sample
//!   sequence 0.
//! - \b ADC_INT_DCON_SS1 - interrupt due to digital comparator on ADC sample
//!   sequence 1.
//! - \b ADC_INT_DCON_SS2 - interrupt due to digital comparator on ADC sample
//!   sequence 2.
//! - \b ADC_INT_DCON_SS3 - interrupt due to digital comparator on ADC sample
//!   sequence 3.
//!
//! \return None.
//
//*****************************************************************************
void
ADCIntDisableEx(uint32_t ui32Base, uint32_t ui32IntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));

    //
    // Disable the requested interrupts.
    //
    HWREG(ui32Base + ADC_O_IM) &= ~ui32IntFlags;
}

//*****************************************************************************
//
//! Enables ADC interrupt sources.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32IntFlags is the bit mask of the interrupt sources to disable.
//!
//! This function enables the indicated ADC interrupt sources.  Only the
//! sources that are enabled can be reflected to the processor interrupt;
//! disabled sources have no effect on the processor.
//!
//! The \e ui32IntFlags parameter is the logical OR of any of the following:
//!
//! - \b ADC_INT_SS0 - interrupt due to ADC sample sequence 0.
//! - \b ADC_INT_SS1 - interrupt due to ADC sample sequence 1.
//! - \b ADC_INT_SS2 - interrupt due to ADC sample sequence 2.
//! - \b ADC_INT_SS3 - interrupt due to ADC sample sequence 3.
//! - \b ADC_INT_DMA_SS0 - interrupt due to DMA on ADC sample sequence 0.
//! - \b ADC_INT_DMA_SS1 - interrupt due to DMA on ADC sample sequence 1.
//! - \b ADC_INT_DMA_SS2 - interrupt due to DMA on ADC sample sequence 2.
//! - \b ADC_INT_DMA_SS3 - interrupt due to DMA on ADC sample sequence 3.
//! - \b ADC_INT_DCON_SS0 - interrupt due to digital comparator on ADC sample
//!   sequence 0.
//! - \b ADC_INT_DCON_SS1 - interrupt due to digital comparator on ADC sample
//!   sequence 1.
//! - \b ADC_INT_DCON_SS2 - interrupt due to digital comparator on ADC sample
//!   sequence 2.
//! - \b ADC_INT_DCON_SS3 - interrupt due to digital comparator on ADC sample
//!   sequence 3.
//!
//! \return None.
//
//*****************************************************************************
void
ADCIntEnableEx(uint32_t ui32Base, uint32_t ui32IntFlags)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));

    //
    // Enable the requested interrupts.
    //
    HWREG(ui32Base + ADC_O_IM) |= ui32IntFlags;
}

//*****************************************************************************
//
//! Gets interrupt status for the specified ADC module.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param bMasked specifies whether masked or raw interrupt status is
//! returned.
//!
//! If \e bMasked is set as \b true, then the masked interrupt status is
//! returned; otherwise, the raw interrupt status is returned.
//!
//! \return Returns the current interrupt status for the specified ADC module.
//! The value returned is the logical OR of the \b ADC_INT_* values that are
//! currently active.
//
//*****************************************************************************
uint32_t
ADCIntStatusEx(uint32_t ui32Base, bool bMasked)
{
    uint32_t ui32Temp;

    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));

    //
    // Return either the masked interrupt status or the raw interrupt status as
    // requested.
    //
    if(bMasked)
    {
        ui32Temp = HWREG(ui32Base + ADC_O_ISC);
    }
    else
    {
        //
        // Read the Raw interrupt status to see if a digital comparator
        // interrupt is active.
        //
        ui32Temp = HWREG(ui32Base + ADC_O_RIS);

        //
        // Since, the raw interrupt status only indicates that any one of the
        // digital comparators caused an interrupt, if the raw interrupt status
        // is set then the return value is modified to indicate that all sample
        // sequences have a pending digital comparator interrupt.
        // This is exactly how the hardware works so the return code is
        // modified to match this behavior.
        //
        if(ui32Temp & ADC_RIS_INRDC)
        {
            ui32Temp |= (ADC_INT_DCON_SS3 | ADC_INT_DCON_SS2 |
                         ADC_INT_DCON_SS1 | ADC_INT_DCON_SS0);
        }
    }
    return(ui32Temp);
}

//*****************************************************************************
//
//! Clears the specified ADC interrupt sources.
//!
//! \param ui32Base is the base address of the ADC port.
//! \param ui32IntFlags is the bit mask of the interrupt sources to disable.
//!
//! Clears the interrupt for the specified interrupt source(s).
//!
//! The \e ui32IntFlags parameter is the logical OR of the \b ADC_INT_* values.
//! See the ADCIntEnableEx() function for the list of possible \b ADC_INT*
//! values.
//!
//! \note Because there is a write buffer in the Cortex-M processor, it may
//! take several clock cycles before the interrupt source is actually cleared.
//! Therefore, it is recommended that the interrupt source be cleared early in
//! the interrupt handler (as opposed to the very last action) to avoid
//! returning from the interrupt handler before the interrupt source is
//! actually cleared.  Failure to do so may result in the interrupt handler
//! being immediately reentered (because the interrupt controller still sees
//! the interrupt source asserted).
//!
//! \return None.
//
//*****************************************************************************
void
ADCIntClearEx(uint32_t ui32Base, uint32_t ui32IntFlags)
{
    //
    // Note: The interrupt bits are "W1C" so we DO NOT use a logical OR
    // here to clear the requested bits. Doing so would clear all outstanding
    // interrupts rather than just those which the caller has specified.
    //
    HWREG(ui32Base + ADC_O_ISC) = ui32IntFlags;
}

//*****************************************************************************
//
//! Selects the ADC reference.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32Ref is the reference to use.
//!
//! The ADC reference is set as specified by \e ui32Ref.  It must be one of
//! \b ADC_REF_INT, or \b ADC_REF_EXT_3V for internal or external reference
//! If \b ADC_REF_INT is chosen, then an internal 3V reference is used and 
//! no external reference is needed.  If \b ADC_REF_EXT_3V is chosen, then
//! a 3V reference must be supplied to the AVREF pin.
//!
//! \note The ADC reference can only be selected on parts that have an external
//! reference.  Consult the data sheet for your part to determine if there is
//! an external reference.
//!
//! \return None.
//
//*****************************************************************************
void
ADCReferenceSet(uint32_t ui32Base, uint32_t ui32Ref)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT((ui32Ref == ADC_REF_INT) || (ui32Ref == ADC_REF_EXT_3V));

    //
    // Set the reference.
    //
    HWREG(ui32Base + ADC_O_CTL) =
        (HWREG(ui32Base + ADC_O_CTL) & ~ADC_CTL_VREF_M) | ui32Ref;
}

//*****************************************************************************
//
//! Returns the current setting of the ADC reference.
//!
//! \param ui32Base is the base address of the ADC module.
//!
//! Returns the value of the ADC reference setting.  The returned value is one
//! of \b ADC_REF_INT, or \b ADC_REF_EXT_3V.
//!
//! \note The value returned by this function is only meaningful if used on a
//! part that is capable of using an external reference.  Consult the data
//! sheet for your part to determine if it has an external reference input.
//!
//! \return The current setting of the ADC reference.
//
//*****************************************************************************
uint32_t
ADCReferenceGet(uint32_t ui32Base)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));

    //
    // Return the value of the reference.
    //
    return(HWREG(ui32Base + ADC_O_CTL) & ADC_CTL_VREF_M);
}

//*****************************************************************************
//
//! Sets the phase delay between a trigger and the start of a sequence.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32Phase is the phase delay, specified as one of \b ADC_PHASE_0,
//! \b ADC_PHASE_22_5, \b ADC_PHASE_45, \b ADC_PHASE_67_5, \b ADC_PHASE_90,
//! \b ADC_PHASE_112_5, \b ADC_PHASE_135, \b ADC_PHASE_157_5, \b ADC_PHASE_180,
//! \b ADC_PHASE_202_5, \b ADC_PHASE_225, \b ADC_PHASE_247_5, \b ADC_PHASE_270,
//! \b ADC_PHASE_292_5, \b ADC_PHASE_315, or \b ADC_PHASE_337_5.
//!
//! This function sets the phase delay between the detection of an ADC trigger
//! event and the start of the sample sequence.  By selecting a different phase
//! delay for a pair of ADC modules (such as \b ADC_PHASE_0 and
//! \b ADC_PHASE_180) and having each ADC module sample the same analog input,
//! it is possible to increase the sampling rate of the analog input (with
//! samples N, N+2, N+4, and so on, coming from the first ADC and samples N+1,
//! N+3, N+5, and so on, coming from the second ADC).  The ADC module has a
//! single phase delay that is applied to all sample sequences within that
//! module.
//!
//! \note This capability is not available on all parts.
//!
//! \return None.
//
//*****************************************************************************
void
ADCPhaseDelaySet(uint32_t ui32Base, uint32_t ui32Phase)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT((ui32Phase == ADC_PHASE_0) || (ui32Phase == ADC_PHASE_22_5) ||
           (ui32Phase == ADC_PHASE_45) || (ui32Phase == ADC_PHASE_67_5) ||
           (ui32Phase == ADC_PHASE_90) || (ui32Phase == ADC_PHASE_112_5) ||
           (ui32Phase == ADC_PHASE_135) || (ui32Phase == ADC_PHASE_157_5) ||
           (ui32Phase == ADC_PHASE_180) || (ui32Phase == ADC_PHASE_202_5) ||
           (ui32Phase == ADC_PHASE_225) || (ui32Phase == ADC_PHASE_247_5) ||
           (ui32Phase == ADC_PHASE_270) || (ui32Phase == ADC_PHASE_292_5) ||
           (ui32Phase == ADC_PHASE_315) || (ui32Phase == ADC_PHASE_337_5));

    //
    // Set the phase delay.
    //
    HWREG(ui32Base + ADC_O_SPC) = ui32Phase;
}

//*****************************************************************************
//
//! Gets the phase delay between a trigger and the start of a sequence.
//!
//! \param ui32Base is the base address of the ADC module.
//!
//! This function gets the current phase delay between the detection of an ADC
//! trigger event and the start of the sample sequence.
//!
//! \return Returns the phase delay, specified as one of \b ADC_PHASE_0,
//! \b ADC_PHASE_22_5, \b ADC_PHASE_45, \b ADC_PHASE_67_5, \b ADC_PHASE_90,
//! \b ADC_PHASE_112_5, \b ADC_PHASE_135, \b ADC_PHASE_157_5, \b ADC_PHASE_180,
//! \b ADC_PHASE_202_5, \b ADC_PHASE_225, \b ADC_PHASE_247_5, \b ADC_PHASE_270,
//! \b ADC_PHASE_292_5, \b ADC_PHASE_315, or \b ADC_PHASE_337_5.
//
//*****************************************************************************
uint32_t
ADCPhaseDelayGet(uint32_t ui32Base)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));

    //
    // Return the phase delay.
    //
    return(HWREG(ui32Base + ADC_O_SPC));
}

//*****************************************************************************
//
//! Enables DMA for sample sequencers.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! Allows DMA requests to be generated based on the FIFO level of the sample
//! sequencer.
//!
//! \return None.
//
//*****************************************************************************
void
ADCSequenceDMAEnable(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Enable the DMA on the specified sequencer.
    //
    HWREG(ui32Base + ADC_O_ACTSS) |= 0x100 << ui32SequenceNum;
}

//*****************************************************************************
//
//! Disables DMA for sample sequencers.
//!
//! \param ui32Base is the base address of the ADC module.
//! \param ui32SequenceNum is the sample sequence number.
//!
//! Prevents the specified sample sequencer from generating DMA requests.
//!
//! \return None.
//
//*****************************************************************************
void
ADCSequenceDMADisable(uint32_t ui32Base, uint32_t ui32SequenceNum)
{
    //
    // Check the arguments.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));
    ASSERT(ui32SequenceNum < 4);

    //
    // Disable the DMA on the specified sequencer.
    //
    HWREG(ui32Base + ADC_O_ACTSS) &= ~(0x100 << ui32SequenceNum);
}

//*****************************************************************************
//
//! Determines whether the ADC is busy or not.
//!
//! \param ui32Base is the base address of the ADC.
//!
//! This function allows the caller to determine whether or not the ADC is
//! currently sampling .  If \b false is returned, then the ADC is not
//! sampling data.
//!
//! Use this function to detect that the ADC is finished sampling data before
//! putting the device into deep sleep.  Before using this function, it is
//! highly recommended that the event trigger is changed to
//! \b ADC_TRIGGER_NEVER on all enabled sequencers to prevent the ADC from
//! starting after checking the busy status.
//!
//! \return Returns \b true if the ADC is sampling or \b false if all
//! samples are complete.
//
//*****************************************************************************
bool
ADCBusy(uint32_t ui32Base)
{
    //
    // Check the argument.
    //
    ASSERT((ui32Base == ADC0_BASE) || (ui32Base == ADC1_BASE));

    //
    // Determine if the ADC is busy.
    //
    return((HWREG(ui32Base + ADC_O_ACTSS) & ADC_ACTSS_BUSY) ? true : false);
}

//*****************************************************************************
//
//! Sets the clock configuration for the ADC.
//!
//! \param ui32Base is the base address of the ADC to configure, which must
//! always be \b ADC0_BASE.
//! \param ui32Config is a combination of the \b ADC_CLOCK_SRC_ and
//! \b ADC_CLOCK_RATE_* values used to configure the ADC clock input.
//! \param ui32ClockDiv is the input clock divider for the clock selected by
//! the \b ADC_CLOCK_SRC value.
//!
//! This function is used to configure the input clock to the ADC modules.  The
//! clock configuration is shared across ADC units so \e ui32Base must
//! always be \b ADC0_BASE.  The \e ui32Config value is logical OR of one
//! of the \b ADC_CLOCK_RATE_ and one of the \b ADC_CLOCK_SRC_ values defined
//! below. The \b ADC_CLOCK_SRC_* values determine the input clock for the ADC.
//! Not all values are available on all devices so check the device data sheet
//! to determine value configuration options.  Regardless of the source, the
//! final frequency for TM4C123x devices must be 16 MHz and for TM4C129x parts
//! after dividing must be between 16 and 32 MHz.
//!
//! \note For TM4C123x devices, if the PLL is enabled, the PLL/25 is used as
//! the ADC clock unless ADC_CLOCK_SRC_PIOSC is specified.  If the PLL is
//! disabled, the MOSC is used as the clock source unless ADC_CLOCK_SRC_PIOSC
//! is specified.
//!
//! - \b ADC_CLOCK_SRC_PLL - The main PLL output (TM4x129 class only).
//! - \b ADC_CLOCK_SRC_PIOSC - The internal PIOSC at 16 MHz.
//! - \b ADC_CLOCK_SRC_ALTCLK - The output of the ALTCLK in the system control
//!   module (TM4x129 class only).
//! - \b ADC_CLOCK_SRC_MOSC - The external MOSC (TM4x129 class only).
//!
//! \b ADC_CLOCK_RATE values control how often samples are provided back to the
//! application.  The values are the following:
//!
//! - \b ADC_CLOCK_RATE_FULL - All samples.
//! - \b ADC_CLOCK_RATE_HALF - Every other sample.
//! - \b ADC_CLOCK_RATE_QUARTER - Every fourth sample.
//! - \b ADC_CLOCK_RATE_EIGHTH - Every either sample.
//!
//! The \e ui32ClockDiv parameter allows for dividing a higher frequency down
//! into the valid range for the ADCs.  This parameter is typically only used
//! \b ADC_CLOCK_SRC_PLL option because it is the only clock value that can be
//! with the in the correct range to use the divider.  The actual value ranges
//! from 1 to 64.
//!
//! \b Example: ADC Clock Configurations
//!
//! \verbatim
//!
//! //
//! // Configure the ADC to use PIOSC divided by one (16 MHz) and sample at
//! // half the rate.
//! //
//! ADCClockConfigSet(ADC0_BASE, ADC_CLOCK_SRC_PIOSC | ADC_CLOCK_RATE_HALF, 1);
//!
//! ...
//!
//! //
//! // Configure the ADC to use PLL at 480 MHz divided by 24 to get an ADC
//! // clock of 20 MHz.
//! //
//! ADCClockConfigSet(ADC0_BASE, ADC_CLOCK_SRC_PLL | ADC_CLOCK_RATE_FULL, 24);
//! \endverbatim
//!
//! \return None.
//
//*****************************************************************************
void
ADCClockConfigSet(uint32_t ui32Base, uint32_t ui32Config,
                  uint32_t ui32ClockDiv)
{
    //
    // Check the argument.
    //
    ASSERT(ui32Base == ADC0_BASE);
    ASSERT((ui32ClockDiv - 1) <= (ADC_CC_CLKDIV_M >> ADC_CC_CLKDIV_S));

    //
    // A rate must be supplied.
    //
    ASSERT((ui32Config & ADC_CLOCK_RATE_FULL) != 0);

    //
    // Write the sample conversion rate.
    //
    HWREG(ui32Base + ADC_O_PC) = (ui32Config >> 4) & ADC_PC_SR_M;

    //
    // Write the clock select and divider.
    //
    HWREG(ui32Base + ADC_O_CC) = (ui32Config & ADC_CC_CS_M) |
                                 (((ui32ClockDiv - 1) << ADC_CC_CLKDIV_S)) ;
}

//*****************************************************************************
//
//! Returns the clock configuration for the ADC.
//!
//! \param ui32Base is the base address of the ADC to configure, which must
//! always be \b ADC0_BASE.
//! \param pui32ClockDiv is a pointer to the input clock divider for the clock
//! selected by the \b ADC_CLOCK_SRC in use by the ADCs.
//!
//! This function returns the ADC clock configuration and the clock divider for
//! the ADCs.
//!
//! \b Example: Read the current ADC clock configuration.
//!
//! \verbatim
//! uint32_t ui32Config, ui32ClockDiv;
//!
//! //
//! // Read the current ADC clock configuration.
//! //
//! ui32Config = ADCClockConfigGet(ADC0_BASE, &ui32ClockDiv);
//! \endverbatim
//!
//! \return The current clock configuration of the ADC defined as a combination
//! of one of \b ADC_CLOCK_SRC_PLL, \b ADC_CLOCK_SRC_PIOSC,
//! \b ADC_CLOCK_SRC_MOSC, or \b ADC_CLOCK_SRC_ALTCLK logical ORed with one of
//! \b ADC_CLOCK_RATE_FULL, \b ADC_CLOCK_RATE_HALF, \b ADC_CLOCK_RATE_QUARTER,
//! or \b ADC_CLOCK_RATE_EIGHTH.  See ADCClockConfigSet() for more information
//! on these values.
//
//*****************************************************************************
uint32_t
ADCClockConfigGet(uint32_t ui32Base, uint32_t *pui32ClockDiv)
{
    uint32_t ui32Config;

    //
    // Check the argument.
    //
    ASSERT(ui32Base == ADC0_BASE);

    //
    // Read the current configuration.
    //
    ui32Config = HWREG(ADC0_BASE + ADC_O_CC);

    //
    // If the clock divider was requested provide the current value.
    //
    if(pui32ClockDiv)
    {
        *pui32ClockDiv =
                    ((ui32Config & ADC_CC_CLKDIV_M) >> ADC_CC_CLKDIV_S) + 1;
    }

    //
    // Clear out the divider bits.
    //
    ui32Config &= ~ADC_CC_CLKDIV_M;

    //
    // Add in the sample interval to the configuration.
    //
    ui32Config |= (HWREG(ADC0_BASE + ADC_O_PC) & ADC_PC_SR_M) << 4;

    return(ui32Config);
}

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
