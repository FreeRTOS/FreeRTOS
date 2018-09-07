/* --COPYRIGHT--,BSD
 * Copyright (c) 2014, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * --/COPYRIGHT--*/
//*****************************************************************************
//
// sfr.h - Driver for the SFR Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_SFR_H__
#define __MSP430WARE_SFR_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_SFR__

//*****************************************************************************
//
// If building with a C++ compiler, make all of the definitions in this header
// have a C binding.
//
//*****************************************************************************
#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// The following are values that can be passed to the interruptMask parameter
// for functions: SFR_enableInterrupt(), and SFR_disableInterrupt(); the
// interruptFlagMask parameter for functions: SFR_getInterruptStatus(), and
// SFR_clearInterrupt() as well as returned by the SFR_getInterruptStatus()
// function.
//
//*****************************************************************************
#define SFR_JTAG_OUTBOX_INTERRUPT                                      JMBOUTIE
#define SFR_JTAG_INBOX_INTERRUPT                                        JMBINIE
#define SFR_NMI_PIN_INTERRUPT                                             NMIIE
#define SFR_VACANT_MEMORY_ACCESS_INTERRUPT                                VMAIE
#define SFR_OSCILLATOR_FAULT_INTERRUPT                                     OFIE
#define SFR_WATCHDOG_INTERVAL_TIMER_INTERRUPT                             WDTIE

//*****************************************************************************
//
// The following are values that can be passed to the pullResistorSetup
// parameter for functions: SFR_setResetPinPullResistor().
//
//*****************************************************************************
#define SFR_RESISTORDISABLE                            (!(SYSRSTRE + SYSRSTUP))
#define SFR_RESISTORENABLE_PULLUP                         (SYSRSTRE + SYSRSTUP)
#define SFR_RESISTORENABLE_PULLDOWN                                  (SYSRSTRE)

//*****************************************************************************
//
// The following are values that can be passed to the edgeDirection parameter
// for functions: SFR_setNMIEdge().
//
//*****************************************************************************
#define SFR_NMI_RISINGEDGE                                       (!(SYSNMIIES))
#define SFR_NMI_FALLINGEDGE                                         (SYSNMIIES)

//*****************************************************************************
//
// The following are values that can be passed to the resetPinFunction
// parameter for functions: SFR_setResetNMIPinFunction().
//
//*****************************************************************************
#define SFR_RESETPINFUNC_RESET                                      (!(SYSNMI))
#define SFR_RESETPINFUNC_NMI                                           (SYSNMI)

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Enables selected SFR interrupt sources.
//!
//! This function enables the selected SFR interrupt sources. Only the sources
//! that are enabled can be reflected to the processor interrupt; disabled
//! sources have no effect on the processor. Does not clear interrupt flags.
//!
//! \param interruptMask is the bit mask of interrupts that will be enabled.
//!        Mask value is the logical OR of any of the following:
//!        - \b SFR_JTAG_OUTBOX_INTERRUPT - JTAG outbox interrupt
//!        - \b SFR_JTAG_INBOX_INTERRUPT - JTAG inbox interrupt
//!        - \b SFR_NMI_PIN_INTERRUPT - NMI pin interrupt, if NMI function is
//!           chosen
//!        - \b SFR_VACANT_MEMORY_ACCESS_INTERRUPT - Vacant memory access
//!           interrupt
//!        - \b SFR_OSCILLATOR_FAULT_INTERRUPT - Oscillator fault interrupt
//!        - \b SFR_WATCHDOG_INTERVAL_TIMER_INTERRUPT - Watchdog interval timer
//!           interrupt
//!
//! \return None
//
//*****************************************************************************
extern void SFR_enableInterrupt(uint8_t interruptMask);

//*****************************************************************************
//
//! \brief Disables selected SFR interrupt sources.
//!
//! This function disables the selected SFR interrupt sources. Only the sources
//! that are enabled can be reflected to the processor interrupt; disabled
//! sources have no effect on the processor.
//!
//! \param interruptMask is the bit mask of interrupts that will be disabled.
//!        Mask value is the logical OR of any of the following:
//!        - \b SFR_JTAG_OUTBOX_INTERRUPT - JTAG outbox interrupt
//!        - \b SFR_JTAG_INBOX_INTERRUPT - JTAG inbox interrupt
//!        - \b SFR_NMI_PIN_INTERRUPT - NMI pin interrupt, if NMI function is
//!           chosen
//!        - \b SFR_VACANT_MEMORY_ACCESS_INTERRUPT - Vacant memory access
//!           interrupt
//!        - \b SFR_OSCILLATOR_FAULT_INTERRUPT - Oscillator fault interrupt
//!        - \b SFR_WATCHDOG_INTERVAL_TIMER_INTERRUPT - Watchdog interval timer
//!           interrupt
//!
//! \return None
//
//*****************************************************************************
extern void SFR_disableInterrupt(uint8_t interruptMask);

//*****************************************************************************
//
//! \brief Returns the status of the selected SFR interrupt flags.
//!
//! This function returns the status of the selected SFR interrupt flags in a
//! bit mask format matching that passed into the interruptFlagMask parameter.
//!
//! \param interruptFlagMask is the bit mask of interrupt flags that the status
//!        of should be returned.
//!        Mask value is the logical OR of any of the following:
//!        - \b SFR_JTAG_OUTBOX_INTERRUPT - JTAG outbox interrupt
//!        - \b SFR_JTAG_INBOX_INTERRUPT - JTAG inbox interrupt
//!        - \b SFR_NMI_PIN_INTERRUPT - NMI pin interrupt, if NMI function is
//!           chosen
//!        - \b SFR_VACANT_MEMORY_ACCESS_INTERRUPT - Vacant memory access
//!           interrupt
//!        - \b SFR_OSCILLATOR_FAULT_INTERRUPT - Oscillator fault interrupt
//!        - \b SFR_WATCHDOG_INTERVAL_TIMER_INTERRUPT - Watchdog interval timer
//!           interrupt
//!
//! \return A bit mask of the status of the selected interrupt flags.
//!         Return Logical OR of any of the following:
//!         - \b SFR_JTAG_OUTBOX_INTERRUPT JTAG outbox interrupt
//!         - \b SFR_JTAG_INBOX_INTERRUPT JTAG inbox interrupt
//!         - \b SFR_NMI_PIN_INTERRUPT NMI pin interrupt, if NMI function is
//!         chosen
//!         - \b SFR_VACANT_MEMORY_ACCESS_INTERRUPT Vacant memory access
//!         interrupt
//!         - \b SFR_OSCILLATOR_FAULT_INTERRUPT Oscillator fault interrupt
//!         - \b SFR_WATCHDOG_INTERVAL_TIMER_INTERRUPT Watchdog interval timer
//!         interrupt
//!         \n indicating the status of the masked interrupts
//
//*****************************************************************************
extern uint8_t SFR_getInterruptStatus(uint8_t interruptFlagMask);

//*****************************************************************************
//
//! \brief Clears the selected SFR interrupt flags.
//!
//! This function clears the status of the selected SFR interrupt flags.
//!
//! \param interruptFlagMask is the bit mask of interrupt flags that will be
//!        cleared.
//!        Mask value is the logical OR of any of the following:
//!        - \b SFR_JTAG_OUTBOX_INTERRUPT - JTAG outbox interrupt
//!        - \b SFR_JTAG_INBOX_INTERRUPT - JTAG inbox interrupt
//!        - \b SFR_NMI_PIN_INTERRUPT - NMI pin interrupt, if NMI function is
//!           chosen
//!        - \b SFR_VACANT_MEMORY_ACCESS_INTERRUPT - Vacant memory access
//!           interrupt
//!        - \b SFR_OSCILLATOR_FAULT_INTERRUPT - Oscillator fault interrupt
//!        - \b SFR_WATCHDOG_INTERVAL_TIMER_INTERRUPT - Watchdog interval timer
//!           interrupt
//!
//! \return None
//
//*****************************************************************************
extern void SFR_clearInterrupt(uint8_t interruptFlagMask);

//*****************************************************************************
//
//! \brief Sets the pull-up/down resistor on the ~RST/NMI pin.
//!
//! This function sets the pull-up/down resistors on the ~RST/NMI pin to the
//! settings from the pullResistorSetup parameter.
//!
//! \param pullResistorSetup is the selection of how the pull-up/down resistor
//!        on the ~RST/NMI pin should be setup or disabled.
//!        Valid values are:
//!        - \b SFR_RESISTORDISABLE
//!        - \b SFR_RESISTORENABLE_PULLUP [Default]
//!        - \b SFR_RESISTORENABLE_PULLDOWN
//!        \n Modified bits are \b SYSRSTUP and \b SYSRSTRE of \b SFRRPCR
//!        register.
//!
//! \return None
//
//*****************************************************************************
extern void SFR_setResetPinPullResistor(uint16_t pullResistorSetup);

//*****************************************************************************
//
//! \brief Sets the edge direction that will assert an NMI from a signal on the
//! ~RST/NMI pin if NMI function is active.
//!
//! This function sets the edge direction that will assert an NMI from a signal
//! on the ~RST/NMI pin if the NMI function is active. To activate the NMI
//! function of the ~RST/NMI use the SFR_setResetNMIPinFunction() passing
//! SFR_RESETPINFUNC_NMI into the resetPinFunction parameter.
//!
//! \param edgeDirection is the direction that the signal on the ~RST/NMI pin
//!        should go to signal an interrupt, if enabled.
//!        Valid values are:
//!        - \b SFR_NMI_RISINGEDGE [Default]
//!        - \b SFR_NMI_FALLINGEDGE
//!        \n Modified bits are \b SYSNMIIES of \b SFRRPCR register.
//!
//! \return None
//
//*****************************************************************************
extern void SFR_setNMIEdge(uint16_t edgeDirection);

//*****************************************************************************
//
//! \brief Sets the function of the ~RST/NMI pin.
//!
//! This function sets the functionality of the ~RST/NMI pin, whether in reset
//! mode which will assert a reset if a low signal is observed on that pin, or
//! an NMI which will assert an interrupt from an edge of the signal dependent
//! on the setting of the edgeDirection parameter in SFR_setNMIEdge().
//!
//! \param resetPinFunction is the function that the ~RST/NMI pin should take
//!        on.
//!        Valid values are:
//!        - \b SFR_RESETPINFUNC_RESET [Default]
//!        - \b SFR_RESETPINFUNC_NMI
//!        \n Modified bits are \b SYSNMI of \b SFRRPCR register.
//!
//! \return None
//
//*****************************************************************************
extern void SFR_setResetNMIPinFunction(uint8_t resetPinFunction);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_SFR_H__
