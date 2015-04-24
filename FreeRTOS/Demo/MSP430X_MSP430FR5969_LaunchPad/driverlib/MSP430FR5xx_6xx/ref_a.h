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
// ref_a.h - Driver for the REF_A Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_REF_A_H__
#define __MSP430WARE_REF_A_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_REF_A__

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
// The following are values that can be passed to the referenceVoltageSelect
// parameter for functions: Ref_A_setReferenceVoltage().
//
//*****************************************************************************
#define REF_A_VREF1_2V                                              (REFVSEL_0)
#define REF_A_VREF2_0V                                              (REFVSEL_1)
#define REF_A_VREF2_5V                                              (REFVSEL_2)

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the Ref_A_isBandgapActive() function and the
// Ref_A_isRefGenActive() function.
//
//*****************************************************************************
#define REF_A_ACTIVE                                                       true
#define REF_A_INACTIVE                                                    false

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the Ref_A_getBandgapMode() function.
//
//*****************************************************************************
#define REF_A_STATICMODE                                                   0x00
#define REF_A_SAMPLEMODE                                                 BGMODE

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the Ref_A_isRefGenBusy() function.
//
//*****************************************************************************
#define REF_A_NOTBUSY                                                      0x00
#define REF_A_BUSY                                                   REFGENBUSY

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the Ref_A_isVariableReferenceVoltageOutputReady()
// function and the Ref_A_isBufferedBandgapVoltageReady() function.
//
//*****************************************************************************
#define REF_A_NOTREADY                                                    false
#define REF_A_READY                                                        true

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Sets the reference voltage for the voltage generator.
//!
//! This function sets the reference voltage generated by the voltage generator
//! to be used by other peripherals. This reference voltage will only be valid
//! while the Ref_A module is in control. Please note, if the
//! Ref_A_isRefGenBusy() returns Ref_A_BUSY, this function will have no effect.
//!
//! \param baseAddress is the base address of the REF_A module.
//! \param referenceVoltageSelect is the desired voltage to generate for a
//!        reference voltage.
//!        Valid values are:
//!        - \b REF_A_VREF1_2V [Default]
//!        - \b REF_A_VREF2_0V
//!        - \b REF_A_VREF2_5V
//!        \n Modified bits are \b REFVSEL of \b REFCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void Ref_A_setReferenceVoltage(uint16_t baseAddress,
                                      uint8_t referenceVoltageSelect);

//*****************************************************************************
//
//! \brief Disables the internal temperature sensor to save power consumption.
//!
//! This function is used to turn off the internal temperature sensor to save
//! on power consumption. The temperature sensor is enabled by default. Please
//! note, that giving ADC12 module control over the Ref_A module, the state of
//! the temperature sensor is dependent on the controls of the ADC12 module.
//! Please note, if the Ref_A_isRefGenBusy() returns Ref_A_BUSY, this function
//! will have no effect.
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! Modified bits are \b REFTCOFF of \b REFCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void Ref_A_disableTempSensor(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Enables the internal temperature sensor.
//!
//! This function is used to turn on the internal temperature sensor to use by
//! other peripherals. The temperature sensor is enabled by default. Please
//! note, if the Ref_A_isRefGenBusy() returns Ref_A_BUSY, this function will
//! have no effect.
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! Modified bits are \b REFTCOFF of \b REFCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void Ref_A_enableTempSensor(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Outputs the reference voltage to an output pin.
//!
//! This function is used to output the reference voltage being generated to an
//! output pin. Please note, the output pin is device specific. Please note,
//! that giving ADC12 module control over the Ref_A module, the state of the
//! reference voltage as an output to a pin is dependent on the controls of the
//! ADC12 module. Please note, if the Ref_A_isRefGenBusy() returns Ref_A_BUSY,
//! this function will have no effect.
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! Modified bits are \b REFOUT of \b REFCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void Ref_A_enableReferenceVoltageOutput(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Disables the reference voltage as an output to a pin.
//!
//! This function is used to disables the reference voltage being generated to
//! be given to an output pin. Please note, if the Ref_A_isRefGenBusy() returns
//! Ref_A_BUSY, this function will have no effect.
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! Modified bits are \b REFOUT of \b REFCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void Ref_A_disableReferenceVoltageOutput(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Enables the reference voltage to be used by peripherals.
//!
//! This function is used to enable the generated reference voltage to be used
//! other peripherals or by an output pin, if enabled. Please note, that giving
//! ADC12 module control over the Ref_A module, the state of the reference
//! voltage is dependent on the controls of the ADC12 module. Please note, if
//! the Ref_A_isRefGenBusy() returns Ref_A_BUSY, this function will have no
//! effect.
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! Modified bits are \b REFON of \b REFCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void Ref_A_enableReferenceVoltage(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Disables the reference voltage.
//!
//! This function is used to disable the generated reference voltage. Please
//! note, if the Ref_A_isRefGenBusy() returns Ref_A_BUSY, this function will
//! have no effect.
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! Modified bits are \b REFON of \b REFCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void Ref_A_disableReferenceVoltage(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Returns the bandgap mode of the Ref_A module.
//!
//! This function is used to return the bandgap mode of the Ref_A module,
//! requested by the peripherals using the bandgap. If a peripheral requests
//! static mode, then the bandgap mode will be static for all modules, whereas
//! if all of the peripherals using the bandgap request sample mode, then that
//! will be the mode returned. Sample mode allows the bandgap to be active only
//! when necessary to save on power consumption, static mode requires the
//! bandgap to be active until no peripherals are using it anymore.
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! \return One of the following:
//!         - \b Ref_A_STATICMODE if the bandgap is operating in static mode
//!         - \b Ref_A_SAMPLEMODE if the bandgap is operating in sample mode
//!         \n indicating the bandgap mode of the module
//
//*****************************************************************************
extern uint16_t Ref_A_getBandgapMode(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Returns the active status of the bandgap in the Ref_A module.
//!
//! This function is used to return the active status of the bandgap in the
//! Ref_A module. If the bandgap is in use by a peripheral, then the status
//! will be seen as active.
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! \return One of the following:
//!         - \b Ref_A_ACTIVE if active
//!         - \b Ref_A_INACTIVE if not active
//!         \n indicating the bandgap active status of the module
//
//*****************************************************************************
extern bool Ref_A_isBandgapActive(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Returns the busy status of the reference generator in the Ref_A
//! module.
//!
//! This function is used to return the busy status of the reference generator
//! in the Ref_A module. If the ref generator is in use by a peripheral, then
//! the status will be seen as busy.
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! \return One of the following:
//!         - \b Ref_A_NOTBUSY if the reference generator is not being used
//!         - \b Ref_A_BUSY if the reference generator is being used,
//!         disallowing changes to be made to the Ref_A module controls
//!         \n indicating the reference generator busy status of the module
//
//*****************************************************************************
extern uint16_t Ref_A_isRefGenBusy(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Returns the active status of the reference generator in the Ref_A
//! module.
//!
//! This function is used to return the active status of the reference
//! generator in the Ref_A module. If the ref generator is on and ready to use,
//! then the status will be seen as active.
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! \return One of the following:
//!         - \b Ref_A_ACTIVE if active
//!         - \b Ref_A_INACTIVE if not active
//!         \n indicating the reference generator active status of the module
//
//*****************************************************************************
extern bool Ref_A_isRefGenActive(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Returns the busy status of the reference generator in the Ref_A
//! module.
//!
//! This function is used to return the buys status of the buffered bandgap
//! voltage in the Ref_A module. If the ref generator is on and ready to use,
//! then the status will be seen as active.
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! \return One of the following:
//!         - \b Ref_A_NOTREADY if NOT ready to be used
//!         - \b Ref_A_READY if ready to be used
//!         \n indicating the the busy status of the reference generator in the
//!         module
//
//*****************************************************************************
extern bool Ref_A_isBufferedBandgapVoltageReady(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Returns the busy status of the variable reference voltage in the
//! Ref_A module.
//!
//! This function is used to return the busy status of the variable reference
//! voltage in the Ref_A module. If the ref generator is on and ready to use,
//! then the status will be seen as active.
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! \return One of the following:
//!         - \b Ref_A_NOTREADY if NOT ready to be used
//!         - \b Ref_A_READY if ready to be used
//!         \n indicating the the busy status of the variable reference voltage
//!         in the module
//
//*****************************************************************************
extern bool Ref_A_isVariableReferenceVoltageOutputReady(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Enables the one-time trigger of the reference voltage.
//!
//! Triggers the one-time generation of the variable reference voltage. Once
//! the reference voltage request is set, this bit is cleared by hardware
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! Modified bits are \b REFGENOT of \b REFCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void Ref_A_setReferenceVoltageOneTimeTrigger(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Enables the one-time trigger of the buffered bandgap voltage.
//!
//! Triggers the one-time generation of the buffered bandgap voltage. Once the
//! buffered bandgap voltage request is set, this bit is cleared by hardware
//!
//! \param baseAddress is the base address of the REF_A module.
//!
//! Modified bits are \b REFBGOT of \b REFCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void Ref_A_setBufferedBandgapVoltageOneTimeTrigger(uint16_t baseAddress);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_REF_A_H__
