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
// comp_e.h - Driver for the COMP_E Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_COMP_E_H__
#define __MSP430WARE_COMP_E_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_COMP_E__

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

#include "inc/hw_regaccess.h"
//*****************************************************************************
//
//! \brief Used in the Comp_E_init() function as the param parameter.
//
//*****************************************************************************
typedef struct Comp_E_initParam
{
    //! Selects the input to the positive terminal.
    //! \n Valid values are:
    //! - \b COMP_E_INPUT0 [Default]
    //! - \b COMP_E_INPUT1
    //! - \b COMP_E_INPUT2
    //! - \b COMP_E_INPUT3
    //! - \b COMP_E_INPUT4
    //! - \b COMP_E_INPUT5
    //! - \b COMP_E_INPUT6
    //! - \b COMP_E_INPUT7
    //! - \b COMP_E_INPUT8
    //! - \b COMP_E_INPUT9
    //! - \b COMP_E_INPUT10
    //! - \b COMP_E_INPUT11
    //! - \b COMP_E_INPUT12
    //! - \b COMP_E_INPUT13
    //! - \b COMP_E_INPUT14
    //! - \b COMP_E_INPUT15
    //! - \b COMP_E_VREF
    uint16_t posTerminalInput;
    //! Selects the input to the negative terminal.
    //! \n Valid values are:
    //! - \b COMP_E_INPUT0 [Default]
    //! - \b COMP_E_INPUT1
    //! - \b COMP_E_INPUT2
    //! - \b COMP_E_INPUT3
    //! - \b COMP_E_INPUT4
    //! - \b COMP_E_INPUT5
    //! - \b COMP_E_INPUT6
    //! - \b COMP_E_INPUT7
    //! - \b COMP_E_INPUT8
    //! - \b COMP_E_INPUT9
    //! - \b COMP_E_INPUT10
    //! - \b COMP_E_INPUT11
    //! - \b COMP_E_INPUT12
    //! - \b COMP_E_INPUT13
    //! - \b COMP_E_INPUT14
    //! - \b COMP_E_INPUT15
    //! - \b COMP_E_VREF
    uint16_t negTerminalInput;
    //! Controls the output filter delay state, which is either off or enabled
    //! with a specified delay level. This parameter is device specific and
    //! delay levels should be found in the device's datasheet.
    //! \n Valid values are:
    //! - \b COMP_E_FILTEROUTPUT_OFF [Default]
    //! - \b COMP_E_FILTEROUTPUT_DLYLVL1
    //! - \b COMP_E_FILTEROUTPUT_DLYLVL2
    //! - \b COMP_E_FILTEROUTPUT_DLYLVL3
    //! - \b COMP_E_FILTEROUTPUT_DLYLVL4
    uint8_t outputFilterEnableAndDelayLevel;
    //! Controls if the output will be inverted or not
    //! \n Valid values are:
    //! - \b COMP_E_NORMALOUTPUTPOLARITY
    //! - \b COMP_E_INVERTEDOUTPUTPOLARITY
    uint16_t invertedOutputPolarity;
} Comp_E_initParam;

//*****************************************************************************
//
// The following are values that can be passed to the
// outputFilterEnableAndDelayLevel parameter for functions: Comp_E_init(); the
// param parameter for functions: Comp_E_init().
//
//*****************************************************************************
#define COMP_E_FILTEROUTPUT_OFF                                            0x00
#define COMP_E_FILTEROUTPUT_DLYLVL1                            (CEF + CEFDLY_0)
#define COMP_E_FILTEROUTPUT_DLYLVL2                            (CEF + CEFDLY_1)
#define COMP_E_FILTEROUTPUT_DLYLVL3                            (CEF + CEFDLY_2)
#define COMP_E_FILTEROUTPUT_DLYLVL4                            (CEF + CEFDLY_3)

//*****************************************************************************
//
// The following are values that can be passed to the posTerminalInput
// parameter for functions: Comp_E_init(); the inputPort parameter for
// functions: Comp_E_disableInputBuffer(), and Comp_E_enableInputBuffer(); the
// param parameter for functions: Comp_E_init(), and Comp_E_init(); the
// negTerminalInput parameter for functions: Comp_E_init().
//
//*****************************************************************************
#define COMP_E_INPUT0                                                    (0x01)
#define COMP_E_INPUT1                                                    (0x02)
#define COMP_E_INPUT2                                                    (0x04)
#define COMP_E_INPUT3                                                    (0x08)
#define COMP_E_INPUT4                                                    (0x10)
#define COMP_E_INPUT5                                                    (0x20)
#define COMP_E_INPUT6                                                    (0x40)
#define COMP_E_INPUT7                                                    (0x80)
#define COMP_E_INPUT8                                                   (0x100)
#define COMP_E_INPUT9                                                   (0x200)
#define COMP_E_INPUT10                                                  (0x400)
#define COMP_E_INPUT11                                                  (0x800)
#define COMP_E_INPUT12                                                 (0x1000)
#define COMP_E_INPUT13                                                 (0x2000)
#define COMP_E_INPUT14                                                 (0x4000)
#define COMP_E_INPUT15                                                 (0x8000)
#define COMP_E_VREF                                                      (0x9F)

//*****************************************************************************
//
// The following are values that can be passed to the invertedOutputPolarity
// parameter for functions: Comp_E_init(); the param parameter for functions:
// Comp_E_init().
//
//*****************************************************************************
#define COMP_E_NORMALOUTPUTPOLARITY                               (!(CEOUTPOL))
#define COMP_E_INVERTEDOUTPUTPOLARITY                                (CEOUTPOL)

//*****************************************************************************
//
// The following are values that can be passed to the
// supplyVoltageReferenceBase parameter for functions:
// Comp_E_setReferenceVoltage().
//
//*****************************************************************************
#define COMP_E_REFERENCE_AMPLIFIER_DISABLED                          (CEREFL_0)
#define COMP_E_VREFBASE1_2V                                          (CEREFL_1)
#define COMP_E_VREFBASE2_0V                                          (CEREFL_2)
#define COMP_E_VREFBASE2_5V                                          (CEREFL_3)

//*****************************************************************************
//
// The following are values that can be passed to the referenceAccuracy
// parameter for functions: Comp_E_setReferenceAccuracy().
//
//*****************************************************************************
#define COMP_E_ACCURACY_STATIC                                      (!CEREFACC)
#define COMP_E_ACCURACY_CLOCKED                                      (CEREFACC)

//*****************************************************************************
//
// The following are values that can be passed to the powerMode parameter for
// functions: Comp_E_setPowerMode().
//
//*****************************************************************************
#define COMP_E_HIGH_SPEED_MODE                                      (CEPWRMD_0)
#define COMP_E_NORMAL_MODE                                          (CEPWRMD_1)
#define COMP_E_ULTRA_LOW_POWER_MODE                                 (CEPWRMD_2)

//*****************************************************************************
//
// The following are values that can be passed to the interruptMask parameter
// for functions: Comp_E_enableInterrupt(), and Comp_E_disableInterrupt().
//
//*****************************************************************************
#define COMP_E_OUTPUT_INTERRUPT                                          (CEIE)
#define COMP_E_INVERTED_POLARITY_INTERRUPT                              (CEIIE)
#define COMP_E_READY_INTERRUPT                                        (CERDYIE)

//*****************************************************************************
//
// The following are values that can be passed to the interruptFlagMask
// parameter for functions: Comp_E_clearInterrupt(), and
// Comp_E_getInterruptStatus() as well as returned by the
// Comp_E_getInterruptStatus() function.
//
//*****************************************************************************
#define COMP_E_OUTPUT_INTERRUPT_FLAG                                    (CEIFG)
#define COMP_E_INTERRUPT_FLAG_INVERTED_POLARITY                        (CEIIFG)
#define COMP_E_INTERRUPT_FLAG_READY                                  (CERDYIFG)

//*****************************************************************************
//
// The following are values that can be passed to the edgeDirection parameter
// for functions: Comp_E_setInterruptEdgeDirection().
//
//*****************************************************************************
#define COMP_E_FALLINGEDGE                                           (!(CEIES))
#define COMP_E_RISINGEDGE                                               (CEIES)

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the Comp_E_outputValue() function.
//
//*****************************************************************************
#define COMP_E_LOW                                                        (0x0)
#define COMP_E_HIGH                                                     (CEOUT)

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Initializes the Comp_E Module.
//!
//! Upon successful initialization of the Comp_E module, this function will
//! have reset all necessary register bits and set the given options in the
//! registers. To actually use the Comp_E module, the Comp_E_enable() function
//! must be explicitly called before use. If a Reference Voltage is set to a
//! terminal, the Voltage should be set using the setReferenceVoltage()
//! function.
//!
//! \param baseAddress is the base address of the COMP_E module.
//! \param param is the pointer to struct for initialization.
//!
//! \return STATUS_SUCCESS or STATUS_FAILURE of the initialization process
//
//*****************************************************************************
extern bool Comp_E_init(uint16_t baseAddress,
                        Comp_E_initParam *param);

//*****************************************************************************
//
//! \brief Generates a Reference Voltage to the terminal selected during
//! initialization.
//!
//! Use this function to generate a voltage to serve as a reference to the
//! terminal selected at initialization. The voltage is determined by the
//! equation: Vbase * (Numerator / 32). If the upper and lower limit voltage
//! numerators are equal, then a static reference is defined, whereas they are
//! different then a hysteresis effect is generated.
//!
//! \param baseAddress is the base address of the COMP_E module.
//! \param supplyVoltageReferenceBase decides the source and max amount of
//!        Voltage that can be used as a reference.
//!        Valid values are:
//!        - \b COMP_E_REFERENCE_AMPLIFIER_DISABLED
//!        - \b COMP_E_VREFBASE1_2V
//!        - \b COMP_E_VREFBASE2_0V
//!        - \b COMP_E_VREFBASE2_5V
//!        \n Modified bits are \b CEREFL of \b CECTL2 register.
//! \param lowerLimitSupplyVoltageFractionOf32 is the numerator of the equation
//!        to generate the reference voltage for the lower limit reference
//!        voltage.
//!        \n Modified bits are \b CEREF0 of \b CECTL2 register.
//! \param upperLimitSupplyVoltageFractionOf32 is the numerator of the equation
//!        to generate the reference voltage for the upper limit reference
//!        voltage.
//!        \n Modified bits are \b CEREF1 of \b CECTL2 register.
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_setReferenceVoltage(uint16_t baseAddress,
                                       uint16_t supplyVoltageReferenceBase,
                                       uint16_t lowerLimitSupplyVoltageFractionOf32,
                                       uint16_t upperLimitSupplyVoltageFractionOf32);

//*****************************************************************************
//
//! \brief Sets the reference accuracy
//!
//! The reference accuracy is set to the desired setting. Clocked is better for
//! low power operations but has a lower accuracy.
//!
//! \param baseAddress is the base address of the COMP_E module.
//! \param referenceAccuracy is the reference accuracy setting of the COMP_E.
//!        Valid values are:
//!        - \b COMP_E_ACCURACY_STATIC
//!        - \b COMP_E_ACCURACY_CLOCKED - for low power / low accuracy
//!        \n Modified bits are \b CEREFACC of \b CECTL2 register.
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_setReferenceAccuracy(uint16_t baseAddress,
                                        uint16_t referenceAccuracy);

//*****************************************************************************
//
//! \brief Sets the power mode
//!
//! \param baseAddress is the base address of the COMP_E module.
//! \param powerMode decides the power mode
//!        Valid values are:
//!        - \b COMP_E_HIGH_SPEED_MODE
//!        - \b COMP_E_NORMAL_MODE
//!        - \b COMP_E_ULTRA_LOW_POWER_MODE
//!        \n Modified bits are \b CEPWRMD of \b CECTL1 register.
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_setPowerMode(uint16_t baseAddress,
                                uint16_t powerMode);

//*****************************************************************************
//
//! \brief Enables selected Comp_E interrupt sources.
//!
//! Enables the indicated Comp_E interrupt sources.  Only the sources that are
//! enabled can be reflected to the processor interrupt; disabled sources have
//! no effect on the processor. <b>Does not clear interrupt flags.</b>
//!
//! \param baseAddress is the base address of the COMP_E module.
//! \param interruptMask
//!        Mask value is the logical OR of any of the following:
//!        - \b COMP_E_OUTPUT_INTERRUPT - Output interrupt
//!        - \b COMP_E_INVERTED_POLARITY_INTERRUPT - Output interrupt inverted
//!           polarity
//!        - \b COMP_E_READY_INTERRUPT - Ready interrupt
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_enableInterrupt(uint16_t baseAddress,
                                   uint16_t interruptMask);

//*****************************************************************************
//
//! \brief Disables selected Comp_E interrupt sources.
//!
//! Disables the indicated Comp_E interrupt sources.  Only the sources that are
//! enabled can be reflected to the processor interrupt; disabled sources have
//! no effect on the processor.
//!
//! \param baseAddress is the base address of the COMP_E module.
//! \param interruptMask
//!        Mask value is the logical OR of any of the following:
//!        - \b COMP_E_OUTPUT_INTERRUPT - Output interrupt
//!        - \b COMP_E_INVERTED_POLARITY_INTERRUPT - Output interrupt inverted
//!           polarity
//!        - \b COMP_E_READY_INTERRUPT - Ready interrupt
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_disableInterrupt(uint16_t baseAddress,
                                    uint16_t interruptMask);

//*****************************************************************************
//
//! \brief Clears Comp_E interrupt flags.
//!
//! The Comp_E interrupt source is cleared, so that it no longer asserts. The
//! highest interrupt flag is automatically cleared when an interrupt vector
//! generator is used.
//!
//! \param baseAddress is the base address of the COMP_E module.
//! \param interruptFlagMask
//!        Mask value is the logical OR of any of the following:
//!        - \b COMP_E_OUTPUT_INTERRUPT_FLAG - Output interrupt flag
//!        - \b COMP_E_INTERRUPT_FLAG_INVERTED_POLARITY - Output interrupt flag
//!           inverted polarity
//!        - \b COMP_E_INTERRUPT_FLAG_READY - Ready interrupt flag
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_clearInterrupt(uint16_t baseAddress,
                                  uint16_t interruptFlagMask);

//*****************************************************************************
//
//! \brief Gets the current Comp_E interrupt status.
//!
//! This returns the interrupt status for the Comp_E module based on which flag
//! is passed.
//!
//! \param baseAddress is the base address of the COMP_E module.
//! \param interruptFlagMask
//!        Mask value is the logical OR of any of the following:
//!        - \b COMP_E_OUTPUT_INTERRUPT_FLAG - Output interrupt flag
//!        - \b COMP_E_INTERRUPT_FLAG_INVERTED_POLARITY - Output interrupt flag
//!           inverted polarity
//!        - \b COMP_E_INTERRUPT_FLAG_READY - Ready interrupt flag
//!
//! \return Logical OR of any of the following:
//!         - \b Comp_E_OUTPUT_INTERRUPT_FLAG Output interrupt flag
//!         - \b Comp_E_INTERRUPT_FLAG_INVERTED_POLARITY Output interrupt flag
//!         inverted polarity
//!         - \b Comp_E_INTERRUPT_FLAG_READY Ready interrupt flag
//!         \n indicating the status of the masked flags
//
//*****************************************************************************
extern uint8_t Comp_E_getInterruptStatus(uint16_t baseAddress,
                                         uint16_t interruptFlagMask);

//*****************************************************************************
//
//! \brief Explicitly sets the edge direction that would trigger an interrupt.
//!
//! This function will set which direction the output will have to go, whether
//! rising or falling, to generate an interrupt based on a non-inverted
//! interrupt.
//!
//! \param baseAddress is the base address of the COMP_E module.
//! \param edgeDirection determines which direction the edge would have to go
//!        to generate an interrupt based on the non-inverted interrupt flag.
//!        Valid values are:
//!        - \b COMP_E_FALLINGEDGE [Default] - sets the bit to generate an
//!           interrupt when the output of the Comp_E falls from HIGH to LOW if
//!           the normal interrupt bit is set(and LOW to HIGH if the inverted
//!           interrupt enable bit is set).
//!        - \b COMP_E_RISINGEDGE - sets the bit to generate an interrupt when
//!           the output of the Comp_E rises from LOW to HIGH if the normal
//!           interrupt bit is set(and HIGH to LOW if the inverted interrupt
//!           enable bit is set).
//!        \n Modified bits are \b CEIES of \b CECTL1 register.
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_setInterruptEdgeDirection(uint16_t baseAddress,
                                             uint16_t edgeDirection);

//*****************************************************************************
//
//! \brief Toggles the edge direction that would trigger an interrupt.
//!
//! This function will toggle which direction the output will have to go,
//! whether rising or falling, to generate an interrupt based on a non-inverted
//! interrupt. If the direction was rising, it is now falling, if it was
//! falling, it is now rising.
//!
//! \param baseAddress is the base address of the COMP_E module.
//!
//! Modified bits are \b CEIES of \b CECTL1 register.
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_toggleInterruptEdgeDirection(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Turns on the Comp_E module.
//!
//! This function sets the bit that enables the operation of the Comp_E module.
//!
//! \param baseAddress is the base address of the COMP_E module.
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_enable(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Turns off the Comp_E module.
//!
//! This function clears the CEON bit disabling the operation of the Comp_E
//! module, saving from excess power consumption.
//!
//! \param baseAddress is the base address of the COMP_E module.
//!
//! Modified bits are \b CEON of \b CECTL1 register.
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_disable(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Shorts the two input pins chosen during initialization.
//!
//! This function sets the bit that shorts the devices attached to the input
//! pins chosen from the initialization of the Comp_E.
//!
//! \param baseAddress is the base address of the COMP_E module.
//!
//! Modified bits are \b CESHORT of \b CECTL1 register.
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_shortInputs(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Disables the short of the two input pins chosen during
//! initialization.
//!
//! This function clears the bit that shorts the devices attached to the input
//! pins chosen from the initialization of the Comp_E.
//!
//! \param baseAddress is the base address of the COMP_E module.
//!
//! Modified bits are \b CESHORT of \b CECTL1 register.
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_unshortInputs(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Disables the input buffer of the selected input port to effectively
//! allow for analog signals.
//!
//! This function sets the bit to disable the buffer for the specified input
//! port to allow for analog signals from any of the Comp_E input pins. This
//! bit is automatically set when the input is initialized to be used with the
//! Comp_E module. This function should be used whenever an analog input is
//! connected to one of these pins to prevent parasitic voltage from causing
//! unexpected results.
//!
//! \param baseAddress is the base address of the COMP_E module.
//! \param inputPort is the port in which the input buffer will be disabled.
//!        Mask value is the logical OR of any of the following:
//!        - \b COMP_E_INPUT0 [Default]
//!        - \b COMP_E_INPUT1
//!        - \b COMP_E_INPUT2
//!        - \b COMP_E_INPUT3
//!        - \b COMP_E_INPUT4
//!        - \b COMP_E_INPUT5
//!        - \b COMP_E_INPUT6
//!        - \b COMP_E_INPUT7
//!        - \b COMP_E_INPUT8
//!        - \b COMP_E_INPUT9
//!        - \b COMP_E_INPUT10
//!        - \b COMP_E_INPUT11
//!        - \b COMP_E_INPUT12
//!        - \b COMP_E_INPUT13
//!        - \b COMP_E_INPUT14
//!        - \b COMP_E_INPUT15
//!        - \b COMP_E_VREF
//!        \n Modified bits are \b CEPDx of \b CECTL3 register.
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_disableInputBuffer(uint16_t baseAddress,
                                      uint16_t inputPort);

//*****************************************************************************
//
//! \brief Enables the input buffer of the selected input port to allow for
//! digital signals.
//!
//! This function clears the bit to enable the buffer for the specified input
//! port to allow for digital signals from any of the Comp_E input pins. This
//! should not be reset if there is an analog signal connected to the specified
//! input pin to prevent from unexpected results.
//!
//! \param baseAddress is the base address of the COMP_E module.
//! \param inputPort is the port in which the input buffer will be enabled.
//!        Mask value is the logical OR of any of the following:
//!        - \b COMP_E_INPUT0 [Default]
//!        - \b COMP_E_INPUT1
//!        - \b COMP_E_INPUT2
//!        - \b COMP_E_INPUT3
//!        - \b COMP_E_INPUT4
//!        - \b COMP_E_INPUT5
//!        - \b COMP_E_INPUT6
//!        - \b COMP_E_INPUT7
//!        - \b COMP_E_INPUT8
//!        - \b COMP_E_INPUT9
//!        - \b COMP_E_INPUT10
//!        - \b COMP_E_INPUT11
//!        - \b COMP_E_INPUT12
//!        - \b COMP_E_INPUT13
//!        - \b COMP_E_INPUT14
//!        - \b COMP_E_INPUT15
//!        - \b COMP_E_VREF
//!        \n Modified bits are \b CEPDx of \b CECTL3 register.
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_enableInputBuffer(uint16_t baseAddress,
                                     uint16_t inputPort);

//*****************************************************************************
//
//! \brief Toggles the bit that swaps which terminals the inputs go to, while
//! also inverting the output of the Comp_E.
//!
//! This function toggles the bit that controls which input goes to which
//! terminal. After initialization, this bit is set to 0, after toggling it
//! once the inputs are routed to the opposite terminal and the output is
//! inverted.
//!
//! \param baseAddress is the base address of the COMP_E module.
//!
//! \return None
//
//*****************************************************************************
extern void Comp_E_swapIO(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Returns the output value of the Comp_E module.
//!
//! Returns the output value of the Comp_E module.
//!
//! \param baseAddress is the base address of the COMP_E module.
//!
//! \return One of the following:
//!         - \b Comp_E_LOW
//!         - \b Comp_E_HIGH
//!         \n indicating the output value of the Comp_E module
//
//*****************************************************************************
extern uint16_t Comp_E_outputValue(uint16_t baseAddress);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_COMP_E_H__
