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
// gpio.h - Driver for the GPIO Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_GPIO_H__
#define __MSP430WARE_GPIO_H__

#include "inc/hw_memmap.h"

#if defined(__MSP430_HAS_PORT1_R__) || defined(__MSP430_HAS_PORT2_R__) || \
    defined(__MSP430_HAS_PORTA_R__)

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
// The following are values that can be passed to the selectedPort parameter
// for functions: GPIO_setAsOutputPin(), GPIO_setAsInputPin(),
// GPIO_setAsPeripheralModuleFunctionOutputPin(),
// GPIO_setAsPeripheralModuleFunctionInputPin(), GPIO_setOutputHighOnPin(),
// GPIO_setOutputLowOnPin(), GPIO_toggleOutputOnPin(),
// GPIO_setAsInputPinWithPullDownResistor(),
// GPIO_setAsInputPinWithPullUpResistor(), GPIO_getInputPinValue(),
// GPIO_selectInterruptEdge(), GPIO_enableInterrupt(), GPIO_disableInterrupt(),
// GPIO_getInterruptStatus(), and GPIO_clearInterrupt().
//
//*****************************************************************************
#define GPIO_PORT_P1                                                          1
#define GPIO_PORT_P2                                                          2
#define GPIO_PORT_P3                                                          3
#define GPIO_PORT_P4                                                          4
#define GPIO_PORT_P5                                                          5
#define GPIO_PORT_P6                                                          6
#define GPIO_PORT_P7                                                          7
#define GPIO_PORT_P8                                                          8
#define GPIO_PORT_P9                                                          9
#define GPIO_PORT_P10                                                        10
#define GPIO_PORT_P11                                                        11
#define GPIO_PORT_PA                                                          1
#define GPIO_PORT_PB                                                          3
#define GPIO_PORT_PC                                                          5
#define GPIO_PORT_PD                                                          7
#define GPIO_PORT_PE                                                          9
#define GPIO_PORT_PF                                                         11
#define GPIO_PORT_PJ                                                         13

//*****************************************************************************
//
// The following are values that can be passed to the selectedPins parameter
// for functions: GPIO_setAsOutputPin(), GPIO_setAsInputPin(),
// GPIO_setAsPeripheralModuleFunctionOutputPin(),
// GPIO_setAsPeripheralModuleFunctionInputPin(), GPIO_setOutputHighOnPin(),
// GPIO_setOutputLowOnPin(), GPIO_toggleOutputOnPin(),
// GPIO_setAsInputPinWithPullDownResistor(),
// GPIO_setAsInputPinWithPullUpResistor(), GPIO_getInputPinValue(),
// GPIO_enableInterrupt(), GPIO_disableInterrupt(), GPIO_getInterruptStatus(),
// GPIO_clearInterrupt(), and GPIO_selectInterruptEdge() as well as returned by
// the GPIO_getInterruptStatus() function.
//
//*****************************************************************************
#define GPIO_PIN0                                                      (0x0001)
#define GPIO_PIN1                                                      (0x0002)
#define GPIO_PIN2                                                      (0x0004)
#define GPIO_PIN3                                                      (0x0008)
#define GPIO_PIN4                                                      (0x0010)
#define GPIO_PIN5                                                      (0x0020)
#define GPIO_PIN6                                                      (0x0040)
#define GPIO_PIN7                                                      (0x0080)
#define GPIO_PIN8                                                      (0x0100)
#define GPIO_PIN9                                                      (0x0200)
#define GPIO_PIN10                                                     (0x0400)
#define GPIO_PIN11                                                     (0x0800)
#define GPIO_PIN12                                                     (0x1000)
#define GPIO_PIN13                                                     (0x2000)
#define GPIO_PIN14                                                     (0x4000)
#define GPIO_PIN15                                                     (0x8000)

//*****************************************************************************
//
// The following are values that can be passed to the mode parameter for
// functions: GPIO_setAsPeripheralModuleFunctionOutputPin(), and
// GPIO_setAsPeripheralModuleFunctionInputPin().
//
//*****************************************************************************
#define GPIO_PRIMARY_MODULE_FUNCTION                                     (0x01)
#define GPIO_SECONDARY_MODULE_FUNCTION                                   (0x02)
#define GPIO_TERNARY_MODULE_FUNCTION                                     (0x03)

//*****************************************************************************
//
// The following are values that can be passed to the edgeSelect parameter for
// functions: GPIO_selectInterruptEdge().
//
//*****************************************************************************
#define GPIO_HIGH_TO_LOW_TRANSITION                                      (0x01)
#define GPIO_LOW_TO_HIGH_TRANSITION                                      (0x00)

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the GPIO_getInputPinValue() function.
//
//*****************************************************************************
#define GPIO_INPUT_PIN_HIGH                                              (0x01)
#define GPIO_INPUT_PIN_LOW                                               (0x00)

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief This function configures the selected Pin as output pin
//!
//! This function selected pins on a selected port as output pins.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//!
//! Modified bits of \b PxDIR register and bits of \b PxSEL register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_setAsOutputPin(uint8_t selectedPort,
                                uint16_t selectedPins);

//*****************************************************************************
//
//! \brief This function configures the selected Pin as input pin
//!
//! This function selected pins on a selected port as input pins.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//!
//! Modified bits of \b PxDIR register, bits of \b PxREN register and bits of
//! \b PxSEL register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_setAsInputPin(uint8_t selectedPort,
                               uint16_t selectedPins);

//*****************************************************************************
//
//! \brief This function configures the peripheral module function in the
//! output direction for the selected pin.
//!
//! This function configures the peripheral module function in the output
//! direction for the selected pin for either primary, secondary or ternary
//! module function modes. Note that MSP430F5xx/6xx family doesn't support
//! these function modes.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//! \param mode is the specified mode that the pin should be configured for the
//!        module function.
//!        Valid values are:
//!        - \b GPIO_PRIMARY_MODULE_FUNCTION
//!        - \b GPIO_SECONDARY_MODULE_FUNCTION
//!        - \b GPIO_TERNARY_MODULE_FUNCTION
//!
//! Modified bits of \b PxDIR register and bits of \b PxSEL register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_setAsPeripheralModuleFunctionOutputPin(uint8_t selectedPort,
                                                        uint16_t selectedPins,
                                                        uint8_t mode);

//*****************************************************************************
//
//! \brief This function configures the peripheral module function in the input
//! direction for the selected pin.
//!
//! This function configures the peripheral module function in the input
//! direction for the selected pin for either primary, secondary or ternary
//! module function modes. Note that MSP430F5xx/6xx family doesn't support
//! these function modes.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//! \param mode is the specified mode that the pin should be configured for the
//!        module function.
//!        Valid values are:
//!        - \b GPIO_PRIMARY_MODULE_FUNCTION
//!        - \b GPIO_SECONDARY_MODULE_FUNCTION
//!        - \b GPIO_TERNARY_MODULE_FUNCTION
//!
//! Modified bits of \b PxDIR register and bits of \b PxSEL register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_setAsPeripheralModuleFunctionInputPin(uint8_t selectedPort,
                                                       uint16_t selectedPins,
                                                       uint8_t mode);

//*****************************************************************************
//
//! \brief This function sets output HIGH on the selected Pin
//!
//! This function sets output HIGH on the selected port's pin.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//!
//! Modified bits of \b PxOUT register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_setOutputHighOnPin(uint8_t selectedPort,
                                    uint16_t selectedPins);

//*****************************************************************************
//
//! \brief This function sets output LOW on the selected Pin
//!
//! This function sets output LOW on the selected port's pin.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//!
//! Modified bits of \b PxOUT register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_setOutputLowOnPin(uint8_t selectedPort,
                                   uint16_t selectedPins);

//*****************************************************************************
//
//! \brief This function toggles the output on the selected Pin
//!
//! This function toggles the output on the selected port's pin.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//!
//! Modified bits of \b PxOUT register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_toggleOutputOnPin(uint8_t selectedPort,
                                   uint16_t selectedPins);

//*****************************************************************************
//
//! \brief This function sets the selected Pin in input Mode with Pull Down
//! resistor
//!
//! This function sets the selected Pin in input Mode with Pull Down resistor.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//!
//! Modified bits of \b PxDIR register, bits of \b PxOUT register and bits of
//! \b PxREN register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_setAsInputPinWithPullDownResistor(uint8_t selectedPort,
                                                   uint16_t selectedPins);

//*****************************************************************************
//
//! \brief This function sets the selected Pin in input Mode with Pull Up
//! resistor
//!
//! This function sets the selected Pin in input Mode with Pull Up resistor.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//!
//! Modified bits of \b PxDIR register, bits of \b PxOUT register and bits of
//! \b PxREN register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_setAsInputPinWithPullUpResistor(uint8_t selectedPort,
                                                 uint16_t selectedPins);

//*****************************************************************************
//
//! \brief This function gets the input value on the selected pin
//!
//! This function gets the input value on the selected pin.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Valid values are:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//!
//! \return One of the following:
//!         - \b GPIO_INPUT_PIN_HIGH
//!         - \b GPIO_INPUT_PIN_LOW
//!         \n indicating the status of the pin
//
//*****************************************************************************
extern uint8_t GPIO_getInputPinValue(uint8_t selectedPort,
                                     uint16_t selectedPins);

//*****************************************************************************
//
//! \brief This function enables the port interrupt on the selected pin
//!
//! This function enables the port interrupt on the selected pin. Please refer
//! to family user's guide for available ports with interrupt capability.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//!
//! Modified bits of \b PxIE register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_enableInterrupt(uint8_t selectedPort,
                                 uint16_t selectedPins);

//*****************************************************************************
//
//! \brief This function disables the port interrupt on the selected pin
//!
//! This function disables the port interrupt on the selected pin. Please refer
//! to family user's guide for available ports with interrupt capability.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//!
//! Modified bits of \b PxIE register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_disableInterrupt(uint8_t selectedPort,
                                  uint16_t selectedPins);

//*****************************************************************************
//
//! \brief This function gets the interrupt status of the selected pin
//!
//! This function gets the interrupt status of the selected pin. Please refer
//! to family user's guide for available ports with interrupt capability.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//!
//! \return Logical OR of any of the following:
//!         - \b GPIO_PIN0
//!         - \b GPIO_PIN1
//!         - \b GPIO_PIN2
//!         - \b GPIO_PIN3
//!         - \b GPIO_PIN4
//!         - \b GPIO_PIN5
//!         - \b GPIO_PIN6
//!         - \b GPIO_PIN7
//!         - \b GPIO_PIN8
//!         - \b GPIO_PIN9
//!         - \b GPIO_PIN10
//!         - \b GPIO_PIN11
//!         - \b GPIO_PIN12
//!         - \b GPIO_PIN13
//!         - \b GPIO_PIN14
//!         - \b GPIO_PIN15
//!         \n indicating the interrupt status of the selected pins [Default:
//!         0]
//
//*****************************************************************************
extern uint16_t GPIO_getInterruptStatus(uint8_t selectedPort,
                                        uint16_t selectedPins);

//*****************************************************************************
//
//! \brief This function clears the interrupt flag on the selected pin
//!
//! This function clears the interrupt flag on the selected pin. Please refer
//! to family user's guide for available ports with interrupt capability.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//!
//! Modified bits of \b PxIFG register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_clearInterrupt(uint8_t selectedPort,
                                uint16_t selectedPins);

//*****************************************************************************
//
//! \brief This function selects on what edge the port interrupt flag should be
//! set for a transition
//!
//! This function selects on what edge the port interrupt flag should be set
//! for a transition. Values for edgeSelect should be
//! GPIO_LOW_TO_HIGH_TRANSITION or GPIO_HIGH_TO_LOW_TRANSITION. Please refer to
//! family user's guide for available ports with interrupt capability.
//!
//! \param selectedPort is the selected port.
//!        Valid values are:
//!        - \b GPIO_PORT_P1
//!        - \b GPIO_PORT_P2
//!        - \b GPIO_PORT_P3
//!        - \b GPIO_PORT_P4
//!        - \b GPIO_PORT_P5
//!        - \b GPIO_PORT_P6
//!        - \b GPIO_PORT_P7
//!        - \b GPIO_PORT_P8
//!        - \b GPIO_PORT_P9
//!        - \b GPIO_PORT_P10
//!        - \b GPIO_PORT_P11
//!        - \b GPIO_PORT_PA
//!        - \b GPIO_PORT_PB
//!        - \b GPIO_PORT_PC
//!        - \b GPIO_PORT_PD
//!        - \b GPIO_PORT_PE
//!        - \b GPIO_PORT_PF
//!        - \b GPIO_PORT_PJ
//! \param selectedPins is the specified pin in the selected port.
//!        Mask value is the logical OR of any of the following:
//!        - \b GPIO_PIN0
//!        - \b GPIO_PIN1
//!        - \b GPIO_PIN2
//!        - \b GPIO_PIN3
//!        - \b GPIO_PIN4
//!        - \b GPIO_PIN5
//!        - \b GPIO_PIN6
//!        - \b GPIO_PIN7
//!        - \b GPIO_PIN8
//!        - \b GPIO_PIN9
//!        - \b GPIO_PIN10
//!        - \b GPIO_PIN11
//!        - \b GPIO_PIN12
//!        - \b GPIO_PIN13
//!        - \b GPIO_PIN14
//!        - \b GPIO_PIN15
//! \param edgeSelect specifies what transition sets the interrupt flag
//!        Valid values are:
//!        - \b GPIO_HIGH_TO_LOW_TRANSITION
//!        - \b GPIO_LOW_TO_HIGH_TRANSITION
//!
//! Modified bits of \b PxIES register.
//!
//! \return None
//
//*****************************************************************************
extern void GPIO_selectInterruptEdge(uint8_t selectedPort,
                                     uint16_t selectedPins,
                                     uint8_t edgeSelect);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_GPIO_H__
