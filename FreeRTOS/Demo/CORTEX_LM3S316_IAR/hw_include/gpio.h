//*****************************************************************************
//
// gpio.h - Defines and Macros for GPIO API.
//
// Copyright (c) 2005,2006 Luminary Micro, Inc.  All rights reserved.
//
// Software License Agreement
//
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's Stellaris Family of microcontroller products.
//
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  Any use in violation
// of the foregoing restrictions may subject the user to criminal sanctions
// under applicable laws, as well as to civil liability for the breach of the
// terms and conditions of this license.
//
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
//
// This is part of revision 635 of the Stellaris Driver Library.
//
//*****************************************************************************

#ifndef __GPIO_H__
#define __GPIO_H__

#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// The following values define the bit field for the ucPins argument to several
// of the APIs.
//
//*****************************************************************************
#define GPIO_PIN_0              0x00000001  // GPIO pin 0
#define GPIO_PIN_1              0x00000002  // GPIO pin 1
#define GPIO_PIN_2              0x00000004  // GPIO pin 2
#define GPIO_PIN_3              0x00000008  // GPIO pin 3
#define GPIO_PIN_4              0x00000010  // GPIO pin 4
#define GPIO_PIN_5              0x00000020  // GPIO pin 5
#define GPIO_PIN_6              0x00000040  // GPIO pin 6
#define GPIO_PIN_7              0x00000080  // GPIO pin 7

//*****************************************************************************
//
// Values that can be passed to GPIODirModeSet as the ulPinIO parameter, and
// returned from GPIODirModeGet.
//
//*****************************************************************************
#define GPIO_DIR_MODE_IN        0x00000000  // Pin is a GPIO input
#define GPIO_DIR_MODE_OUT       0x00000001  // Pin is a GPIO output
#define GPIO_DIR_MODE_HW        0x00000002  // Pin is a peripheral function

//*****************************************************************************
//
// Values that can be passed to GPIOIntTypeSet as the ulIntType parameter, and
// returned from GPIOIntTypeGet.
//
//*****************************************************************************
#define GPIO_FALLING_EDGE       0x00000000  // Interrupt on falling edge
#define GPIO_RISING_EDGE        0x00000004  // Interrupt on rising edge
#define GPIO_BOTH_EDGES         0x00000001  // Interrupt on both edges
#define GPIO_LOW_LEVEL          0x00000002  // Interrupt on low level
#define GPIO_HIGH_LEVEL         0x00000007  // Interrupt on high level

//*****************************************************************************
//
// Values that can be passed to GPIOPadConfigSet as the ulStrength parameter,
// and returned by GPIOPadConfigGet in the *pulStrength parameter.
//
//*****************************************************************************
#define GPIO_STRENGTH_2MA       0x00000001  // 2mA drive strength
#define GPIO_STRENGTH_4MA       0x00000002  // 4mA drive strength
#define GPIO_STRENGTH_8MA       0x00000004  // 8mA drive strength
#define GPIO_STRENGTH_8MA_SC    0x0000000C  // 8mA drive with slew rate control

//*****************************************************************************
//
// Values that can be passed to GPIOPadConfigSet as the ulPadType parameter,
// and returned by GPIOPadConfigGet in the *pulPadType parameter.
//
//*****************************************************************************
#define GPIO_PIN_TYPE_STD       0x00000008  // Push-pull
#define GPIO_PIN_TYPE_STD_WPU   0x0000000A  // Push-pull with weak pull-up
#define GPIO_PIN_TYPE_STD_WPD   0x0000000C  // Push-pull with weak pull-down
#define GPIO_PIN_TYPE_OD        0x00000009  // Open-drain
#define GPIO_PIN_TYPE_OD_WPU    0x0000000B  // Open-drain with weak pull-up
#define GPIO_PIN_TYPE_OD_WPD    0x0000000D  // Open-drain with weak pull-down
#define GPIO_PIN_TYPE_ANALOG    0x00000000  // Analog comparator

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************
extern void GPIODirModeSet(unsigned long ulPort, unsigned char ucPins,
                           unsigned long ulPinIO);
extern unsigned long GPIODirModeGet(unsigned long ulPort, unsigned char ucPin);
extern void GPIOIntTypeSet(unsigned long ulPort, unsigned char ucPins,
                           unsigned long ulIntType);
extern unsigned long GPIOIntTypeGet(unsigned long ulPort, unsigned char ucPin);
extern void GPIOPadConfigSet(unsigned long ulPort, unsigned char ucPins,
                             unsigned long ulStrength,
                             unsigned long ulPadType);
extern void GPIOPadConfigGet(unsigned long ulPort, unsigned char ucPin,
                             unsigned long *pulStrength,
                             unsigned long *pulPadType);
extern void GPIOPinIntEnable(unsigned long ulPort, unsigned char ucPins);
extern void GPIOPinIntDisable(unsigned long ulPort, unsigned char ucPins);
extern long GPIOPinIntStatus(unsigned long ulPort, tBoolean bMasked);
extern void GPIOPinIntClear(unsigned long ulPort, unsigned char ucPins);
extern void GPIOPortIntRegister(unsigned long ulPort,
                                void (*pfIntHandler)(void));
extern void GPIOPortIntUnregister(unsigned long ulPort);
extern long GPIOPinRead(unsigned long ulPort, unsigned char ucPins);
extern void GPIOPinWrite(unsigned long ulPort, unsigned char ucPins,
                         unsigned char ucVal);
extern void GPIOPinTypeComparator(unsigned long ulPort, unsigned char ucPins);
extern void GPIOPinTypeI2C(unsigned long ulPort, unsigned char ucPins);
extern void GPIOPinTypePWM(unsigned long ulPort, unsigned char ucPins);
extern void GPIOPinTypeSSI(unsigned long ulPort, unsigned char ucPins);
extern void GPIOPinTypeTimer(unsigned long ulPort, unsigned char ucPins);
extern void GPIOPinTypeUART(unsigned long ulPort, unsigned char ucPins);

#ifdef __cplusplus
}
#endif

#endif //  __GPIO_H__
