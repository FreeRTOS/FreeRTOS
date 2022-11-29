//*****************************************************************************
//
// sysctl.h - Prototypes for the system control driver.
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
// This is part of revision 523 of the Stellaris Driver Library.
//
//*****************************************************************************

#ifndef __SYSCTL_H__
#define __SYSCTL_H__

#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// The following are values that can be passed to the
// SysCtlPeripheralPresent(), SysCtlPeripheralEnable(),
// SysCtlPeripheralDisable(), and SysCtlPeripheralReset() APIs as the
// ulPeripheral parameter.  The peripherals in the fourth group (upper nibble
// is 3) can only be used with the SysCtlPeripheralPresent() API.
//
//*****************************************************************************
#define SYSCTL_PERIPH_WDOG      0x00000008  // Watchdog
#define SYSCTL_PERIPH_UART0     0x10000001  // UART 0
#define SYSCTL_PERIPH_SSI       0x10000010  // SSI
#define SYSCTL_PERIPH_I2C       0x10001000  // I2C
#define SYSCTL_PERIPH_TIMER0    0x10010000  // Timer 0
#define SYSCTL_PERIPH_TIMER1    0x10020000  // Timer 1
#define SYSCTL_PERIPH_COMP0     0x11000000  // Analog comparator 0
#define SYSCTL_PERIPH_COMP1     0x12000000  // Analog comparator 1
#define SYSCTL_PERIPH_GPIOA     0x20000001  // GPIO A
#define SYSCTL_PERIPH_GPIOB     0x20000002  // GPIO B
#define SYSCTL_PERIPH_GPIOC     0x20000004  // GPIO C
#define SYSCTL_PERIPH_PLL       0x30000010  // PLL

//*****************************************************************************
//
// The following are values that can be passed to the SysCtlPinPresent() API
// as the ulPin parameter.
//
//*****************************************************************************
#define SYSCTL_PIN_C0MINUS      0x00000040  // C0- pin
#define SYSCTL_PIN_C0PLUS       0x00000080  // C0+ pin
#define SYSCTL_PIN_C0O          0x00000100  // C0o pin
#define SYSCTL_PIN_C1MINUS      0x00000200  // C1- pin
#define SYSCTL_PIN_CCP0         0x01000000  // CCP0 pin
#define SYSCTL_PIN_CCP1         0x02000000  // CCP1 pin
#define SYSCTL_PIN_32KHZ        0x80000000  // 32kHz pin

//*****************************************************************************
//
// The following are values that can be passed to the SysCtlLDOSet() API as
// the ulVoltage value, or returned by the SysCtlLDOGet() API.
//
//*****************************************************************************
#define SYSCTL_LDO_2_25V        0x00000005  // LDO output of 2.25V
#define SYSCTL_LDO_2_30V        0x00000004  // LDO output of 2.30V
#define SYSCTL_LDO_2_35V        0x00000003  // LDO output of 2.35V
#define SYSCTL_LDO_2_40V        0x00000002  // LDO output of 2.40V
#define SYSCTL_LDO_2_45V        0x00000001  // LDO output of 2.45V
#define SYSCTL_LDO_2_50V        0x00000000  // LDO output of 2.50V
#define SYSCTL_LDO_2_55V        0x0000001f  // LDO output of 2.55V
#define SYSCTL_LDO_2_60V        0x0000001e  // LDO output of 2.60V
#define SYSCTL_LDO_2_65V        0x0000001d  // LDO output of 2.65V
#define SYSCTL_LDO_2_70V        0x0000001c  // LDO output of 2.70V
#define SYSCTL_LDO_2_75V        0x0000001b  // LDO output of 2.75V

//*****************************************************************************
//
// The following are values that can be passed to the SysCtlLDOConfigSet() API.
//
//*****************************************************************************
#define SYSCTL_LDOCFG_ARST      0x00000001  // Allow LDO failure to reset
#define SYSCTL_LDOCFG_NORST     0x00000000  // Do not reset on LDO failure

//*****************************************************************************
//
// The following are values that can be passed to the SysCtlIntEnable(),
// SysCtlIntDisable(), and SysCtlIntClear() APIs, or returned in the bit mask
// by the SysCtlIntStatus() API.
//
//*****************************************************************************
#define SYSCTL_INT_PLL_LOCK     0x00000040  // PLL lock interrupt
#define SYSCTL_INT_CUR_LIMIT    0x00000020  // Current limit interrupt
#define SYSCTL_INT_BOSC_FAIL    0x00000010  // Boot oscillator failure int
#define SYSCTL_INT_MOSC_FAIL    0x00000008  // Main oscillator failure int
#define SYSCTL_INT_POR          0x00000004  // Power on reset interrupt
#define SYSCTL_INT_BOR          0x00000002  // Brown out interrupt
#define SYSCTL_INT_PLL_FAIL     0x00000001  // PLL failure interrupt

//*****************************************************************************
//
// The following are values that can be passed to the SysCtlResetCauseClear()
// API or returned by the SysCtlResetCauseGet() API.
//
//*****************************************************************************
#define SYSCTL_CAUSE_LDO        0x00000020  // LDO power not OK reset
#define SYSCTL_CAUSE_SW         0x00000010  // Software reset
#define SYSCTL_CAUSE_WDOG       0x00000008  // Watchdog reset
#define SYSCTL_CAUSE_BOR        0x00000004  // Brown-out reset
#define SYSCTL_CAUSE_POR        0x00000002  // Power on reset
#define SYSCTL_CAUSE_EXT        0x00000001  // External reset

//*****************************************************************************
//
// The following are values that can be passed to the SysCtlBrownOutConfigSet()
// API as the ulConfig parameter.
//
//*****************************************************************************
#define SYSCTL_BOR_RESET        0x00000002  // Reset instead of interrupting
#define SYSCTL_BOR_RESAMPLE     0x00000001  // Resample BOR before asserting

//*****************************************************************************
//
// The following are values that can be passed to the SysCtlClockSet() API as
// the ulConfig parameter.
//
//*****************************************************************************
#define SYSCTL_SYSDIV_1         0x07800000  // Processor clock is osc/pll /1
#define SYSCTL_SYSDIV_2         0x00C00000  // Processor clock is osc/pll /2
#define SYSCTL_SYSDIV_3         0x01400000  // Processor clock is osc/pll /3
#define SYSCTL_SYSDIV_4         0x01C00000  // Processor clock is osc/pll /4
#define SYSCTL_SYSDIV_5         0x02400000  // Processor clock is osc/pll /5
#define SYSCTL_SYSDIV_6         0x02C00000  // Processor clock is osc/pll /6
#define SYSCTL_SYSDIV_7         0x03400000  // Processor clock is osc/pll /7
#define SYSCTL_SYSDIV_8         0x03C00000  // Processor clock is osc/pll /8
#define SYSCTL_SYSDIV_9         0x04400000  // Processor clock is osc/pll /9
#define SYSCTL_SYSDIV_10        0x04C00000  // Processor clock is osc/pll /10
#define SYSCTL_SYSDIV_11        0x05400000  // Processor clock is osc/pll /11
#define SYSCTL_SYSDIV_12        0x05C00000  // Processor clock is osc/pll /12
#define SYSCTL_SYSDIV_13        0x06400000  // Processor clock is osc/pll /13
#define SYSCTL_SYSDIV_14        0x06C00000  // Processor clock is osc/pll /14
#define SYSCTL_SYSDIV_15        0x07400000  // Processor clock is osc/pll /15
#define SYSCTL_SYSDIV_16        0x07C00000  // Processor clock is osc/pll /16
#define SYSCTL_USE_PLL          0x00000000  // System clock is the PLL clock
#define SYSCTL_USE_OSC          0x00003800  // System clock is the osc clock
#define SYSCTL_XTAL_3_57MHZ     0x00000100  // External crystal is 3.579545MHz
#define SYSCTL_XTAL_3_68MHZ     0x00000140  // External crystal is 3.6864MHz
#define SYSCTL_XTAL_4MHZ        0x00000180  // External crystal is 4MHz
#define SYSCTL_XTAL_4_09MHZ     0x000001C0  // External crystal is 4.096MHz
#define SYSCTL_XTAL_4_91MHZ     0x00000200  // External crystal is 4.9152MHz
#define SYSCTL_XTAL_5MHZ        0x00000240  // External crystal is 5MHz
#define SYSCTL_XTAL_5_12MHZ     0x00000280  // External crystal is 5.12MHz
#define SYSCTL_XTAL_6MHZ        0x000002C0  // External crystal is 6MHz
#define SYSCTL_XTAL_6_14MHZ     0x00000300  // External crystal is 6.144MHz
#define SYSCTL_XTAL_7_37MHZ     0x00000340  // External crystal is 7.3728MHz
#define SYSCTL_XTAL_8MHZ        0x00000380  // External crystal is 8MHz
#define SYSCTL_XTAL_8_19MHZ     0x000003C0  // External crystal is 8.192MHz
#define SYSCTL_OSC_MAIN         0x00000000  // Oscillator source is main osc
#define SYSCTL_OSC_BOOT         0x00000010  // Oscillator source is boot osc
#define SYSCTL_OSC_BOOT4        0x00000020  // Oscillator source is boot osc /4
#define SYSCTL_BOOT_OSC_DIS     0x00000002  // Disable boot oscillator
#define SYSCTL_MAIN_OSC_DIS     0x00000001  // Disable main oscillator

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************
extern unsigned long SysCtlSRAMSizeGet(void);
extern unsigned long SysCtlFlashSizeGet(void);
extern tBoolean SysCtlPinPresent(unsigned long ulPin);
extern tBoolean SysCtlPeripheralPresent(unsigned long ulPeripheral);
extern void SysCtlPeripheralReset(unsigned long ulPeripheral);
extern void SysCtlPeripheralEnable(unsigned long ulPeripheral);
extern void SysCtlPeripheralDisable(unsigned long ulPeripheral);
extern void SysCtlPeripheralSleepEnable(unsigned long ulPeripheral);
extern void SysCtlPeripheralSleepDisable(unsigned long ulPeripheral);
extern void SysCtlPeripheralDeepSleepEnable(unsigned long ulPeripheral);
extern void SysCtlPeripheralDeepSleepDisable(unsigned long ulPeripheral);
extern void SysCtlPeripheralClockGating(tBoolean bEnable);
extern void SysCtlIntRegister(void (*pfnHandler)(void));
extern void SysCtlIntUnregister(void);
extern void SysCtlIntEnable(unsigned long ulInts);
extern void SysCtlIntDisable(unsigned long ulInts);
extern void SysCtlIntClear(unsigned long ulInts);
extern unsigned long SysCtlIntStatus(tBoolean bMasked);
extern void SysCtlLDOSet(unsigned long ulVoltage);
extern unsigned long SysCtlLDOGet(void);
extern void SysCtlLDOConfigSet(unsigned long ulConfig);
extern void SysCtlReset(void);
extern void SysCtlSleep(void);
extern void SysCtlDeepSleep(void);
extern unsigned long SysCtlResetCauseGet(void);
extern void SysCtlResetCauseClear(unsigned long ulCauses);
extern void SysCtlBrownOutConfigSet(unsigned long ulConfig,
                                    unsigned long ulDelay);
extern void SysCtlClockSet(unsigned long ulConfig);
extern unsigned long SysCtlClockGet(void);
extern void SysCtlBOSCVerificationSet(tBoolean bEnable);
extern void SysCtlMOSCVerificationSet(tBoolean bEnable);
extern void SysCtlPLLVerificationSet(tBoolean bEnable);
extern void SysCtlClkVerificationClear(void);

#ifdef __cplusplus
}
#endif

#endif // __SYSCTL_H__
