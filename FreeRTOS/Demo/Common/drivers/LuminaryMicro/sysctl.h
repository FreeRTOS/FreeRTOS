//*****************************************************************************
//
// sysctl.h - Prototypes for the system control driver.
//
// Copyright (c) 2005-2008 Luminary Micro, Inc.  All rights reserved.
// 
// Software License Agreement
// 
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
// 
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  You may not combine
// this software with "viral" open-source software in order to form a larger
// program.  Any use in violation of the foregoing restrictions may subject
// the user to criminal sanctions under applicable laws, as well as to civil
// liability for the breach of the terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
// 
// This is part of revision 2523 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __SYSCTL_H__
#define __SYSCTL_H__

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
// The following are values that can be passed to the
// SysCtlPeripheralPresent(), SysCtlPeripheralEnable(),
// SysCtlPeripheralDisable(), and SysCtlPeripheralReset() APIs as the
// ulPeripheral parameter.  The peripherals in the fourth group (upper nibble
// is 3) can only be used with the SysCtlPeripheralPresent() API.
//
//*****************************************************************************
#define SYSCTL_PERIPH_WDOG      0x00000008  // Watchdog
#define SYSCTL_PERIPH_HIBERNATE 0x00000040  // Hibernation module
#define SYSCTL_PERIPH_ADC       0x00100001  // ADC
#define SYSCTL_PERIPH_PWM       0x00100010  // PWM
#define SYSCTL_PERIPH_CAN0      0x00100100  // CAN 0
#define SYSCTL_PERIPH_CAN1      0x00100200  // CAN 1
#define SYSCTL_PERIPH_CAN2      0x00100400  // CAN 2
#define SYSCTL_PERIPH_UART0     0x10000001  // UART 0
#define SYSCTL_PERIPH_UART1     0x10000002  // UART 1
#define SYSCTL_PERIPH_UART2     0x10000004  // UART 2
#ifndef DEPRECATED
#define SYSCTL_PERIPH_SSI       0x10000010  // SSI
#endif
#define SYSCTL_PERIPH_SSI0      0x10000010  // SSI 0
#define SYSCTL_PERIPH_SSI1      0x10000020  // SSI 1
#ifndef DEPRECATED
#define SYSCTL_PERIPH_QEI       0x10000100  // QEI
#endif
#define SYSCTL_PERIPH_QEI0      0x10000100  // QEI 0
#define SYSCTL_PERIPH_QEI1      0x10000200  // QEI 1
#ifndef DEPRECATED
#define SYSCTL_PERIPH_I2C       0x10001000  // I2C
#endif
#define SYSCTL_PERIPH_I2C0      0x10001000  // I2C 0
#define SYSCTL_PERIPH_I2C1      0x10004000  // I2C 1
#define SYSCTL_PERIPH_TIMER0    0x10100001  // Timer 0
#define SYSCTL_PERIPH_TIMER1    0x10100002  // Timer 1
#define SYSCTL_PERIPH_TIMER2    0x10100004  // Timer 2
#define SYSCTL_PERIPH_TIMER3    0x10100008  // Timer 3
#define SYSCTL_PERIPH_COMP0     0x10100100  // Analog comparator 0
#define SYSCTL_PERIPH_COMP1     0x10100200  // Analog comparator 1
#define SYSCTL_PERIPH_COMP2     0x10100400  // Analog comparator 2
#define SYSCTL_PERIPH_GPIOA     0x20000001  // GPIO A
#define SYSCTL_PERIPH_GPIOB     0x20000002  // GPIO B
#define SYSCTL_PERIPH_GPIOC     0x20000004  // GPIO C
#define SYSCTL_PERIPH_GPIOD     0x20000008  // GPIO D
#define SYSCTL_PERIPH_GPIOE     0x20000010  // GPIO E
#define SYSCTL_PERIPH_GPIOF     0x20000020  // GPIO F
#define SYSCTL_PERIPH_GPIOG     0x20000040  // GPIO G
#define SYSCTL_PERIPH_GPIOH     0x20000080  // GPIO H
#define SYSCTL_PERIPH_UDMA      0x20002000  // uDMA
#define SYSCTL_PERIPH_USB0      0x20100001  // USB0
#define SYSCTL_PERIPH_ETH       0x20105000  // ETH
#define SYSCTL_PERIPH_IEEE1588  0x20100100  // IEEE1588
#define SYSCTL_PERIPH_PLL       0x30000010  // PLL
#define SYSCTL_PERIPH_TEMP      0x30000020  // Temperature sensor
#define SYSCTL_PERIPH_MPU       0x30000080  // Cortex-M3 MPU

//*****************************************************************************
//
// The following are values that can be passed to the SysCtlPinPresent() API
// as the ulPin parameter.
//
//*****************************************************************************
#define SYSCTL_PIN_PWM0         0x00000001  // PWM0 pin
#define SYSCTL_PIN_PWM1         0x00000002  // PWM1 pin
#define SYSCTL_PIN_PWM2         0x00000004  // PWM2 pin
#define SYSCTL_PIN_PWM3         0x00000008  // PWM3 pin
#define SYSCTL_PIN_PWM4         0x00000010  // PWM4 pin
#define SYSCTL_PIN_PWM5         0x00000020  // PWM5 pin
#define SYSCTL_PIN_PWM6         0x00000040  // PWM6 pin
#define SYSCTL_PIN_PWM7         0x00000080  // PWM7 pin
#define SYSCTL_PIN_C0MINUS      0x00000040  // C0- pin
#define SYSCTL_PIN_C0PLUS       0x00000080  // C0+ pin
#define SYSCTL_PIN_C0O          0x00000100  // C0o pin
#define SYSCTL_PIN_C1MINUS      0x00000200  // C1- pin
#define SYSCTL_PIN_C1PLUS       0x00000400  // C1+ pin
#define SYSCTL_PIN_C1O          0x00000800  // C1o pin
#define SYSCTL_PIN_C2MINUS      0x00001000  // C2- pin
#define SYSCTL_PIN_C2PLUS       0x00002000  // C2+ pin
#define SYSCTL_PIN_C2O          0x00004000  // C2o pin
#define SYSCTL_PIN_MC_FAULT0    0x00008000  // MC0 Fault pin
#define SYSCTL_PIN_ADC0         0x00010000  // ADC0 pin
#define SYSCTL_PIN_ADC1         0x00020000  // ADC1 pin
#define SYSCTL_PIN_ADC2         0x00040000  // ADC2 pin
#define SYSCTL_PIN_ADC3         0x00080000  // ADC3 pin
#define SYSCTL_PIN_ADC4         0x00100000  // ADC4 pin
#define SYSCTL_PIN_ADC5         0x00200000  // ADC5 pin
#define SYSCTL_PIN_ADC6         0x00400000  // ADC6 pin
#define SYSCTL_PIN_ADC7         0x00800000  // ADC7 pin
#define SYSCTL_PIN_CCP0         0x01000000  // CCP0 pin
#define SYSCTL_PIN_CCP1         0x02000000  // CCP1 pin
#define SYSCTL_PIN_CCP2         0x04000000  // CCP2 pin
#define SYSCTL_PIN_CCP3         0x08000000  // CCP3 pin
#define SYSCTL_PIN_CCP4         0x10000000  // CCP4 pin
#define SYSCTL_PIN_CCP5         0x20000000  // CCP5 pin
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
#define SYSCTL_INT_IOSC_FAIL    0x00000010  // Internal oscillator failure int
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
// The following are values that can be passed to the SysCtlPWMClockSet() API
// as the ulConfig parameter, and can be returned by the SysCtlPWMClockGet()
// API.
//
//*****************************************************************************
#define SYSCTL_PWMDIV_1         0x00000000  // PWM clock is processor clock /1
#define SYSCTL_PWMDIV_2         0x00100000  // PWM clock is processor clock /2
#define SYSCTL_PWMDIV_4         0x00120000  // PWM clock is processor clock /4
#define SYSCTL_PWMDIV_8         0x00140000  // PWM clock is processor clock /8
#define SYSCTL_PWMDIV_16        0x00160000  // PWM clock is processor clock /16
#define SYSCTL_PWMDIV_32        0x00180000  // PWM clock is processor clock /32
#define SYSCTL_PWMDIV_64        0x001A0000  // PWM clock is processor clock /64

//*****************************************************************************
//
// The following are values that can be passed to the SysCtlADCSpeedSet() API
// as the ulSpeed parameter, and can be returned by the SyCtlADCSpeedGet()
// API.
//
//*****************************************************************************
#define SYSCTL_ADCSPEED_1MSPS   0x00000300  // 1,000,000 samples per second
#define SYSCTL_ADCSPEED_500KSPS 0x00000200  // 500,000 samples per second
#define SYSCTL_ADCSPEED_250KSPS 0x00000100  // 250,000 samples per second
#define SYSCTL_ADCSPEED_125KSPS 0x00000000  // 125,000 samples per second

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
#define SYSCTL_SYSDIV_17        0x88400000  // Processor clock is osc/pll /17
#define SYSCTL_SYSDIV_18        0x88C00000  // Processor clock is osc/pll /18
#define SYSCTL_SYSDIV_19        0x89400000  // Processor clock is osc/pll /19
#define SYSCTL_SYSDIV_20        0x89C00000  // Processor clock is osc/pll /20
#define SYSCTL_SYSDIV_21        0x8A400000  // Processor clock is osc/pll /21
#define SYSCTL_SYSDIV_22        0x8AC00000  // Processor clock is osc/pll /22
#define SYSCTL_SYSDIV_23        0x8B400000  // Processor clock is osc/pll /23
#define SYSCTL_SYSDIV_24        0x8BC00000  // Processor clock is osc/pll /24
#define SYSCTL_SYSDIV_25        0x8C400000  // Processor clock is osc/pll /25
#define SYSCTL_SYSDIV_26        0x8CC00000  // Processor clock is osc/pll /26
#define SYSCTL_SYSDIV_27        0x8D400000  // Processor clock is osc/pll /27
#define SYSCTL_SYSDIV_28        0x8DC00000  // Processor clock is osc/pll /28
#define SYSCTL_SYSDIV_29        0x8E400000  // Processor clock is osc/pll /29
#define SYSCTL_SYSDIV_30        0x8EC00000  // Processor clock is osc/pll /30
#define SYSCTL_SYSDIV_31        0x8F400000  // Processor clock is osc/pll /31
#define SYSCTL_SYSDIV_32        0x8FC00000  // Processor clock is osc/pll /32
#define SYSCTL_SYSDIV_33        0x90400000  // Processor clock is osc/pll /33
#define SYSCTL_SYSDIV_34        0x90C00000  // Processor clock is osc/pll /34
#define SYSCTL_SYSDIV_35        0x91400000  // Processor clock is osc/pll /35
#define SYSCTL_SYSDIV_36        0x91C00000  // Processor clock is osc/pll /36
#define SYSCTL_SYSDIV_37        0x92400000  // Processor clock is osc/pll /37
#define SYSCTL_SYSDIV_38        0x92C00000  // Processor clock is osc/pll /38
#define SYSCTL_SYSDIV_39        0x93400000  // Processor clock is osc/pll /39
#define SYSCTL_SYSDIV_40        0x93C00000  // Processor clock is osc/pll /40
#define SYSCTL_SYSDIV_41        0x94400000  // Processor clock is osc/pll /41
#define SYSCTL_SYSDIV_42        0x94C00000  // Processor clock is osc/pll /42
#define SYSCTL_SYSDIV_43        0x95400000  // Processor clock is osc/pll /43
#define SYSCTL_SYSDIV_44        0x95C00000  // Processor clock is osc/pll /44
#define SYSCTL_SYSDIV_45        0x96400000  // Processor clock is osc/pll /45
#define SYSCTL_SYSDIV_46        0x96C00000  // Processor clock is osc/pll /46
#define SYSCTL_SYSDIV_47        0x97400000  // Processor clock is osc/pll /47
#define SYSCTL_SYSDIV_48        0x97C00000  // Processor clock is osc/pll /48
#define SYSCTL_SYSDIV_49        0x98400000  // Processor clock is osc/pll /49
#define SYSCTL_SYSDIV_50        0x98C00000  // Processor clock is osc/pll /50
#define SYSCTL_SYSDIV_51        0x99400000  // Processor clock is osc/pll /51
#define SYSCTL_SYSDIV_52        0x99C00000  // Processor clock is osc/pll /52
#define SYSCTL_SYSDIV_53        0x9A400000  // Processor clock is osc/pll /53
#define SYSCTL_SYSDIV_54        0x9AC00000  // Processor clock is osc/pll /54
#define SYSCTL_SYSDIV_55        0x9B400000  // Processor clock is osc/pll /55
#define SYSCTL_SYSDIV_56        0x9BC00000  // Processor clock is osc/pll /56
#define SYSCTL_SYSDIV_57        0x9C400000  // Processor clock is osc/pll /57
#define SYSCTL_SYSDIV_58        0x9CC00000  // Processor clock is osc/pll /58
#define SYSCTL_SYSDIV_59        0x9D400000  // Processor clock is osc/pll /59
#define SYSCTL_SYSDIV_60        0x9DC00000  // Processor clock is osc/pll /60
#define SYSCTL_SYSDIV_61        0x9E400000  // Processor clock is osc/pll /61
#define SYSCTL_SYSDIV_62        0x9EC00000  // Processor clock is osc/pll /62
#define SYSCTL_SYSDIV_63        0x9F400000  // Processor clock is osc/pll /63
#define SYSCTL_SYSDIV_64        0x9FC00000  // Processor clock is osc/pll /64
#define SYSCTL_USE_PLL          0x00000000  // System clock is the PLL clock
#define SYSCTL_USE_OSC          0x00003800  // System clock is the osc clock
#define SYSCTL_XTAL_1MHZ        0x00000000  // External crystal is 1MHz
#define SYSCTL_XTAL_1_84MHZ     0x00000040  // External crystal is 1.8432MHz
#define SYSCTL_XTAL_2MHZ        0x00000080  // External crystal is 2MHz
#define SYSCTL_XTAL_2_45MHZ     0x000000C0  // External crystal is 2.4576MHz
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
#define SYSCTL_XTAL_10MHZ       0x00000400  // External crystal is 10 MHz
#define SYSCTL_XTAL_12MHZ       0x00000440  // External crystal is 12 MHz
#define SYSCTL_XTAL_12_2MHZ     0x00000480  // External crystal is 12.288 MHz
#define SYSCTL_XTAL_13_5MHZ     0x000004C0  // External crystal is 13.56 MHz
#define SYSCTL_XTAL_14_3MHZ     0x00000500  // External crystal is 14.31818 MHz
#define SYSCTL_XTAL_16MHZ       0x00000540  // External crystal is 16 MHz
#define SYSCTL_XTAL_16_3MHZ     0x00000580  // External crystal is 16.384 MHz
#define SYSCTL_OSC_MAIN         0x00000000  // Oscillator source is main osc
#define SYSCTL_OSC_INT          0x00000010  // Oscillator source is int. osc
#define SYSCTL_OSC_INT4         0x00000020  // Oscillator source is int. osc /4
#define SYSCTL_OSC_INT30        0x80000030  // Oscillator source is int. 30 KHz
#define SYSCTL_OSC_EXT32        0x80000038  // Oscillator source is ext. 32 KHz
#define SYSCTL_INT_OSC_DIS      0x00000002  // Disable internal oscillator
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
extern void SysCtlDelay(unsigned long ulCount);
extern void SysCtlClockSet(unsigned long ulConfig);
extern unsigned long SysCtlClockGet(void);
extern void SysCtlPWMClockSet(unsigned long ulConfig);
extern unsigned long SysCtlPWMClockGet(void);
extern void SysCtlADCSpeedSet(unsigned long ulSpeed);
extern unsigned long SysCtlADCSpeedGet(void);
extern void SysCtlIOSCVerificationSet(tBoolean bEnable);
extern void SysCtlMOSCVerificationSet(tBoolean bEnable);
extern void SysCtlPLLVerificationSet(tBoolean bEnable);
extern void SysCtlClkVerificationClear(void);
extern void SysCtlGPIOAHBEnable(unsigned long ulGPIOPeripheral);
extern void SysCtlGPIOAHBDisable(unsigned long ulGPIOPeripheral);
extern void SysCtlUSBPLLEnable(void);
extern void SysCtlUSBPLLDisable(void);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif // __SYSCTL_H__
