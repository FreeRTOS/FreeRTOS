//*****************************************************************************
//
// rom.h - Macros to facilitate calling functions in the ROM.
//
// Copyright (c) 2007-2008 Luminary Micro, Inc.  All rights reserved.
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

#ifndef __ROM_H__
#define __ROM_H__

//*****************************************************************************
//
// Pointers to the main API tables.
//
//*****************************************************************************
#define ROM_APITABLE            ((unsigned long *)0x01000010)
#define ROM_VERSION             (ROM_APITABLE[0])
#define ROM_UARTTABLE           ((unsigned long *)(ROM_APITABLE[1]))
#define ROM_SSITABLE            ((unsigned long *)(ROM_APITABLE[2]))
#define ROM_I2CTABLE            ((unsigned long *)(ROM_APITABLE[3]))
#define ROM_GPIOTABLE           ((unsigned long *)(ROM_APITABLE[4]))
#define ROM_ADCTABLE            ((unsigned long *)(ROM_APITABLE[5]))
#define ROM_COMPARATORTABLE     ((unsigned long *)(ROM_APITABLE[6]))
#define ROM_FLASHTABLE          ((unsigned long *)(ROM_APITABLE[7]))
#define ROM_PWMTABLE            ((unsigned long *)(ROM_APITABLE[8]))
#define ROM_QEITABLE            ((unsigned long *)(ROM_APITABLE[9]))
#define ROM_SYSTICKTABLE        ((unsigned long *)(ROM_APITABLE[10]))
#define ROM_TIMERTABLE          ((unsigned long *)(ROM_APITABLE[11]))
#define ROM_WATCHDOGTABLE       ((unsigned long *)(ROM_APITABLE[12]))
#define ROM_SYSCTLTABLE         ((unsigned long *)(ROM_APITABLE[13]))
#define ROM_INTERRUPTTABLE      ((unsigned long *)(ROM_APITABLE[14]))

//*****************************************************************************
//
// Macros for calling ROM functions in the ADC API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCSequenceDataGet                                                \
        ((long (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum,                               \
                   unsigned long *pulBuffer))ROM_ADCTABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCIntDisable                                                     \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum))ROM_ADCTABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCIntEnable                                                      \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum))ROM_ADCTABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCIntStatus                                                      \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            unsigned long ulSequenceNum,                      \
                            tBoolean bMasked))ROM_ADCTABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCIntClear                                                       \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum))ROM_ADCTABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCSequenceEnable                                                 \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum))ROM_ADCTABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCSequenceDisable                                                \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum))ROM_ADCTABLE[6])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCSequenceConfigure                                              \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum,                               \
                   unsigned long ulTrigger,                                   \
                   unsigned long ulPriority))ROM_ADCTABLE[7])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCSequenceStepConfigure                                          \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum,                               \
                   unsigned long ulStep,                                      \
                   unsigned long ulConfig))ROM_ADCTABLE[8])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCSequenceOverflow                                               \
        ((long (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum))ROM_ADCTABLE[9])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCSequenceOverflowClear                                          \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum))ROM_ADCTABLE[10])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCSequenceUnderflow                                              \
        ((long (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum))ROM_ADCTABLE[11])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCSequenceUnderflowClear                                         \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum))ROM_ADCTABLE[12])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCProcessorTrigger                                               \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulSequenceNum))ROM_ADCTABLE[13])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ADCHardwareOversampleConfigure                                    \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulFactor))ROM_ADCTABLE[14])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the Comparator API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ComparatorIntClear                                                \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulComp))ROM_COMPARATORTABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ComparatorConfigure                                               \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulComp,                                      \
                   unsigned long ulConfig))ROM_COMPARATORTABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ComparatorRefSet                                                  \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulRef))ROM_COMPARATORTABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ComparatorValueGet                                                \
        ((tBoolean (*)(unsigned long ulBase,                                  \
                       unsigned long ulComp))ROM_COMPARATORTABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ComparatorIntEnable                                               \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulComp))ROM_COMPARATORTABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ComparatorIntDisable                                              \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulComp))ROM_COMPARATORTABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_ComparatorIntStatus                                               \
        ((tBoolean (*)(unsigned long ulBase,                                  \
                       unsigned long ulComp,                                  \
                       tBoolean bMasked))ROM_COMPARATORTABLE[6])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the Flash API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashProgram                                                      \
        ((long (*)(unsigned long *pulData,                                    \
                   unsigned long ulAddress,                                   \
                   unsigned long ulCount))ROM_FLASHTABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashUsecGet                                                      \
        ((unsigned long (*)(void))ROM_FLASHTABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashUsecSet                                                      \
        ((void (*)(unsigned long ulClocks))ROM_FLASHTABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashErase                                                        \
        ((long (*)(unsigned long ulAddress))ROM_FLASHTABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashProtectGet                                                   \
        ((tFlashProtection (*)(unsigned long ulAddress))ROM_FLASHTABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashProtectSet                                                   \
        ((long (*)(unsigned long ulAddress,                                   \
                   tFlashProtection eProtect))ROM_FLASHTABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashProtectSave                                                  \
        ((long (*)(void))ROM_FLASHTABLE[6])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashUserGet                                                      \
        ((long (*)(unsigned long *pulUser0,                                   \
                   unsigned long *pulUser1))ROM_FLASHTABLE[7])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashUserSet                                                      \
        ((long (*)(unsigned long ulUser0,                                     \
                   unsigned long ulUser1))ROM_FLASHTABLE[8])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashUserSave                                                     \
        ((long (*)(void))ROM_FLASHTABLE[9])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashIntEnable                                                    \
        ((void (*)(unsigned long ulIntFlags))ROM_FLASHTABLE[10])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashIntDisable                                                   \
        ((void (*)(unsigned long ulIntFlags))ROM_FLASHTABLE[11])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashIntGetStatus                                                 \
        ((unsigned long (*)(tBoolean bMasked))ROM_FLASHTABLE[12])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_FlashIntClear                                                     \
        ((void (*)(unsigned long ulIntFlags))ROM_FLASHTABLE[13])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the GPIO API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinWrite                                                      \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins,                                      \
                   unsigned char ucVal))ROM_GPIOTABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIODirModeSet                                                    \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins,                                      \
                   unsigned long ulPinIO))ROM_GPIOTABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIODirModeGet                                                    \
        ((unsigned long (*)(unsigned long ulPort,                             \
                            unsigned char ucPin))ROM_GPIOTABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOIntTypeSet                                                    \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins,                                      \
                   unsigned long ulIntType))ROM_GPIOTABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOIntTypeGet                                                    \
        ((unsigned long (*)(unsigned long ulPort,                             \
                            unsigned char ucPin))ROM_GPIOTABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPadConfigSet                                                  \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins,                                      \
                   unsigned long ulStrength,                                  \
                   unsigned long ulPadType))ROM_GPIOTABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPadConfigGet                                                  \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPin,                                       \
                   unsigned long *pulStrength,                                \
                   unsigned long *pulPadType))ROM_GPIOTABLE[6])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinIntEnable                                                  \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[7])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinIntDisable                                                 \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[8])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinIntStatus                                                  \
        ((long (*)(unsigned long ulPort,                                      \
                   tBoolean bMasked))ROM_GPIOTABLE[9])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinIntClear                                                   \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[10])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinRead                                                       \
        ((long (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[11])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinTypeCAN                                                    \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[12])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinTypeComparator                                             \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[13])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinTypeGPIOInput                                              \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[14])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinTypeGPIOOutput                                             \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[15])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinTypeI2C                                                    \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[16])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinTypePWM                                                    \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[17])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinTypeQEI                                                    \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[18])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinTypeSSI                                                    \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[19])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinTypeTimer                                                  \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[20])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinTypeUART                                                   \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[21])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_GPIOPinTypeGPIOOutputOD                                           \
        ((void (*)(unsigned long ulPort,                                      \
                   unsigned char ucPins))ROM_GPIOTABLE[22])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the I2C API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterDataPut                                                  \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned char ucData))ROM_I2CTABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterInitExpClk                                               \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulI2CClk,                                    \
                   tBoolean bFast))ROM_I2CTABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CSlaveInit                                                      \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned char ucSlaveAddr))ROM_I2CTABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterEnable                                                   \
        ((void (*)(unsigned long ulBase))ROM_I2CTABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CSlaveEnable                                                    \
        ((void (*)(unsigned long ulBase))ROM_I2CTABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterDisable                                                  \
        ((void (*)(unsigned long ulBase))ROM_I2CTABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CSlaveDisable                                                   \
        ((void (*)(unsigned long ulBase))ROM_I2CTABLE[6])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterIntEnable                                                \
        ((void (*)(unsigned long ulBase))ROM_I2CTABLE[7])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CSlaveIntEnable                                                 \
        ((void (*)(unsigned long ulBase))ROM_I2CTABLE[8])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterIntDisable                                               \
        ((void (*)(unsigned long ulBase))ROM_I2CTABLE[9])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CSlaveIntDisable                                                \
        ((void (*)(unsigned long ulBase))ROM_I2CTABLE[10])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterIntStatus                                                \
        ((tBoolean (*)(unsigned long ulBase,                                  \
                       tBoolean bMasked))ROM_I2CTABLE[11])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CSlaveIntStatus                                                 \
        ((tBoolean (*)(unsigned long ulBase,                                  \
                       tBoolean bMasked))ROM_I2CTABLE[12])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterIntClear                                                 \
        ((void (*)(unsigned long ulBase))ROM_I2CTABLE[13])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CSlaveIntClear                                                  \
        ((void (*)(unsigned long ulBase))ROM_I2CTABLE[14])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterSlaveAddrSet                                             \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned char ucSlaveAddr,                                 \
                   tBoolean bReceive))ROM_I2CTABLE[15])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterBusy                                                     \
        ((tBoolean (*)(unsigned long ulBase))ROM_I2CTABLE[16])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterBusBusy                                                  \
        ((tBoolean (*)(unsigned long ulBase))ROM_I2CTABLE[17])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterControl                                                  \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulCmd))ROM_I2CTABLE[18])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterErr                                                      \
        ((unsigned long (*)(unsigned long ulBase))ROM_I2CTABLE[19])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CMasterDataGet                                                  \
        ((unsigned long (*)(unsigned long ulBase))ROM_I2CTABLE[20])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CSlaveStatus                                                    \
        ((unsigned long (*)(unsigned long ulBase))ROM_I2CTABLE[21])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CSlaveDataPut                                                   \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned char ucData))ROM_I2CTABLE[22])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_I2CSlaveDataGet                                                   \
        ((unsigned long (*)(unsigned long ulBase))ROM_I2CTABLE[23])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UpdateI2C                                                         \
        ((void (*)(void))ROM_I2CTABLE[24])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the Interrupt API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_IntEnable                                                         \
        ((void (*)(unsigned long ulInterrupt))ROM_INTERRUPTTABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_IntDisable                                                        \
        ((void (*)(unsigned long ulInterrupt))ROM_INTERRUPTTABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_IntPriorityGroupingSet                                            \
        ((void (*)(unsigned long ulBits))ROM_INTERRUPTTABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_IntPriorityGroupingGet                                            \
        ((unsigned long (*)(void))ROM_INTERRUPTTABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_IntPrioritySet                                                    \
        ((void (*)(unsigned long ulInterrupt,                                 \
                   unsigned char ucPriority))ROM_INTERRUPTTABLE[6])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_IntPriorityGet                                                    \
        ((long (*)(unsigned long ulInterrupt))ROM_INTERRUPTTABLE[7])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the PWM API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMPulseWidthSet                                                  \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulPWMOut,                                    \
                   unsigned long ulWidth))ROM_PWMTABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMGenConfigure                                                   \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGen,                                       \
                   unsigned long ulConfig))ROM_PWMTABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMGenPeriodSet                                                   \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGen,                                       \
                   unsigned long ulPeriod))ROM_PWMTABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMGenPeriodGet                                                   \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            unsigned long ulGen))ROM_PWMTABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMGenEnable                                                      \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGen))ROM_PWMTABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMGenDisable                                                     \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGen))ROM_PWMTABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMPulseWidthGet                                                  \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            unsigned long ulPWMOut))ROM_PWMTABLE[6])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMDeadBandEnable                                                 \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGen,                                       \
                   unsigned short usRise,                                     \
                   unsigned short usFall))ROM_PWMTABLE[7])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMDeadBandDisable                                                \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGen))ROM_PWMTABLE[8])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMSyncUpdate                                                     \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGenBits))ROM_PWMTABLE[9])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMSyncTimeBase                                                   \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGenBits))ROM_PWMTABLE[10])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMOutputState                                                    \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulPWMOutBits,                                \
                   tBoolean bEnable))ROM_PWMTABLE[11])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMOutputInvert                                                   \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulPWMOutBits,                                \
                   tBoolean bInvert))ROM_PWMTABLE[12])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMOutputFault                                                    \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulPWMOutBits,                                \
                   tBoolean bFaultSuppress))ROM_PWMTABLE[13])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMGenIntTrigEnable                                               \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGen,                                       \
                   unsigned long ulIntTrig))ROM_PWMTABLE[14])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMGenIntTrigDisable                                              \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGen,                                       \
                   unsigned long ulIntTrig))ROM_PWMTABLE[15])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMGenIntStatus                                                   \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            unsigned long ulGen,                              \
                            tBoolean bMasked))ROM_PWMTABLE[16])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMGenIntClear                                                    \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGen,                                       \
                   unsigned long ulInts))ROM_PWMTABLE[17])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMIntEnable                                                      \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGenFault))ROM_PWMTABLE[18])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMIntDisable                                                     \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulGenFault))ROM_PWMTABLE[19])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMFaultIntClear                                                  \
        ((void (*)(unsigned long ulBase))ROM_PWMTABLE[20])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_PWMIntStatus                                                      \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            tBoolean bMasked))ROM_PWMTABLE[21])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the QEI API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIPositionGet                                                    \
        ((unsigned long (*)(unsigned long ulBase))ROM_QEITABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIEnable                                                         \
        ((void (*)(unsigned long ulBase))ROM_QEITABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIDisable                                                        \
        ((void (*)(unsigned long ulBase))ROM_QEITABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIConfigure                                                      \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulConfig,                                    \
                   unsigned long ulMaxPosition))ROM_QEITABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIPositionSet                                                    \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulPosition))ROM_QEITABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIDirectionGet                                                   \
        ((long (*)(unsigned long ulBase))ROM_QEITABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIErrorGet                                                       \
        ((tBoolean (*)(unsigned long ulBase))ROM_QEITABLE[6])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIVelocityEnable                                                 \
        ((void (*)(unsigned long ulBase))ROM_QEITABLE[7])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIVelocityDisable                                                \
        ((void (*)(unsigned long ulBase))ROM_QEITABLE[8])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIVelocityConfigure                                              \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulPreDiv,                                    \
                   unsigned long ulPeriod))ROM_QEITABLE[9])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIVelocityGet                                                    \
        ((unsigned long (*)(unsigned long ulBase))ROM_QEITABLE[10])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIIntEnable                                                      \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulIntFlags))ROM_QEITABLE[11])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIIntDisable                                                     \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulIntFlags))ROM_QEITABLE[12])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIIntStatus                                                      \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            tBoolean bMasked))ROM_QEITABLE[13])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_QEIIntClear                                                       \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulIntFlags))ROM_QEITABLE[14])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the SSI API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SSIDataPut                                                        \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulData))ROM_SSITABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SSIConfigSetExpClk                                                \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulSSIClk,                                    \
                   unsigned long ulProtocol,                                  \
                   unsigned long ulMode,                                      \
                   unsigned long ulBitRate,                                   \
                   unsigned long ulDataWidth))ROM_SSITABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SSIEnable                                                         \
        ((void (*)(unsigned long ulBase))ROM_SSITABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SSIDisable                                                        \
        ((void (*)(unsigned long ulBase))ROM_SSITABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SSIIntEnable                                                      \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulIntFlags))ROM_SSITABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SSIIntDisable                                                     \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulIntFlags))ROM_SSITABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SSIIntStatus                                                      \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            tBoolean bMasked))ROM_SSITABLE[6])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SSIIntClear                                                       \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulIntFlags))ROM_SSITABLE[7])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SSIDataPutNonBlocking                                             \
        ((long (*)(unsigned long ulBase,                                      \
                   unsigned long ulData))ROM_SSITABLE[8])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SSIDataGet                                                        \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long *pulData))ROM_SSITABLE[9])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SSIDataGetNonBlocking                                             \
        ((long (*)(unsigned long ulBase,                                      \
                   unsigned long *pulData))ROM_SSITABLE[10])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UpdateSSI                                                         \
        ((void (*)(void))ROM_SSITABLE[11])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the SysCtl API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlSleep                                                       \
        ((void (*)(void))ROM_SYSCTLTABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlSRAMSizeGet                                                 \
        ((unsigned long (*)(void))ROM_SYSCTLTABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlFlashSizeGet                                                \
        ((unsigned long (*)(void))ROM_SYSCTLTABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlPinPresent                                                  \
        ((tBoolean (*)(unsigned long ulPin))ROM_SYSCTLTABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlPeripheralPresent                                           \
        ((tBoolean (*)(unsigned long ulPeripheral))ROM_SYSCTLTABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlPeripheralReset                                             \
        ((void (*)(unsigned long ulPeripheral))ROM_SYSCTLTABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlPeripheralEnable                                            \
        ((void (*)(unsigned long ulPeripheral))ROM_SYSCTLTABLE[6])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlPeripheralDisable                                           \
        ((void (*)(unsigned long ulPeripheral))ROM_SYSCTLTABLE[7])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlPeripheralSleepEnable                                       \
        ((void (*)(unsigned long ulPeripheral))ROM_SYSCTLTABLE[8])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlPeripheralSleepDisable                                      \
        ((void (*)(unsigned long ulPeripheral))ROM_SYSCTLTABLE[9])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlPeripheralDeepSleepEnable                                   \
        ((void (*)(unsigned long ulPeripheral))ROM_SYSCTLTABLE[10])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlPeripheralDeepSleepDisable                                  \
        ((void (*)(unsigned long ulPeripheral))ROM_SYSCTLTABLE[11])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlPeripheralClockGating                                       \
        ((void (*)(tBoolean bEnable))ROM_SYSCTLTABLE[12])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlIntEnable                                                   \
        ((void (*)(unsigned long ulInts))ROM_SYSCTLTABLE[13])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlIntDisable                                                  \
        ((void (*)(unsigned long ulInts))ROM_SYSCTLTABLE[14])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlIntClear                                                    \
        ((void (*)(unsigned long ulInts))ROM_SYSCTLTABLE[15])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlIntStatus                                                   \
        ((unsigned long (*)(tBoolean bMasked))ROM_SYSCTLTABLE[16])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlLDOSet                                                      \
        ((void (*)(unsigned long ulVoltage))ROM_SYSCTLTABLE[17])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlLDOGet                                                      \
        ((unsigned long (*)(void))ROM_SYSCTLTABLE[18])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlReset                                                       \
        ((void (*)(void))ROM_SYSCTLTABLE[19])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlDeepSleep                                                   \
        ((void (*)(void))ROM_SYSCTLTABLE[20])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlResetCauseGet                                               \
        ((unsigned long (*)(void))ROM_SYSCTLTABLE[21])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlResetCauseClear                                             \
        ((void (*)(unsigned long ulCauses))ROM_SYSCTLTABLE[22])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlClockSet                                                    \
        ((void (*)(unsigned long ulConfig))ROM_SYSCTLTABLE[23])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlClockGet                                                    \
        ((unsigned long (*)(void))ROM_SYSCTLTABLE[24])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlPWMClockSet                                                 \
        ((void (*)(unsigned long ulConfig))ROM_SYSCTLTABLE[25])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlPWMClockGet                                                 \
        ((unsigned long (*)(void))ROM_SYSCTLTABLE[26])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlADCSpeedSet                                                 \
        ((void (*)(unsigned long ulSpeed))ROM_SYSCTLTABLE[27])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlADCSpeedGet                                                 \
        ((unsigned long (*)(void))ROM_SYSCTLTABLE[28])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlGPIOAHBEnable                                               \
        ((void (*)(unsigned long ulGPIOPeripheral))ROM_SYSCTLTABLE[29])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysCtlGPIOAHBDisable                                              \
        ((void (*)(unsigned long ulGPIOPeripheral))ROM_SYSCTLTABLE[30])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the SysTick API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysTickValueGet                                                   \
        ((unsigned long (*)(void))ROM_SYSTICKTABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysTickEnable                                                     \
        ((void (*)(void))ROM_SYSTICKTABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysTickDisable                                                    \
        ((void (*)(void))ROM_SYSTICKTABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysTickIntEnable                                                  \
        ((void (*)(void))ROM_SYSTICKTABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysTickIntDisable                                                 \
        ((void (*)(void))ROM_SYSTICKTABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysTickPeriodSet                                                  \
        ((void (*)(unsigned long ulPeriod))ROM_SYSTICKTABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_SysTickPeriodGet                                                  \
        ((unsigned long (*)(void))ROM_SYSTICKTABLE[6])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the Timer API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerIntClear                                                     \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulIntFlags))ROM_TIMERTABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerEnable                                                       \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulTimer))ROM_TIMERTABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerDisable                                                      \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulTimer))ROM_TIMERTABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerConfigure                                                    \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulConfig))ROM_TIMERTABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerControlLevel                                                 \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulTimer,                                     \
                   tBoolean bInvert))ROM_TIMERTABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerControlTrigger                                               \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulTimer,                                     \
                   tBoolean bEnable))ROM_TIMERTABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerControlEvent                                                 \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulTimer,                                     \
                   unsigned long ulEvent))ROM_TIMERTABLE[6])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerControlStall                                                 \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulTimer,                                     \
                   tBoolean bStall))ROM_TIMERTABLE[7])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerRTCEnable                                                    \
        ((void (*)(unsigned long ulBase))ROM_TIMERTABLE[8])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerRTCDisable                                                   \
        ((void (*)(unsigned long ulBase))ROM_TIMERTABLE[9])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerPrescaleSet                                                  \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulTimer,                                     \
                   unsigned long ulValue))ROM_TIMERTABLE[10])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerPrescaleGet                                                  \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            unsigned long ulTimer))ROM_TIMERTABLE[11])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerLoadSet                                                      \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulTimer,                                     \
                   unsigned long ulValue))ROM_TIMERTABLE[14])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerLoadGet                                                      \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            unsigned long ulTimer))ROM_TIMERTABLE[15])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerValueGet                                                     \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            unsigned long ulTimer))ROM_TIMERTABLE[16])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerMatchSet                                                     \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulTimer,                                     \
                   unsigned long ulValue))ROM_TIMERTABLE[17])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerMatchGet                                                     \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            unsigned long ulTimer))ROM_TIMERTABLE[18])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerIntEnable                                                    \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulIntFlags))ROM_TIMERTABLE[19])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerIntDisable                                                   \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulIntFlags))ROM_TIMERTABLE[20])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_TimerIntStatus                                                    \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            tBoolean bMasked))ROM_TIMERTABLE[21])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the UART API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTCharPut                                                       \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned char ucData))ROM_UARTTABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTParityModeSet                                                 \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulParity))ROM_UARTTABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTParityModeGet                                                 \
        ((unsigned long (*)(unsigned long ulBase))ROM_UARTTABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTFIFOLevelSet                                                  \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulTxLevel,                                   \
                   unsigned long ulRxLevel))ROM_UARTTABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTFIFOLevelGet                                                  \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long *pulTxLevel,                                 \
                   unsigned long *pulRxLevel))ROM_UARTTABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTConfigSetExpClk                                               \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulUARTClk,                                   \
                   unsigned long ulBaud,                                      \
                   unsigned long ulConfig))ROM_UARTTABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTConfigGetExpClk                                               \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulUARTClk,                                   \
                   unsigned long *pulBaud,                                    \
                   unsigned long *pulConfig))ROM_UARTTABLE[6])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTEnable                                                        \
        ((void (*)(unsigned long ulBase))ROM_UARTTABLE[7])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTDisable                                                       \
        ((void (*)(unsigned long ulBase))ROM_UARTTABLE[8])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTEnableSIR                                                     \
        ((void (*)(unsigned long ulBase,                                      \
                   tBoolean bLowPower))ROM_UARTTABLE[9])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTDisableSIR                                                    \
        ((void (*)(unsigned long ulBase))ROM_UARTTABLE[10])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTCharsAvail                                                    \
        ((tBoolean (*)(unsigned long ulBase))ROM_UARTTABLE[11])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTSpaceAvail                                                    \
        ((tBoolean (*)(unsigned long ulBase))ROM_UARTTABLE[12])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTCharGetNonBlocking                                            \
        ((long (*)(unsigned long ulBase))ROM_UARTTABLE[13])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTCharGet                                                       \
        ((long (*)(unsigned long ulBase))ROM_UARTTABLE[14])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTCharPutNonBlocking                                            \
        ((tBoolean (*)(unsigned long ulBase,                                  \
                       unsigned char ucData))ROM_UARTTABLE[15])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTBreakCtl                                                      \
        ((void (*)(unsigned long ulBase,                                      \
                   tBoolean bBreakState))ROM_UARTTABLE[16])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTIntEnable                                                     \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulIntFlags))ROM_UARTTABLE[17])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTIntDisable                                                    \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulIntFlags))ROM_UARTTABLE[18])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTIntStatus                                                     \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            tBoolean bMasked))ROM_UARTTABLE[19])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UARTIntClear                                                      \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulIntFlags))ROM_UARTTABLE[20])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_UpdateUART                                                        \
        ((void (*)(void))ROM_UARTTABLE[21])
#endif

//*****************************************************************************
//
// Macros for calling ROM functions in the Watchdog API.
//
//*****************************************************************************
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogIntClear                                                  \
        ((void (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[0])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogRunning                                                   \
        ((tBoolean (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[1])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogEnable                                                    \
        ((void (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[2])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogResetEnable                                               \
        ((void (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[3])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogResetDisable                                              \
        ((void (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[4])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogLock                                                      \
        ((void (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[5])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogUnlock                                                    \
        ((void (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[6])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogLockState                                                 \
        ((tBoolean (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[7])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogReloadSet                                                 \
        ((void (*)(unsigned long ulBase,                                      \
                   unsigned long ulLoadVal))ROM_WATCHDOGTABLE[8])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogReloadGet                                                 \
        ((unsigned long (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[9])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogValueGet                                                  \
        ((unsigned long (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[10])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogIntEnable                                                 \
        ((void (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[11])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogIntStatus                                                 \
        ((unsigned long (*)(unsigned long ulBase,                             \
                            tBoolean bMasked))ROM_WATCHDOGTABLE[12])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogStallEnable                                               \
        ((void (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[13])
#endif
#if defined(TARGET_IS_DUSTDEVIL_RA0)
#define ROM_WatchdogStallDisable                                              \
        ((void (*)(unsigned long ulBase))ROM_WATCHDOGTABLE[14])
#endif

#endif // __ROM_H__
