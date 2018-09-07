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
// lcd_c.h - Driver for the LCD_C Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_LCD_C_H__
#define __MSP430WARE_LCD_C_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_LCD_C__

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
//! \brief Used in the LCD_C_init() function as the initParams parameter.
//
//*****************************************************************************
typedef struct LCD_C_initParam
{
    //! Selects the clock that will be used by the LCD.
    //! \n Valid values are:
    //! - \b LCD_C_CLOCKSOURCE_ACLK [Default]
    //! - \b LCD_C_CLOCKSOURCE_VLOCLK
    uint16_t clockSource;
    //! Selects the divider for LCD_frequency.
    //! \n Valid values are:
    //! - \b LCD_C_CLOCKDIVIDER_1 [Default]
    //! - \b LCD_C_CLOCKDIVIDER_2
    //! - \b LCD_C_CLOCKDIVIDER_3
    //! - \b LCD_C_CLOCKDIVIDER_4
    //! - \b LCD_C_CLOCKDIVIDER_5
    //! - \b LCD_C_CLOCKDIVIDER_6
    //! - \b LCD_C_CLOCKDIVIDER_7
    //! - \b LCD_C_CLOCKDIVIDER_8
    //! - \b LCD_C_CLOCKDIVIDER_9
    //! - \b LCD_C_CLOCKDIVIDER_10
    //! - \b LCD_C_CLOCKDIVIDER_11
    //! - \b LCD_C_CLOCKDIVIDER_12
    //! - \b LCD_C_CLOCKDIVIDER_13
    //! - \b LCD_C_CLOCKDIVIDER_14
    //! - \b LCD_C_CLOCKDIVIDER_15
    //! - \b LCD_C_CLOCKDIVIDER_16
    //! - \b LCD_C_CLOCKDIVIDER_17
    //! - \b LCD_C_CLOCKDIVIDER_18
    //! - \b LCD_C_CLOCKDIVIDER_19
    //! - \b LCD_C_CLOCKDIVIDER_20
    //! - \b LCD_C_CLOCKDIVIDER_21
    //! - \b LCD_C_CLOCKDIVIDER_22
    //! - \b LCD_C_CLOCKDIVIDER_23
    //! - \b LCD_C_CLOCKDIVIDER_24
    //! - \b LCD_C_CLOCKDIVIDER_25
    //! - \b LCD_C_CLOCKDIVIDER_26
    //! - \b LCD_C_CLOCKDIVIDER_27
    //! - \b LCD_C_CLOCKDIVIDER_28
    //! - \b LCD_C_CLOCKDIVIDER_29
    //! - \b LCD_C_CLOCKDIVIDER_30
    //! - \b LCD_C_CLOCKDIVIDER_31
    //! - \b LCD_C_CLOCKDIVIDER_32
    uint16_t clockDivider;
    //! Selects the prescalar for frequency.
    //! \n Valid values are:
    //! - \b LCD_C_CLOCKPRESCALAR_1 [Default]
    //! - \b LCD_C_CLOCKPRESCALAR_2
    //! - \b LCD_C_CLOCKPRESCALAR_4
    //! - \b LCD_C_CLOCKPRESCALAR_8
    //! - \b LCD_C_CLOCKPRESCALAR_16
    //! - \b LCD_C_CLOCKPRESCALAR_32
    uint16_t clockPrescalar;
    //! Selects LCD mux rate.
    //! \n Valid values are:
    //! - \b LCD_C_STATIC [Default]
    //! - \b LCD_C_2_MUX
    //! - \b LCD_C_3_MUX
    //! - \b LCD_C_4_MUX
    //! - \b LCD_C_5_MUX
    //! - \b LCD_C_6_MUX
    //! - \b LCD_C_7_MUX
    //! - \b LCD_C_8_MUX
    uint16_t muxRate;
    //! Selects LCD waveform mode.
    //! \n Valid values are:
    //! - \b LCD_C_STANDARD_WAVEFORMS [Default]
    //! - \b LCD_C_LOW_POWER_WAVEFORMS
    uint16_t waveforms;
    //! Sets LCD segment on/off.
    //! \n Valid values are:
    //! - \b LCD_C_SEGMENTS_DISABLED [Default]
    //! - \b LCD_C_SEGMENTS_ENABLED
    uint16_t segments;
} LCD_C_initParam;

extern const LCD_C_initParam LCD_C_INIT_PARAM;

//*****************************************************************************
//
// The following are values that can be passed to the initParams parameter for
// functions: LCD_C_init().
//
//*****************************************************************************
#define LCD_C_CLOCKSOURCE_ACLK                                            (0x0)
#define LCD_C_CLOCKSOURCE_VLOCLK                                      (LCDSSEL)

//*****************************************************************************
//
// The following are values that can be passed to the initParams parameter for
// functions: LCD_C_init().
//
//*****************************************************************************
#define LCD_C_CLOCKDIVIDER_1                                         (LCDDIV_0)
#define LCD_C_CLOCKDIVIDER_2                                         (LCDDIV_1)
#define LCD_C_CLOCKDIVIDER_3                                         (LCDDIV_2)
#define LCD_C_CLOCKDIVIDER_4                                         (LCDDIV_3)
#define LCD_C_CLOCKDIVIDER_5                                         (LCDDIV_4)
#define LCD_C_CLOCKDIVIDER_6                                         (LCDDIV_5)
#define LCD_C_CLOCKDIVIDER_7                                         (LCDDIV_6)
#define LCD_C_CLOCKDIVIDER_8                                         (LCDDIV_7)
#define LCD_C_CLOCKDIVIDER_9                                         (LCDDIV_8)
#define LCD_C_CLOCKDIVIDER_10                                        (LCDDIV_9)
#define LCD_C_CLOCKDIVIDER_11                                       (LCDDIV_10)
#define LCD_C_CLOCKDIVIDER_12                                       (LCDDIV_11)
#define LCD_C_CLOCKDIVIDER_13                                       (LCDDIV_12)
#define LCD_C_CLOCKDIVIDER_14                                       (LCDDIV_13)
#define LCD_C_CLOCKDIVIDER_15                                       (LCDDIV_14)
#define LCD_C_CLOCKDIVIDER_16                                       (LCDDIV_15)
#define LCD_C_CLOCKDIVIDER_17                                       (LCDDIV_16)
#define LCD_C_CLOCKDIVIDER_18                                       (LCDDIV_17)
#define LCD_C_CLOCKDIVIDER_19                                       (LCDDIV_18)
#define LCD_C_CLOCKDIVIDER_20                                       (LCDDIV_19)
#define LCD_C_CLOCKDIVIDER_21                                       (LCDDIV_20)
#define LCD_C_CLOCKDIVIDER_22                                       (LCDDIV_21)
#define LCD_C_CLOCKDIVIDER_23                                       (LCDDIV_22)
#define LCD_C_CLOCKDIVIDER_24                                       (LCDDIV_23)
#define LCD_C_CLOCKDIVIDER_25                                       (LCDDIV_24)
#define LCD_C_CLOCKDIVIDER_26                                       (LCDDIV_25)
#define LCD_C_CLOCKDIVIDER_27                                       (LCDDIV_26)
#define LCD_C_CLOCKDIVIDER_28                                       (LCDDIV_27)
#define LCD_C_CLOCKDIVIDER_29                                       (LCDDIV_28)
#define LCD_C_CLOCKDIVIDER_30                                       (LCDDIV_29)
#define LCD_C_CLOCKDIVIDER_31                                       (LCDDIV_30)
#define LCD_C_CLOCKDIVIDER_32                                       (LCDDIV_31)

//*****************************************************************************
//
// The following are values that can be passed to the initParams parameter for
// functions: LCD_C_init().
//
//*****************************************************************************
#define LCD_C_CLOCKPRESCALAR_1                                       (LCDPRE_0)
#define LCD_C_CLOCKPRESCALAR_2                                       (LCDPRE_1)
#define LCD_C_CLOCKPRESCALAR_4                                       (LCDPRE_2)
#define LCD_C_CLOCKPRESCALAR_8                                       (LCDPRE_3)
#define LCD_C_CLOCKPRESCALAR_16                                      (LCDPRE_4)
#define LCD_C_CLOCKPRESCALAR_32                                      (LCDPRE_5)

//*****************************************************************************
//
// The following are values that can be passed to the initParams parameter for
// functions: LCD_C_init().
//
//*****************************************************************************
#define LCD_C_STATIC                                                      (0x0)
#define LCD_C_2_MUX                                                    (LCDMX0)
#define LCD_C_3_MUX                                                    (LCDMX1)
#define LCD_C_4_MUX                                           (LCDMX1 | LCDMX0)
#define LCD_C_5_MUX                                                    (LCDMX2)
#define LCD_C_6_MUX                                           (LCDMX2 | LCDMX0)
#define LCD_C_7_MUX                                           (LCDMX2 | LCDMX1)
#define LCD_C_8_MUX                                  (LCDMX2 | LCDMX1 | LCDMX0)

//*****************************************************************************
//
// The following are values that can be passed to the initParams parameter for
// functions: LCD_C_init().
//
//*****************************************************************************
#define LCD_C_STANDARD_WAVEFORMS                                          (0x0)
#define LCD_C_LOW_POWER_WAVEFORMS                                       (LCDLP)

//*****************************************************************************
//
// The following are values that can be passed to the initParams parameter for
// functions: LCD_C_init().
//
//*****************************************************************************
#define LCD_C_SEGMENTS_DISABLED                                           (0x0)
#define LCD_C_SEGMENTS_ENABLED                                         (LCDSON)

//*****************************************************************************
//
// The following are values that can be passed to the mask parameter for
// functions: LCD_C_clearInterrupt(), LCD_C_getInterruptStatus(),
// LCD_C_enableInterrupt(), and LCD_C_disableInterrupt() as well as returned by
// the LCD_C_getInterruptStatus() function.
//
//*****************************************************************************
#define LCD_C_NO_CAPACITANCE_CONNECTED_INTERRUPT                   (LCDNOCAPIE)
#define LCD_C_BLINKING_SEGMENTS_ON_INTERRUPT                       (LCDBLKONIE)
#define LCD_C_BLINKING_SEGMENTS_OFF_INTERRUPT                     (LCDBLKOFFIE)
#define LCD_C_FRAME_INTERRUPT                                        (LCDFRMIE)

//*****************************************************************************
//
// The following are values that can be passed to the displayMemory parameter
// for functions: LCD_C_selectDisplayMemory().
//
//*****************************************************************************
#define LCD_C_DISPLAYSOURCE_MEMORY                                        (0x0)
#define LCD_C_DISPLAYSOURCE_BLINKINGMEMORY                            (LCDDISP)

//*****************************************************************************
//
// The following are values that can be passed to the clockDivider parameter
// for functions: LCD_C_setBlinkingControl().
//
//*****************************************************************************
#define LCD_C_BLINK_FREQ_CLOCK_DIVIDER_1                                  (0x0)
#define LCD_C_BLINK_FREQ_CLOCK_DIVIDER_2                           (LCDBLKDIV0)
#define LCD_C_BLINK_FREQ_CLOCK_DIVIDER_3                           (LCDBLKDIV1)
#define LCD_C_BLINK_FREQ_CLOCK_DIVIDER_4              (LCDBLKDIV0 | LCDBLKDIV1)
#define LCD_C_BLINK_FREQ_CLOCK_DIVIDER_5                           (LCDBLKDIV2)
#define LCD_C_BLINK_FREQ_CLOCK_DIVIDER_6              (LCDBLKDIV2 | LCDBLKDIV0)
#define LCD_C_BLINK_FREQ_CLOCK_DIVIDER_7              (LCDBLKDIV2 | LCDBLKDIV1)
#define LCD_C_BLINK_FREQ_CLOCK_DIVIDER_8 (LCDBLKDIV2 | LCDBLKDIV1 | LCDBLKDIV0)

//*****************************************************************************
//
// The following are values that can be passed to the clockPrescalar parameter
// for functions: LCD_C_setBlinkingControl().
//
//*****************************************************************************
#define LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_512                              (0x0)
#define LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_1024                      (LCDBLKPRE0)
#define LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_2048                      (LCDBLKPRE1)
#define LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_4096         (LCDBLKPRE1 | LCDBLKPRE0)
#define LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_8162                      (LCDBLKPRE2)
#define LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_16384        (LCDBLKPRE2 | LCDBLKPRE0)
#define LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_32768        (LCDBLKPRE2 | LCDBLKPRE1)
#define LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_65536                                \
    (LCDBLKPRE2 | LCDBLKPRE1 | LCDBLKPRE0)

//*****************************************************************************
//
// The following are values that can be passed to the blinkingMode parameter
// for functions: LCD_C_setBlinkingControl().
//
//*****************************************************************************
#define LCD_C_BLINK_MODE_DISABLED                                 (LCDBLKMOD_0)
#define LCD_C_BLINK_MODE_INDIVIDUAL_SEGMENTS                      (LCDBLKMOD_1)
#define LCD_C_BLINK_MODE_ALL_SEGMENTS                             (LCDBLKMOD_2)
#define LCD_C_BLINK_MODE_SWITCHING_BETWEEN_DISPLAY_CONTENTS       (LCDBLKMOD_3)

//*****************************************************************************
//
// The following are values that can be passed to the bias parameter for
// functions: LCD_C_selectBias().
//
//*****************************************************************************
#define LCD_C_BIAS_1_3                                                    (0x0)
#define LCD_C_BIAS_1_2                                                  (LCD2B)

//*****************************************************************************
//
// The following are values that can be passed to the reference parameter for
// functions: LCD_C_selectChargePumpReference().
//
//*****************************************************************************
#define LCD_C_INTERNAL_REFERENCE_VOLTAGE                            (VLCDREF_0)
#define LCD_C_EXTERNAL_REFERENCE_VOLTAGE                            (VLCDREF_1)
#define LCD_C_INTERNAL_REFERENCE_VOLTAGE_SWITCHED_TO_EXTERNAL_PIN   (VLCDREF_2)

//*****************************************************************************
//
// The following are values that can be passed to the vlcdSource parameter for
// functions: LCD_C_setVLCDSource().
//
//*****************************************************************************
#define LCD_C_VLCD_GENERATED_INTERNALLY                                   (0x0)
#define LCD_C_VLCD_SOURCED_EXTERNALLY                                 (VLCDEXT)

//*****************************************************************************
//
// The following are values that can be passed to the v2v3v4Source parameter
// for functions: LCD_C_setVLCDSource().
//
//*****************************************************************************
#define LCD_C_V2V3V4_GENERATED_INTERNALLY_NOT_SWITCHED_TO_PINS            (0x0)
#define LCD_C_V2V3V4_GENERATED_INTERNALLY_SWITCHED_TO_PINS            (LCDREXT)
#define LCD_C_V2V3V4_SOURCED_EXTERNALLY                            (LCDEXTBIAS)

//*****************************************************************************
//
// The following are values that can be passed to the v5Source parameter for
// functions: LCD_C_setVLCDSource().
//
//*****************************************************************************
#define LCD_C_V5_VSS                                                      (0x0)
#define LCD_C_V5_SOURCED_FROM_R03                                      (R03EXT)

//*****************************************************************************
//
// The following are values that can be passed to the voltage parameter for
// functions: LCD_C_setVLCDVoltage().
//
//*****************************************************************************
#define LCD_C_CHARGEPUMP_DISABLED                                         (0x0)
#define LCD_C_CHARGEPUMP_VOLTAGE_2_60V_OR_2_17VREF                      (VLCD0)
#define LCD_C_CHARGEPUMP_VOLTAGE_2_66V_OR_2_22VREF                      (VLCD1)
#define LCD_C_CHARGEPUMP_VOLTAGE_2_72V_OR_2_27VREF              (VLCD1 | VLCD0)
#define LCD_C_CHARGEPUMP_VOLTAGE_2_78V_OR_2_32VREF                      (VLCD2)
#define LCD_C_CHARGEPUMP_VOLTAGE_2_84V_OR_2_37VREF              (VLCD2 | VLCD0)
#define LCD_C_CHARGEPUMP_VOLTAGE_2_90V_OR_2_42VREF              (VLCD2 | VLCD1)
#define LCD_C_CHARGEPUMP_VOLTAGE_2_96V_OR_2_47VREF      (VLCD2 | VLCD1 | VLCD0)
#define LCD_C_CHARGEPUMP_VOLTAGE_3_02V_OR_2_52VREF                      (VLCD3)
#define LCD_C_CHARGEPUMP_VOLTAGE_3_08V_OR_2_57VREF              (VLCD3 | VLCD0)
#define LCD_C_CHARGEPUMP_VOLTAGE_3_14V_OR_2_62VREF              (VLCD3 | VLCD1)
#define LCD_C_CHARGEPUMP_VOLTAGE_3_20V_OR_2_67VREF      (VLCD3 | VLCD1 | VLCD0)
#define LCD_C_CHARGEPUMP_VOLTAGE_3_26V_OR_2_72VREF              (VLCD3 | VLCD2)
#define LCD_C_CHARGEPUMP_VOLTAGE_3_32V_OR_2_77VREF      (VLCD3 | VLCD2 | VLCD0)
#define LCD_C_CHARGEPUMP_VOLTAGE_3_38V_OR_2_82VREF      (VLCD3 | VLCD2 | VLCD1)
#define LCD_C_CHARGEPUMP_VOLTAGE_3_44V_OR_2_87VREF                            \
    (VLCD3 | VLCD2 | VLCD1 | VLCD0)

//*****************************************************************************
//
// The following are values that can be passed to the startPin parameter for
// functions: LCD_C_setPinAsLCDFunctionEx(); the endPin parameter for
// functions: LCD_C_setPinAsLCDFunctionEx(); the pin parameter for functions:
// LCD_C_setPinAsLCDFunction(), LCD_C_setPinAsPortFunction(),
// LCD_C_setMemory(), and LCD_C_setBlinkingMemory().
//
//*****************************************************************************
#define LCD_C_SEGMENT_LINE_0                                                (0)
#define LCD_C_SEGMENT_LINE_1                                                (1)
#define LCD_C_SEGMENT_LINE_2                                                (2)
#define LCD_C_SEGMENT_LINE_3                                                (3)
#define LCD_C_SEGMENT_LINE_4                                                (4)
#define LCD_C_SEGMENT_LINE_5                                                (5)
#define LCD_C_SEGMENT_LINE_6                                                (6)
#define LCD_C_SEGMENT_LINE_7                                                (7)
#define LCD_C_SEGMENT_LINE_8                                                (8)
#define LCD_C_SEGMENT_LINE_9                                                (9)
#define LCD_C_SEGMENT_LINE_10                                              (10)
#define LCD_C_SEGMENT_LINE_11                                              (11)
#define LCD_C_SEGMENT_LINE_12                                              (12)
#define LCD_C_SEGMENT_LINE_13                                              (13)
#define LCD_C_SEGMENT_LINE_14                                              (14)
#define LCD_C_SEGMENT_LINE_15                                              (15)
#define LCD_C_SEGMENT_LINE_16                                              (16)
#define LCD_C_SEGMENT_LINE_17                                              (17)
#define LCD_C_SEGMENT_LINE_18                                              (18)
#define LCD_C_SEGMENT_LINE_19                                              (19)
#define LCD_C_SEGMENT_LINE_20                                              (20)
#define LCD_C_SEGMENT_LINE_21                                              (21)
#define LCD_C_SEGMENT_LINE_22                                              (22)
#define LCD_C_SEGMENT_LINE_23                                              (23)
#define LCD_C_SEGMENT_LINE_24                                              (24)
#define LCD_C_SEGMENT_LINE_25                                              (25)
#define LCD_C_SEGMENT_LINE_26                                              (26)
#define LCD_C_SEGMENT_LINE_27                                              (27)
#define LCD_C_SEGMENT_LINE_28                                              (28)
#define LCD_C_SEGMENT_LINE_29                                              (29)
#define LCD_C_SEGMENT_LINE_30                                              (30)
#define LCD_C_SEGMENT_LINE_31                                              (31)
#define LCD_C_SEGMENT_LINE_32                                              (32)
#define LCD_C_SEGMENT_LINE_33                                              (33)
#define LCD_C_SEGMENT_LINE_34                                              (34)
#define LCD_C_SEGMENT_LINE_35                                              (35)
#define LCD_C_SEGMENT_LINE_36                                              (36)
#define LCD_C_SEGMENT_LINE_37                                              (37)
#define LCD_C_SEGMENT_LINE_38                                              (38)
#define LCD_C_SEGMENT_LINE_39                                              (39)
#define LCD_C_SEGMENT_LINE_40                                              (40)
#define LCD_C_SEGMENT_LINE_41                                              (41)
#define LCD_C_SEGMENT_LINE_42                                              (42)
#define LCD_C_SEGMENT_LINE_43                                              (43)
#define LCD_C_SEGMENT_LINE_44                                              (44)
#define LCD_C_SEGMENT_LINE_45                                              (45)
#define LCD_C_SEGMENT_LINE_46                                              (46)
#define LCD_C_SEGMENT_LINE_47                                              (47)
#define LCD_C_SEGMENT_LINE_48                                              (48)
#define LCD_C_SEGMENT_LINE_49                                              (49)
#define LCD_C_SEGMENT_LINE_50                                              (50)
#define LCD_C_SEGMENT_LINE_51                                              (51)
#define LCD_C_SEGMENT_LINE_52                                              (52)
#define LCD_C_SEGMENT_LINE_53                                              (53)
#define LCD_C_SEGMENT_LINE_54                                              (54)
#define LCD_C_SEGMENT_LINE_55                                              (55)
#define LCD_C_SEGMENT_LINE_56                                              (56)
#define LCD_C_SEGMENT_LINE_57                                              (57)
#define LCD_C_SEGMENT_LINE_58                                              (58)
#define LCD_C_SEGMENT_LINE_59                                              (59)
#define LCD_C_SEGMENT_LINE_60                                              (60)
#define LCD_C_SEGMENT_LINE_61                                              (61)
#define LCD_C_SEGMENT_LINE_62                                              (62)
#define LCD_C_SEGMENT_LINE_63                                              (63)

//*****************************************************************************
//
// The following are values that can be passed to the syncToClock parameter for
// functions: LCD_C_configChargePump().
//
//*****************************************************************************
#define LCD_C_SYNCHRONIZATION_DISABLED                                    (0x0)
#define LCD_C_SYNCHRONIZATION_ENABLED                            (LCDCPCLKSYNC)

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Initializes the LCD Module.
//!
//! his function initializes the LCD but without turning on. It bascially setup
//! the clock source, clock divider, clock prescalar, mux rate, low-power
//! waveform and segments on/off. After calling this function, user can config
//! charge pump, internal reference voltage and voltage sources.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param initParams is the pointer to LCD_InitParam structure. See the
//!        following parameters for each field.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_init(uint16_t baseAddress,
                       LCD_C_initParam *initParams);

//*****************************************************************************
//
//! \brief Turns on the LCD module.
//!
//! \param baseAddress is the base address of the LCD_C module.
//!
//! Modified bits are \b LCDON of \b LCDCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_on(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Turns off the LCD module.
//!
//! \param baseAddress is the base address of the LCD_C module.
//!
//! Modified bits are \b LCDON of \b LCDCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_off(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Clears the LCD interrupt flags.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param mask is the masked interrupt flag to be cleared.
//!        Valid values are:
//!        - \b LCD_C_NO_CAPACITANCE_CONNECTED_INTERRUPT
//!        - \b LCD_C_BLINKING_SEGMENTS_ON_INTERRUPT
//!        - \b LCD_C_BLINKING_SEGMENTS_OFF_INTERRUPT
//!        - \b LCD_C_FRAME_INTERRUPT
//!        \n Modified bits are \b LCDCAPIFG, \b LCDBLKONIFG, \b LCDBLKOFFIFG
//!        and \b LCDFRMIFG of \b LCDCTL1 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_clearInterrupt(uint16_t baseAddress,
                                 uint16_t mask);

//*****************************************************************************
//
//! \brief Gets the LCD interrupt status.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param mask is the masked interrupt flags.
//!        Valid values are:
//!        - \b LCD_C_NO_CAPACITANCE_CONNECTED_INTERRUPT
//!        - \b LCD_C_BLINKING_SEGMENTS_ON_INTERRUPT
//!        - \b LCD_C_BLINKING_SEGMENTS_OFF_INTERRUPT
//!        - \b LCD_C_FRAME_INTERRUPT
//!
//! \return None
//!         Return Logical OR of any of the following:
//!         - \b LCD_C_NO_CAPACITANCE_CONNECTED_INTERRUPT
//!         - \b LCD_C_BLINKING_SEGMENTS_ON_INTERRUPT
//!         - \b LCD_C_BLINKING_SEGMENTS_OFF_INTERRUPT
//!         - \b LCD_C_FRAME_INTERRUPT
//!         \n indicating the status of the masked interrupts
//
//*****************************************************************************
extern uint16_t LCD_C_getInterruptStatus(uint16_t baseAddress,
                                         uint16_t mask);

//*****************************************************************************
//
//! \brief Enables LCD interrupt sources.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param mask is the interrupts to be enabled.
//!        Valid values are:
//!        - \b LCD_C_NO_CAPACITANCE_CONNECTED_INTERRUPT
//!        - \b LCD_C_BLINKING_SEGMENTS_ON_INTERRUPT
//!        - \b LCD_C_BLINKING_SEGMENTS_OFF_INTERRUPT
//!        - \b LCD_C_FRAME_INTERRUPT
//!        \n Modified bits are \b LCDCAPIE, \b LCDBLKONIE, \b LCDBLKOFFIE and
//!        \b LCDFRMIE of \b LCDCTL1 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_enableInterrupt(uint16_t baseAddress,
                                  uint16_t mask);

//*****************************************************************************
//
//! \brief Disables LCD interrupt sources.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param mask is the interrupts to be disabled.
//!        Valid values are:
//!        - \b LCD_C_NO_CAPACITANCE_CONNECTED_INTERRUPT
//!        - \b LCD_C_BLINKING_SEGMENTS_ON_INTERRUPT
//!        - \b LCD_C_BLINKING_SEGMENTS_OFF_INTERRUPT
//!        - \b LCD_C_FRAME_INTERRUPT
//!        \n Modified bits are \b LCDCAPIE, \b LCDBLKONIE, \b LCDBLKOFFIE and
//!        \b LCDFRMIE of \b LCDCTL1 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_disableInterrupt(uint16_t baseAddress,
                                   uint16_t mask);

//*****************************************************************************
//
//! \brief Clears all LCD memory registers.
//!
//! \param baseAddress is the base address of the LCD_C module.
//!
//! Modified bits are \b LCDCLRM of \b LCDMEMCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_clearMemory(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Clears all LCD blinking memory registers.
//!
//! \param baseAddress is the base address of the LCD_C module.
//!
//! Modified bits are \b LCDCLRBM of \b LCDMEMCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_clearBlinkingMemory(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Selects display memory.
//!
//! This function selects display memory either from memory or blinking memory.
//! Please note if the blinking mode is selected as
//! LCD_BLINKMODE_INDIVIDUALSEGMENTS or LCD_BLINKMODE_ALLSEGMENTS or mux rate
//! >=5, display memory can not be changed. If
//! LCD_BLINKMODE_SWITCHDISPLAYCONTENTS is selected, display memory bit
//! reflects current displayed memory.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param displayMemory is the desired displayed memory.
//!        Valid values are:
//!        - \b LCD_C_DISPLAYSOURCE_MEMORY  [Default]
//!        - \b LCD_C_DISPLAYSOURCE_BLINKINGMEMORY
//!        \n Modified bits are \b LCDDISP of \b LCDMEMCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_selectDisplayMemory(uint16_t baseAddress,
                                      uint16_t displayMemory);

//*****************************************************************************
//
//! \brief Sets the blink settings.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param clockDivider is the clock divider for blinking frequency.
//!        Valid values are:
//!        - \b LCD_C_BLINK_FREQ_CLOCK_DIVIDER_1 [Default]
//!        - \b LCD_C_BLINK_FREQ_CLOCK_DIVIDER_2
//!        - \b LCD_C_BLINK_FREQ_CLOCK_DIVIDER_3
//!        - \b LCD_C_BLINK_FREQ_CLOCK_DIVIDER_4
//!        - \b LCD_C_BLINK_FREQ_CLOCK_DIVIDER_5
//!        - \b LCD_C_BLINK_FREQ_CLOCK_DIVIDER_6
//!        - \b LCD_C_BLINK_FREQ_CLOCK_DIVIDER_7
//!        - \b LCD_C_BLINK_FREQ_CLOCK_DIVIDER_8
//!        \n Modified bits are \b LCDBLKDIVx of \b LCDBLKCTL register.
//! \param clockPrescalar is the clock pre-scalar for blinking frequency.
//!        Valid values are:
//!        - \b LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_512 [Default]
//!        - \b LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_1024
//!        - \b LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_2048
//!        - \b LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_4096
//!        - \b LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_8162
//!        - \b LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_16384
//!        - \b LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_32768
//!        - \b LCD_C_BLINK_FREQ_CLOCK_PRESCALAR_65536
//!        \n Modified bits are \b LCDBLKPREx of \b LCDBLKCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_setBlinkingControl(uint16_t baseAddress,
                                     uint8_t clockDivider,
                                     uint8_t clockPrescalar,
                                     uint8_t mode);

//*****************************************************************************
//
//! \brief Enables the charge pump.
//!
//! \param baseAddress is the base address of the LCD_C module.
//!
//! Modified bits are \b LCDCPEN of \b LCDVCTL register; bits \b LCDON of \b
//! LCDCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_enableChargePump(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Disables the charge pump.
//!
//! \param baseAddress is the base address of the LCD_C module.
//!
//! Modified bits are \b LCDCPEN of \b LCDVCTL register; bits \b LCDON of \b
//! LCDCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_disableChargePump(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Selects the bias level.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param bias is the select for bias level.
//!        Valid values are:
//!        - \b LCD_C_BIAS_1_3 [Default] - 1/3 bias
//!        - \b LCD_C_BIAS_1_2 - 1/2 bias
//!
//! Modified bits are \b LCD2B of \b LCDVCTL register; bits \b LCDON of \b
//! LCDCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_selectBias(uint16_t baseAddress,
                             uint16_t bias);

//*****************************************************************************
//
//! \brief Selects the charge pump reference.
//!
//! The charge pump reference does not support
//! LCD_C_EXTERNAL_REFERENCE_VOLTAGE,
//! LCD_C_INTERNAL_REFERENCE_VOLTAGE_SWITCHED_TO_EXTERNAL_PIN when
//! LCD_C_V2V3V4_SOURCED_EXTERNALLY or
//! LCD_C_V2V3V4_GENERATED_INTERNALLY_SWITCHED_TO_PINS is selected.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param reference is the select for charge pump reference.
//!        Valid values are:
//!        - \b LCD_C_INTERNAL_REFERENCE_VOLTAGE [Default]
//!        - \b LCD_C_EXTERNAL_REFERENCE_VOLTAGE
//!        - \b LCD_C_INTERNAL_REFERENCE_VOLTAGE_SWITCHED_TO_EXTERNAL_PIN
//!
//! Modified bits are \b VLCDREFx of \b LCDVCTL register; bits \b LCDON of \b
//! LCDCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_selectChargePumpReference(uint16_t baseAddress,
                                            uint16_t reference);

//*****************************************************************************
//
//! \brief Sets the voltage source for V2/V3/V4 and V5.
//!
//! The charge pump reference does not support
//! LCD_C_EXTERNAL_REFERENCE_VOLTAGE,
//! LCD_C_INTERNAL_REFERENCE_VOLTAGE_SWITCHED_TO_EXTERNAL_PIN when
//! LCD_C_V2V3V4_SOURCED_EXTERNALLY or
//! LCD_C_V2V3V4_GENERATED_INTERNALLY_SWITCHED_TO_PINS is selected.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param vlcdSource is the V(LCD) source select.
//!        Valid values are:
//!        - \b LCD_C_VLCD_GENERATED_INTERNALLY [Default]
//!        - \b LCD_C_VLCD_SOURCED_EXTERNALLY
//! \param v2v3v4Source is the V2/V3/V4 source select.
//!        Valid values are:
//!        - \b LCD_C_V2V3V4_GENERATED_INTERNALLY_NOT_SWITCHED_TO_PINS
//!           [Default]
//!        - \b LCD_C_V2V3V4_GENERATED_INTERNALLY_SWITCHED_TO_PINS
//!        - \b LCD_C_V2V3V4_SOURCED_EXTERNALLY
//! \param v5Source is the V5 source select.
//!        Valid values are:
//!        - \b LCD_C_V5_VSS [Default]
//!        - \b LCD_C_V5_SOURCED_FROM_R03
//!
//! Modified bits are \b VLCDEXT, \b LCDREXT, \b LCDEXTBIAS and \b R03EXT of \b
//! LCDVCTL register; bits \b LCDON of \b LCDCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_setVLCDSource(uint16_t baseAddress,
                                uint16_t vlcdSource,
                                uint16_t v2v3v4Source,
                                uint16_t v5Source);

//*****************************************************************************
//
//! \brief Selects the charge pump reference.
//!
//! Sets LCD charge pump voltage.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param voltage is the charge pump select.
//!        Valid values are:
//!        - \b LCD_C_CHARGEPUMP_DISABLED [Default]
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_2_60V_OR_2_17VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_2_66V_OR_2_22VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_2_72V_OR_2_27VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_2_78V_OR_2_32VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_2_84V_OR_2_37VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_2_90V_OR_2_42VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_2_96V_OR_2_47VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_3_02V_OR_2_52VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_3_08V_OR_2_57VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_3_14V_OR_2_62VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_3_20V_OR_2_67VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_3_26V_OR_2_72VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_3_32V_OR_2_77VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_3_38V_OR_2_82VREF
//!        - \b LCD_C_CHARGEPUMP_VOLTAGE_3_44V_OR_2_87VREF
//!
//! Modified bits are \b VLCDx of \b LCDVCTL register; bits \b LCDON of \b
//! LCDCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_setVLCDVoltage(uint16_t baseAddress,
                                 uint16_t voltage);

//*****************************************************************************
//
//! \brief Sets the LCD Pin as LCD functions.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param pin is the select pin set as LCD function.
//!        Valid values are:
//!        - \b LCD_C_SEGMENT_LINE_0
//!        - \b LCD_C_SEGMENT_LINE_1
//!        - \b LCD_C_SEGMENT_LINE_2
//!        - \b LCD_C_SEGMENT_LINE_3
//!        - \b LCD_C_SEGMENT_LINE_4
//!        - \b LCD_C_SEGMENT_LINE_5
//!        - \b LCD_C_SEGMENT_LINE_6
//!        - \b LCD_C_SEGMENT_LINE_7
//!        - \b LCD_C_SEGMENT_LINE_8
//!        - \b LCD_C_SEGMENT_LINE_9
//!        - \b LCD_C_SEGMENT_LINE_10
//!        - \b LCD_C_SEGMENT_LINE_11
//!        - \b LCD_C_SEGMENT_LINE_12
//!        - \b LCD_C_SEGMENT_LINE_13
//!        - \b LCD_C_SEGMENT_LINE_14
//!        - \b LCD_C_SEGMENT_LINE_15
//!        - \b LCD_C_SEGMENT_LINE_16
//!        - \b LCD_C_SEGMENT_LINE_17
//!        - \b LCD_C_SEGMENT_LINE_18
//!        - \b LCD_C_SEGMENT_LINE_19
//!        - \b LCD_C_SEGMENT_LINE_20
//!        - \b LCD_C_SEGMENT_LINE_21
//!        - \b LCD_C_SEGMENT_LINE_22
//!        - \b LCD_C_SEGMENT_LINE_23
//!        - \b LCD_C_SEGMENT_LINE_24
//!        - \b LCD_C_SEGMENT_LINE_25
//!        - \b LCD_C_SEGMENT_LINE_26
//!        - \b LCD_C_SEGMENT_LINE_27
//!        - \b LCD_C_SEGMENT_LINE_28
//!        - \b LCD_C_SEGMENT_LINE_29
//!        - \b LCD_C_SEGMENT_LINE_30
//!        - \b LCD_C_SEGMENT_LINE_31
//!        - \b LCD_C_SEGMENT_LINE_32
//!        - \b LCD_C_SEGMENT_LINE_33
//!        - \b LCD_C_SEGMENT_LINE_34
//!        - \b LCD_C_SEGMENT_LINE_35
//!        - \b LCD_C_SEGMENT_LINE_36
//!        - \b LCD_C_SEGMENT_LINE_37
//!        - \b LCD_C_SEGMENT_LINE_38
//!        - \b LCD_C_SEGMENT_LINE_39
//!        - \b LCD_C_SEGMENT_LINE_40
//!        - \b LCD_C_SEGMENT_LINE_41
//!        - \b LCD_C_SEGMENT_LINE_42
//!        - \b LCD_C_SEGMENT_LINE_43
//!        - \b LCD_C_SEGMENT_LINE_44
//!        - \b LCD_C_SEGMENT_LINE_45
//!        - \b LCD_C_SEGMENT_LINE_46
//!        - \b LCD_C_SEGMENT_LINE_47
//!        - \b LCD_C_SEGMENT_LINE_48
//!        - \b LCD_C_SEGMENT_LINE_49
//!        - \b LCD_C_SEGMENT_LINE_50
//!        - \b LCD_C_SEGMENT_LINE_51
//!        - \b LCD_C_SEGMENT_LINE_52
//!        - \b LCD_C_SEGMENT_LINE_53
//!        - \b LCD_C_SEGMENT_LINE_54
//!        - \b LCD_C_SEGMENT_LINE_55
//!        - \b LCD_C_SEGMENT_LINE_56
//!        - \b LCD_C_SEGMENT_LINE_57
//!        - \b LCD_C_SEGMENT_LINE_58
//!        - \b LCD_C_SEGMENT_LINE_59
//!        - \b LCD_C_SEGMENT_LINE_60
//!        - \b LCD_C_SEGMENT_LINE_61
//!        - \b LCD_C_SEGMENT_LINE_62
//!        - \b LCD_C_SEGMENT_LINE_63
//!
//! Modified bits are \b LCDSx of \b LCDPCTLx register; bits \b LCDON of \b
//! LCDCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_setPinAsLCDFunction(uint16_t baseAddress,
                                      uint8_t pin);

//*****************************************************************************
//
//! \brief Sets the LCD Pin as Port functions.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param pin is the select pin set as Port function.
//!        Valid values are:
//!        - \b LCD_C_SEGMENT_LINE_0
//!        - \b LCD_C_SEGMENT_LINE_1
//!        - \b LCD_C_SEGMENT_LINE_2
//!        - \b LCD_C_SEGMENT_LINE_3
//!        - \b LCD_C_SEGMENT_LINE_4
//!        - \b LCD_C_SEGMENT_LINE_5
//!        - \b LCD_C_SEGMENT_LINE_6
//!        - \b LCD_C_SEGMENT_LINE_7
//!        - \b LCD_C_SEGMENT_LINE_8
//!        - \b LCD_C_SEGMENT_LINE_9
//!        - \b LCD_C_SEGMENT_LINE_10
//!        - \b LCD_C_SEGMENT_LINE_11
//!        - \b LCD_C_SEGMENT_LINE_12
//!        - \b LCD_C_SEGMENT_LINE_13
//!        - \b LCD_C_SEGMENT_LINE_14
//!        - \b LCD_C_SEGMENT_LINE_15
//!        - \b LCD_C_SEGMENT_LINE_16
//!        - \b LCD_C_SEGMENT_LINE_17
//!        - \b LCD_C_SEGMENT_LINE_18
//!        - \b LCD_C_SEGMENT_LINE_19
//!        - \b LCD_C_SEGMENT_LINE_20
//!        - \b LCD_C_SEGMENT_LINE_21
//!        - \b LCD_C_SEGMENT_LINE_22
//!        - \b LCD_C_SEGMENT_LINE_23
//!        - \b LCD_C_SEGMENT_LINE_24
//!        - \b LCD_C_SEGMENT_LINE_25
//!        - \b LCD_C_SEGMENT_LINE_26
//!        - \b LCD_C_SEGMENT_LINE_27
//!        - \b LCD_C_SEGMENT_LINE_28
//!        - \b LCD_C_SEGMENT_LINE_29
//!        - \b LCD_C_SEGMENT_LINE_30
//!        - \b LCD_C_SEGMENT_LINE_31
//!        - \b LCD_C_SEGMENT_LINE_32
//!        - \b LCD_C_SEGMENT_LINE_33
//!        - \b LCD_C_SEGMENT_LINE_34
//!        - \b LCD_C_SEGMENT_LINE_35
//!        - \b LCD_C_SEGMENT_LINE_36
//!        - \b LCD_C_SEGMENT_LINE_37
//!        - \b LCD_C_SEGMENT_LINE_38
//!        - \b LCD_C_SEGMENT_LINE_39
//!        - \b LCD_C_SEGMENT_LINE_40
//!        - \b LCD_C_SEGMENT_LINE_41
//!        - \b LCD_C_SEGMENT_LINE_42
//!        - \b LCD_C_SEGMENT_LINE_43
//!        - \b LCD_C_SEGMENT_LINE_44
//!        - \b LCD_C_SEGMENT_LINE_45
//!        - \b LCD_C_SEGMENT_LINE_46
//!        - \b LCD_C_SEGMENT_LINE_47
//!        - \b LCD_C_SEGMENT_LINE_48
//!        - \b LCD_C_SEGMENT_LINE_49
//!        - \b LCD_C_SEGMENT_LINE_50
//!        - \b LCD_C_SEGMENT_LINE_51
//!        - \b LCD_C_SEGMENT_LINE_52
//!        - \b LCD_C_SEGMENT_LINE_53
//!        - \b LCD_C_SEGMENT_LINE_54
//!        - \b LCD_C_SEGMENT_LINE_55
//!        - \b LCD_C_SEGMENT_LINE_56
//!        - \b LCD_C_SEGMENT_LINE_57
//!        - \b LCD_C_SEGMENT_LINE_58
//!        - \b LCD_C_SEGMENT_LINE_59
//!        - \b LCD_C_SEGMENT_LINE_60
//!        - \b LCD_C_SEGMENT_LINE_61
//!        - \b LCD_C_SEGMENT_LINE_62
//!        - \b LCD_C_SEGMENT_LINE_63
//!
//! Modified bits are \b LCDSx of \b LCDPCTLx register; bits \b LCDON of \b
//! LCDCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_setPinAsPortFunction(uint16_t baseAddress,
                                       uint8_t pin);

//*****************************************************************************
//
//! \brief Sets the LCD pins as LCD function pin.
//!
//! This function sets the LCD pins as LCD function pin. Instead of passing the
//! all the possible pins, it just requires the start pin and the end pin.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param startPin is the starting pin to be configed as LCD function pin.
//!        Valid values are:
//!        - \b LCD_C_SEGMENT_LINE_0
//!        - \b LCD_C_SEGMENT_LINE_1
//!        - \b LCD_C_SEGMENT_LINE_2
//!        - \b LCD_C_SEGMENT_LINE_3
//!        - \b LCD_C_SEGMENT_LINE_4
//!        - \b LCD_C_SEGMENT_LINE_5
//!        - \b LCD_C_SEGMENT_LINE_6
//!        - \b LCD_C_SEGMENT_LINE_7
//!        - \b LCD_C_SEGMENT_LINE_8
//!        - \b LCD_C_SEGMENT_LINE_9
//!        - \b LCD_C_SEGMENT_LINE_10
//!        - \b LCD_C_SEGMENT_LINE_11
//!        - \b LCD_C_SEGMENT_LINE_12
//!        - \b LCD_C_SEGMENT_LINE_13
//!        - \b LCD_C_SEGMENT_LINE_14
//!        - \b LCD_C_SEGMENT_LINE_15
//!        - \b LCD_C_SEGMENT_LINE_16
//!        - \b LCD_C_SEGMENT_LINE_17
//!        - \b LCD_C_SEGMENT_LINE_18
//!        - \b LCD_C_SEGMENT_LINE_19
//!        - \b LCD_C_SEGMENT_LINE_20
//!        - \b LCD_C_SEGMENT_LINE_21
//!        - \b LCD_C_SEGMENT_LINE_22
//!        - \b LCD_C_SEGMENT_LINE_23
//!        - \b LCD_C_SEGMENT_LINE_24
//!        - \b LCD_C_SEGMENT_LINE_25
//!        - \b LCD_C_SEGMENT_LINE_26
//!        - \b LCD_C_SEGMENT_LINE_27
//!        - \b LCD_C_SEGMENT_LINE_28
//!        - \b LCD_C_SEGMENT_LINE_29
//!        - \b LCD_C_SEGMENT_LINE_30
//!        - \b LCD_C_SEGMENT_LINE_31
//!        - \b LCD_C_SEGMENT_LINE_32
//!        - \b LCD_C_SEGMENT_LINE_33
//!        - \b LCD_C_SEGMENT_LINE_34
//!        - \b LCD_C_SEGMENT_LINE_35
//!        - \b LCD_C_SEGMENT_LINE_36
//!        - \b LCD_C_SEGMENT_LINE_37
//!        - \b LCD_C_SEGMENT_LINE_38
//!        - \b LCD_C_SEGMENT_LINE_39
//!        - \b LCD_C_SEGMENT_LINE_40
//!        - \b LCD_C_SEGMENT_LINE_41
//!        - \b LCD_C_SEGMENT_LINE_42
//!        - \b LCD_C_SEGMENT_LINE_43
//!        - \b LCD_C_SEGMENT_LINE_44
//!        - \b LCD_C_SEGMENT_LINE_45
//!        - \b LCD_C_SEGMENT_LINE_46
//!        - \b LCD_C_SEGMENT_LINE_47
//!        - \b LCD_C_SEGMENT_LINE_48
//!        - \b LCD_C_SEGMENT_LINE_49
//!        - \b LCD_C_SEGMENT_LINE_50
//!        - \b LCD_C_SEGMENT_LINE_51
//!        - \b LCD_C_SEGMENT_LINE_52
//!        - \b LCD_C_SEGMENT_LINE_53
//!        - \b LCD_C_SEGMENT_LINE_54
//!        - \b LCD_C_SEGMENT_LINE_55
//!        - \b LCD_C_SEGMENT_LINE_56
//!        - \b LCD_C_SEGMENT_LINE_57
//!        - \b LCD_C_SEGMENT_LINE_58
//!        - \b LCD_C_SEGMENT_LINE_59
//!        - \b LCD_C_SEGMENT_LINE_60
//!        - \b LCD_C_SEGMENT_LINE_61
//!        - \b LCD_C_SEGMENT_LINE_62
//!        - \b LCD_C_SEGMENT_LINE_63
//! \param endPin is the ending pin to be configed as LCD function pin.
//!        Valid values are:
//!        - \b LCD_C_SEGMENT_LINE_0
//!        - \b LCD_C_SEGMENT_LINE_1
//!        - \b LCD_C_SEGMENT_LINE_2
//!        - \b LCD_C_SEGMENT_LINE_3
//!        - \b LCD_C_SEGMENT_LINE_4
//!        - \b LCD_C_SEGMENT_LINE_5
//!        - \b LCD_C_SEGMENT_LINE_6
//!        - \b LCD_C_SEGMENT_LINE_7
//!        - \b LCD_C_SEGMENT_LINE_8
//!        - \b LCD_C_SEGMENT_LINE_9
//!        - \b LCD_C_SEGMENT_LINE_10
//!        - \b LCD_C_SEGMENT_LINE_11
//!        - \b LCD_C_SEGMENT_LINE_12
//!        - \b LCD_C_SEGMENT_LINE_13
//!        - \b LCD_C_SEGMENT_LINE_14
//!        - \b LCD_C_SEGMENT_LINE_15
//!        - \b LCD_C_SEGMENT_LINE_16
//!        - \b LCD_C_SEGMENT_LINE_17
//!        - \b LCD_C_SEGMENT_LINE_18
//!        - \b LCD_C_SEGMENT_LINE_19
//!        - \b LCD_C_SEGMENT_LINE_20
//!        - \b LCD_C_SEGMENT_LINE_21
//!        - \b LCD_C_SEGMENT_LINE_22
//!        - \b LCD_C_SEGMENT_LINE_23
//!        - \b LCD_C_SEGMENT_LINE_24
//!        - \b LCD_C_SEGMENT_LINE_25
//!        - \b LCD_C_SEGMENT_LINE_26
//!        - \b LCD_C_SEGMENT_LINE_27
//!        - \b LCD_C_SEGMENT_LINE_28
//!        - \b LCD_C_SEGMENT_LINE_29
//!        - \b LCD_C_SEGMENT_LINE_30
//!        - \b LCD_C_SEGMENT_LINE_31
//!        - \b LCD_C_SEGMENT_LINE_32
//!        - \b LCD_C_SEGMENT_LINE_33
//!        - \b LCD_C_SEGMENT_LINE_34
//!        - \b LCD_C_SEGMENT_LINE_35
//!        - \b LCD_C_SEGMENT_LINE_36
//!        - \b LCD_C_SEGMENT_LINE_37
//!        - \b LCD_C_SEGMENT_LINE_38
//!        - \b LCD_C_SEGMENT_LINE_39
//!        - \b LCD_C_SEGMENT_LINE_40
//!        - \b LCD_C_SEGMENT_LINE_41
//!        - \b LCD_C_SEGMENT_LINE_42
//!        - \b LCD_C_SEGMENT_LINE_43
//!        - \b LCD_C_SEGMENT_LINE_44
//!        - \b LCD_C_SEGMENT_LINE_45
//!        - \b LCD_C_SEGMENT_LINE_46
//!        - \b LCD_C_SEGMENT_LINE_47
//!        - \b LCD_C_SEGMENT_LINE_48
//!        - \b LCD_C_SEGMENT_LINE_49
//!        - \b LCD_C_SEGMENT_LINE_50
//!        - \b LCD_C_SEGMENT_LINE_51
//!        - \b LCD_C_SEGMENT_LINE_52
//!        - \b LCD_C_SEGMENT_LINE_53
//!        - \b LCD_C_SEGMENT_LINE_54
//!        - \b LCD_C_SEGMENT_LINE_55
//!        - \b LCD_C_SEGMENT_LINE_56
//!        - \b LCD_C_SEGMENT_LINE_57
//!        - \b LCD_C_SEGMENT_LINE_58
//!        - \b LCD_C_SEGMENT_LINE_59
//!        - \b LCD_C_SEGMENT_LINE_60
//!        - \b LCD_C_SEGMENT_LINE_61
//!        - \b LCD_C_SEGMENT_LINE_62
//!        - \b LCD_C_SEGMENT_LINE_63
//!
//! Modified bits are \b LCDSx of \b LCDPCTLx register; bits \b LCDON of \b
//! LCDCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_setPinAsLCDFunctionEx(uint16_t baseAddress,
                                        uint8_t startPin,
                                        uint8_t endPin);

//*****************************************************************************
//
//! \brief Sets the LCD memory register.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param pin is the select pin for setting value.
//!        Valid values are:
//!        - \b LCD_C_SEGMENT_LINE_0
//!        - \b LCD_C_SEGMENT_LINE_1
//!        - \b LCD_C_SEGMENT_LINE_2
//!        - \b LCD_C_SEGMENT_LINE_3
//!        - \b LCD_C_SEGMENT_LINE_4
//!        - \b LCD_C_SEGMENT_LINE_5
//!        - \b LCD_C_SEGMENT_LINE_6
//!        - \b LCD_C_SEGMENT_LINE_7
//!        - \b LCD_C_SEGMENT_LINE_8
//!        - \b LCD_C_SEGMENT_LINE_9
//!        - \b LCD_C_SEGMENT_LINE_10
//!        - \b LCD_C_SEGMENT_LINE_11
//!        - \b LCD_C_SEGMENT_LINE_12
//!        - \b LCD_C_SEGMENT_LINE_13
//!        - \b LCD_C_SEGMENT_LINE_14
//!        - \b LCD_C_SEGMENT_LINE_15
//!        - \b LCD_C_SEGMENT_LINE_16
//!        - \b LCD_C_SEGMENT_LINE_17
//!        - \b LCD_C_SEGMENT_LINE_18
//!        - \b LCD_C_SEGMENT_LINE_19
//!        - \b LCD_C_SEGMENT_LINE_20
//!        - \b LCD_C_SEGMENT_LINE_21
//!        - \b LCD_C_SEGMENT_LINE_22
//!        - \b LCD_C_SEGMENT_LINE_23
//!        - \b LCD_C_SEGMENT_LINE_24
//!        - \b LCD_C_SEGMENT_LINE_25
//!        - \b LCD_C_SEGMENT_LINE_26
//!        - \b LCD_C_SEGMENT_LINE_27
//!        - \b LCD_C_SEGMENT_LINE_28
//!        - \b LCD_C_SEGMENT_LINE_29
//!        - \b LCD_C_SEGMENT_LINE_30
//!        - \b LCD_C_SEGMENT_LINE_31
//!        - \b LCD_C_SEGMENT_LINE_32
//!        - \b LCD_C_SEGMENT_LINE_33
//!        - \b LCD_C_SEGMENT_LINE_34
//!        - \b LCD_C_SEGMENT_LINE_35
//!        - \b LCD_C_SEGMENT_LINE_36
//!        - \b LCD_C_SEGMENT_LINE_37
//!        - \b LCD_C_SEGMENT_LINE_38
//!        - \b LCD_C_SEGMENT_LINE_39
//!        - \b LCD_C_SEGMENT_LINE_40
//!        - \b LCD_C_SEGMENT_LINE_41
//!        - \b LCD_C_SEGMENT_LINE_42
//!        - \b LCD_C_SEGMENT_LINE_43
//!        - \b LCD_C_SEGMENT_LINE_44
//!        - \b LCD_C_SEGMENT_LINE_45
//!        - \b LCD_C_SEGMENT_LINE_46
//!        - \b LCD_C_SEGMENT_LINE_47
//!        - \b LCD_C_SEGMENT_LINE_48
//!        - \b LCD_C_SEGMENT_LINE_49
//!        - \b LCD_C_SEGMENT_LINE_50
//!        - \b LCD_C_SEGMENT_LINE_51
//!        - \b LCD_C_SEGMENT_LINE_52
//!        - \b LCD_C_SEGMENT_LINE_53
//!        - \b LCD_C_SEGMENT_LINE_54
//!        - \b LCD_C_SEGMENT_LINE_55
//!        - \b LCD_C_SEGMENT_LINE_56
//!        - \b LCD_C_SEGMENT_LINE_57
//!        - \b LCD_C_SEGMENT_LINE_58
//!        - \b LCD_C_SEGMENT_LINE_59
//!        - \b LCD_C_SEGMENT_LINE_60
//!        - \b LCD_C_SEGMENT_LINE_61
//!        - \b LCD_C_SEGMENT_LINE_62
//!        - \b LCD_C_SEGMENT_LINE_63
//! \param value is the designated value for corresponding pin.
//!
//! Modified bits are \b MBITx of \b LCDMx register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_setMemory(uint16_t baseAddress,
                            uint8_t pin,
                            uint8_t value);

//*****************************************************************************
//
//! \brief Sets the LCD blink memory register.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param pin is the select pin for setting value.
//!        Valid values are:
//!        - \b LCD_C_SEGMENT_LINE_0
//!        - \b LCD_C_SEGMENT_LINE_1
//!        - \b LCD_C_SEGMENT_LINE_2
//!        - \b LCD_C_SEGMENT_LINE_3
//!        - \b LCD_C_SEGMENT_LINE_4
//!        - \b LCD_C_SEGMENT_LINE_5
//!        - \b LCD_C_SEGMENT_LINE_6
//!        - \b LCD_C_SEGMENT_LINE_7
//!        - \b LCD_C_SEGMENT_LINE_8
//!        - \b LCD_C_SEGMENT_LINE_9
//!        - \b LCD_C_SEGMENT_LINE_10
//!        - \b LCD_C_SEGMENT_LINE_11
//!        - \b LCD_C_SEGMENT_LINE_12
//!        - \b LCD_C_SEGMENT_LINE_13
//!        - \b LCD_C_SEGMENT_LINE_14
//!        - \b LCD_C_SEGMENT_LINE_15
//!        - \b LCD_C_SEGMENT_LINE_16
//!        - \b LCD_C_SEGMENT_LINE_17
//!        - \b LCD_C_SEGMENT_LINE_18
//!        - \b LCD_C_SEGMENT_LINE_19
//!        - \b LCD_C_SEGMENT_LINE_20
//!        - \b LCD_C_SEGMENT_LINE_21
//!        - \b LCD_C_SEGMENT_LINE_22
//!        - \b LCD_C_SEGMENT_LINE_23
//!        - \b LCD_C_SEGMENT_LINE_24
//!        - \b LCD_C_SEGMENT_LINE_25
//!        - \b LCD_C_SEGMENT_LINE_26
//!        - \b LCD_C_SEGMENT_LINE_27
//!        - \b LCD_C_SEGMENT_LINE_28
//!        - \b LCD_C_SEGMENT_LINE_29
//!        - \b LCD_C_SEGMENT_LINE_30
//!        - \b LCD_C_SEGMENT_LINE_31
//!        - \b LCD_C_SEGMENT_LINE_32
//!        - \b LCD_C_SEGMENT_LINE_33
//!        - \b LCD_C_SEGMENT_LINE_34
//!        - \b LCD_C_SEGMENT_LINE_35
//!        - \b LCD_C_SEGMENT_LINE_36
//!        - \b LCD_C_SEGMENT_LINE_37
//!        - \b LCD_C_SEGMENT_LINE_38
//!        - \b LCD_C_SEGMENT_LINE_39
//!        - \b LCD_C_SEGMENT_LINE_40
//!        - \b LCD_C_SEGMENT_LINE_41
//!        - \b LCD_C_SEGMENT_LINE_42
//!        - \b LCD_C_SEGMENT_LINE_43
//!        - \b LCD_C_SEGMENT_LINE_44
//!        - \b LCD_C_SEGMENT_LINE_45
//!        - \b LCD_C_SEGMENT_LINE_46
//!        - \b LCD_C_SEGMENT_LINE_47
//!        - \b LCD_C_SEGMENT_LINE_48
//!        - \b LCD_C_SEGMENT_LINE_49
//!        - \b LCD_C_SEGMENT_LINE_50
//!        - \b LCD_C_SEGMENT_LINE_51
//!        - \b LCD_C_SEGMENT_LINE_52
//!        - \b LCD_C_SEGMENT_LINE_53
//!        - \b LCD_C_SEGMENT_LINE_54
//!        - \b LCD_C_SEGMENT_LINE_55
//!        - \b LCD_C_SEGMENT_LINE_56
//!        - \b LCD_C_SEGMENT_LINE_57
//!        - \b LCD_C_SEGMENT_LINE_58
//!        - \b LCD_C_SEGMENT_LINE_59
//!        - \b LCD_C_SEGMENT_LINE_60
//!        - \b LCD_C_SEGMENT_LINE_61
//!        - \b LCD_C_SEGMENT_LINE_62
//!        - \b LCD_C_SEGMENT_LINE_63
//! \param value is the designated value for corresponding blink pin.
//!
//! Modified bits are \b MBITx of \b LCDBMx register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_setBlinkingMemory(uint16_t baseAddress,
                                    uint8_t pin,
                                    uint8_t value);

//*****************************************************************************
//
//! \brief Configs the charge pump for synchronization and disabled capability.
//!
//! This function is device-specific. The charge pump clock can be synchronized
//! to a device-specific clock, and also can be disabled by connected function.
//!
//! \param baseAddress is the base address of the LCD_C module.
//! \param syncToClock is the synchronization select.
//!        Valid values are:
//!        - \b LCD_C_SYNCHRONIZATION_DISABLED [Default]
//!        - \b LCD_C_SYNCHRONIZATION_ENABLED
//! \param functionControl is the connected function control select. Setting 0
//!        to make connected function not disable charge pump.
//!
//! Modified bits are \b MBITx of \b LCDBMx register.
//!
//! \return None
//
//*****************************************************************************
extern void LCD_C_configChargePump(uint16_t baseAddress,
                                   uint16_t syncToClock,
                                   uint16_t functionControl);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_LCD_C_H__
