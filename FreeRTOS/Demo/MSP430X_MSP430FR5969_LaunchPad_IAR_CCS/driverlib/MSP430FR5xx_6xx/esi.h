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
// esi.h - Driver for the ESI Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_ESI_H__
#define __MSP430WARE_ESI_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_ESI__

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

uint16_t ESI_getCounter0(void);
uint16_t ESI_getCounter1(void);
uint16_t ESI_getCounter2(void);
uint16_t ESI_getOscCounter(void);

//*****************************************************************************
//
//The following are values that can be passed to excitationCircuitSelect
//parameter in ESI_AFE_InitParams
//
//*****************************************************************************
#define ESI_EXCITATION_CIRCUIT_DISABLED 0x0
#define ESI_EXCITATION_CIRCUIT_ENABLED  ESITEN

//*****************************************************************************
//
//The following are values that can be passed to sampleAndHoldSelect
//parameter in ESI_AFE_InitParams
//
//*****************************************************************************
#define ESI_SAMPLE_HOLD_DISABLED 0x0
#define ESI_SAMPLE_HOLD_ENABLED  ESISH

//*****************************************************************************
//
//The following are values that can be passed to midVoltageGeneratorSelect
//parameter in ESI_AFE_InitParams
//
//*****************************************************************************
#define ESI_MID_VOLTAGE_GENERATOR_DISABLED 0x0
#define ESI_MID_VOLTAGE_GENERATOR_ENABLED  ESIVCC2

//*****************************************************************************
//
//The following are values that can be passed to sampleAndHoldVSSConnect
//parameter in ESI_AFE_InitParams
//
//*****************************************************************************
#define ESI_SAMPLE_HOLD_VSS_TO_ESIVSS   0x0
#define ESI_SAMPLE_HOLD_VSS_BY_TSM      ESIVSS

//*****************************************************************************
//
//The following are values that can be passed to
//inputSelectAFE1 parameter in ESI_AFE1_InitParams
//
//*****************************************************************************
#define ESI_AFE1_INPUT_SELECT_CHx        0
#define ESI_AFE1_INPUT_SELECT_CIx        1
#define ESI_AFE1_INPUT_SELECT_CI3        2
#define ESI_AFE1_INPUT_SELECT_CI         3

//*****************************************************************************
//
//The following are values that can be passed to
//inputSelectAFE2 parameter in ESI_AFE2_InitParams
//
//*****************************************************************************
#define ESI_AFE2_INPUT_SELECT_CHx        0
#define ESI_AFE2_INPUT_SELECT_CIx        ESICA2X

//*****************************************************************************
//
//The following are values that can be passed to
//inverterSelectOutputAFE1 parameter in ESI_AFE1_InitParams
//
//*****************************************************************************
#define ESI_INVERTER_FOR_AFE1_DISABLE   0x0
#define ESI_INVERTER_FOR_AFE1_ENABLE    ESICA1INV

//*****************************************************************************
//
//The following are values that can be passed to
//inverterSelectOutputAFE2 parameter in ESI_AFE2_InitParams
//
//*****************************************************************************
#define ESI_INVERTER_FOR_AFE2_DISABLE   0x0
#define ESI_INVERTER_FOR_AFE2_ENABLE    ESICA2INV

//*****************************************************************************
//
//The following are values that can be passed to
//tsmControlOfComparatorAFE2 parameter in ESI_AFE2_InitParams
//
//*****************************************************************************
#define ESI_TSM_COMPARATOR_CONTROL_AFE2_DISABLE    0x0
#define ESI_TSM_COMPARATOR_CONTROL_AFE2_ENABLE     ESICA2EN

//*****************************************************************************
//
//The following are values that can be passed to
//tsmControlDacAFE2 parameter in ESI_AFE2_InitParams
//
//*****************************************************************************
#define ESI_TSM_DAC_CONTROL_AFE2_DISABLE    0x0
#define ESI_TSM_DAC_CONTROL_AFE2_ENABLE     ESIDAC2EN

typedef struct ESI_AFE1_InitParams
{
    uint16_t excitationCircuitSelect;
    uint16_t sampleAndHoldSelect;
    uint16_t midVoltageGeneratorSelect;
    uint16_t sampleAndHoldVSSConnect;
    uint16_t inputSelectAFE1;
    uint16_t inverterSelectOutputAFE1;
} ESI_AFE1_InitParams;

extern const ESI_AFE1_InitParams ESI_AFE1_INITPARAMS_DEFAULT;

void ESI_AFE1_init(ESI_AFE1_InitParams *params);

typedef struct ESI_AFE2_InitParams
{
    uint16_t inputSelectAFE2;
    uint16_t inverterSelectOutputAFE2;
    uint16_t tsmControlComparatorAFE2;
    uint16_t tsmControlDacAFE2;
} ESI_AFE2_InitParams;

extern const ESI_AFE2_InitParams ESI_AFE2_INITPARAMS_DEFAULT;

void ESI_AFE2_init(ESI_AFE2_InitParams *params);

//*****************************************************************************
//
//The following are values that can be passed to
//channelSelect parameter in ESI_getLatchedComparatorOutput
//
//*****************************************************************************
#define ESI_AFE1_CHANNEL0_SELECT            ESIOUT0
#define ESI_AFE1_CHANNEL1_SELECT            ESIOUT1
#define ESI_AFE1_CHANNEL2_SELECT            ESIOUT2
#define ESI_AFE1_CHANNEL3_SELECT            ESIOUT3
#define ESI_AFE2_CHANNEL0_SELECT            ESIOUT4
#define ESI_AFE2_CHANNEL1_SELECT            ESIOUT5
#define ESI_AFE2_CHANNEL2_SELECT            ESIOUT6
#define ESI_AFE2_CHANNEL3_SELECT            ESIOUT7
#define ESI_AFE1_TEST_CHANNEL0_SELECT       ESITCHOUT0
#define ESI_AFE1_TEST_CHANNEL1_SELECT       ESITCHOUT1

//*****************************************************************************
//
//The following are values that are returned by ESI_getLatchedComparatorOutput
//
//*****************************************************************************
#define ESI_AFE_OUTPUT_HIGH   0x1
#define ESI_AFE_OUTPUT_LOW  0x0

uint16_t ESI_getLatchedComparatorOutput(uint16_t channelSelect);

//*****************************************************************************
//
//The following are values that can be passed to
//smclkDivider parameter in ESI_TSM_InitParams
//
//*****************************************************************************
#define ESI_TSM_SMCLK_DIV_1     0x0
#define ESI_TSM_SMCLK_DIV_2     ESIDIV10
#define ESI_TSM_SMCLK_DIV_4     ESIDIV11
#define ESI_TSM_SMCLK_DIV_8     ESIDIV10 + ESIDIV11

//*****************************************************************************
//
//The following are values that can be passed to
//aclkDivider parameter in ESI_TSM_InitParams
//
//*****************************************************************************
#define ESI_TSM_ACLK_DIV_1     0x0
#define ESI_TSM_ACLK_DIV_2     ESIDIV20
#define ESI_TSM_ACLK_DIV_4     ESIDIV21
#define ESI_TSM_ACLK_DIV_8     ESIDIV20 + ESIDIV21

//*****************************************************************************
//
//The following are values that can be passed to
//startTriggerAclkDivider parameter in ESI_TSM_InitParams
//
//*****************************************************************************
#define ESI_TSM_START_TRIGGER_DIV_2     0x0
#define ESI_TSM_START_TRIGGER_DIV_6     ESIDIV3A0
#define ESI_TSM_START_TRIGGER_DIV_10    ESIDIV3A1
#define ESI_TSM_START_TRIGGER_DIV_14    ESIDIV3A0 + ESIDIV3A1
#define ESI_TSM_START_TRIGGER_DIV_18    ESIDIV3A2
#define ESI_TSM_START_TRIGGER_DIV_22    ESIDIV3A2 + ESIDIV3A0
#define ESI_TSM_START_TRIGGER_DIV_26    ESIDIV3A2 + ESIDIV3A1
#define ESI_TSM_START_TRIGGER_DIV_30    ESIDIV3A2 + ESIDIV3A1 + ESIDIV3A0
#define ESI_TSM_START_TRIGGER_DIV_42    ESIDIV3A0 + ESIDIV3A1 + ESIDIV3B0
#define ESI_TSM_START_TRIGGER_DIV_50    ESIDIV3A1 + ESIDIV3B1
#define ESI_TSM_START_TRIGGER_DIV_54    ESIDIV3A2 + ESIDIV3B0
#define ESI_TSM_START_TRIGGER_DIV_66    ESIDIV3A2 + ESIDIV3A0 + ESIDIV3B0
#define ESI_TSM_START_TRIGGER_DIV_70    ESIDIV3A1 + ESIDIV3A0 + ESIDIV3B1
#define ESI_TSM_START_TRIGGER_DIV_78    ESIDIV3A2 + ESIDIV3A1 + ESIDIV3B0
#define ESI_TSM_START_TRIGGER_DIV_90    ESIDIV3A2 + ESIDIV3A1 + ESIDIV3A0 + \
    ESIDIV3B0
#define ESI_TSM_START_TRIGGER_DIV_98    ESIDIV3A0 + ESIDIV3A1 + ESIDIV3B0 + \
    ESIDIV3B1
#define ESI_TSM_START_TRIGGER_DIV_110   ESIDIV3A2 + ESIDIV3A0 + ESIDIV3B1
#define ESI_TSM_START_TRIGGER_DIV_126   ESIDIV3A2 + ESIDIV3B0 + ESIDIV3B1
#define ESI_TSM_START_TRIGGER_DIV_130   ESIDIV3A2 + ESIDIV3A1 + ESIDIV3B1
#define ESI_TSM_START_TRIGGER_DIV_150   ESIDIV3A2 + ESIDIV3A1 + ESIDIV3A0 + \
    ESIDIV3B1
#define ESI_TSM_START_TRIGGER_DIV_154   ESIDIV3A2 + ESIDIV3A0 + ESIDIV3B0 + \
    ESIDIV3B1
#define ESI_TSM_START_TRIGGER_DIV_162   ESIDIV3A2 + ESIDIV3B2
#define ESI_TSM_START_TRIGGER_DIV_182   ESIDIV3A2 + ESIDIV3A1 + ESIDIV3B0 + \
    ESIDIV3B1
#define ESI_TSM_START_TRIGGER_DIV_198   ESIDIV3A2 + ESIDIV3A0 + ESIDIV3B2
#define ESI_TSM_START_TRIGGER_DIV_210   ESIDIV3A2 + ESIDIV3A1 + ESIDIV3A0 + \
    ESIDIV3B0 + ESIDIV3B1
#define ESI_TSM_START_TRIGGER_DIV_234   ESIDIV3A2 + ESIDIV3A1 + ESIDIV3B2
#define ESI_TSM_START_TRIGGER_DIV_242   ESIDIV3A2 + ESIDIV3A0 + ESIDIV3B2 + \
    ESIDIV3B0
#define ESI_TSM_START_TRIGGER_DIV_270   ESIDIV3A2 + ESIDIV3A1 + ESIDIV3A0 + \
    ESIDIV3B2
#define ESI_TSM_START_TRIGGER_DIV_286   ESIDIV3A2 + ESIDIV3A1 + ESIDIV3B2 + \
    ESIDIV3B0
#define ESI_TSM_START_TRIGGER_DIV_330   ESIDIV3A2 + ESIDIV3A1 + ESIDIV3A0 + \
    ESIDIV3B2 + ESIDIV3B0
#define ESI_TSM_START_TRIGGER_DIV_338   ESIDIV3A2 + ESIDIV3A1 + ESIDIV3B2 + \
    ESIDIV3B1
#define ESI_TSM_START_TRIGGER_DIV_390   ESIDIV3A2 + ESIDIV3A1 + ESIDIV3A0 + \
    ESIDIV3B2 + ESIDIV3B1
#define ESI_TSM_START_TRIGGER_DIV_450   ESIDIV3A2 + ESIDIV3A1 + ESIDIV3A0 + \
    ESIDIV3B2 + ESIDIV3B1 + ESIDIV3B0

//*****************************************************************************
//
//The following are values that can be passed to
//repeatMode parameter in ESI_TSM_InitParams
//
//*****************************************************************************
#define ESI_TSM_REPEAT_NEW_TRIGGER          0x0
#define ESI_TSM_REPEAT_END_OF_PREVIOUS_SEQ  ESITSMRP

//*****************************************************************************
//
//The following are values that can be passed to
//startTriggerSelection parameter in ESI_TSM_InitParams
//
//*****************************************************************************
#define ESI_TSM_STOP_SEQUENCE                   0x0
#define ESI_TSM_START_TRIGGER_ACLK              ESITSMTRG0
#define ESI_TSM_START_TRIGGER_SOFTWARE          ESITSMTRG1
#define ESI_TSM_START_TRIGGER_ACLK_OR_SOFTWARE  ESITSMTRG1 + ESITSMTRG0

//*****************************************************************************
//
//The following are values that can be passed to
//tsmFunctionalitySelection parameter in ESI_TSM_InitParams
//
//*****************************************************************************
#define ESI_TSM_HIGH_FREQ_CLK_FUNCTION_ON   0x0
#define ESI_TSM_AUTOZERO_CYCLE_FUNCTION_ON  ESICLKAZSEL

typedef struct ESI_TSM_InitParams
{
    uint16_t smclkDivider;
    uint16_t aclkDivider;
    uint16_t startTriggerAclkDivider;
    uint16_t repeatMode;
    uint16_t startTriggerSelection;
    uint16_t tsmFunctionSelection;
} ESI_TSM_InitParams;

extern const ESI_TSM_InitParams ESI_TSM_INITPARAMS_DEFAULT;

void ESI_TSM_init(ESI_TSM_InitParams *params);

void ESI_TSM_clearTable(void);

void ESI_TSM_copyTable(uint16_t* tsmTable,
                       uint16_t size);

void ESI_TSM_softwareTrigger(void);

uint8_t ESI_TSM_getTSMStateDuration(uint8_t stateRegNum);

void ESI_TSM_setTSMStateDuration(uint8_t stateRegNum,
                                 uint8_t duration);

//*****************************************************************************
//
//The following are values that can be passed to
//Q6Select parameter in ESI_PSM_InitParams
//
//*****************************************************************************
#define ESI_PSM_Q6_DISABLE  0x0
#define ESI_PSM_Q6_ENABLE   ESIQ6EN

//*****************************************************************************
//
//The following are values that can be passed to
//Q7TriggerSelect parameter in ESI_PSM_InitParams
//
//*****************************************************************************
#define ESI_PSM_Q7_TRIGGER_DISABLE  0x0
#define ESI_PSM_Q7_TRIGGER_ENABLE   ESIQ7TRG

//*****************************************************************************
//
//The following are values that can be passed to
//count0Select parameter in ESI_PSM_InitParams
//
//*****************************************************************************
#define ESI_PSM_CNT0_DISABLE 0x0
#define ESI_PSM_CNT0_ENABLE ESICNT0EN

//*****************************************************************************
//
//The following are values that can be passed to
//count0Reset parameter in ESI_PSM_InitParams
//
//*****************************************************************************
#define ESI_PSM_CNT0_NO_RESET 0x0
#define ESI_PSM_CNT0_RESET ESICNT0RST

//*****************************************************************************
//
//The following are values that can be passed to
//count1Select parameter in ESI_PSM_InitParams
//
//*****************************************************************************
#define ESI_PSM_CNT1_DISABLE 0x0
#define ESI_PSM_CNT1_ENABLE ESICNT1EN

//*****************************************************************************
//
//The following are values that can be passed to
//count1Reset parameter in ESI_PSM_InitParams
//
//*****************************************************************************
#define ESI_PSM_CNT1_NO_RESET 0x0
#define ESI_PSM_CNT1_RESET ESICNT1RST

//*****************************************************************************
//
//The following are values that can be passed to
//count2Select parameter in ESI_PSM_InitParams
//
//*****************************************************************************
#define ESI_PSM_CNT2_DISABLE 0x0
#define ESI_PSM_CNT2_ENABLE ESICNT2EN

//*****************************************************************************
//
//The following are values that can be passed to
//count2Reset parameter in ESI_PSM_InitParams
//
//*****************************************************************************
#define ESI_PSM_CNT2_NO_RESET 0x0
#define ESI_PSM_CNT2_RESET ESICNT2RST

//*****************************************************************************
//
//The following are values that can be passed to
//V2Select parameter in ESI_PSM_InitParams
//
//*****************************************************************************
#define ESI_PSM_S3_SELECT   0x0
#define ESI_PSM_Q0_SELECT   ESIV2SEL

//*****************************************************************************
//
//The following are values that can be passed to
//TEST4Select parameter in ESI_PSM_InitParams
//
//*****************************************************************************
#define ESI_PSM_TEST4_IS_Q2         0x0
#define ESI_PSM_TEST4_IS_Q1         ESITEST4SEL0
#define ESI_PSM_TEST4_IS_TSM_CLK    ESITEST4SEL1
#define ESI_PSM_TEST4_IS_AFE1_COMPARATOR   ESITEST4SEL0 + ESITEST4SEL1

typedef struct ESI_PSM_InitParams
{
    uint16_t Q6Select;
    uint16_t Q7TriggerSelect;
    uint16_t count0Select;
    uint16_t count0Reset;
    uint16_t count1Select;
    uint16_t count1Reset;
    uint16_t count2Select;
    uint16_t count2Reset;
    uint16_t V2Select;
    uint16_t TEST4Select;
} ESI_PSM_InitParams;

extern const ESI_PSM_InitParams ESI_PSM_INITPARAMS_DEFAULT;

void ESI_PSM_init(ESI_PSM_InitParams *params);

void ESI_PSM_clearTable(void);
void ESI_PSM_copyTable(uint8_t * psmTable,
                       uint8_t size);

//*****************************************************************************
//
//The following are values that can be passed to
//counterToReset parameter in ESI_PSM_counterReset
//
//*****************************************************************************
#define ESI_PSM_CNT0_RST    ESICNT0RST
#define ESI_PSM_CNT1_RST    ESICNT1RST
#define ESI_PSM_CNT2_RST    ESICNT2RST

void ESI_PSM_resetCounter(uint16_t counterToReset);

//*****************************************************************************
//
//The following are values that can be passed to
//testCycleInsertion parameter in ESI_InitParams
//
//*****************************************************************************
#define ESI_TEST_CYCLE_INSERTION_DISABLE    0x0
#define ESI_TEST_CYCLE_INSERTION_ENABLE     ESITESTD

//*****************************************************************************
//
//The following are values that can be passed to
//timerAInputSelection parameter in ESI_InitParams
//
//*****************************************************************************
#define ESI_TIMERA_INPUT_TSM_COMPOUT    0x0
#define ESI_TIMERA_INPUT_TSM_PPUSRC     ESICS

//*****************************************************************************
//
//The following are values that can be passed to
//testChannel0Select parameter in ESI_InitParams
//
//*****************************************************************************
#define ESI_TEST_CHANNEL0_SOURCE_IS_CH0_CI0 0x0
#define ESI_TEST_CHANNEL0_SOURCE_IS_CH1_CI1 ESITCH00
#define ESI_TEST_CHANNEL0_SOURCE_IS_CH2_CI2 ESITCH01
#define ESI_TEST_CHANNEL0_SOURCE_IS_CH3_CI3 ESITCH00 + ESITCH01

//*****************************************************************************
//
//The following are values that can be passed to
//testChannel1Select parameter in ESI_InitParams
//
//*****************************************************************************
#define ESI_TEST_CHANNEL1_SOURCE_IS_CH0_CI0 0x0
#define ESI_TEST_CHANNEL1_SOURCE_IS_CH1_CI1 ESITCH10
#define ESI_TEST_CHANNEL1_SOURCE_IS_CH2_CI2 ESITCH11
#define ESI_TEST_CHANNEL1_SOURCE_IS_CH3_CI3 ESITCH10 + ESITCH11

//*****************************************************************************
//
//The following are values that can be passed to
//internalOscSelect parameter in ESI_InitParams
//
//*****************************************************************************
#define ESI_INTERNAL_OSC_DISABLE    0x0
#define ESI_INTERNAL_OSC_ENABLE     ESIHFSEL

//*****************************************************************************
//
//The following are values that can be passed to
//sourceNum parameter in ESI_psmSourceSelect
//
//*****************************************************************************
#define PSM_S1_SOURCE   1
#define PSM_S2_SOURCE   2
#define PSM_S3_SOURCE   3

//*****************************************************************************
//
//The following are values that can be passed to
//sourceSelect parameter in ESI_psmSourceSelect
//
//*****************************************************************************
#define ESI_PSM_SOURCE_IS_ESIOUT0    0
#define ESI_PSM_SOURCE_IS_ESIOUT1    1
#define ESI_PSM_SOURCE_IS_ESIOUT2    2
#define ESI_PSM_SOURCE_IS_ESIOUT3    3
#define ESI_PSM_SOURCE_IS_ESIOUT4    4
#define ESI_PSM_SOURCE_IS_ESIOUT5    5
#define ESI_PSM_SOURCE_IS_ESIOUT6    6
#define ESI_PSM_SOURCE_IS_ESIOUT7    7

void ESI_timerAInputSelect(uint16_t select);
void ESI_psmSourceSelect(uint16_t sourceNum,
                         uint16_t sourceSelect);
void ESI_testChannel0SourceSelect(uint16_t sourceSelect);
void ESI_testChannel1SourceSelect(uint16_t sourceSelect);
void ESI_enable(void);
void ESI_disable(void);

void ESI_enableInternalOscillator();
void ESI_disableInternalOscillator();
void ESI_startInternalOscCal(void);
void ESI_stopInternalOscCal(void);

//*****************************************************************************
//
//The following are values that can be passed to
//oversample parameter in ESI_measureESIOSCOversample
//
//*****************************************************************************
#define ESI_ESIOSC_NO_OVERSAMPLE                        0
#define ESI_ESIOSC_OVERSAMPLE_2                         2
#define ESI_ESIOSC_OVERSAMPLE_4                         4
#define ESI_ESIOSC_OVERSAMPLE_8                         8
uint16_t ESI_measureESIOSC(uint8_t oversample);
uint8_t ESI_getESICLKFQ(void);

//*****************************************************************************
//
//The following are values that can be passed to
//incOrDec parameter in ESI_adjustInternalOscFreq
//
//*****************************************************************************
#define ESI_INTERNAL_OSC_FREQ_DECREASE  0x0
#define ESI_INTERNAL_OSC_FREQ_INCREASE  0x1

void ESI_adjustInternalOscFreq(uint16_t incOrDec);
void ESI_setNominalInternalOscFreq(void);
void ESI_calibrateInternalOscFreq(uint16_t targetAclkCounts);
void ESI_setPSMCounter1IncreaseThreshold(uint16_t threshold);

void ESI_setPSMCounter1DecreaseThreshold(uint16_t threshold);

//*****************************************************************************
//
//The following are values that can be passed to
//resultNum parameter in ESI_getConversionResult
//
//*****************************************************************************
#define ESI_CONVERSION_RESULT_1 ESIADMEM1
#define ESI_CONVERSION_RESULT_2 ESIADMEM2
#define ESI_CONVERSION_RESULT_3 ESIADMEM3
#define ESI_CONVERSION_RESULT_4 ESIADMEM4

uint16_t ESI_getConversionResult(uint16_t resultNum);

//*****************************************************************************
//
//The following are values that can be passed to
//dacRegNum parameter in ESI_setAFE1DACValue and ESI_getAFE1DACValue
//
//*****************************************************************************
#define ESI_DAC1_REG0   0
#define ESI_DAC1_REG1   1
#define ESI_DAC1_REG2   2
#define ESI_DAC1_REG3   3
#define ESI_DAC1_REG4   4
#define ESI_DAC1_REG5   5
#define ESI_DAC1_REG6   6
#define ESI_DAC1_REG7   7

void ESI_setAFE1DACValue(uint16_t dacValue,
                         uint8_t dacRegNum);
uint16_t ESI_getAFE1DACValue(uint8_t dacRegNum);

//*****************************************************************************
//
//The following are values that can be passed to
//dacRegNum parameter in ESI_setAFE2DACValue and ESI_getAFE2DACValue
//
//*****************************************************************************
#define ESI_DAC2_REG0   0
#define ESI_DAC2_REG1   1
#define ESI_DAC2_REG2   2
#define ESI_DAC2_REG3   3
#define ESI_DAC2_REG4   4
#define ESI_DAC2_REG5   5
#define ESI_DAC2_REG6   6
#define ESI_DAC2_REG7   7

void ESI_setAFE2DACValue(uint16_t dacValue,
                         uint8_t dacRegNum);
uint16_t ESI_getAFE2DACValue(uint8_t dacRegNum);

//*****************************************************************************
//
//The following are values that can be passed to
//stateRegNum parameter in ESI_setTSMstateReg
//
//*****************************************************************************
#define ESI_TSM_STATE_REG_0 0
#define ESI_TSM_STATE_REG_1 1
#define ESI_TSM_STATE_REG_2 2
#define ESI_TSM_STATE_REG_3 3
#define ESI_TSM_STATE_REG_4 4
#define ESI_TSM_STATE_REG_5 5
#define ESI_TSM_STATE_REG_6 6
#define ESI_TSM_STATE_REG_7 7
#define ESI_TSM_STATE_REG_8 8
#define ESI_TSM_STATE_REG_9 9
#define ESI_TSM_STATE_REG_10 10
#define ESI_TSM_STATE_REG_11 11
#define ESI_TSM_STATE_REG_12 12
#define ESI_TSM_STATE_REG_13 13
#define ESI_TSM_STATE_REG_14 14
#define ESI_TSM_STATE_REG_15 15
#define ESI_TSM_STATE_REG_16 16
#define ESI_TSM_STATE_REG_17 17
#define ESI_TSM_STATE_REG_18 18
#define ESI_TSM_STATE_REG_19 19
#define ESI_TSM_STATE_REG_20 20
#define ESI_TSM_STATE_REG_21 21
#define ESI_TSM_STATE_REG_22 22
#define ESI_TSM_STATE_REG_23 23
#define ESI_TSM_STATE_REG_24 24
#define ESI_TSM_STATE_REG_25 25
#define ESI_TSM_STATE_REG_26 26
#define ESI_TSM_STATE_REG_27 27
#define ESI_TSM_STATE_REG_28 28
#define ESI_TSM_STATE_REG_29 29
#define ESI_TSM_STATE_REG_30 30
#define ESI_TSM_STATE_REG_31 31

//*****************************************************************************
//
//The following are values that can be passed to
//inputChannelSelect parameter in ESI_TSM_StateParams
//
//*****************************************************************************
#define ESI_TSM_STATE_CHANNEL_SELECT_CH0 0
#define ESI_TSM_STATE_CHANNEL_SELECT_CH1 ESICH0
#define ESI_TSM_STATE_CHANNEL_SELECT_CH2 ESICH1
#define ESI_TSM_STATE_CHANNEL_SELECT_CH3 (ESICH1 | ESICH0)

//*****************************************************************************
//
//The following are values that can be passed to
//LCDampingSelect parameter in ESI_TSM_StateParams
//
//*****************************************************************************
#define ESI_TSM_STATE_LC_DAMPING_DISABLE  0x0
#define ESI_TSM_STATE_LC_DAMPING_ENABLE  ESILCEN

//*****************************************************************************
//
//The following are values that can be passed to
//excitationSelect parameter in ESI_TSM_StateParams
//
//*****************************************************************************
#define ESI_TSM_STATE_EXCITATION_DISABLE    0x0
#define ESI_TSM_STATE_EXCITATION_ENABLE     ESIEX

//*****************************************************************************
//
//The following are values that can be passed to
//comparatorSelect parameter in ESI_TSM_StateParams
//
//*****************************************************************************
#define ESI_TSM_STATE_COMPARATOR_DISABLE    0x0
#define ESI_TSM_STATE_COMPARATOR_ENABLE     ESICA

//*****************************************************************************
//
//The following are values that can be passed to
//highFreqClkOn_or_compAutoZeroCycle parameter in ESI_TSM_StateParams
//
//*****************************************************************************
#define ESI_TSM_STATE_HIGH_FREQ_CLK_ON        0x0
#define ESI_TSM_STATE_COMP_AUTOZERO_CYCLE     ESICLKON

//*****************************************************************************
//
//The following are values that can be passed to
//outputLatchSelect parameter in ESI_TSM_StateParams
//
//*****************************************************************************
#define ESI_TSM_STATE_OUTPUT_LATCH_DISABLE  0x0
#define ESI_TSM_STATE_OUTPUT_LATCH_ENABLE   ESIRSON

//*****************************************************************************
//
//The following are values that can be passed to
//testCycleSelect parameter in ESI_TSM_StateParams
//
//*****************************************************************************
#define ESI_TSM_STATE_TEST_CYCLE_DISABLE    0x0
#define ESI_TSM_STATE_TEST_CYCLE_ENABLE     ESITESTS1

//*****************************************************************************
//
//The following are values that can be passed to
//dacSelect parameter in ESI_TSM_StateParams
//
//*****************************************************************************
#define ESI_TSM_STATE_DAC_DISABLE   0x0
#define ESI_TSM_STATE_DAC_ENABLE    ESIDAC

//*****************************************************************************
//
//The following are values that can be passed to
//tsmStop parameter in ESI_TSM_StateParams
//
//*****************************************************************************
#define ESI_TSM_STATE_CONTINUE  0x0
#define ESI_TSM_STATE_STOP      ESISTOP

//*****************************************************************************
//
//The following are values that can be passed to
//tsmClkSrc parameter in ESI_TSM_StateParams
//
//*****************************************************************************
#define ESI_TSM_STATE_HIGH_FREQ_CLK 0x0
#define ESI_TSM_STATE_ACLK          ESICLK

//*****************************************************************************
//
//Values between these min and max can be pased to
//duration parameter in ESI_TSM_StateParams
//
//*****************************************************************************
#define ESI_TSM_STATE_DURATION_MIN  0x00
#define ESI_TSM_STATE_DURATION_MAX  0x1F

typedef struct ESI_TSM_StateParams
{
    uint16_t inputChannelSelect;
    uint16_t LCDampingSelect;
    uint16_t excitationSelect;
    uint16_t comparatorSelect;
    uint16_t highFreqClkOn_or_compAutoZeroCycle;
    uint16_t outputLatchSelect;
    uint16_t testCycleSelect;
    uint16_t dacSelect;
    uint16_t tsmStop;
    uint16_t tsmClkSrc;
    uint16_t duration;
} ESI_TSM_StateParams;

void ESI_setTSMstateReg(ESI_TSM_StateParams *params,
                        uint8_t stateRegNum);

uint16_t ESIgetInterruptVectorRegister(void);

//*****************************************************************************
//
//The following values can be be used to form the interrupt mask for
//ESI_enableInterrupt and ESI_disableInterrupt
//
//*****************************************************************************
#define ESI_INTERRUPT_AFE1_ESIOUTX \
    ESIIE0
#define ESI_INTERRUPT_ESISTOP                                       ESIIE1
#define ESI_INTERRUPT_ESISTART                                      ESIIE2
#define ESI_INTERRUPT_ESICNT1                                       ESIIE3
#define ESI_INTERRUPT_ESICNT2                                       ESIIE4
#define ESI_INTERRUPT_Q6_BIT_SET                                    ESIIE5
#define ESI_INTERRUPT_Q7_BIT_SET                                    ESIIE6
#define ESI_INTERRUPT_ESICNT0_COUNT_INTERVAL                ESIIE7
#define ESI_INTERRUPT_AFE2_ESIOUTX \
    ESIIE8

void ESI_enableInterrupt(uint16_t interruptMask);
void ESI_disableInterrupt(uint16_t interruptMask);

//*****************************************************************************
//
//Return values for ESI_getInterruptStatus
//
//*****************************************************************************
#define ESI_INTERRUPT_FLAG_AFE1_ESIOUTX                             ESIIFG0
#define ESI_INTERRUPT_FLAG_ESISTOP                                      ESIIFG1
#define ESI_INTERRUPT_FLAG_ESISTART                                     ESIIFG2
#define ESI_INTERRUPT_FLAG_ESICNT1                                      ESIIFG3
#define ESI_INTERRUPT_FLAG_ESICNT2                                      ESIIFG4
#define ESI_INTERRUPT_FLAG_Q6_BIT_SET                           ESIIFG5
#define ESI_INTERRUPT_FLAG_Q7_BIT_SET                           ESIIFG6
#define ESI_INTERRUPT_FLAG_ESICNT0_COUNT_INTERVAL               ESIIFG7
#define ESI_INTERRUPT_FLAG_AFE2_ESIOUTX                                 ESIIFG8

uint16_t ESI_getInterruptStatus(uint16_t interruptMask);
void ESI_clearInterrupt(uint16_t interruptMask);

//*****************************************************************************
//
//Values for ifg0Src in ESI_setIFG0Source
//
//*****************************************************************************
#define ESI_IFG0_SET_WHEN_ESIOUT0_SET       ESIIFGSET1_0
#define ESI_IFG0_SET_WHEN_ESIOUT0_RESET     ESIIFGSET1_1
#define ESI_IFG0_SET_WHEN_ESIOUT1_SET       ESIIFGSET1_2
#define ESI_IFG0_SET_WHEN_ESIOUT1_RESET     ESIIFGSET1_3
#define ESI_IFG0_SET_WHEN_ESIOUT2_SET       ESIIFGSET1_4
#define ESI_IFG0_SET_WHEN_ESIOUT2_RESET     ESIIFGSET1_5
#define ESI_IFG0_SET_WHEN_ESIOUT3_SET       ESIIFGSET1_6
#define ESI_IFG0_SET_WHEN_ESIOUT3_RESET     ESIIFGSET1_7

void ESI_setIFG0Source(uint16_t ifg0Src);

//*****************************************************************************
//
//Values for ifg8Src in ESI_setIFG8Source
//
//*****************************************************************************
#define ESI_IFG8_SET_WHEN_ESIOUT4_SET       ESIIFGSET2_0
#define ESI_IFG8_SET_WHEN_ESIOUT4_RESET     ESIIFGSET2_1
#define ESI_IFG8_SET_WHEN_ESIOUT5_SET       ESIIFGSET2_2
#define ESI_IFG8_SET_WHEN_ESIOUT5_RESET     ESIIFGSET2_3
#define ESI_IFG8_SET_WHEN_ESIOUT6_SET       ESIIFGSET2_4
#define ESI_IFG8_SET_WHEN_ESIOUT6_RESET     ESIIFGSET2_5
#define ESI_IFG8_SET_WHEN_ESIOUT7_SET       ESIIFGSET2_6
#define ESI_IFG8_SET_WHEN_ESIOUT7_RESET     ESIIFGSET2_7

void ESI_setIFG8Source(uint16_t ifg8Src);

//*****************************************************************************
//
//Values for ifg7Src in ESI_setIFG7Source
//
//*****************************************************************************
#define ESI_IFG7_SOURCE_EVERY_COUNT_OF_CNT0     ESIIS0_0
#define ESI_IFG7_SOURCE_CNT0_MOD4               ESIIS0_1
#define ESI_IFG7_SOURCE_CNT0_MOD256             ESIIS0_2
#define ESI_IFG7_SOURCE_CNT0_ROLLOVER           ESIIS0_3

void ESI_setIFG7Source(uint16_t ifg7Src);

//*****************************************************************************
//
//Values for ifg4Src in ESI_setIFG4Source
//
//*****************************************************************************
#define ESI_IFG4_SOURCE_EVERY_COUNT_OF_CNT2     ESIIS2_0
#define ESI_IFG4_SOURCE_CNT2_MOD4               ESIIS2_1
#define ESI_IFG4_SOURCE_CNT2_MOD256             ESIIS2_2
#define ESI_IFG4_SOURCE_CNT2_ROLLOVER           ESIIS2_3

void ESI_setIFG4Source(uint16_t ifg4Src);

void ESI_setPSMCounter1UpperThreshold(uint16_t threshold);
void ESI_setPSMCounter1LowerThreshold(uint16_t threshold);

//*****************************************************************************
//
// Set correct DAC values for LC sensors
//
//*****************************************************************************
void ESI_LC_DAC_calibration(uint8_t selected_channel);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif
