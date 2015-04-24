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

//*****************************************************************************
//
//! \addtogroup esi_api
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_ESI__
#include "esi.h"

#include <assert.h>

// Uncomment for finding lower peak of the lower half cycle.
// This required to set ESI comparator output as inverted
#define INVERTED

static uint16_t measureESIOSC(void);
static void FindDAC(uint8_t selected_channel,
                    uint8_t software_trigger);

const ESI_AFE1_InitParams ESI_AFE1_INITPARAMS_DEFAULT =
{ESI_EXCITATION_CIRCUIT_DISABLED,
 ESI_SAMPLE_HOLD_DISABLED,
 ESI_MID_VOLTAGE_GENERATOR_DISABLED,
 ESI_SAMPLE_HOLD_VSS_TO_ESIVSS,
 ESI_INVERTER_FOR_AFE1_DISABLE};

const ESI_AFE2_InitParams ESI_AFE2_INITPARAMS_DEFAULT = {
    ESI_AFE2_INPUT_SELECT_CHx,
    ESI_INVERTER_FOR_AFE2_DISABLE,
    ESI_TSM_COMPARATOR_CONTROL_AFE2_DISABLE,
    ESI_TSM_DAC_CONTROL_AFE2_DISABLE
};

const ESI_TSM_InitParams ESI_TSM_INITPARAMS_DEFAULT = { ESI_TSM_SMCLK_DIV_1,
                                                        ESI_TSM_ACLK_DIV_1,
                                                        ESI_TSM_START_TRIGGER_DIV_2,
                                                        ESI_TSM_REPEAT_NEW_TRIGGER,
                                                        ESI_TSM_STOP_SEQUENCE,
                                                        ESI_TSM_HIGH_FREQ_CLK_FUNCTION_ON};

const ESI_PSM_InitParams ESI_PSM_INITPARAMS_DEFAULT = { ESI_PSM_Q6_DISABLE,
                                                        ESI_PSM_Q7_TRIGGER_DISABLE,
                                                        ESI_PSM_CNT0_DISABLE,
                                                        ESI_PSM_CNT0_RESET,
                                                        ESI_PSM_CNT1_DISABLE,
                                                        ESI_PSM_CNT1_RESET,
                                                        ESI_PSM_CNT2_DISABLE,
                                                        ESI_PSM_CNT2_RESET,
                                                        ESI_PSM_S3_SELECT,
                                                        ESI_PSM_TEST4_IS_Q2,};

//*****************************************************************************
//
//! Get ESI PSM Counter 0 Value
//!
//! This function reads the ESI Counter 0 register
//!
//! \return  Counter value
//
//*****************************************************************************
uint16_t ESI_getCounter0(void)
{
    return (ESICNT0);
}

//*****************************************************************************
//
//! Get ESI PSM Counter 1 Value
//!
//! This function reads the ESI Counter1 register
//!
//! \return Counter value
//
//*****************************************************************************
uint16_t ESI_getCounter1(void)
{
    return (ESICNT1);
}

//*****************************************************************************
//
//! Get ESI PSM Counter 2 Value
//!
//! This function reads the ESI Counter2 register
//!
//! \return Counter value
//
//*****************************************************************************
uint16_t ESI_getCounter2(void)
{
    return (ESICNT2);
}

//*****************************************************************************
//
//! Get ESI PSM Oscillator Counter Value
//!
//! This function reads the ESI Oscillator Counter register
//!
//! \return Counter value
//
//*****************************************************************************
uint16_t ESI_getOscCounter(void)
{
    return (ESICNT3);
}

//*****************************************************************************
//
//! Initializes the ESI analog front end AFE1
//!
//! \param params is ESI_AFE1_InitParams struct
//!
//! This functions initializes the ESI analog front end AFE1.
//!
//! \return None
//
//*****************************************************************************

void ESI_AFE1_init(ESI_AFE1_InitParams *params)
{
    // Unset the AFE1 bits
    ESIAFE &= ~(ESITEN + ESISH + ESIVCC2 + ESIVSS + ESICACI3 + ESICISEL +
                ESICA1X + ESICA1INV);
    ESIAFE |=
        params->excitationCircuitSelect +
        params->sampleAndHoldSelect +
        params->midVoltageGeneratorSelect +
        params->sampleAndHoldVSSConnect +
        params->inverterSelectOutputAFE1
    ;

    switch(params->inputSelectAFE1)
    {
    case ESI_AFE1_INPUT_SELECT_CHx:
        break;
    case ESI_AFE1_INPUT_SELECT_CIx:
        ESIAFE |= ESICA1X;
        break;
    case ESI_AFE1_INPUT_SELECT_CI3:
        ESIAFE |= ESICA1X;
        ESIAFE &= ~ESICISEL;
        ESIAFE |= ESICACI3;
        break;
    case ESI_AFE1_INPUT_SELECT_CI:
        ESIAFE |= ESICA1X;
        ESIAFE |= ESICISEL;
        break;
    default:
        break;
    }
}

//*****************************************************************************
//
//! Initializes the ESI analog front end - AFE2
//!
//! \param params is ESI_AFE2_InitParams struct
//!
//! This functions initializes the ESI analog front end AFE2
//!
//! \return None
//
//*****************************************************************************

void ESI_AFE2_init(ESI_AFE2_InitParams *params)
{
    // Unset the AFE2 bits
    ESIAFE &= ~(ESICA2X + ESICA2INV + ESICA2EN + ESIDAC2EN);

    ESIAFE |=
        params->inputSelectAFE2 +
        params->inverterSelectOutputAFE2 +
        params->tsmControlComparatorAFE2 +
        params->tsmControlDacAFE2
    ;
}

//*****************************************************************************
//
//! Reads the latched comparator outputs form the AFEs
//!
//! \param channelSelect. Valid values are
//!                 ESI_AFE1_CHANNEL0_SELECT
//!                 ESI_AFE1_CHANNEL1_SELECT
//!                 ESI_AFE1_CHANNEL2_SELECT
//!                 ESI_AFE1_CHANNEL3_SELECT
//!                 ESI_AFE2_CHANNEL0_SELECT
//!                 ESI_AFE2_CHANNEL1_SELECT
//!                 ESI_AFE2_CHANNEL2_SELECT
//!                 ESI_AFE2_CHANNEL3_SELECT
//!                 ESI_AFE1_TEST_CHANNEL0_SELECT
//!                 ESI_AFE1_TEST_CHANNEL1_SELECT
//!
//! This function gets the ESIPPU register to get latched output values of the
//! comparator outputs for AFE1 and AFE2
//!
//! \return Valid values are
//!                 ESI_AFE_OUTPUT_LOW
//!                 ESI_AFE_OUTPUT_HIGH
//
//*****************************************************************************
uint16_t ESI_getLatchedComparatorOutput(uint16_t channelSelect)
{
    uint16_t result;

    result = ESIPPU;

    return (result &= channelSelect);
}

//*****************************************************************************
//
//! Initializes the TSM
//!
//! \param params is ESI_TSM_InitParams struct
//!
//! This function initializes the TSM.
//!
//! \return None
//
//*****************************************************************************

void ESI_TSM_init(ESI_TSM_InitParams *params)
{
    ESITSM =
        params->smclkDivider +
        params->aclkDivider +
        params->startTriggerAclkDivider +
        params->repeatMode +
        params->startTriggerSelection +
        params->tsmFunctionSelection
    ;
}

//*****************************************************************************
//
//! Clear TSM entries
//!
//! This function clears all TSM entries
//!
//! \return None
//
//*****************************************************************************
void ESI_TSM_clearTable(void)
{
    uint16_t *pTsm, i;

    // Clear TSM Table (for testing only. not neccessary in real application)
    pTsm = (uint16_t *)&ESITSM0;
    for(i = 0; i < 32; i++)
    {
        *pTsm++ = 0x0200;
    }
}

//*****************************************************************************
//
//! Copy TSM entries
//!
//! This function copies all TSM entries
//!
//! \return None
//
//*****************************************************************************
void ESI_TSM_copyTable(uint16_t* tsmTable,
                       uint16_t size)
{
    uint16_t *pt_tsmTable;
    uint16_t i;

    // Copy the TSM_Table into ESI TSM registers
    // Destination pointer
    pt_tsmTable = (uint16_t *)&ESITSM0;
    // Divided by 2 because of unsigned integer (2bytes)
    i = size / 2;

    do
    {
        *pt_tsmTable++ = *tsmTable++;
    }
    while(--i);
}

//*****************************************************************************
//
//! TSM trigger using software
//!
//! This function starts a software initiated TSM sequence
//!
//! \return None
//
//*****************************************************************************
void ESI_TSM_softwareTrigger(void)
{
    ESITSM |= ESISTART;
}

//*****************************************************************************
//
//! TSM trigger using software
//!
//! This function starts a software initiated TSM sequence
//!
//! \return ESIREATx bits from selected stateRegNum
//
//*****************************************************************************
uint8_t ESI_TSM_getTSMStateDuration(uint8_t stateRegNum)
{
    volatile uint16_t* stateRegBase = (volatile uint16_t*)&ESITSM0;

    return((*(stateRegBase + stateRegNum) & 0xf800) >> 11);
}

//*****************************************************************************
//
//! TSM trigger using software
//!
//! This function starts a software initiated TSM sequence
//!
//! \return ESIREATx bits from selected stateRegNum
//
//*****************************************************************************
void ESI_TSM_setTSMStateDuration(uint8_t stateRegNum,
                                 uint8_t duration)
{
    assert(stateRegNum <= ESI_TSM_STATE_REG_31);
    assert(duration <= ESI_TSM_STATE_DURATION_MAX);

    volatile uint16_t* stateRegBase = (volatile uint16_t*)&ESITSM0;

    *(stateRegBase + stateRegNum) &= ~0xF800;

    *(stateRegBase + stateRegNum) |= (duration << 11);
}

//*****************************************************************************
//
//! Initialize Processing State Machine
//
//! \param params is ESI_PSM_InitParams struct
//!
//! This function initializes the PSM registers.
//!
//! \return None
//
//*****************************************************************************
void ESI_PSM_init(ESI_PSM_InitParams *params)
{
    ESIPSM =
        params->Q6Select +
        params->Q7TriggerSelect +
        params->count0Select +
        params->count0Reset +
        params->count1Select +
        params->count1Reset +
        params->count2Select +
        params->count2Reset +
        params->V2Select +
        params->TEST4Select
    ;
}

//*****************************************************************************
//
//! Clear PSM entries
//!
//! This function clears all PSM entries
//!
//! \return None
//
//*****************************************************************************
void ESI_PSM_clearTable(void)
{
    uint8_t *pPsm, i;

    // Clear TSM Table (for testing only. not neccessary in real application)
    pPsm = (uint8_t *)&ESIRAM0;
    for(i = 0; i < 128; i++)
    {
        *pPsm++ = 0x0;
    }
}

//*****************************************************************************
//
//! Copy PSM entries
//!
//! This function copies all PSM entries
//!
//! \return None
//
//*****************************************************************************
void ESI_PSM_copyTable(uint8_t* psmTable,
                       uint8_t size)
{
    uint8_t *pt_psmTable;
    uint8_t i;

    assert(size <= 128);

    // Copy the TSM_Table into ESI TSM registers
    pt_psmTable = (uint8_t *)&ESIRAM0;                                  // Destination pointer
    i = size;

    do
    {
        *pt_psmTable++ = *psmTable++;
    }
    while(--i);
}

//*****************************************************************************
//
//! Reset PSM counters
//!
//! \param counterToReset is the counter that needs t be reset
//!
//! This function resets the PSM counters
//!
//! \return None
//
//*****************************************************************************
void ESI_PSM_resetCounter(uint16_t counterToReset)
{
    ESIPSM |= counterToReset;
}

//*****************************************************************************
//
//! Enables the internal Oscillator
//!
//!
//! This function enables the high frequency internal oscillator
//!
//! \return None
//
//*****************************************************************************
void ESI_enableInternalOscillator(void)
{
    ESIOSC |= ESIHFSEL;
}

//*****************************************************************************
//
//! Disables the internal Oscillator
//!
//!
//! This function disables the high frequency internal oscillator
//!
//! \return None
//
//*****************************************************************************
void ESI_disableInternalOscillator(void)
{
    ESIOSC &= ~ESIHFSEL;
}

//*****************************************************************************
//
//! Connects comparator output to timerA input
//!
//! \param counterToReset ESI_TIMERA_INPUT_TSM_COMPOUT or
//!                       ESI_TIMERA_INPUT_TSM_PPUSRC
//!
//! This function connects the chosen comparator output to TimerA
//!
//! \return None
//
//*****************************************************************************
void ESI_timerAInputSelect(uint16_t select)
{
    ESICTL |= select;
}

//*****************************************************************************
//
//! Connects psm source to comparator output
//!
//! \param sourceNum PSM_S1_SOURCE, PSM_S2_SOURCE  or PSM_S3_SOURCE
//! \param sourceSelect can have the following values
//!         ESI_PSM_SOURCE_IS_ESIOUT0
//!         ESI_PSM_SOURCE_IS_ESIOUT1
//!         ESI_PSM_SOURCE_IS_ESIOUT2
//!         ESI_PSM_SOURCE_IS_ESIOUT3
//!         ESI_PSM_SOURCE_IS_ESIOUT4
//!         ESI_PSM_SOURCE_IS_ESIOUT5
//!         ESI_PSM_SOURCE_IS_ESIOUT6
//!         ESI_PSM_SOURCE_IS_ESIOUT7
//!
//! This function connects the chosen comparator output to TimerA
//!
//! \return None
//
//*****************************************************************************
void ESI_psmSourceSelect(uint16_t sourceNum,
                         uint16_t sourceSelect)
{
    switch(sourceNum)
    {
    case PSM_S1_SOURCE:
        ESICTL &= ~(ESIS1SEL0 | ESIS1SEL1 | ESIS1SEL2);
        ESICTL |= (sourceSelect << 7);
        break;
    case PSM_S2_SOURCE:
        ESICTL &= ~(ESIS2SEL0 | ESIS2SEL1 | ESIS2SEL2);
        ESICTL |= (sourceSelect << 10);
        break;
    case PSM_S3_SOURCE:
        ESICTL &= ~(ESIS3SEL0 | ESIS3SEL1 | ESIS3SEL2);
        ESICTL |= (sourceSelect << 13);
        break;
    default:
        break;
    }
}

//*****************************************************************************
//
//! Connects testChannel0 to comparator input
//!
//! \param sourceSelect can have the following values
//!         ESI_TEST_CHANNEL0_SOURCE_IS_CH0_CI0
//!         ESI_TEST_CHANNEL0_SOURCE_IS_CH1_CI1
//!         ESI_TEST_CHANNEL0_SOURCE_IS_CH2_CI2
//!         ESI_TEST_CHANNEL0_SOURCE_IS_CH3_CI3
//!
//! This function connects the chosen comparator input to the test channel0
//!
//! \return None
//
//*****************************************************************************
void ESI_testChannel0SourceSelect(uint16_t sourceSelect)
{
    ESICTL &= ~(ESI_TEST_CHANNEL0_SOURCE_IS_CH3_CI3);
    ESICTL |= sourceSelect;
}

//*****************************************************************************
//
//! Connects testChannel1to comparator input
//!
//! \param sourceSelect can have the following values
//!         ESI_TEST_CHANNEL1_SOURCE_IS_CH0_CI0
//!         ESI_TEST_CHANNEL1_SOURCE_IS_CH1_CI1
//!         ESI_TEST_CHANNEL1_SOURCE_IS_CH2_CI2
//!         ESI_TEST_CHANNEL1_SOURCE_IS_CH3_CI3
//!
//! This function connects the chosen comparator input to the test channel1
//!
//! \return None
//
//*****************************************************************************
void ESI_testChannel1SourceSelect(uint16_t sourceSelect)
{
    ESICTL &= ~(ESI_TEST_CHANNEL1_SOURCE_IS_CH3_CI3);
    ESICTL |= sourceSelect;
}

//*****************************************************************************
//
//! Enable ESI peripheral
//!
//! \return None
//
//*****************************************************************************
void ESI_enable(void)
{
    ESICTL |= ESIEN;
}

//*****************************************************************************
//
//! Disable ESI peripheral
//!
//! \return None
//
//*****************************************************************************
void ESI_disable(void)
{
    ESICTL &= ~ESIEN;
}

//*****************************************************************************
//
//! Start calibration on ESI internal Oscillator
//!
//! This function starts calibration of internal osciallator. After calling this
//! function the user and use ESI_adjustInternalOscFreq() to adjust the freq. of
//! the oscillator.
//!
//! \return None
//
//*****************************************************************************
void ESI_startInternalOscCal(void)
{
    assert(ESIOSC | ESIHFSEL);
    ESIOSC |= ESICLKGON;
}

//*****************************************************************************
//
//! Adjusts frequency ESI internal Oscillator
//!
//! This function adjusts frequency ESI internal Oscillator. It increases or
//! decrease the freq by 3% based on incOrDec value.
//!
//! \return None
//
//*****************************************************************************
void ESI_adjustInternalOscFreq(uint16_t incOrDec)
{
    uint16_t adjustValue;

    assert(ESIOSC | ESIHFSEL);

    adjustValue = ESIOSC >> 8;

    if(incOrDec == ESI_INTERNAL_OSC_FREQ_INCREASE)
    {
        adjustValue = adjustValue + 1;
        adjustValue = adjustValue << 8;
    }
    else
    {
        adjustValue = adjustValue - 1;
        adjustValue = adjustValue << 8;
    }

    ESIOSC |= adjustValue;
}

//*****************************************************************************
//
//! Sets frequency of ESI internal Oscillator
//!
//!
//! \return None
//
//*****************************************************************************
void ESI_setNominalInternalOscFreq(void)
{
    ESIOSC = ESICLKFQ5 + ESICLKGON + ESIHFSEL;
}

//*****************************************************************************
//
//! The following function return the number of ESIOSC cycle during an ACLK
//! cycle.
//!
//!
//! \return None
//
//*****************************************************************************
static uint16_t measureESIOSC(void){
    // This and next instruction realizes a clear->set ESICLKGON bit.
    ESIOSC &= ~(ESICLKGON);

    // This starts measurement.
    ESIOSC |= ESICLKGON + ESIHFSEL;

    // Reading ESICNT3 while counting always result in reading a 0x01.
    while(ESICNT3 == 1)
    {
        ;
    }

    // Stop ESIOSC oscillator
    ESIOSC &= ~(ESICLKGON);

    return (ESICNT3);
}

//******************************************************************************
//! The following function returns the ESICLKFQx bits on ESIOSC register
//
//! \param none
//
//! \return ESICLKFQ bits only
//******************************************************************************

uint8_t ESI_getESICLKFQ(void){
    uint16_t temp;

    // Store ESIOSC content
    temp = ESIOSC;
    // Get ESICLKFQx bits
    temp = (temp >> 8) & 0x3F;

    return(temp);
}

//******************************************************************************
//! The following function sets ESICLKFQx bits on ESIOSC register
//
//! \param setting is to the loaded to ESIOSC. Valid parameters a value between
//!		   0x00 and 0x3F. 0x00 corresponds to minimum frequency, 0x20
//!		   corresponds to nominal frequency and 0x3F corresponds to maximum
//!		   frequency.
//
//! \return none
//******************************************************************************
void ESI_setESICLKFQ(uint8_t setting)
{
    uint16_t temp;

    assert(setting < 0x40);

    temp = ESIOSC;                         // get actual ESIOSC register content
    temp &= ~(0x3F00);
    temp = ((uint16_t) setting << 8) + temp;     // and update ESICLKFQ bits
    ESIOSC = temp;
}

//*****************************************************************************
//
//! Calibrate ESI internal Oscillator
//!
//!
//! \return None
//
//*****************************************************************************
void ESI_calibrateInternalOscFreq(uint16_t targetAclkCounts)
{
    ESI_setNominalInternalOscFreq();

    ESI_measureESIOSC(ESI_ESIOSC_OVERSAMPLE_4);

    if(ESICNT3 > targetAclkCounts)
    {
        //freq is too high
        do
        {
            ESI_adjustInternalOscFreq(ESI_INTERNAL_OSC_FREQ_DECREASE);
        }
        while(ESI_measureESIOSC(ESI_ESIOSC_OVERSAMPLE_4) > targetAclkCounts);
    }
    else
    {
        //freq is too low
        do
        {
            ESI_adjustInternalOscFreq(ESI_INTERNAL_OSC_FREQ_INCREASE);
        }
        while(ESI_measureESIOSC(ESI_ESIOSC_OVERSAMPLE_4) > targetAclkCounts);
        ESI_adjustInternalOscFreq(ESI_INTERNAL_OSC_FREQ_DECREASE);
    }
}

//*****************************************************************************
//
//! The following function returns an average of ESIOSC measurement.
//!
//! \param
//!
//! \return averaged ESIOSC measurement.
//
//*****************************************************************************
uint16_t ESI_measureESIOSC(uint8_t oversample){
    uint8_t i;
    uint16_t temp = 0;

    assert(oversample < 9);

    for(i = oversample; i > 0; i--)
    {
        temp += measureESIOSC();
    }

    temp /= oversample;
    return(temp);
}

//*****************************************************************************
//
//! Set upper threshold for PSM counter 1
//!
//! \param threshold is the upper threashold that causes ESIIFG3 to get set.
//!
//! This function sets the threshold value for PSM counter 1. ESIIFG3 gets set
//! when counter value and this threahold are equal.
//!
//! \return None
//
//*****************************************************************************
void ESI_setPSMCounter1UpperThreshold(uint16_t threshold)
{
    ESITHR1 = threshold;
}

//*****************************************************************************
//
//! Set lower threshold for PSM counter 1
//!
//! \param threshold is the lower threashold that causes ESIIFG3 to get set.
//!
//! This function set the threshold value for PSM counter 1. ESIIFG3 gets set
//! when counter value and this threahold are equal.
//!
//! \return None
//
//*****************************************************************************
void ESI_setPSMCounter1LowerThreshold(uint16_t threshold)
{
    ESITHR2 = threshold;
}

//*****************************************************************************
//
//! sets AFE1 DAC threshold Value
//!
//! \param dacValue is value to be written to DAC register.
//! \param dacRegNum is DAC register number
//!
//! Write DAC threshold value into selected DAC register
//!
//! \return None
//
//*****************************************************************************
void ESI_setAFE1DACValue(uint16_t dacValue,
                         uint8_t dacRegNum)
{
    volatile uint16_t* dacRegBase = (volatile uint16_t*) &ESIDAC1R0;
    *(dacRegBase + dacRegNum) = dacValue;
}

//*****************************************************************************
//
//! gets AFE1 DAC threshold Value
//!
//! \param dacValue is value to be written to DAC register.
//! \param dacRegNum is DAC register number
//!
//! Read DAC threshold value into selected DAC register
//!
//! \return DAC value from selected DAC register.
//
//*****************************************************************************
uint16_t ESI_getAFE1DACValue(uint8_t dacRegNum)
{
    volatile uint16_t* dacRegBase = (volatile uint16_t*) &ESIDAC1R0;
    return(*(dacRegBase + dacRegNum));
}

//*****************************************************************************
//
//! sets AFE2 DAC threshold Value
//!
//! \param dacValue is value to be written to DAC register.
//! \param dacRegNum is DAC register number
//!
//! Write DAC threshold value into selected DAC register
//!
//! \return None
//
//*****************************************************************************
void ESI_setAFE2DACValue(uint16_t dacValue,
                         uint8_t dacRegNum)
{
    volatile uint16_t* dacRegBase = (volatile uint16_t*) &ESIDAC2R0;
    *(dacRegBase + dacRegNum) = dacValue;
}

//*****************************************************************************
//
//! gets AFE2 DAC threshold Value
//!
//! \param dacValue is value to be written to DAC register.
//! \param dacRegNum is DAC register number
//!
//! Read DAC threshold value into selected DAC register
//!
//! \return DAC value from selected DAC register.
//
//*****************************************************************************
uint16_t ESI_getAFE2DACValue(uint8_t dacRegNum)
{
    volatile uint16_t* dacRegBase = (volatile uint16_t*) &ESIDAC2R0;
    return(*(dacRegBase + dacRegNum));
}

//*****************************************************************************
//
//! sets TSM state register
//!
//! \param params constructs the state value
//! \param stateRegNum is state register offset
//!
//! Sets selected TSM state register.
//!
//! \return None
//
//*****************************************************************************
void ESI_setTSMstateReg(ESI_TSM_StateParams *params,
                        uint8_t stateRegNum)
{
    volatile uint16_t* stateRegBase = (volatile uint16_t*) &ESITSM0;
    *(stateRegBase + stateRegNum) =
        (params->inputChannelSelect +
         params->LCDampingSelect +
         params->excitationSelect +
         params->comparatorSelect +
         params->highFreqClkOn_or_compAutoZeroCycle +
         params->outputLatchSelect +
         params->testCycleSelect +
         params->dacSelect +
         params->tsmStop +
         params->tsmClkSrc) |
        (params->duration << 11);
}

//*****************************************************************************
//
//! Get ESI interrupt Vector Register
//!
//! \return None
//
//*****************************************************************************
uint16_t ESI_getInterruptVectorRegister(void)
{
    return (ESIIV);
}

//*****************************************************************************
//
//! Enables ESI interrupts
//!
//! \param interruptMask is the bit mask of the interrupt sources to
//!        be enabled. Mask value is the logical OR of any of the following:
//!        \b ESI_INTERRUPT_AFE1_ESIOUTX
//!		   \b ESI_INTERRUPT_ESISTOP
//!		   \b ESI_INTERRUPT_ESISTART
//!		   \b ESI_INTERRUPT_ESICNT1
//!		   \b ESI_INTERRUPT_ESICNT2
//!		   \b ESI_INTERRUPT_Q6_BIT_SET
//!		   \b ESI_INTERRUPT_Q7_BIT_SET
//!		   \b ESI_INTERRUPT_ESICNT0_COUNT_INTERVAL
//!		   \b ESI_INTERRUPT_AFE2_ESIOUTX
//!
//! Modified bits of \b ESIINT1 register.
//!
//! \return None
//
//*****************************************************************************
void ESI_enableInterrupt(uint16_t interruptMask)
{
    ESIINT1 |= (interruptMask);
}

//*****************************************************************************
//
//! Disables ESI interrupts
//!
//! \param interruptMask is the bit mask of the interrupt sources to
//!        be disabled. Mask value is the logical OR of any of the following:
//!        \b ESI_INTERRUPT_AFE1_ESIOUTX
//!		   \b ESI_INTERRUPT_ESISTOP
//!		   \b ESI_INTERRUPT_ESISTART
//!		   \b ESI_INTERRUPT_ESICNT1
//!		   \b ESI_INTERRUPT_ESICNT2
//!		   \b ESI_INTERRUPT_Q6_BIT_SET
//!		   \b ESI_INTERRUPT_Q7_BIT_SET
//!		   \b ESI_INTERRUPT_ESICNT0_COUNT_INTERVAL
//!		   \b ESI_INTERRUPT_AFE2_ESIOUTX
//!
//! Modified bits of \b ESIINT1 register.
//!
//! \return None
//
//*****************************************************************************
void ESI_disableInterrupt(uint16_t interruptMask)
{
    ESIINT1 &= ~(interruptMask);
}

//*****************************************************************************
//
//! Get ESI interrupt status
//!
//! \param interruptMask is the masked interrupt flag status to be returned.
//!        Mask value is the logical OR of any of the following:
//!        - \b ESI_INTERRUPT_FLAG_AFE1_ESIOUTX
//!        - \b ESI_INTERRUPT_FLAG_ESISTOP
//!        - \b ESI_INTERRUPT_FLAG_ESISTART
//!        - \b ESI_INTERRUPT_FLAG_ESICNT1
//!        - \b ESI_INTERRUPT_FLAG_ESICNT2
//!		   - \b ESI_INTERRUPT_FLAG_Q6_BIT_SET
//!        - \b ESI_INTERRUPT_FLAG_Q7_BIT_SET
//!        - \b ESI_INTERRUPT_FLAG_ESICNT0_COUNT_INTERVAL
//!        - \b ESI_INTERRUPT_FLAG_AFE2_ESIOUTX
//!
//! \return Logical OR of any of the following:
//!        - \b ESI_INTERRUPT_FLAG_AFE1_ESIOUTX
//!        - \b ESI_INTERRUPT_FLAG_ESISTOP
//!        - \b ESI_INTERRUPT_FLAG_ESISTART
//!        - \b ESI_INTERRUPT_FLAG_ESICNT1
//!        - \b ESI_INTERRUPT_FLAG_ESICNT2
//!        - \b ESI_INTERRUPT_FLAG_Q6_BIT_SET
//!        - \b ESI_INTERRUPT_FLAG_Q7_BIT_SET
//!        - \b ESI_INTERRUPT_FLAG_ESICNT0_COUNT_INTERVAL
//!        - \b ESI_INTERRUPT_FLAG_AFE2_ESIOUTX
//!         \n indicating the status of the masked flags
//
//*****************************************************************************
uint16_t ESI_getInterruptStatus(uint16_t interruptMask)
{
    return (ESIINT2 & interruptMask);
}

//*****************************************************************************
//
//! Clear ESI interrupt flag
//!
//! \param interruptMask is the masked interrupt flag status to be returned.
//!        Mask value is the logical OR of any of the following:
//!        - \b ESI_INTERRUPT_FLAG_AFE1_ESIOUTX
//!        - \b ESI_INTERRUPT_FLAG_ESISTOP
//!        - \b ESI_INTERRUPT_FLAG_ESISTART
//!        - \b ESI_INTERRUPT_FLAG_ESICNT1
//!        - \b ESI_INTERRUPT_FLAG_ESICNT2
//!		   - \b ESI_INTERRUPT_FLAG_Q6_BIT_SET
//!        - \b ESI_INTERRUPT_FLAG_Q7_BIT_SET
//!        - \b ESI_INTERRUPT_FLAG_ESICNT0_COUNT_INTERVAL
//!        - \b ESI_INTERRUPT_FLAG_AFE2_ESIOUTX
//!
//! \return None
//
//*****************************************************************************
void ESI_clearInterrupt(uint16_t interruptMask)
{
    ESIINT2 &= ~(interruptMask);
}

//*****************************************************************************
//
//! Set source of IFG0 interrupt flag
//!
//! \param ifg0Src values are as follows
//!         ESI_IFG0_SET_WHEN_ESIOUT0_SET
//!         ESI_IFG0_SET_WHEN_ESIOUT0_RESET
//!         ESI_IFG0_SET_WHEN_ESIOUT1_SET
//!         ESI_IFG0_SET_WHEN_ESIOUT1_RESET
//!         ESI_IFG0_SET_WHEN_ESIOUT2_SET
//!         ESI_IFG0_SET_WHEN_ESIOUT2_RESET
//!         ESI_IFG0_SET_WHEN_ESIOUT3_SET
//!         ESI_IFG0_SET_WHEN_ESIOUT3_RESET
//!
//! \return None
//
//*****************************************************************************
void ESI_setIFG0Source(uint16_t ifg0Src)
{
    ESIINT1 &= ~ESI_IFG0_SET_WHEN_ESIOUT3_RESET;
    ESIINT1 |= ifg0Src;
}

//*****************************************************************************
//
//! Set source of IFG8 interrupt flag
//!
//! \param ifg8Src values are as follows
//!         ESI_IFG8_SET_WHEN_ESIOUT4_SET
//!         ESI_IFG8_SET_WHEN_ESIOUT4_RESET
//!         ESI_IFG8_SET_WHEN_ESIOUT5_SET
//!         ESI_IFG8_SET_WHEN_ESIOUT5_RESET
//!         ESI_IFG8_SET_WHEN_ESIOUT6_SET
//!         ESI_IFG8_SET_WHEN_ESIOUT6_RESET
//!         ESI_IFG8_SET_WHEN_ESIOUT7_SET
//!         ESI_IFG8_SET_WHEN_ESIOUT7_RESET
//!
//! \return None
//
//*****************************************************************************
void ESI_setIFG8Source(uint16_t ifg8Src)
{
    ESIINT1 &= ~ESI_IFG8_SET_WHEN_ESIOUT7_RESET;
    ESIINT1 |= ifg8Src;
}

//*****************************************************************************
//
//! Set source of IFG7 interrupt flag
//!
//! \param ifg7Src values are as follows
//!         ESI_IFG7_SOURCE_EVERY_COUNT_OF_CNT0
//!         ESI_IFG7_SOURCE_CNT0_MOD4
//!         ESI_IFG7_SOURCE_CNT0_MOD256
//!         ESI_IFG7_SOURCE_CNT0_ROLLOVER
//!
//! \return None
//
//*****************************************************************************
void ESI_setIFG7Source(uint16_t ifg7Src)
{
    ESIINT2 &= ~ESI_IFG7_SOURCE_CNT0_ROLLOVER;
    ESIINT2 |= ifg7Src;
}

//*****************************************************************************
//
//! Set source of IFG4 interrupt flag
//!
//! \param ifg4Src values are as follows
//!         ESI_IFG4_SOURCE_EVERY_COUNT_OF_CNT2
//!         ESI_IFG4_SOURCE_CNT2_MOD4
//!         ESI_IFG4_SOURCE_CNT2_MOD256
//!         ESI_IFG4_SOURCE_CNT2_ROLLOVER
//!
//! \return None
//
//*****************************************************************************
void ESI_setIFG4Source(uint16_t ifg4Src)
{
    ESIINT2 &= ~ESI_IFG4_SOURCE_CNT2_ROLLOVER;
    ESIINT2 |= ifg4Src;
}

//*****************************************************************************
//
//! Simple DAC calibration code using pre-defined TSM
//! Supports AFE1 only.
//! \param selected_channel acceptable values
//!         ESI_AFE1_CHANNEL0_SELECT
//!         ESI_AFE1_CHANNEL1_SELECT
//!         ESI_AFE1_CHANNEL2_SELECT
//!         ESI_AFE1_CHANNEL3_SELECT
//!
//!
//! \return None
//
//*****************************************************************************
void ESI_LC_DAC_calibration(uint8_t selected_channel)
{
#define NUM_SENSOR_CAL  4
#define MIN_HYSTERESIS  30
#define STEP_TO_FINISH  4

    unsigned int i;
    unsigned char test_bit, done;
    unsigned int hysteresis[NUM_SENSOR_CAL],
                 hysteresis_hi[NUM_SENSOR_CAL],
                 hysteresis_lo[NUM_SENSOR_CAL],
                 current[NUM_SENSOR_CAL],
                 average[NUM_SENSOR_CAL],
                 max[NUM_SENSOR_CAL],
                 min[NUM_SENSOR_CAL];

    // State:	0 = output low
    //			1 = output high
    //			2 = undetermined (between 2 hysteresis level)
    unsigned char previous_state[NUM_SENSOR_CAL],
                  current_state[NUM_SENSOR_CAL],
                  step[NUM_SENSOR_CAL];

    // Reset values
    for(i = 0; i < NUM_SENSOR_CAL; i++)
    {
        max[i] = 0;
        min[i] = 0xffff;
        previous_state[i] = 2;
        step[i] = 0;
    }

    do
    {
        // Find the current oscillating level, using software mode
        FindDAC(selected_channel, 1);

        test_bit = 1;
        done = 1;

        for(i = 0; i < NUM_SENSOR_CAL; i++)
        {
            // skip if the channel is not selected
            if(test_bit & selected_channel)
            {
                current[i] = ESI_getAFE1DACValue(i * 2);

                // Record max and min value
                if(current[i] > max[i])
                {
                    max[i] = current[i];
                }
                if(current[i] < min[i])
                {
                    min[i] = current[i];
                }

                // Update average and hysteresis level
                average[i] = (max[i] + min[i]) >> 1;
                hysteresis[i] = (max[i] - min[i]) >> 3;

                if(hysteresis[i] < MIN_HYSTERESIS)
                {
                    hysteresis[i] = MIN_HYSTERESIS;
                }

                hysteresis[i] >>= 1;
                hysteresis_hi[i] = average[i] + hysteresis[i];
                hysteresis_lo[i] = average[i] - hysteresis[i];

                // Determine output state based on hysteresis_hi and hysteresis_lo
                if(current[i] < hysteresis_lo[i])
                {
                    current_state[i] = 0;
                }
                else if(current[i] > hysteresis_hi[i])
                {
                    current_state[i] = 1;
                }
                else
                {
                    current_state[i] = 2;
                }

                // If there is state change, proceed to next step
                switch(current_state[i])
                {
                case 0:
                case 1:
                    if(previous_state[i] != current_state[i])
                    {
                        step[i]++;
                        previous_state[i] = current_state[i];
                    }
                    break;

                default:
                    break;
                }

                // Any selected sensor which has not finished calibration will set done to zero
                if(step[i] < STEP_TO_FINISH)
                {
                    done = 0;
                }
            }
            test_bit <<= 1;
        }
    }
    while(!done);

    // Record DAC Values
    test_bit = 1;
    done = ESI_DAC1_REG0;               // Temp value for recording DAC
    for(i = 0; i < NUM_SENSOR_CAL; i++)
    {
        if(test_bit & selected_channel)
        {
            ESI_setAFE1DACValue(hysteresis_hi[i], done++);
            ESI_setAFE1DACValue(hysteresis_lo[i], done++);
        }
        test_bit <<= 1;
    }
}

//*****************************************************************************
//
//! Find the current oscillating level, using software mode
//!
//!
//! \return None
//
//*****************************************************************************

static void FindDAC(unsigned char selected_channel,
                    unsigned char software_trigger)
{
    // DAC Level tester, using successive approximation approach
    unsigned int DAC_BIT = 0x0800, Prev_DAC_BIT = 0x0C00;

    unsigned int i;
    unsigned int test_bit, DAC_index;

    // Set initial DAC value for each selected channel

    // AFE 1
    if(selected_channel & 0x0f)
    {
        test_bit = 0x01;
        DAC_index = ESI_DAC1_REG0;
        for(i = 0; i < 4; i++)
        {
            if(selected_channel & test_bit)
            {
                ESI_setAFE1DACValue(DAC_BIT, DAC_index++);
                ESI_setAFE1DACValue(DAC_BIT, DAC_index++);
            }
            else
            {
                DAC_index += 2;
            }
            test_bit <<= 1;
        }
    }

    // AFE 2
    if(selected_channel & 0xf0)
    {
        test_bit = 0x10;
        DAC_index = ESI_DAC2_REG0;
        for(i = 0; i < 4; i++)
        {
            if(selected_channel & test_bit)
            {
                ESI_setAFE2DACValue(DAC_BIT, DAC_index++);
                ESI_setAFE2DACValue(DAC_BIT, DAC_index++);
            }
            else
            {
                DAC_index += 2;
            }
            test_bit <<= 1;
        }
    }

    ESI_enableInterrupt(ESI_INTERRUPT_ESISTOP);                 // enable ESISTOP INT

    // Find the DAC value for each selected channel
    do
    {
        ESI_clearInterrupt (ESI_INTERRUPT_FLAG_ESISTOP);

        if(software_trigger)
        {
            ESI_TSM_softwareTrigger();
        }

        __bis_SR_register(LPM3_bits + GIE);                     // wait for the ESISTOP flag
        DAC_BIT >>= 1;                                                          // right shift one bit

        // AFE 1
        if(selected_channel & 0x0f)
        {
            test_bit = 0x01;
            DAC_index = ESI_DAC1_REG0;
            for(i = 0; i < 4; i++)
            {
                if(selected_channel & test_bit)
                {
#ifndef INVERTED
                    if(ESI_getLatchedComparatorOutput(test_bit) ==
                       ESI_AFE_OUTPUT_HIGH)
#else
                    if(ESI_getLatchedComparatorOutput(test_bit) ==
                       ESI_AFE_OUTPUT_LOW)
#endif
                    {
                        ESI_setAFE1DACValue(ESI_getAFE1DACValue(
                                                DAC_index) | DAC_BIT,
                                            DAC_index);
                        DAC_index++;
                        ESI_setAFE1DACValue(ESI_getAFE1DACValue(
                                                DAC_index) | DAC_BIT,
                                            DAC_index);
                        DAC_index++;
                    }
                    else
                    {
                        ESI_setAFE1DACValue(ESI_getAFE1DACValue(
                                                DAC_index) ^ Prev_DAC_BIT,
                                            DAC_index);
                        DAC_index++;
                        ESI_setAFE1DACValue(ESI_getAFE1DACValue(
                                                DAC_index) ^ Prev_DAC_BIT,
                                            DAC_index);
                        DAC_index++;
                    }
                }
                else
                {
                    DAC_index += 2;
                }
                test_bit <<= 1;
            }
        }

        // AFE 2
        if(selected_channel & 0xf0)
        {
            test_bit = 0x10;
            DAC_index = ESI_DAC2_REG0;
            for(i = 0; i < 4; i++)
            {
                if(selected_channel & test_bit)
                {
#ifndef INVERTED
                    if(ESI_getLatchedComparatorOutput(test_bit) ==
                       ESI_AFE_OUTPUT_HIGH)
#else
                    if(ESI_getLatchedComparatorOutput(test_bit) ==
                       ESI_AFE_OUTPUT_LOW)
#endif
                    {
                        ESI_setAFE1DACValue(ESI_getAFE2DACValue(
                                                DAC_index) | DAC_BIT,
                                            DAC_index);
                        DAC_index++;
                        ESI_setAFE1DACValue(ESI_getAFE2DACValue(
                                                DAC_index) | DAC_BIT,
                                            DAC_index);
                        DAC_index++;
                    }
                    else
                    {
                        ESI_setAFE1DACValue(ESI_getAFE2DACValue(
                                                DAC_index) ^ Prev_DAC_BIT,
                                            DAC_index);
                        DAC_index++;
                        ESI_setAFE1DACValue(ESI_getAFE2DACValue(
                                                DAC_index) ^ Prev_DAC_BIT,
                                            DAC_index);
                        DAC_index++;
                    }
                }
                else
                {
                    DAC_index += 2;
                }
                test_bit <<= 1;
            }
        }
        Prev_DAC_BIT >>= 1;                                             // right shift one bit
    }
    while(DAC_BIT);

    ESI_disableInterrupt(ESI_INTERRUPT_ESISTOP);
    __no_operation();
}

//*****************************************************************************
//
//! Close the doxygen group for esi_api
//! @}
//
//*****************************************************************************
#endif
