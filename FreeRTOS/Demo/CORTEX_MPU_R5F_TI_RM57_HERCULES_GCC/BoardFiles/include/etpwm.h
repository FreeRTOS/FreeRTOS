/** @file etpwm.h
 *   @brief ETPWM Driver Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#ifndef __ETPWM_H__
#define __ETPWM_H__

#include "reg_etpwm.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */
#define COUNT_UP   ( 1U << 13U )
#define COUNT_DOWN 0U

/** @brief Enumeration to define the pulse width modulation (ETPWM) clock divider
 *   TBCLK = VCLK4 / (HSPCLKDIV × CLKDIV)
 */
typedef enum
{
    ClkDiv_by_1 = ( ( uint16 ) 0U << 10U ),  /** CLKDIV = 1   */
    ClkDiv_by_2 = ( ( uint16 ) 1U << 10U ),  /** CLKDIV = 2   */
    ClkDiv_by_4 = ( ( uint16 ) 2U << 10U ),  /** CLKDIV = 4   */
    ClkDiv_by_8 = ( ( uint16 ) 3U << 10U ),  /** CLKDIV = 8   */
    ClkDiv_by_16 = ( ( uint16 ) 4U << 10U ), /** CLKDIV = 16  */
    ClkDiv_by_32 = ( ( uint16 ) 5U << 10U ), /** CLKDIV = 32  */
    ClkDiv_by_64 = ( ( uint16 ) 6U << 10U ), /** CLKDIV = 64  */
    ClkDiv_by_128 = ( ( uint16 ) 7U << 10U ) /** CLKDIV = 128 */
} etpwmClkDiv_t;

/** @brief Enumeration to define the pulse width modulation (ETPWM) high speed clock
 * divider TBCLK = VCLK4 / (HSPCLKDIV × CLKDIV)
 */
typedef enum
{
    HspClkDiv_by_1 = ( ( uint16 ) 0U << 7U ),  /** HSPCLKDIV = 1   */
    HspClkDiv_by_2 = ( ( uint16 ) 1U << 7U ),  /** HSPCLKDIV = 2   */
    HspClkDiv_by_4 = ( ( uint16 ) 2U << 7U ),  /** HSPCLKDIV = 4   */
    HspClkDiv_by_6 = ( ( uint16 ) 3U << 7U ),  /** HSPCLKDIV = 8   */
    HspClkDiv_by_8 = ( ( uint16 ) 4U << 7U ),  /** HSPCLKDIV = 16  */
    HspClkDiv_by_10 = ( ( uint16 ) 5U << 7U ), /** HSPCLKDIV = 32  */
    HspClkDiv_by_12 = ( ( uint16 ) 6U << 7U ), /** HSPCLKDIV = 64  */
    HspClkDiv_by_14 = ( ( uint16 ) 7U << 7U )  /** HSPCLKDIV = 128 */
} etpwmHspClkDiv_t;

/** @brief Enumeration to select the source of Synchronization Output signal (EPWMxSYNCO)
 */
typedef enum
{
    SyncOut_EPWMxSYNCI = 0x00U, /** EPWMxSYNCI                */
    SyncOut_CtrEqZero = 0x10U,  /** CTR = zero                */
    SyncOut_CtrEqCmpB = 0x20U,  /** CTR = CMPB                */
    SyncOut_Disable = 0x30U     /** Disable EPWMxSYNCO signal */
} etpwmSyncOut_t;

/** @brief Enumeration to define the pulse width modulation (ETPWM) counter modes
 */
typedef enum
{
    CounterMode_Up = 0U,     /** Up-count mode                  */
    Countermode_Down = 1U,   /** Down-count mode                */
    CounterMode_UpDown = 2U, /** Up-down-count mode             */
    CounterMode_Stop = 3U    /** Stop - freeze counter operaton */
} etpwmCounterMode_t;

/** @brief Enumeration to the behavior of the ePWM time-base counter during emulation
 * events
 */
typedef enum
{
    RunMode_SoftStopAfterIncr = ( ( uint16 ) 0U << 14U ),  /** Stop after the next
                                                              time-base counter increment
                                                            */
    RunMode_SoftStopAfterDecr = ( ( uint16 ) 0U << 14U ),  /** Stop after the next
                                                              time-base counter decrement
                                                            */
    RunMode_SoftStopAfterCycle = ( ( uint16 ) 1U << 14U ), /** Stop when counter completes
                                                              a whole cycle       */
    RunMode_FreeRun = ( ( uint16 ) 2U << 14U )             /** Free run             */
} etpwmRunMode_t;

/** @brief Enumeration to define the pulse width modulation (ETPWM) load modes
 */
typedef enum
{
    LoadMode_CtrEqZero = 0U,       /** Load on CTR = Zero              */
    LoadMode_CtrEqPeriod = 1U,     /** Load on CTR = PRD               */
    LoadMode_CtrEqZeroPeriod = 2U, /** Load on CTR = Zero or CTR = PRD */
    LoadMode_Freeze = 3U           /** Freeze (no loads possible)      */
} etpwmLoadMode_t;

/** @brief Enumeration to define the pulse width modulation (ETPWM) trip zone sources
 */
typedef enum
{
    CycleByCycle_TZ1 = ( ( uint16 ) 1U << 0U ),
    CycleByCycle_TZ2 = ( ( uint16 ) 1U << 1U ),
    CycleByCycle_TZ3 = ( ( uint16 ) 1U << 2U ),
    CycleByCycle_TZ4 = ( ( uint16 ) 1U << 3U ),
    CycleByCycle_TZ5 = ( ( uint16 ) 1U << 4U ),
    CycleByCycle_TZ6 = ( ( uint16 ) 1U << 5U ),
    CycleByCycle_DCAEVT2 = ( ( uint16 ) 1U << 6U ),
    CycleByCycle_DCBEVT2 = ( ( uint16 ) 1U << 7U ),
    OneShot_TZ1 = ( ( uint16 ) 1U << 8U ),
    OneShot_TZ2 = ( ( uint16 ) 1U << 9U ),
    OneShot_TZ3 = ( ( uint16 ) 1U << 10U ),
    OneShot_TZ4 = ( ( uint16 ) 1U << 11U ),
    OneShot_TZ5 = ( ( uint16 ) 1U << 12U ),
    OneShot_TZ6 = ( ( uint16 ) 1U << 13U ),
    OneShot_DCAEVT1 = ( ( uint16 ) 1U << 14U ),
    OneShot_DCBEVT1 = ( ( uint16 ) 1U << 15U )
} etpwmTripZoneSrc_t;

/** @brief Enumeration to define the pulse width modulation (ETPWM) trip events
 */
typedef enum
{
    CycleByCycleTrip = ( ( uint16 ) 1U << 1U ), /** Trip Zone Cycle-By-Cycle            */
    OneShotTrip = ( ( uint16 ) 1U << 2U ),      /** TripZone One-shot                   */
    DCAEVT1_inter = ( ( uint16 ) 1U << 3U ),    /** Digital Comparator Output A Event 1 */
    DCAEVT2_inter = ( ( uint16 ) 1U << 4U ),    /** Digital Comparator Output A Event 2 */
    DCBEVT1_inter = ( ( uint16 ) 1U << 5U ),    /** Digital Comparator Output B Event 1 */
    DCBEVT2_inter = ( ( uint16 ) 1U << 6U )     /** Digital Comparator Output B Event 2 */
} etpwmTrip_t;

/** @brief Enumeration to define the sources for EPWMx_INT, SOCA or SOCB
 */
typedef enum
{
    NO_EVENT = 0U,      /** Reserved                                             */
    DCAEVT1 = 0U,       /** DCAEVT1.soc event                                    */
    DCBEVT1 = 0U,       /** DCBEVT1.soc event                                    */
    CTR_ZERO = 1U,      /** Event CTR = Zero                                     */
    CTR_PRD = 2U,       /** Event CTR = PRD                                      */
    CTR_ZERO_PRD = 3U,  /** Event CTR = Zero or CTR = PRD                        */
    CTR_UP_CMPA = 4U,   /** Event CTR = CMPA when when the timer is incrementing */
    CTR_D0WM_CMPA = 5U, /** Event CTR = CMPA when when the timer is decrementing */
    CTR_UP_CMPB = 6U,   /** Event CTR = CMPB when when the timer is incrementing */
    CTR_D0WM_CMPB = 7U  /** Event CTR = CMPB when when the timer is decrementing */
} etpwmEventSrc_t;

/** @brief Enumeration to define the period of EPWMx_INT, SOCA or SOCB
 */
typedef enum
{
    EventPeriod_Disable = 0U,    /** Disable EPWMx_INT/SOCA/SOCB event counter    */
    EventPeriod_FirstEvent = 1U, /** Generate EPWMx_INT/SOCA/SOCB pulse on the first event
                                  */
    EventPeriod_SecondEvent = 2U, /** Generate EPWMx_INT/SOCA/SOCB pulse on the second
                                     event */
    EventPeriod_ThirdEvent = 3U /** Generate EPWMx_INT/SOCA/SOCB pulse on the third event
                                 */
} etpwmEventPeriod_t;

/** @brief Enumeration to define the output events from ETPWMx
 */
typedef enum
{
    Event_Interrupt = 1U, /** EPWM Interrupt        */
    Event_SOCA = 4U,      /** Start Of Conversion A */
    Event_SOCB = 8U       /** Start Of conversion B */
} etpwmEvent_t;

/** @brief Enumeration to define the pulse width modulation (ETPWM) action qualifiers
 *
 *   @note This enum should be use to populate the struct passed as the parameter
 *   to the APIs etpwmSetActionQualPwmA and etpwmSetActionQualPwmB
 */
typedef enum
{
    ActionQual_Disabled = 0U, /** Do nothing (action disabled)           */
    ActionQual_Clear = 1U,    /** Clear: force EPTWMxA/ETPWMB output low */
    ActionQual_Set = 2U,      /** Set: force ETPWMxA/ETPWMxB output high */
    ActionQual_Toggle = 3U,   /** Toggle EPWMxA/ETPWMxB output           */

    ForceSize_ActionQual = 0xFFFFU /** Do not use (Makes sure that etpwmActionQual_t is at
                                      least 16 bits wide)  */
} etpwmActionQual_t;

/** @brief Enumeration to define the DeadBand input mode
 *
 *   @note This enum should be use to populate the struct passed as the parameter
 *   to the API etpwmEnableDeadBand
 */
typedef enum
{
    PWMA_RED_FED = 0x00U, /** Source of Rising edge delay: ETPWMxA, Source of Falling edge
                             delay: ETPWMxA */
    PWMA_FED_PWMB_RED = 0x10U, /** Source of Rising edge delay: ETPWMxB, Source of Falling
                                  edge delay: ETPWMxA */
    PWMA_RED_PWMB_FED = 0x20U, /** Source of Rising edge delay: ETPWMxA, Source of Falling
                                  edge delay: ETPWMxB */
    PWMB_RED_FED = 0x30U, /** Source of Rising edge delay: ETPWMxB, Source of Falling edge
                             delay: ETPWMxB */

    ForceSize_DBInput = 0xFFFFU /** Do not use (Makes sure that etpwmDeadBandInputMode_t
                                   is at least 16 bits wide)  */
} etpwmDeadBandInputMode_t;

/** @brief Enumeration to define the DeadBand output mode
 *
 *   @note This enum should be use to populate the struct passed as the parameter
 *   to the API etpwmEnableDeadBand
 */
typedef enum
{
    PWMA_PWMB_NIL = 0U, /** Deadband generation is bypassed for both output signals     */
    PWMA_NIL_PWMB_FED = 1U, /** Disable rising-edge delay. The falling-edge delayed signal
                               is seen on output EPWMxB.          */
    PWMA_RED_PWMB_NIL = 2U, /** Disable falling-edge delay. The rising-edge delayed signal
                               is seen on output EPWMxA.          */
    PWMB_FED_PWMA_RED = 3U, /** Rising-edge delayed signal on output EPWMxA and
                               falling-edge delayed signal on output EPWMxB. */

    ForceSize_DBOutput = 0xFFFFU /** Do not use (Makes sure that etpwmDeadBandOutputMode_t
                                    is at least 16 bits wide)  */
} etpwmDeadBandOutputMode_t;

/** @brief Enumeration to define the DeadBand polarity
 *
 *   @note This enum should be use to populate the struct passed as the parameter
 *   to the API etpwmEnableDeadBand
 *
 */
typedef enum
{
    DisableInvert = ( ( uint16 ) 0U << 2U ), /** Neither EPWMxA nor EPWMxB is inverted */
    Invert_PWMA = ( ( uint16 ) 1U << 2U ),   /** EPWMxA is inverted                    */
    Invert_PWMB = ( ( uint16 ) 2U << 2U ),   /** EPWMxB is inverted                    */
    Invert_PWMA_PWMB = ( ( uint16 ) 3U << 2U ), /** Both EPWMxA and EPWMxB are inverted */

    ForceSize_DBPol = 0xFFFFU /** Do not use (Makes sure that etpwmDeadBandPolarity_t is
                                 at least 16 bits wide)  */
} etpwmDeadBandPolarity_t;

/** @brief Enumeration to define the action on EPWMA/EPWMB when a trip event happens
 *
 *   @note This enum should be use to populate the struct passed as the parameter
 *   to the API etpwmSetTripAction
 *
 */
typedef enum
{
    TripZoneState_HighImp = 0U,   /** High-Impedance state */
    TripZoneState_EPWM_High = 1U, /** Force to High state  */
    TripZoneState_EPWM_Low = 2U,  /** Force to Low state   */
    TripZoneState_DoNothing = 3U, /** Do nothing           */

    ForceSize_TripZoneState = 0xFFFFU /** Do not use (Makes sure that etpwmTripZoneState_t
                                         is at least 16 bits wide)  */
} etpwmTripZoneState_t;

/** @brief Enumeration to define One-Shot Pulse Width in chopper submodule
 *
 *   @note This enum should be use to populate the struct passed as the parameter
 *   to the API etpwmEnableChopping
 *
 */
typedef enum
{
    ChoppingPulseWidth_8_VCLK4 = ( ( uint16 ) 0U << 1U ),    /** 1 x VCLK4/8 wide  */
    ChoppingPulseWidth_16_VCLK4 = ( ( uint16 ) 1U << 1U ),   /** 2 x VCLK4/8 wide  */
    ChoppingPulseWidth_24_VCLK4 = ( ( uint16 ) 2U << 1U ),   /** 3 x VCLK4/8 wide  */
    ChoppingPulseWidth_32_VCLK4 = ( ( uint16 ) 3U << 1U ),   /** 4 x VCLK4/8 wide  */
    ChoppingPulseWidth_40_VCLK4 = ( ( uint16 ) 4U << 1U ),   /** 5 x VCLK4/8 wide  */
    ChoppingPulseWidth_48_VCLK4 = ( ( uint16 ) 5U << 1U ),   /** 6 x VCLK4/8 wide  */
    ChoppingPulseWidth_56_VCLK4 = ( ( uint16 ) 6U << 1U ),   /** 7 x VCLK4/8 wide  */
    ChoppingPulseWidth_64_VCLK4 = ( ( uint16 ) 7U << 1U ),   /** 8 x VCLK4/8 wide  */
    ChoppingPulseWidth_72_VCLK4 = ( ( uint16 ) 8U << 1U ),   /** 9 x VCLK4/8 wide  */
    ChoppingPulseWidth_80_VCLK4 = ( ( uint16 ) 9U << 1U ),   /** 10 x VCLK4/8 wide */
    ChoppingPulseWidth_88_VCLK4 = ( ( uint16 ) 10U << 1U ),  /** 11 x VCLK4/8 wide */
    ChoppingPulseWidth_96_VCLK4 = ( ( uint16 ) 11U << 1U ),  /** 12 x VCLK4/8 wide */
    ChoppingPulseWidth_104_VCLK4 = ( ( uint16 ) 12U << 1U ), /** 13 x VCLK4/8 wide */
    ChoppingPulseWidth_112_VCLK4 = ( ( uint16 ) 13U << 1U ), /** 14 x VCLK4/8 wide */
    ChoppingPulseWidth_120_VCLK4 = ( ( uint16 ) 14U << 1U ), /** 15 x VCLK4/8 wide */
    ChoppingPulseWidth_128_VCLK4 = ( ( uint16 ) 15U << 1U ), /** 16 x VCLK4/8 wide */

    ForceSize_ChopPulseWidth = 0xFFFFU /** Do not use (Makes sure that
                                          etpwmChoppingPulseWidth_t is at least 16 bits
                                          wide)  */
} etpwmChoppingPulseWidth_t;

/** @brief Enumeration to define Chopping Clock Frequency
 *
 *   @note This enum should be use to populate the struct passed as the parameter
 *   to the API etpwmEnableChopping
 *
 */
typedef enum
{
    ChoppingClkFreq_VCLK4_by_8 = ( ( uint16 ) 0U << 5U ),  /** VCLK4/8 divided by 1 */
    ChoppingClkFreq_VCLK4_by_16 = ( ( uint16 ) 1U << 5U ), /** VCLK4/8 divided by 2 */
    ChoppingClkFreq_VCLK4_by_24 = ( ( uint16 ) 2U << 5U ), /** VCLK4/8 divided by 3 */
    ChoppingClkFreq_VCLK4_by_32 = ( ( uint16 ) 3U << 5U ), /** VCLK4/8 divided by 4 */
    ChoppingClkFreq_VCLK4_by_40 = ( ( uint16 ) 4U << 5U ), /** VCLK4/8 divided by 5 */
    ChoppingClkFreq_VCLK4_by_48 = ( ( uint16 ) 5U << 5U ), /** VCLK4/8 divided by 6 */
    ChoppingClkFreq_VCLK4_by_56 = ( ( uint16 ) 6U << 5U ), /** VCLK4/8 divided by 7 */
    ChoppingClkFreq_VCLK4_by_64 = ( ( uint16 ) 7U << 5U ), /** VCLK4/8 divided by 8 */

    ForceSize_ChopClkFreq = 0xFFFFU /** Do not use (Makes sure that etpwmChoppingClkFreq_t
                                       is at least 16 bits wide)  */
} etpwmChoppingClkFreq_t;

/** @brief Enumeration to define Chopping Clock duty cycle
 *
 *   @note This enum should be use to populate the struct passed as the parameter
 *   to the API etpwmEnableChopping
 *
 */
typedef enum
{
    ChoppingDutyCycle_One_Eighth = 0x0000U,    /** Duty = 1/8 (12.5%) */
    ChoppingDutyCycle_Two_Eighths = 0x0100U,   /** Duty = 2/8 (25.0%) */
    ChoppingDutyCycle_Three_Eighths = 0x0200U, /** Duty = 3/8 (37.5%) */
    ChoppingDutyCycle_Four_Eighths = 0x0300U,  /** Duty = 4/8 (50.0%) */
    ChoppingDutyCycle_Five_Eighths = 0x0400U,  /** Duty = 5/8 (62.5%) */
    ChoppingDutyCycle_Six_Eighths = 0x0500U,   /** Duty = 6/8 (75.0%) */
    ChoppingDutyCycle_Seven_Eighths = 0x0600U, /** Duty = 7/8 (87.5%) */

    ForceSize_ChopDuty = 0xFFFFU /** Do not use (Makes sure that etpwmChoppingDutyCycle_t
                                    is at least 16 bits wide)  */
} etpwmChoppingDutyCycle_t;

/** @brief Enumeration to define Digital Compare Input
 *
 *   @note This enum should be use to populate the struct passed as the parameter
 *   to the API etpwmEnableDigitalCompareEvents
 *
 */
typedef enum
{
    TZ1 = 0U,
    TZ2 = 1U,
    TZ3 = 2U,

    ForceSize_DCInput = 0xFFFFU /** Do not use (Makes sure that etpwmDCInput_t is at least
                                   16 bits wide)  */
} etpwmDCInput_t;

/** @brief Enumeration to define Digital Compare Output selection
 *
 *   @note This enum should be use to populate the struct passed as the parameter
 *   to the API etpwmEnableDigitalCompareEvents.
 *   @note DCAH_Low, DCAH_High, DCAL_Low, DCAL_High, DCAL_High_DCAH_Low should be used
 * only for selecting DCAEVT1_event and DCAEVT2_event and DCBH_Low, DCBH_High, DCBL_Low,
 * DCBL_High, DCBL_High_DCBH_Low should be used only for selecting DCBEVT1_event and
 * DCBEVT2_event
 *
 */
typedef enum
{
    Event_Disabled = 0U, /** Event Disabled */

    DCAH_Low = 1U,           /** DCAEVTx selection : DCAH = low,  DCAL = don't care  */
    DCAH_High = 2U,          /** DCAEVTx selection : DCAH = high, DCAL = don't care  */
    DCAL_Low = 3U,           /** DCAEVTx selection : DCAL = low,  DCAH = don't care  */
    DCAL_High = 4U,          /** DCAEVTx selection : DCAL = high, DCAH = don't care  */
    DCAL_High_DCAH_Low = 5U, /** DCAEVTx selection : DCAL = high, DCAH = low         */

    DCBH_Low = 1U,           /** DCBEVTx selection : DCBH = low,  DCBL = don't care  */
    DCBH_High = 2U,          /** DCBEVTx selection : DCBH = high, DCBL = don't care  */
    DCBL_Low = 3U,           /** DCBEVTx selection : DCBL = low,  DCBH = don't care  */
    DCBL_High = 4U,          /** DCBEVTx selection : DCBL = high, DCBH = don't care  */
    DCBL_High_DCBH_low = 5U, /** DCBEVTx selection : DCBL = high, DCBH = low         */

    ForceSize_DCSelect = 0xFFFFU /** Do not use (Makes sure that etpwmDCInput_t is at
                                    least 16 bits wide)  */
} etpwmDCOutputSelect_t;

/** @brief ETPWMx Action Qualifier configuration
 */
typedef struct
{
    etpwmActionQual_t CtrEqZero_Action;
    etpwmActionQual_t CtrEqPeriod_Action;
    etpwmActionQual_t CtrEqCmpAUp_Action;
    etpwmActionQual_t CtrEqCmpADown_Action;
    etpwmActionQual_t CtrEqCmpBUp_Action;
    etpwmActionQual_t CtrEqCmpBDown_Action;
} etpwmActionQualConfig_t;

/** @brief ETPWMx Deadband configuration
 */
typedef struct
{
    etpwmDeadBandInputMode_t inputmode;
    etpwmDeadBandOutputMode_t outputmode;
    etpwmDeadBandPolarity_t polarity;
    boolean halfCycleEnable;
} etpwmDeadBandConfig_t;

/** @brief ETPWMx Chopper configuration
 */
typedef struct
{
    etpwmChoppingPulseWidth_t oswdth;
    etpwmChoppingClkFreq_t freq;
    etpwmChoppingDutyCycle_t duty;
} etpwmChoppingConfig_t;

/** @brief ETPWMx Trip action configuration
 */
typedef struct
{
    etpwmTripZoneState_t TripEvent_ActionOnPWMA;
    etpwmTripZoneState_t TripEvent_ActionOnPWMB;
    etpwmTripZoneState_t DCAEVT1_ActionOnPWMA;
    etpwmTripZoneState_t DCAEVT2_ActionOnPWMA;
    etpwmTripZoneState_t DCBEVT1_ActionOnPWMB;
    etpwmTripZoneState_t DCBEVT2_ActionOnPWMB;
} etpwmTripActionConfig_t;

/** @brief ETPWMx Digital Compare configuration
 */
typedef struct
{
    etpwmDCInput_t DCAH_src;
    etpwmDCInput_t DCAL_src;
    etpwmDCInput_t DCBH_src;
    etpwmDCInput_t DCBL_src;
    etpwmDCOutputSelect_t DCAEVT1_event;
    etpwmDCOutputSelect_t DCAEVT2_event;
    etpwmDCOutputSelect_t DCBEVT1_event;
    etpwmDCOutputSelect_t DCBEVT2_event;
} etpwmDigitalCompareConfig_t;

typedef struct etpwm_config_reg
{
    uint16 CONFIG_TBCTL;
    uint16 CONFIG_TBPHS;
    uint16 CONFIG_TBPRD;
    uint16 CONFIG_CMPCTL;
    uint16 CONFIG_CMPA;
    uint16 CONFIG_CMPB;
    uint16 CONFIG_AQCTLA;
    uint16 CONFIG_AQCTLB;
    uint16 CONFIG_DBCTL;
    uint16 CONFIG_DBRED;
    uint16 CONFIG_DBFED;
    uint16 CONFIG_TZSEL;
    uint16 CONFIG_TZDCSEL;
    uint16 CONFIG_TZCTL;
    uint16 CONFIG_TZEINT;
    uint16 CONFIG_ETSEL;
    uint16 CONFIG_ETPS;
    uint16 CONFIG_PCCTL;
    uint16 CONFIG_DCTRIPSEL;
    uint16 CONFIG_DCACTL;
    uint16 CONFIG_DCBCTL;
    uint16 CONFIG_DCFCTL;
    uint16 CONFIG_DCCAPCTL;
    uint16 CONFIG_DCFWINDOW;
    uint16 CONFIG_DCFWINDOWCNT;
} etpwm_config_reg_t;

#define ETPWM1_TBCTL_CONFIGVALUE \
    ( ( uint16 ) ( ( uint16 ) 0U << 7U ) | ( uint16 ) ( ( uint16 ) 0U << 10U ) )
#define ETPWM1_TBPHS_CONFIGVALUE  0x00000000U
#define ETPWM1_TBPRD_CONFIGVALUE  1000U
#define ETPWM1_CMPCTL_CONFIGVALUE 0x00000000U
#define ETPWM1_CMPA_CONFIGVALUE   50U
#define ETPWM1_CMPB_CONFIGVALUE   50U
#define ETPWM1_AQCTLA_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) )
#define ETPWM1_AQCTLB_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) )
#define ETPWM1_DBCTL_CONFIGVALUE                                                \
    ( ( uint16 ) ( ( uint16 ) 0U << 5U ) | ( uint16 ) ( ( uint16 ) 0u << 4U )   \
      | ( uint16 ) ( ( uint16 ) 0U << 3U ) | ( uint16 ) ( ( uint16 ) 0U << 2U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 1U ) | ( uint16 ) ( ( uint16 ) 0U << 0U ) )
#define ETPWM1_DBRED_CONFIGVALUE 1U
#define ETPWM1_DBFED_CONFIGVALUE 1U
#define ETPWM1_TZSEL_CONFIGVALUE                                                    \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U \
      | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM1_TZDCSEL_CONFIGVALUE 0x00000000U
#define ETPWM1_TZCTL_CONFIGVALUE   0x00000000U
#define ETPWM1_TZEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM1_ETSEL_CONFIGVALUE                                                  \
    ( ( ( ( uint16 ) NO_EVENT == 0U ) ? 0x0000U : 0x0008U ) | ( uint16 ) NO_EVENT \
      | ( uint16 ) 0x0000U | ( uint16 ) 0x0000U                                   \
      | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )                                   \
      | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U ) )
#define ETPWM1_ETPS_CONFIGVALUE \
    ( 1U | ( uint16 ) ( ( uint16 ) 1U << 8U ) | ( uint16 ) ( ( uint16 ) 1U << 12U ) )
#define ETPWM1_PCCTL_CONFIGVALUE                                              \
    ( ( uint16 ) ( ( uint16 ) 0U << 0U ) | ( uint16 ) ( ( uint16 ) 1U << 1U ) \
      | ( uint16 ) ( ( uint16 ) 3U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 5U ) )
#define ETPWM1_DCTRIPSEL_CONFIGVALUE    0x00000000U
#define ETPWM1_DCACTL_CONFIGVALUE       0x00000000U
#define ETPWM1_DCBCTL_CONFIGVALUE       0x00000000U
#define ETPWM1_DCFCTL_CONFIGVALUE       0x00000000U
#define ETPWM1_DCCAPCTL_CONFIGVALUE     0x00000000U
#define ETPWM1_DCFWINDOW_CONFIGVALUE    0x00000000U
#define ETPWM1_DCFWINDOWCNT_CONFIGVALUE 0x00000000U

#define ETPWM2_TBCTL_CONFIGVALUE \
    ( ( uint16 ) ( ( uint16 ) 0U << 7U ) | ( uint16 ) ( ( uint16 ) 0U << 10U ) )
#define ETPWM2_TBPHS_CONFIGVALUE  0x00000000U
#define ETPWM2_TBPRD_CONFIGVALUE  1000U
#define ETPWM2_CMPCTL_CONFIGVALUE 0x00000000U
#define ETPWM2_CMPA_CONFIGVALUE   50U
#define ETPWM2_CMPB_CONFIGVALUE   50U
#define ETPWM2_AQCTLA_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) )
#define ETPWM2_AQCTLB_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) )
#define ETPWM2_DBCTL_CONFIGVALUE                                                \
    ( ( uint16 ) ( ( uint16 ) 0U << 5U ) | ( uint16 ) ( ( uint16 ) 0u << 4U )   \
      | ( uint16 ) ( ( uint16 ) 0U << 3U ) | ( uint16 ) ( ( uint16 ) 0U << 2U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 1U ) | ( uint16 ) ( ( uint16 ) 0U << 0U ) )
#define ETPWM2_DBRED_CONFIGVALUE 1U
#define ETPWM2_DBFED_CONFIGVALUE 1U
#define ETPWM2_TZSEL_CONFIGVALUE                                                    \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U \
      | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM2_TZDCSEL_CONFIGVALUE 0x00000000U
#define ETPWM2_TZCTL_CONFIGVALUE   0x00000000U
#define ETPWM2_TZEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM2_ETSEL_CONFIGVALUE                                                  \
    ( ( ( ( uint16 ) NO_EVENT == 0U ) ? 0x0000U : 0x0008U ) | ( uint16 ) NO_EVENT \
      | ( uint16 ) 0x0000U | ( uint16 ) 0x0000U                                   \
      | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )                                   \
      | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U ) )
#define ETPWM2_ETPS_CONFIGVALUE \
    ( 1U | ( uint16 ) ( ( uint16 ) 1U << 8U ) | ( uint16 ) ( ( uint16 ) 1U << 12U ) )
#define ETPWM2_PCCTL_CONFIGVALUE                                              \
    ( ( uint16 ) ( ( uint16 ) 0U << 0U ) | ( uint16 ) ( ( uint16 ) 1U << 1U ) \
      | ( uint16 ) ( ( uint16 ) 3U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 5U ) )
#define ETPWM2_DCTRIPSEL_CONFIGVALUE    0x00000000U
#define ETPWM2_DCACTL_CONFIGVALUE       0x00000000U
#define ETPWM2_DCBCTL_CONFIGVALUE       0x00000000U
#define ETPWM2_DCFCTL_CONFIGVALUE       0x00000000U
#define ETPWM2_DCCAPCTL_CONFIGVALUE     0x00000000U
#define ETPWM2_DCFWINDOW_CONFIGVALUE    0x00000000U
#define ETPWM2_DCFWINDOWCNT_CONFIGVALUE 0x00000000U

#define ETPWM3_TBCTL_CONFIGVALUE \
    ( ( uint16 ) ( ( uint16 ) 0U << 7U ) | ( uint16 ) ( ( uint16 ) 0U << 10U ) )
#define ETPWM3_TBPHS_CONFIGVALUE  0x00000000U
#define ETPWM3_TBPRD_CONFIGVALUE  1000U
#define ETPWM3_CMPCTL_CONFIGVALUE 0x00000000U
#define ETPWM3_CMPA_CONFIGVALUE   50U
#define ETPWM3_CMPB_CONFIGVALUE   50U
#define ETPWM3_AQCTLA_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) )
#define ETPWM3_AQCTLB_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) )
#define ETPWM3_DBCTL_CONFIGVALUE                                                \
    ( ( uint16 ) ( ( uint16 ) 0U << 5U ) | ( uint16 ) ( ( uint16 ) 0u << 4U )   \
      | ( uint16 ) ( ( uint16 ) 0U << 3U ) | ( uint16 ) ( ( uint16 ) 0U << 2U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 1U ) | ( uint16 ) ( ( uint16 ) 0U << 0U ) )
#define ETPWM3_DBRED_CONFIGVALUE 1U
#define ETPWM3_DBFED_CONFIGVALUE 1U
#define ETPWM3_TZSEL_CONFIGVALUE                                                    \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U \
      | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM3_TZDCSEL_CONFIGVALUE 0x00000000U
#define ETPWM3_TZCTL_CONFIGVALUE   0x00000000U
#define ETPWM3_TZEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM3_ETSEL_CONFIGVALUE                                                  \
    ( ( ( ( uint16 ) NO_EVENT == 0U ) ? 0x0000U : 0x0008U ) | ( uint16 ) NO_EVENT \
      | ( uint16 ) 0x0000U | ( uint16 ) 0x0000U                                   \
      | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )                                   \
      | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U ) )
#define ETPWM3_ETPS_CONFIGVALUE \
    ( 1U | ( uint16 ) ( ( uint16 ) 1U << 8U ) | ( uint16 ) ( ( uint16 ) 1U << 12U ) )
#define ETPWM3_PCCTL_CONFIGVALUE                                              \
    ( ( uint16 ) ( ( uint16 ) 0U << 0U ) | ( uint16 ) ( ( uint16 ) 1U << 1U ) \
      | ( uint16 ) ( ( uint16 ) 3U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 5U ) )
#define ETPWM3_DCTRIPSEL_CONFIGVALUE    0x00000000U
#define ETPWM3_DCACTL_CONFIGVALUE       0x00000000U
#define ETPWM3_DCBCTL_CONFIGVALUE       0x00000000U
#define ETPWM3_DCFCTL_CONFIGVALUE       0x00000000U
#define ETPWM3_DCCAPCTL_CONFIGVALUE     0x00000000U
#define ETPWM3_DCFWINDOW_CONFIGVALUE    0x00000000U
#define ETPWM3_DCFWINDOWCNT_CONFIGVALUE 0x00000000U

#define ETPWM4_TBCTL_CONFIGVALUE \
    ( ( uint16 ) ( ( uint16 ) 0U << 7U ) | ( uint16 ) ( ( uint16 ) 0U << 10U ) )
#define ETPWM4_TBPHS_CONFIGVALUE  0x00000000U
#define ETPWM4_TBPRD_CONFIGVALUE  1000U
#define ETPWM4_CMPCTL_CONFIGVALUE 0x00000000U
#define ETPWM4_CMPA_CONFIGVALUE   50U
#define ETPWM4_CMPB_CONFIGVALUE   50U
#define ETPWM4_AQCTLA_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) )
#define ETPWM4_AQCTLB_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) )
#define ETPWM4_DBCTL_CONFIGVALUE                                                \
    ( ( uint16 ) ( ( uint16 ) 0U << 5U ) | ( uint16 ) ( ( uint16 ) 0u << 4U )   \
      | ( uint16 ) ( ( uint16 ) 0U << 3U ) | ( uint16 ) ( ( uint16 ) 0U << 2U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 1U ) | ( uint16 ) ( ( uint16 ) 0U << 0U ) )
#define ETPWM4_DBRED_CONFIGVALUE 1U
#define ETPWM4_DBFED_CONFIGVALUE 1U
#define ETPWM4_TZSEL_CONFIGVALUE                                                    \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U \
      | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM4_TZDCSEL_CONFIGVALUE 0x00000000U
#define ETPWM4_TZCTL_CONFIGVALUE   0x00000000U
#define ETPWM4_TZEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM4_ETSEL_CONFIGVALUE                                                  \
    ( ( ( ( uint16 ) NO_EVENT == 0U ) ? 0x0000U : 0x0008U ) | ( uint16 ) NO_EVENT \
      | ( uint16 ) 0x0000U | ( uint16 ) 0x0000U                                   \
      | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )                                   \
      | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U ) )
#define ETPWM4_ETPS_CONFIGVALUE \
    ( 1U | ( uint16 ) ( ( uint16 ) 1U << 8U ) | ( uint16 ) ( ( uint16 ) 1U << 12U ) )
#define ETPWM4_PCCTL_CONFIGVALUE                                              \
    ( ( uint16 ) ( ( uint16 ) 0U << 0U ) | ( uint16 ) ( ( uint16 ) 1U << 1U ) \
      | ( uint16 ) ( ( uint16 ) 3U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 5U ) )
#define ETPWM4_DCTRIPSEL_CONFIGVALUE    0x00000000U
#define ETPWM4_DCACTL_CONFIGVALUE       0x00000000U
#define ETPWM4_DCBCTL_CONFIGVALUE       0x00000000U
#define ETPWM4_DCFCTL_CONFIGVALUE       0x00000000U
#define ETPWM4_DCCAPCTL_CONFIGVALUE     0x00000000U
#define ETPWM4_DCFWINDOW_CONFIGVALUE    0x00000000U
#define ETPWM4_DCFWINDOWCNT_CONFIGVALUE 0x00000000U

#define ETPWM5_TBCTL_CONFIGVALUE \
    ( ( uint16 ) ( ( uint16 ) 0U << 7U ) | ( uint16 ) ( ( uint16 ) 0U << 10U ) )
#define ETPWM5_TBPHS_CONFIGVALUE  0x00000000U
#define ETPWM5_TBPRD_CONFIGVALUE  1000U
#define ETPWM5_CMPCTL_CONFIGVALUE 0x00000000U
#define ETPWM5_CMPA_CONFIGVALUE   50U
#define ETPWM5_CMPB_CONFIGVALUE   50U
#define ETPWM5_AQCTLA_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) )
#define ETPWM5_AQCTLB_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) )
#define ETPWM5_DBCTL_CONFIGVALUE                                                \
    ( ( uint16 ) ( ( uint16 ) 0U << 5U ) | ( uint16 ) ( ( uint16 ) 0u << 4U )   \
      | ( uint16 ) ( ( uint16 ) 0U << 3U ) | ( uint16 ) ( ( uint16 ) 0U << 2U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 1U ) | ( uint16 ) ( ( uint16 ) 0U << 0U ) )
#define ETPWM5_DBRED_CONFIGVALUE 1U
#define ETPWM5_DBFED_CONFIGVALUE 1U
#define ETPWM5_TZSEL_CONFIGVALUE                                                    \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U \
      | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM5_TZDCSEL_CONFIGVALUE 0x00000000U
#define ETPWM5_TZCTL_CONFIGVALUE   0x00000000U
#define ETPWM5_TZEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM5_ETSEL_CONFIGVALUE                                                  \
    ( ( ( ( uint16 ) NO_EVENT == 0U ) ? 0x0000U : 0x0008U ) | ( uint16 ) NO_EVENT \
      | ( uint16 ) 0x0000U | ( uint16 ) 0x0000U                                   \
      | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )                                   \
      | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U ) )
#define ETPWM5_ETPS_CONFIGVALUE \
    ( 1U | ( uint16 ) ( ( uint16 ) 1U << 8U ) | ( uint16 ) ( ( uint16 ) 1U << 12U ) )
#define ETPWM5_PCCTL_CONFIGVALUE                                              \
    ( ( uint16 ) ( ( uint16 ) 0U << 0U ) | ( uint16 ) ( ( uint16 ) 1U << 1U ) \
      | ( uint16 ) ( ( uint16 ) 3U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 5U ) )
#define ETPWM5_DCTRIPSEL_CONFIGVALUE    0x00000000U
#define ETPWM5_DCACTL_CONFIGVALUE       0x00000000U
#define ETPWM5_DCBCTL_CONFIGVALUE       0x00000000U
#define ETPWM5_DCFCTL_CONFIGVALUE       0x00000000U
#define ETPWM5_DCCAPCTL_CONFIGVALUE     0x00000000U
#define ETPWM5_DCFWINDOW_CONFIGVALUE    0x00000000U
#define ETPWM5_DCFWINDOWCNT_CONFIGVALUE 0x00000000U

#define ETPWM6_TBCTL_CONFIGVALUE \
    ( ( uint16 ) ( ( uint16 ) 0U << 7U ) | ( uint16 ) ( ( uint16 ) 0U << 10U ) )
#define ETPWM6_TBPHS_CONFIGVALUE  0x00000000U
#define ETPWM6_TBPRD_CONFIGVALUE  1000U
#define ETPWM6_CMPCTL_CONFIGVALUE 0x00000000U
#define ETPWM6_CMPA_CONFIGVALUE   50U
#define ETPWM6_CMPB_CONFIGVALUE   50U
#define ETPWM6_AQCTLA_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) )
#define ETPWM6_AQCTLB_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) )
#define ETPWM6_DBCTL_CONFIGVALUE                                                \
    ( ( uint16 ) ( ( uint16 ) 0U << 5U ) | ( uint16 ) ( ( uint16 ) 0u << 4U )   \
      | ( uint16 ) ( ( uint16 ) 0U << 3U ) | ( uint16 ) ( ( uint16 ) 0U << 2U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 1U ) | ( uint16 ) ( ( uint16 ) 0U << 0U ) )
#define ETPWM6_DBRED_CONFIGVALUE 1U
#define ETPWM6_DBFED_CONFIGVALUE 1U
#define ETPWM6_TZSEL_CONFIGVALUE                                                    \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U \
      | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM6_TZDCSEL_CONFIGVALUE 0x00000000U
#define ETPWM6_TZCTL_CONFIGVALUE   0x00000000U
#define ETPWM6_TZEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM6_ETSEL_CONFIGVALUE                                                  \
    ( ( ( ( uint16 ) NO_EVENT == 0U ) ? 0x0000U : 0x0008U ) | ( uint16 ) NO_EVENT \
      | ( uint16 ) 0x0000U | ( uint16 ) 0x0000U                                   \
      | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )                                   \
      | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U ) )
#define ETPWM6_ETPS_CONFIGVALUE \
    ( 1U | ( uint16 ) ( ( uint16 ) 1U << 8U ) | ( uint16 ) ( ( uint16 ) 1U << 12U ) )
#define ETPWM6_PCCTL_CONFIGVALUE                                              \
    ( ( uint16 ) ( ( uint16 ) 0U << 0U ) | ( uint16 ) ( ( uint16 ) 1U << 1U ) \
      | ( uint16 ) ( ( uint16 ) 3U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 5U ) )
#define ETPWM6_DCTRIPSEL_CONFIGVALUE    0x00000000U
#define ETPWM6_DCACTL_CONFIGVALUE       0x00000000U
#define ETPWM6_DCBCTL_CONFIGVALUE       0x00000000U
#define ETPWM6_DCFCTL_CONFIGVALUE       0x00000000U
#define ETPWM6_DCCAPCTL_CONFIGVALUE     0x00000000U
#define ETPWM6_DCFWINDOW_CONFIGVALUE    0x00000000U
#define ETPWM6_DCFWINDOWCNT_CONFIGVALUE 0x00000000U

#define ETPWM7_TBCTL_CONFIGVALUE \
    ( ( uint16 ) ( ( uint16 ) 0U << 7U ) | ( uint16 ) ( ( uint16 ) 0U << 10U ) )
#define ETPWM7_TBPHS_CONFIGVALUE  0x00000000U
#define ETPWM7_TBPRD_CONFIGVALUE  1000U
#define ETPWM7_CMPCTL_CONFIGVALUE 0x00000000U
#define ETPWM7_CMPA_CONFIGVALUE   50U
#define ETPWM7_CMPB_CONFIGVALUE   50U
#define ETPWM7_AQCTLA_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 4U ) )
#define ETPWM7_AQCTLB_CONFIGVALUE                    \
    ( ( uint16 ) ( ( uint16 ) ActionQual_Set << 0U ) \
      | ( uint16 ) ( ( uint16 ) ActionQual_Clear << 8U ) )
#define ETPWM7_DBCTL_CONFIGVALUE                                                \
    ( ( uint16 ) ( ( uint16 ) 0U << 5U ) | ( uint16 ) ( ( uint16 ) 0u << 4U )   \
      | ( uint16 ) ( ( uint16 ) 0U << 3U ) | ( uint16 ) ( ( uint16 ) 0U << 2U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 1U ) | ( uint16 ) ( ( uint16 ) 0U << 0U ) )
#define ETPWM7_DBRED_CONFIGVALUE 1U
#define ETPWM7_DBFED_CONFIGVALUE 1U
#define ETPWM7_TZSEL_CONFIGVALUE                                                    \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U \
      | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM7_TZDCSEL_CONFIGVALUE 0x00000000U
#define ETPWM7_TZCTL_CONFIGVALUE   0x00000000U
#define ETPWM7_TZEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )
#define ETPWM7_ETSEL_CONFIGVALUE                                                  \
    ( ( ( ( uint16 ) NO_EVENT == 0U ) ? 0x0000U : 0x0008U ) | ( uint16 ) NO_EVENT \
      | ( uint16 ) 0x0000U | ( uint16 ) 0x0000U                                   \
      | ( uint16 ) ( ( uint16 ) DCAEVT1 << 8U )                                   \
      | ( uint16 ) ( ( uint16 ) DCBEVT1 << 12U ) )
#define ETPWM7_ETPS_CONFIGVALUE \
    ( 1U | ( uint16 ) ( ( uint16 ) 1U << 8U ) | ( uint16 ) ( ( uint16 ) 1U << 12U ) )
#define ETPWM7_PCCTL_CONFIGVALUE                                              \
    ( ( uint16 ) ( ( uint16 ) 0U << 0U ) | ( uint16 ) ( ( uint16 ) 1U << 1U ) \
      | ( uint16 ) ( ( uint16 ) 3U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 5U ) )
#define ETPWM7_DCTRIPSEL_CONFIGVALUE    0x00000000U
#define ETPWM7_DCACTL_CONFIGVALUE       0x00000000U
#define ETPWM7_DCBCTL_CONFIGVALUE       0x00000000U
#define ETPWM7_DCFCTL_CONFIGVALUE       0x00000000U
#define ETPWM7_DCCAPCTL_CONFIGVALUE     0x00000000U
#define ETPWM7_DCFWINDOW_CONFIGVALUE    0x00000000U
#define ETPWM7_DCFWINDOWCNT_CONFIGVALUE 0x00000000U

/**
 *  @defgroup ePWM ePWM
 *  @brief Enhanced Pulse Width Modulator.
 *
 *  The enhanced pulse width modulator (ePWM) peripheral is a key element in controlling
 * many of the power electronic systems found in both commercial and industrial
 * equipments. The features supported by the ePWM make it especially suitable for digital
 * motor control.
 *
 *    Related Files
 *   - reg_etpwm.h
 *   - etpwm.h
 *   - etpwm.c
 *  @addtogroup ePWM
 *  @{
 */
void etpwmInit( void );
void etpwmStartTBCLK( void );
void etpwmStopTBCLK( void );

void etpwmSetClkDiv( etpwmBASE_t * etpwm,
                     etpwmClkDiv_t clkdiv,
                     etpwmHspClkDiv_t hspclkdiv );
void etpwmSetTimebasePeriod( etpwmBASE_t * etpwm, uint16 period );
void etpwmSetCount( etpwmBASE_t * etpwm, uint16 count );
void etpwmDisableTimebasePeriodShadowMode( etpwmBASE_t * etpwm );
void etpwmEnableTimebasePeriodShadowMode( etpwmBASE_t * etpwm );
void etpwmEnableCounterLoadOnSync( etpwmBASE_t * etpwm, uint16 phase, uint16 direction );
void etpwmDisableCounterLoadOnSync( etpwmBASE_t * etpwm );
void etpwmSetSyncOut( etpwmBASE_t * etpwm, etpwmSyncOut_t syncOutSrc );
void etpwmSetCounterMode( etpwmBASE_t * etpwm, etpwmCounterMode_t countermode );
void etpwmTriggerSWSync( etpwmBASE_t * etpwm );
void etpwmSetRunMode( etpwmBASE_t * etpwm, etpwmRunMode_t runmode );

void etpwmSetCmpA( etpwmBASE_t * etpwm, uint16 value );
void etpwmSetCmpB( etpwmBASE_t * etpwm, uint16 value );
void etpwmEnableCmpAShadowMode( etpwmBASE_t * etpwm, etpwmLoadMode_t loadmode );
void etpwmDisableCmpAShadowMode( etpwmBASE_t * etpwm );
void etpwmEnableCmpBShadowMode( etpwmBASE_t * etpwm, etpwmLoadMode_t loadmode );
void etpwmDisableCmpBShadowMode( etpwmBASE_t * etpwm );

void etpwmSetActionQualPwmA( etpwmBASE_t * etpwm,
                             etpwmActionQualConfig_t actionqualconfig );
void etpwmSetActionQualPwmB( etpwmBASE_t * etpwm,
                             etpwmActionQualConfig_t actionqualconfig );

void etpwmEnableDeadBand( etpwmBASE_t * etpwm, etpwmDeadBandConfig_t deadbandconfig );
void etpwmDisableDeadband( etpwmBASE_t * etpwm );
void etpwmSetDeadBandDelay( etpwmBASE_t * etpwm, uint16 Rdelay, uint16 Fdelay );

void etpwmEnableChopping( etpwmBASE_t * etpwm, etpwmChoppingConfig_t choppingconfig );
void etpwmDisableChopping( etpwmBASE_t * etpwm );

void etpwmEnableTripZoneSources( etpwmBASE_t * etpwm, etpwmTripZoneSrc_t sources );
void etpwmDisableTripZoneSources( etpwmBASE_t * etpwm, etpwmTripZoneSrc_t sources );
void etpwmSetTripAction( etpwmBASE_t * etpwm, etpwmTripActionConfig_t tripactionconfig );

void etpwmEnableTripInterrupt( etpwmBASE_t * etpwm, etpwmTrip_t interrupts );
void etpwmDisableTripInterrupt( etpwmBASE_t * etpwm, etpwmTrip_t interrupts );
void etpwmClearTripCondition( etpwmBASE_t * etpwm, etpwmTrip_t trips );
void etpwmClearTripInterruptFlag( etpwmBASE_t * etpwm );
void etpwmForceTripEvent( etpwmBASE_t * etpwm, etpwmTrip_t trip );
void etpwmEnableSOCA( etpwmBASE_t * etpwm,
                      etpwmEventSrc_t eventsource,
                      etpwmEventPeriod_t eventperiod );
void etpwmDisableSOCA( etpwmBASE_t * etpwm );
void etpwmEnableSOCB( etpwmBASE_t * etpwm,
                      etpwmEventSrc_t eventsource,
                      etpwmEventPeriod_t eventperiod );
void etpwmDisableSOCB( etpwmBASE_t * etpwm );
void etpwmEnableInterrupt( etpwmBASE_t * etpwm,
                           etpwmEventSrc_t eventsource,
                           etpwmEventPeriod_t eventperiod );
void etpwmDisableInterrupt( etpwmBASE_t * etpwm );
uint16 etpwmGetEventStatus( etpwmBASE_t * etpwm );
void etpwmClearEventFlag( etpwmBASE_t * etpwm, etpwmEvent_t events );
void etpwmTriggerEvent( etpwmBASE_t * etpwm, etpwmEvent_t events );
void etpwmEnableDigitalCompareEvents( etpwmBASE_t * etpwm,
                                      etpwmDigitalCompareConfig_t digitalcompareconfig );
void etpwm1GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type );
void etpwm2GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type );
void etpwm3GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type );
void etpwm4GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type );
void etpwm5GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type );
void etpwm6GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type );
void etpwm7GetConfigValue( etpwm_config_reg_t * config_reg, config_value_type_t type );
/** @brief     Notification for ETPWMx Interrupts
 *   @param[in] node  The pulse width modulation (ETPWM) object handle
 */
void etpwmNotification( etpwmBASE_t * node );

/** @brief     Notification for ETPWM Trip zone Interrupts
 *   @param[in] node  The pulse width modulation (ETPWM) object handle
 *   @param[in] flags  Event and Interrupt flag.
 */
void etpwmTripNotification( etpwmBASE_t * node, uint16 flags );

/**@}*/
#ifdef __cplusplus
}
#endif /*extern "C" */

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif /* end of _ETPWM_H_ definition */
