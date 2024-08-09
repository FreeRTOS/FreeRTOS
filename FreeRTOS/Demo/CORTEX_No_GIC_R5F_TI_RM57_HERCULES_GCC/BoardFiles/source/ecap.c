/** @file ecap.c
 *   @brief ECAP Driver Source File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - API Functions
 *   - Interrupt Handlers
 *   .
 *   which are relevant for the ECAP driver.
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

#include "ecap.h"
#include "sys_vim.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/** @fn void ecapInit(void)
 *   @brief Initializes the eCAP Driver
 *
 *   This function initializes the eCAP module.
 */
/* SourceId : ECAP_SourceId_001 */
/* DesignId : ECAP_DesignId_001 */
/* Requirements : CONQ_ECAP_SR2 */
void ecapInit( void )
{
    /* USER CODE BEGIN (1) */
    /* USER CODE END */

    /** @b initialize @b ECAP1 */

    /** - Setup control register 1
     *     - Set polarity and reset enable for Capture Events 1-4
     *     - Enable/Disable loading on a capture event
     *     - Setup Event Filter prescale
     */
    ecapREG1
        ->ECCTL1 = ( ( uint16 ) ( ( uint16 ) RISING_EDGE << 0U )     /* Capture Event 1
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 1U ) /* Counter Reset on
                                                                        Capture Event 1 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 2U )   /* Capture Event 2
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 3U ) /* Counter Reset on
                                                                        Capture Event 2 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 4U )   /* Capture Event 3
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 5U ) /* Counter Reset on
                                                                        Capture Event 3 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 6U )   /* Capture Event 4
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 7U ) /* Counter Reset on
                                                                        Capture Event 4 */
                     | ( uint16 ) ( ( uint16 ) 0U << 8U )    /* Enable/Disable loading on
                                                                a capture event */
                     | ( uint16 ) ( ( uint16 ) 0U << 9U ) ); /* Setup Event Filter
                                                                prescale */

    /** - Setup control register 2
     *     - Set operating mode
     *     - Set Stop/Wrap after capture
     */
    ecapREG1->ECCTL2 = ( uint16 ) ( ( uint16 ) ONE_SHOT << 0U )       /* Capture Mode */
                     | ( uint16 ) ( ( uint16 ) CAPTURE_EVENT1 << 1U ) /* Stop/Wrap value
                                                                       */
                     | ( uint16 ) ( ( uint16 ) 0U << 9U ) /* Enable/Disable APWM mode */
                     | ( uint16 ) 0x00000010U;            /* Start counter */

    /** - Set interrupt enable */
    ecapREG1->ECEINT = 0x0000U  /* Enable/Disable Capture Event 1 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 2 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 3 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 4 Interrupt  */
                     | 0x0000U  /* Enable/Disable counter Overflow Interrupt */
                     | 0x0000U  /* Enable/Disable Period Equal Interrupt     */
                     | 0x0000U; /* Enable/Disable Compare Equal Interrupt    */

    /** @b initialize @b ECAP2 */

    /** - Setup control register 1
     *     - Set polarity and reset enable for Capture Events 1-4
     *     - Enable/Disable loading on a capture event
     *     - Setup Event Filter prescale
     */
    ecapREG2
        ->ECCTL1 = ( ( uint16 ) ( ( uint16 ) RISING_EDGE << 0U )     /* Capture Event 1
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 1U ) /* Counter Reset on
                                                                        Capture Event 1 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 2U )   /* Capture Event 2
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 3U ) /* Counter Reset on
                                                                        Capture Event 2 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 4U )   /* Capture Event 3
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 5U ) /* Counter Reset on
                                                                        Capture Event 3 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 6U )   /* Capture Event 4
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 7U ) /* Counter Reset on
                                                                        Capture Event 4 */
                     | ( uint16 ) ( ( uint16 ) 0U << 8U )    /* Enable/Disable loading on
                                                                a capture event */
                     | ( uint16 ) ( ( uint16 ) 0U << 9U ) ); /* Setup Event Filter
                                                                prescale */

    /** - Setup control register 2
     *     - Set operating mode
     *     - Set Stop/Wrap after capture
     */
    ecapREG2->ECCTL2 = ( uint16 ) ( ( uint16 ) ONE_SHOT << 0U )       /* Capture Mode */
                     | ( uint16 ) ( ( uint16 ) CAPTURE_EVENT1 << 1U ) /* Stop/Wrap value
                                                                       */
                     | ( uint16 ) ( ( uint16 ) 0U << 9U ) /* Enable/Disable APWM mode */
                     | ( uint16 ) 0x00000010U;            /* Start counter */

    /** - Set interrupt enable */
    ecapREG2->ECEINT = 0x0000U  /* Enable/Disable Capture Event 1 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 2 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 3 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 4 Interrupt  */
                     | 0x0000U  /* Enable/Disable counter Overflow Interrupt */
                     | 0x0000U  /* Enable/Disable Period Equal Interrupt     */
                     | 0x0000U; /* Enable/Disable Compare Equal Interrupt    */

    /** @b initialize @b ECAP3 */

    /** - Setup control register 1
     *     - Set polarity and reset enable for Capture Events 1-4
     *     - Enable/Disable loading on a capture event
     *     - Setup Event Filter prescale
     */
    ecapREG3
        ->ECCTL1 = ( ( uint16 ) ( ( uint16 ) RISING_EDGE << 0U )     /* Capture Event 1
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 1U ) /* Counter Reset on
                                                                        Capture Event 1 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 2U )   /* Capture Event 2
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 3U ) /* Counter Reset on
                                                                        Capture Event 2 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 4U )   /* Capture Event 3
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 5U ) /* Counter Reset on
                                                                        Capture Event 3 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 6U )   /* Capture Event 4
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 7U ) /* Counter Reset on
                                                                        Capture Event 4 */
                     | ( uint16 ) ( ( uint16 ) 0U << 8U )    /* Enable/Disable loading on
                                                                a capture event */
                     | ( uint16 ) ( ( uint16 ) 0U << 9U ) ); /* Setup Event Filter
                                                                prescale */

    /** - Setup control register 2
     *     - Set operating mode
     *     - Set Stop/Wrap after capture
     */
    ecapREG3->ECCTL2 = ( uint16 ) ( ( uint16 ) ONE_SHOT << 0U )       /* Capture Mode */
                     | ( uint16 ) ( ( uint16 ) CAPTURE_EVENT1 << 1U ) /* Stop/Wrap value
                                                                       */
                     | ( uint16 ) ( ( uint16 ) 0U << 9U ) /* Enable/Disable APWM mode */
                     | ( uint16 ) 0x00000010U;            /* Start counter */

    /** - Set interrupt enable */
    ecapREG3->ECEINT = 0x0000U  /* Enable/Disable Capture Event 1 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 2 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 3 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 4 Interrupt  */
                     | 0x0000U  /* Enable/Disable counter Overflow Interrupt */
                     | 0x0000U  /* Enable/Disable Period Equal Interrupt     */
                     | 0x0000U; /* Enable/Disable Compare Equal Interrupt    */

    /** @b initialize @b ECAP4 */

    /** - Setup control register 1
     *     - Set polarity and reset enable for Capture Events 1-4
     *     - Enable/Disable loading on a capture event
     *     - Setup Event Filter prescale
     */
    ecapREG4
        ->ECCTL1 = ( ( uint16 ) ( ( uint16 ) RISING_EDGE << 0U )     /* Capture Event 1
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 1U ) /* Counter Reset on
                                                                        Capture Event 1 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 2U )   /* Capture Event 2
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 3U ) /* Counter Reset on
                                                                        Capture Event 2 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 4U )   /* Capture Event 3
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 5U ) /* Counter Reset on
                                                                        Capture Event 3 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 6U )   /* Capture Event 4
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 7U ) /* Counter Reset on
                                                                        Capture Event 4 */
                     | ( uint16 ) ( ( uint16 ) 0U << 8U )    /* Enable/Disable loading on
                                                                a capture event */
                     | ( uint16 ) ( ( uint16 ) 0U << 9U ) ); /* Setup Event Filter
                                                                prescale */

    /** - Setup control register 2
     *     - Set operating mode
     *     - Set Stop/Wrap after capture
     */
    ecapREG4->ECCTL2 = ( uint16 ) ( ( uint16 ) ONE_SHOT << 0U )       /* Capture Mode */
                     | ( uint16 ) ( ( uint16 ) CAPTURE_EVENT1 << 1U ) /* Stop/Wrap value
                                                                       */
                     | ( uint16 ) ( ( uint16 ) 0U << 9U ) /* Enable/Disable APWM mode */
                     | ( uint16 ) 0x00000010U;            /* Start counter */

    /** - Set interrupt enable */
    ecapREG4->ECEINT = 0x0000U  /* Enable/Disable Capture Event 1 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 2 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 3 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 4 Interrupt  */
                     | 0x0000U  /* Enable/Disable counter Overflow Interrupt */
                     | 0x0000U  /* Enable/Disable Period Equal Interrupt     */
                     | 0x0000U; /* Enable/Disable Compare Equal Interrupt    */

    /** @b initialize @b ECAP5 */

    /** - Setup control register 1
     *     - Set polarity and reset enable for Capture Events 1-4
     *     - Enable/Disable loading on a capture event
     *     - Setup Event Filter prescale
     */
    ecapREG5
        ->ECCTL1 = ( ( uint16 ) ( ( uint16 ) RISING_EDGE << 0U )     /* Capture Event 1
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 1U ) /* Counter Reset on
                                                                        Capture Event 1 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 2U )   /* Capture Event 2
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 3U ) /* Counter Reset on
                                                                        Capture Event 2 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 4U )   /* Capture Event 3
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 5U ) /* Counter Reset on
                                                                        Capture Event 3 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 6U )   /* Capture Event 4
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 7U ) /* Counter Reset on
                                                                        Capture Event 4 */
                     | ( uint16 ) ( ( uint16 ) 0U << 8U )    /* Enable/Disable loading on
                                                                a capture event */
                     | ( uint16 ) ( ( uint16 ) 0U << 9U ) ); /* Setup Event Filter
                                                                prescale */

    /** - Setup control register 2
     *     - Set operating mode
     *     - Set Stop/Wrap after capture
     */
    ecapREG5->ECCTL2 = ( uint16 ) ( ( uint16 ) ONE_SHOT << 0U )       /* Capture Mode */
                     | ( uint16 ) ( ( uint16 ) CAPTURE_EVENT1 << 1U ) /* Stop/Wrap value
                                                                       */
                     | ( uint16 ) ( ( uint16 ) 0U << 9U ) /* Enable/Disable APWM mode */
                     | ( uint16 ) 0x00000010U;            /* Start counter */

    /** - Set interrupt enable */
    ecapREG5->ECEINT = 0x0000U  /* Enable/Disable Capture Event 1 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 2 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 3 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 4 Interrupt  */
                     | 0x0000U  /* Enable/Disable counter Overflow Interrupt */
                     | 0x0000U  /* Enable/Disable Period Equal Interrupt     */
                     | 0x0000U; /* Enable/Disable Compare Equal Interrupt    */

    /** @b initialize @b ECAP6 */

    /** - Setup control register 1
     *     - Set polarity and reset enable for Capture Events 1-4
     *     - Enable/Disable loading on a capture event
     *     - Setup Event Filter prescale
     */
    ecapREG6
        ->ECCTL1 = ( ( uint16 ) ( ( uint16 ) RISING_EDGE << 0U )     /* Capture Event 1
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 1U ) /* Counter Reset on
                                                                        Capture Event 1 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 2U )   /* Capture Event 2
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 3U ) /* Counter Reset on
                                                                        Capture Event 2 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 4U )   /* Capture Event 3
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 5U ) /* Counter Reset on
                                                                        Capture Event 3 */
                     | ( uint16 ) ( ( uint16 ) RISING_EDGE << 6U )   /* Capture Event 4
                                                                        Polarity */
                     | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 7U ) /* Counter Reset on
                                                                        Capture Event 4 */
                     | ( uint16 ) ( ( uint16 ) 0U << 8U )    /* Enable/Disable loading on
                                                                a capture event */
                     | ( uint16 ) ( ( uint16 ) 0U << 9U ) ); /* Setup Event Filter
                                                                prescale */

    /** - Setup control register 2
     *     - Set operating mode
     *     - Set Stop/Wrap after capture
     */
    ecapREG6->ECCTL2 = ( uint16 ) ( ( uint16 ) ONE_SHOT << 0U )       /* Capture Mode */
                     | ( uint16 ) ( ( uint16 ) CAPTURE_EVENT1 << 1U ) /* Stop/Wrap value
                                                                       */
                     | ( uint16 ) ( ( uint16 ) 0U << 9U ) /* Enable/Disable APWM mode */
                     | ( uint16 ) 0x00000010U;            /* Start counter */

    /** - Set interrupt enable */
    ecapREG6->ECEINT = 0x0000U  /* Enable/Disable Capture Event 1 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 2 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 3 Interrupt  */
                     | 0x0000U  /* Enable/Disable Capture Event 4 Interrupt  */
                     | 0x0000U  /* Enable/Disable counter Overflow Interrupt */
                     | 0x0000U  /* Enable/Disable Period Equal Interrupt     */
                     | 0x0000U; /* Enable/Disable Compare Equal Interrupt    */
}

/** @fn void ecapSetCounter(ecapBASE_t *ecap, uint32 value)
 *   @brief Set Time-Stamp Counter
 *
 *   @param[in] ecap  The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] value 16-bit Counter value
 *
 *   This function sets the Time-Stamp Counter register
 */
/* SourceId : ECAP_SourceId_002 */
/* DesignId : ECAP_DesignId_002 */
/* Requirements : CONQ_ECAP_SR3 */
void ecapSetCounter( ecapBASE_t * ecap, uint32 value )
{
    ecap->TSCTR = value;
}

/** @fn void ecapEnableCounterLoadOnSync(ecapBASE_t *ecap, uint32 phase)
 *   @brief Enable counter register load from phase register when a sync event occurs
 *
 *   @param[in] ecap  The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] phase Counter value to be loaded when a sync event occurs
 *
 *   This function enables counter register load from phase register when a sync event
 * occurs
 */
/* SourceId : ECAP_SourceId_003 */
/* DesignId : ECAP_DesignId_003 */
/* Requirements : CONQ_ECAP_SR6 */
void ecapEnableCounterLoadOnSync( ecapBASE_t * ecap, uint32 phase )
{
    ecap->ECCTL2 |= 0x0020U;
    ecap->CTRPHS = phase;
}

/** @fn void ecapDisableCounterLoadOnSync(ecapBASE_t *ecap)
 *   @brief Disable counter register load from phase register when a sync event occurs
 *
 *   @param[in] ecap  The capture (eCAP) object handle (ecapREG1..6)
 *
 *   This function disables counter register load from phase register when a sync event
 * occurs
 */
/* SourceId : ECAP_SourceId_004 */
/* DesignId : ECAP_DesignId_004 */
/* Requirements : CONQ_ECAP_SR7 */
void ecapDisableCounterLoadOnSync( ecapBASE_t * ecap )
{
    ecap->ECCTL2 &= ( uint16 ) ~( uint16 ) 0x0020U;
}

/** @fn void ecapSetEventPrescaler(ecapBASE_t *ecap, ecapPrescale_t prescale)
 *   @brief Set Event prescaler
 *
 *   @param[in] ecap      The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] prescale  Event Filter prescale select
 * (ecapPrescale_By_1..ecapPrescale_By_62)
 *
 *   This function disables counter register load from phase register when a sync event
 * occurs
 */
/* SourceId : ECAP_SourceId_005 */
/* DesignId : ECAP_DesignId_005 */
/* Requirements : CONQ_ECAP_SR8 */
void ecapSetEventPrescaler( ecapBASE_t * ecap, ecapPrescale_t prescale )
{
    ecap->ECCTL1 &= ( uint16 ) ~( uint16 ) 0x3E00U;
    ecap->ECCTL1 |= ( uint16 ) prescale;
}

/** @fn void ecapSetCaptureEvent1(ecapBASE_t *ecap, ecapEdgePolarity_t edgePolarity,
 * ecapReset_t resetenable)
 *   @brief Set Capture Event 1
 *
 *   @param[in] ecap           The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] edgePolarity   Capture Event 1 Polarity select
 *                               - RISING_EDGE
 *                               - FALLING_EDGE
 *   @param[in] resetenable    Counter Reset on Capture Event 1
 *                               - RESET_ENABLE
 *                               - RESET_DISABLE
 *
 *   This function sets the polarity and reset enable for Capture event 1
 */
/* SourceId : ECAP_SourceId_006 */
/* DesignId : ECAP_DesignId_006 */
/* Requirements : CONQ_ECAP_SR9 */
void ecapSetCaptureEvent1( ecapBASE_t * ecap,
                           ecapEdgePolarity_t edgePolarity,
                           ecapReset_t resetenable )
{
    ecap->ECCTL1 &= ( uint16 ) ~( uint16 ) ( ( uint16 ) 0x3U << 0U );
    ecap->ECCTL1 |= ( uint16 ) ( ( ( uint16 ) edgePolarity
                                   | ( uint16 ) ( ( uint16 ) resetenable << 1U ) )
                                 << 0U );
}

/** @fn void ecapSetCaptureEvent2(ecapBASE_t *ecap, ecapEdgePolarity_t edgePolarity,
 * ecapReset_t resetenable)
 *   @brief Set Capture Event 2
 *
 *   @param[in] ecap           The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] edgePolarity   Capture Event 2 Polarity select
 *                               - RISING_EDGE
 *                               - FALLING_EDGE
 *   @param[in] resetenable    Counter Reset on Capture Event 2
 *                               - RESET_ENABLE
 *                               - RESET_DISABLE
 *
 *   This function sets the polarity and reset enable for Capture event 2
 */
/* SourceId : ECAP_SourceId_007 */
/* DesignId : ECAP_DesignId_006 */
/* Requirements : CONQ_ECAP_SR9 */
void ecapSetCaptureEvent2( ecapBASE_t * ecap,
                           ecapEdgePolarity_t edgePolarity,
                           ecapReset_t resetenable )
{
    ecap->ECCTL1 &= ( uint16 ) ~( uint16 ) ( ( uint16 ) 0x3U << 2U );
    ecap->ECCTL1 |= ( uint16 ) ( ( ( uint16 ) edgePolarity
                                   | ( uint16 ) ( ( uint16 ) resetenable << 1U ) )
                                 << 2U );
}

/** @fn void ecapSetCaptureEvent3(ecapBASE_t *ecap, ecapEdgePolarity_t edgePolarity,
 * ecapReset_t resetenable)
 *   @brief Set Capture Event 3
 *
 *   @param[in] ecap           The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] edgePolarity   Capture Event 3 Polarity select
 *                               - RISING_EDGE
 *                               - FALLING_EDGE
 *   @param[in] resetenable    Counter Reset on Capture Event 3
 *                              - RESET_ENABLE
 *                              - RESET_DISABLE
 *
 *   This function sets the polarity and reset enable for Capture event 3
 */
/* SourceId : ECAP_SourceId_008 */
/* DesignId : ECAP_DesignId_006 */
/* Requirements : CONQ_ECAP_SR9 */
void ecapSetCaptureEvent3( ecapBASE_t * ecap,
                           ecapEdgePolarity_t edgePolarity,
                           ecapReset_t resetenable )
{
    ecap->ECCTL1 &= ( uint16 ) ~( uint16 ) ( ( uint16 ) 0x3U << 4U );
    ecap->ECCTL1 |= ( uint16 ) ( ( ( uint16 ) edgePolarity
                                   | ( uint16 ) ( ( uint16 ) resetenable << 1U ) )
                                 << 4U );
}

/** @fn void ecapSetCaptureEvent4(ecapBASE_t *ecap, ecapEdgePolarity_t edgePolarity,
 * ecapReset_t resetenable)
 *   @brief Set Capture Event 4
 *
 *   @param[in] ecap           The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] edgePolarity   Capture Event 4 Polarity select
 *                               - RISING_EDGE
 *                               - FALLING_EDGE
 *   @param[in] resetenable    Counter Reset on Capture Event 4
 *                               - RESET_ENABLE
 *                               - RESET_DISABLE
 *
 *   This function sets the polarity and reset enable for Capture event 4
 */
/* SourceId : ECAP_SourceId_009 */
/* DesignId : ECAP_DesignId_006 */
/* Requirements : CONQ_ECAP_SR9 */
void ecapSetCaptureEvent4( ecapBASE_t * ecap,
                           ecapEdgePolarity_t edgePolarity,
                           ecapReset_t resetenable )
{
    ecap->ECCTL1 &= ( uint16 ) ~( uint16 ) ( ( uint16 ) 0x3U << 6U );
    ecap->ECCTL1 |= ( uint16 ) ( ( ( uint16 ) edgePolarity
                                   | ( uint16 ) ( ( uint16 ) resetenable << 1U ) )
                                 << 6U );
}

/** @fn void ecapSetCaptureMode(ecapBASE_t *ecap, ecapMode_t mode, ecapEvent_t event)
 *   @brief Set Capture mode
 *
 *   @param[in] ecap     The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] capMode  Capture mode
 *                         - CONTINUOUS
 *                         - ONE_SHOT
 *   @param[in] event    Stop/Wrap value
 *                         - CAPTURE_EVENT1: Stop after Capture Event 1 in one-shot mode /
 * Wrap after Capture Event 1 in continuous mode
 *                         - CAPTURE_EVENT2: Stop after Capture Event 2 in one-shot mode /
 * Wrap after Capture Event 2 in continuous mode.
 *                         - CAPTURE_EVENT3: Stop after Capture Event 3 in one-shot mode /
 * Wrap after Capture Event 3 in continuous mode.
 *                         - CAPTURE_EVENT4: Stop after Capture Event 4 in one-shot mode /
 * Wrap after Capture Event 4 in continuous mode.
 *
 *   This function sets the capture mode and stop/wrap value
 */
/* SourceId : ECAP_SourceId_010 */
/* DesignId : ECAP_DesignId_007 */
/* Requirements : CONQ_ECAP_SR10 */
void ecapSetCaptureMode( ecapBASE_t * ecap, ecapMode_t capMode, ecapEvent_t event )
{
    ecap->ECCTL2 &= 0xFFF8U;
    ecap->ECCTL2 |= ( ( uint16 ) ( ( uint16 ) event << 1U ) | ( uint16 ) capMode );
}

/** @fn void ecapEnableCapture(ecapBASE_t *ecap)
 *   @brief Enable Capture
 *
 *   @param[in] ecap  The capture (eCAP) object handle (ecapREG1..6)
 *
 *   This function enable loading of CAP1-4 registers on a capture event
 */
/* SourceId : ECAP_SourceId_011 */
/* DesignId : ECAP_DesignId_008 */
/* Requirements : CONQ_ECAP_SR11 */
void ecapEnableCapture( ecapBASE_t * ecap )
{
    ecap->ECCTL1 |= 0x0100U;
}

/** @fn void ecapDisableCapture(ecapBASE_t *ecap)
 *   @brief Disable Capture
 *
 *   @param[in] ecap  The capture (eCAP) object handle (ecapREG1..6)
 *
 *   This function disable loading of CAP1-4 registers on a capture event
 */
/* SourceId : ECAP_SourceId_012 */
/* DesignId : ECAP_DesignId_009 */
/* Requirements : CONQ_ECAP_SR12 */
void ecapDisableCapture( ecapBASE_t * ecap )
{
    ecap->ECCTL1 &= ( uint16 ) ~( uint16 ) 0x0100U;
}

/** @fn void ecapStartCounter(ecapBASE_t *ecap)
 *   @brief Start Time Stamp Counter
 *
 *   @param[in] ecap  The capture (eCAP) object handle (ecapREG1..6)
 *
 *   This function starts Time Stamp Counter
 */
/* SourceId : ECAP_SourceId_013 */
/* DesignId : ECAP_DesignId_010 */
/* Requirements : CONQ_ECAP_SR4 */
void ecapStartCounter( ecapBASE_t * ecap )
{
    ecap->ECCTL2 |= 0x0010U;
}

/** @fn void ecapStopCounter(ecapBASE_t *ecap))
 *   @brief Stop Time Stamp Counter
 *
 *   @param[in] ecap  The capture (eCAP) object handle (ecapREG1..6)
 *
 *   This function stops Time Stamp Counter
 */
/* SourceId : ECAP_SourceId_014 */
/* DesignId : ECAP_DesignId_011 */
/* Requirements : CONQ_ECAP_SR5 */
void ecapStopCounter( ecapBASE_t * ecap )
{
    ecap->ECCTL2 &= ( uint16 ) ~( uint16 ) 0x0010U;
}

/** @fn void ecapSetSyncOut(ecapBASE_t *ecap, ecapSyncOut_t syncOutSrc)
 *   @brief Set the source of Sync-out signal
 *
 *   @param[in] ecap       The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] syncOutSrc Sync-Out Select
 *                           - SyncOut_SyncIn: Sync In used for Sync Out
 *                           - SyncOut_CTRPRD: CTR = PRD used for Sync Out
 *                           - SyncOut_None  : Disables Sync Out
 *
 *   This function sets the source of Sync-out signal
 */
/* SourceId : ECAP_SourceId_015 */
/* DesignId : ECAP_DesignId_012 */
/* Requirements : CONQ_ECAP_SR13 */
void ecapSetSyncOut( ecapBASE_t * ecap, ecapSyncOut_t syncOutSrc )
{
    ecap->ECCTL2 &= ( uint16 ) ~( uint16 ) 0x00C0U;
    ecap->ECCTL2 |= syncOutSrc;
}

/** @fn void ecapEnableAPWMmode(ecapBASE_t *ecap, ecapAPWMPolarity_t pwmPolarity, uint16
 * period, uint16 duty)
 *   @brief Enable APWM mode
 *
 *   @param[in] ecap          The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] pwmPolarity   APWM output polarity select
 *                             - ACTIVE_HIGH
 *                             - ACTIVE_LOW
 *   @param[in] period        APWM period (in terms of ticks)
 *   @param[in] duty          APWM duty (in terms of ticks)
 *
 *   This function enables and sets APWM mode
 */
/* SourceId : ECAP_SourceId_016 */
/* DesignId : ECAP_DesignId_013 */
/* Requirements : CONQ_ECAP_SR14 */
void ecapEnableAPWMmode( ecapBASE_t * ecap,
                         ecapAPWMPolarity_t pwmPolarity,
                         uint32 period,
                         uint32 duty )
{
    ecap->ECCTL2 &= ( uint16 ) ~( uint16 ) 0x0400U;
    ecap->ECCTL2 |= ( uint16 ) ( ( uint16 ) pwmPolarity << 10U )
                  | ( uint16 ) ( ( uint16 ) 1U << 9U );
    ecap->CAP1 = period - 1U;
    ecap->CAP2 = duty;
}

/** @fn void ecapDisableAPWMMode(ecapBASE_t *ecap)
 *   @brief Disable APWM mode
 *
 *   @param[in] ecap       The capture (eCAP) object handle (ecapREG1..6)
 *
 *   This function disables APWM mode
 */
/* SourceId : ECAP_SourceId_017 */
/* DesignId : ECAP_DesignId_014 */
/* Requirements : CONQ_ECAP_SR15 */
void ecapDisableAPWMMode( ecapBASE_t * ecap )
{
    ecap->ECCTL2 &= ( uint16 ) ~( uint16 ) 0x0200U;
}

/** @fn void ecapEnableInterrupt(ecapBASE_t *ecap, ecapInterrupt_t interrupts)
 *   @brief Enable eCAP interrupt sources
 *
 *   @param[in] ecap       The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] interrupts eCAP interrupt sources
 *                           - ecapInt_CTR_CMP: Denotes CTR = CMP interrupt
 *                           - ecapInt_CTR_PRD: Denotes CTR = PRD interrupt
 *                           - ecapInt_CTR_OVF: Denotes CTROVF interrupt
 *                           - ecapInt_CEVT4  : Denotes CEVT4 interrupt
 *                           - ecapInt_CEVT3  : Denotes CEVT3 interrupt
 *                           - ecapInt_CEVT2  : Denotes CEVT2 interrupt
 *                           - ecapInt_CEVT1  : Denotes CEVT1 interrupt
 *                           - ecapInt_All    : Denotes All interrupts
 *
 *   This function enables eCAP interrupt sources
 */
/* SourceId : ECAP_SourceId_018 */
/* DesignId : ECAP_DesignId_015 */
/* Requirements : CONQ_ECAP_SR16 */
void ecapEnableInterrupt( ecapBASE_t * ecap, ecapInterrupt_t interrupts )
{
    ecap->ECEINT |= interrupts;
}

/** @fn void ecapDisableInterrupt(ecapBASE_t *ecap, ecapInterrupt_t interrupts)
 *   @brief Disables eCAP interrupt sources
 *
 *   @param[in] ecap       The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] interrupts eCAP interrupt sources
 *                           - ecapInt_CTR_CMP: Denotes CTR = CMP interrupt
 *                           - ecapInt_CTR_PRD: Denotes CTR = PRD interrupt
 *                           - ecapInt_CTR_OVF: Denotes CTROVF interrupt
 *                           - ecapInt_CEVT4  : Denotes CEVT4 interrupt
 *                           - ecapInt_CEVT3  : Denotes CEVT3 interrupt
 *                           - ecapInt_CEVT2  : Denotes CEVT2 interrupt
 *                           - ecapInt_CEVT1  : Denotes CEVT1 interrupt
 *                           - ecapInt_All    : Denotes All interrupts
 *
 *   This function disables eCAP interrupt sources
 */
/* SourceId : ECAP_SourceId_019 */
/* DesignId : ECAP_DesignId_016 */
/* Requirements : CONQ_ECAP_SR17 */
void ecapDisableInterrupt( ecapBASE_t * ecap, ecapInterrupt_t interrupts )
{
    ecap->ECEINT &= ( uint16 ) ~( uint16 ) interrupts;
}

/** @fn uint16 ecapGetEventStatus(ecapBASE_t *ecap, ecapInterrupt_t events)
 *   @brief Return Event status
 *
 *   @param[in] ecap    The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] events  eCAP events
 *                        - ecapInt_CTR_CMP: Denotes CTR = CMP interrupt
 *                        - ecapInt_CTR_PRD: Denotes CTR = PRD interrupt
 *                        - ecapInt_CTR_OVF: Denotes CTROVF interrupt
 *                        - ecapInt_CEVT4  : Denotes CEVT4 interrupt
 *                        - ecapInt_CEVT3  : Denotes CEVT3 interrupt
 *                        - ecapInt_CEVT2  : Denotes CEVT2 interrupt
 *                        - ecapInt_CEVT1  : Denotes CEVT1 interrupt
 *                        - ecapInt_Global : Denotes Capture global interrupt
 *                        - ecapInt_All    : Denotes All interrupts
 *   @return Event status
 *
 *   This function returns the event status
 */
/* SourceId : ECAP_SourceId_020 */
/* DesignId : ECAP_DesignId_017 */
/* Requirements : CONQ_ECAP_SR18 */
uint16 ecapGetEventStatus( ecapBASE_t * ecap, ecapInterrupt_t events )
{
    return ( ecap->ECFLG & events );
}

/** @fn void ecapClearFlag(ecapBASE_t *ecap, ecapInterrupt_t events)
 *   @brief Clear Event status
 *
 *   @param[in] ecap    The capture (eCAP) object handle (ecapREG1..6)
 *   @param[in] events  eCAP events
 *                        - ecapInt_CTR_CMP: Denotes CTR = CMP interrupt
 *                        - ecapInt_CTR_PRD: Denotes CTR = PRD interrupt
 *                        - ecapInt_CTR_OVF: Denotes CTROVF interrupt
 *                        - ecapInt_CEVT4  : Denotes CEVT4 interrupt
 *                        - ecapInt_CEVT3  : Denotes CEVT3 interrupt
 *                        - ecapInt_CEVT2  : Denotes CEVT2 interrupt
 *                        - ecapInt_CEVT1  : Denotes CEVT1 interrupt
 *                        - ecapInt_Global : Denotes Capture global interrupt
 *                        - ecapInt_All    : Denotes All interrupts
 *
 *   This function clears the event status
 */
/* SourceId : ECAP_SourceId_021 */
/* DesignId : ECAP_DesignId_018 */
/* Requirements : CONQ_ECAP_SR19 */
void ecapClearFlag( ecapBASE_t * ecap, ecapInterrupt_t events )
{
    ecap->ECCLR = events;
}

/** @fn void uint32 ecapGetCAP1(ecapBASE_t *ecap)
 *   @brief Get CAP1 value
 *
 *   @param[in] ecap    The capture (eCAP) object handle (ecapREG1..6)
 *
 *   This function returns Capture 1 value
 */
/* SourceId : ECAP_SourceId_022 */
/* DesignId : ECAP_DesignId_019 */
/* Requirements : CONQ_ECAP_SR20 */
uint32 ecapGetCAP1( ecapBASE_t * ecap )
{
    return ecap->CAP1;
}

/** @fn void uint32 ecapGetCAP2(ecapBASE_t *ecap)
 *   @brief Get CAP2 value
 *
 *   @param[in] ecap    The capture (eCAP) object handle (ecapREG1..6)
 *
 *   This function returns Capture 2 value
 */
/* SourceId : ECAP_SourceId_023 */
/* DesignId : ECAP_DesignId_019 */
/* Requirements : CONQ_ECAP_SR20 */
uint32 ecapGetCAP2( ecapBASE_t * ecap )
{
    return ecap->CAP2;
}

/** @fn void uint32 ecapGetCAP3(ecapBASE_t *ecap)
 *   @brief Get CAP3 value
 *
 *   @param[in] ecap    The capture (eCAP) object handle (ecapREG1..6)
 *
 *   This function returns Capture 3 value
 */
/* SourceId : ECAP_SourceId_024 */
/* DesignId : ECAP_DesignId_019 */
/* Requirements : CONQ_ECAP_SR20 */
uint32 ecapGetCAP3( ecapBASE_t * ecap )
{
    return ecap->CAP3;
}

/** @fn void uint32 ecapGetCAP4(ecapBASE_t *ecap)
 *   @brief Get CAP4 value
 *
 *   @param[in] ecap    The capture (eCAP) object handle (ecapREG1..6)
 *
 *   This function returns Capture 4 value
 */
/* SourceId : ECAP_SourceId_025 */
/* DesignId : ECAP_DesignId_019 */
/* Requirements : CONQ_ECAP_SR20 */
uint32 ecapGetCAP4( ecapBASE_t * ecap )
{
    return ecap->CAP4;
}

/** @fn void ecap1GetConfigValue(ecap_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ECAP_SourceId_026 */
/* DesignId : ECAP_DesignId_020 */
/* Requirements : CONQ_ECAP_SR21 */
void ecap1GetConfigValue( ecap_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_CTRPHS = ECAP1_CTRPHS_CONFIGVALUE;
        config_reg->CONFIG_ECCTL1 = ECAP1_ECCTL1_CONFIGVALUE;
        config_reg->CONFIG_ECCTL2 = ECAP1_ECCTL2_CONFIGVALUE;
        config_reg->CONFIG_ECEINT = ECAP1_ECEINT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_CTRPHS = ecapREG1->CTRPHS;
        config_reg->CONFIG_ECCTL1 = ecapREG1->ECCTL1;
        config_reg->CONFIG_ECCTL2 = ecapREG1->ECCTL2;
        config_reg->CONFIG_ECEINT = ecapREG1->ECEINT;
    }
}

/** @fn void ecap2GetConfigValue(ecap_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ECAP_SourceId_027 */
/* DesignId : ECAP_DesignId_020 */
/* Requirements : CONQ_ECAP_SR21 */
void ecap2GetConfigValue( ecap_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_CTRPHS = ECAP2_CTRPHS_CONFIGVALUE;
        config_reg->CONFIG_ECCTL1 = ECAP2_ECCTL1_CONFIGVALUE;
        config_reg->CONFIG_ECCTL2 = ECAP2_ECCTL2_CONFIGVALUE;
        config_reg->CONFIG_ECEINT = ECAP2_ECEINT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_CTRPHS = ecapREG2->CTRPHS;
        config_reg->CONFIG_ECCTL1 = ecapREG2->ECCTL1;
        config_reg->CONFIG_ECCTL2 = ecapREG2->ECCTL2;
        config_reg->CONFIG_ECEINT = ecapREG2->ECEINT;
    }
}

/** @fn void ecap3GetConfigValue(ecap_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ECAP_SourceId_028 */
/* DesignId : ECAP_DesignId_020 */
/* Requirements : CONQ_ECAP_SR21 */
void ecap3GetConfigValue( ecap_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_CTRPHS = ECAP3_CTRPHS_CONFIGVALUE;
        config_reg->CONFIG_ECCTL1 = ECAP3_ECCTL1_CONFIGVALUE;
        config_reg->CONFIG_ECCTL2 = ECAP3_ECCTL2_CONFIGVALUE;
        config_reg->CONFIG_ECEINT = ECAP3_ECEINT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_CTRPHS = ecapREG3->CTRPHS;
        config_reg->CONFIG_ECCTL1 = ecapREG3->ECCTL1;
        config_reg->CONFIG_ECCTL2 = ecapREG3->ECCTL2;
        config_reg->CONFIG_ECEINT = ecapREG3->ECEINT;
    }
}

/** @fn void ecap4GetConfigValue(ecap_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ECAP_SourceId_029 */
/* DesignId : ECAP_DesignId_020 */
/* Requirements : CONQ_ECAP_SR21 */
void ecap4GetConfigValue( ecap_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_CTRPHS = ECAP4_CTRPHS_CONFIGVALUE;
        config_reg->CONFIG_ECCTL1 = ECAP4_ECCTL1_CONFIGVALUE;
        config_reg->CONFIG_ECCTL2 = ECAP4_ECCTL2_CONFIGVALUE;
        config_reg->CONFIG_ECEINT = ECAP4_ECEINT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_CTRPHS = ecapREG4->CTRPHS;
        config_reg->CONFIG_ECCTL1 = ecapREG4->ECCTL1;
        config_reg->CONFIG_ECCTL2 = ecapREG4->ECCTL2;
        config_reg->CONFIG_ECEINT = ecapREG4->ECEINT;
    }
}

/** @fn void ecap5GetConfigValue(ecap_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ECAP_SourceId_030 */
/* DesignId : ECAP_DesignId_020 */
/* Requirements : CONQ_ECAP_SR21 */
void ecap5GetConfigValue( ecap_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_CTRPHS = ECAP5_CTRPHS_CONFIGVALUE;
        config_reg->CONFIG_ECCTL1 = ECAP5_ECCTL1_CONFIGVALUE;
        config_reg->CONFIG_ECCTL2 = ECAP5_ECCTL2_CONFIGVALUE;
        config_reg->CONFIG_ECEINT = ECAP5_ECEINT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_CTRPHS = ecapREG5->CTRPHS;
        config_reg->CONFIG_ECCTL1 = ecapREG5->ECCTL1;
        config_reg->CONFIG_ECCTL2 = ecapREG5->ECCTL2;
        config_reg->CONFIG_ECEINT = ecapREG5->ECEINT;
    }
}

/** @fn void ecap6GetConfigValue(ecap_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : ECAP_SourceId_031 */
/* DesignId : ECAP_DesignId_020 */
/* Requirements : CONQ_ECAP_SR21 */
void ecap6GetConfigValue( ecap_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_CTRPHS = ECAP6_CTRPHS_CONFIGVALUE;
        config_reg->CONFIG_ECCTL1 = ECAP6_ECCTL1_CONFIGVALUE;
        config_reg->CONFIG_ECCTL2 = ECAP6_ECCTL2_CONFIGVALUE;
        config_reg->CONFIG_ECEINT = ECAP6_ECEINT_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_CTRPHS = ecapREG6->CTRPHS;
        config_reg->CONFIG_ECCTL1 = ecapREG6->ECCTL1;
        config_reg->CONFIG_ECCTL2 = ecapREG6->ECCTL2;
        config_reg->CONFIG_ECEINT = ecapREG6->ECEINT;
    }
}
