/** @file eqep.c
 *   @brief EQEP Driver Source File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - API Functions
 *   - Interrupt Handlers
 *   .
 *   which are relevant for the EQEP driver.
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

#include "eqep.h"
#include "sys_vim.h"

/*the functions
 */

/* USER CODE BEGIN (0) */
/* USER CODE END */

/** @fn void QEPInit(void)
 *   @brief Initializes the eQEP Driver
 *
 *   This function initializes the eQEP module.
 */
/* SourceId : EQEP_SourceId_001 */
/* DesignId : EQEP_DesignId_001 */
/* Requirements : CONQ_QEP_SR1 */
void QEPInit( void )
{
    /* USER CODE BEGIN (1) */
    /* USER CODE END */

    /** - Clear Position Counter register   */
    eqepREG1->QPOSCNT = 0x00000000U;

    /** - Initialize Position Counter value register   */
    eqepREG1->QPOSINIT = 0x00000000U;

    /** - Set Maximum position counter value   */
    eqepREG1->QPOSMAX = 0x00000000U;

    /** - Set the initial Position compare value   */
    eqepREG1->QPOSCMP = 0x00000000U;

    /** - Clear the time base   */
    eqepREG1->QUTMR = 0x00000000U;

    /** - Configure unit period register   */
    eqepREG1->QUPRD = ( uint32 ) 0x00000000U;

    /** - Clear Watchdog Timer register  */
    eqepREG1->QWDTMR = ( uint16 ) 0x00000000U;

    /** - Configure Watchdog Period   */
    eqepREG1->QWDPRD = ( uint16 ) 0x0000U;

    /* USER CODE BEGIN (2) */
    /* USER CODE END */

    /** - Setup Decoder Control Register
     *     - Select Position counter Mode
     *     - Enable / Disable Sync Output
     *     - Select Sync Output Pin
     *     - Select external Clock rate ( resolution)
     *     - Enable / Disable Swap Quadrature clock input
     *     - Enable / Disable Gating of index pulse with Strobe.
     *     - Enable / Disable Negate QEPA input
     *     - Enable / Disable Negate QEPB input
     *     - Enable / Disable Negate QEPI input
     *     - Enable / Disable Negate QEPS input
     */
    eqepREG1->QDECCTL = ( uint16 ) ( ( uint16 ) ( ( uint16 ) eQEP_DIRECTION_COUNT << 14U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 13U )
                                     | ( uint16 ) ( ( uint16 ) eQEP_INDEX_PIN << 12U )
                                     | ( uint16 ) ( ( uint16 ) eQEP_RESOLUTION_1x << 11U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 10U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 9U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 8U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 7U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 6U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 5U )
                                     | ( uint16 ) 0x0000U );

    /** - Setup eQEP Control Register
     *     - Select Position counter Reset Mode
     *     - Enable & Select Stobe event initialization of position counter
     *     - Enable & Select Index event initialization of position counter
     *     - Enable / Disable Software Initialization of Position counter.
     *     - Select Strobe event latch of position counter.
     *     - Select Index event latch of position counter.
     *     - Select EQEP capture Latch mode
     */
    eqepREG1
        ->QEPCTL = ( uint16 ) ( ( uint16 ) ( ( uint16 ) eQEP_MAX_POSITION << 12U )
                                | ( uint16 ) ( ( uint16 ) 0U << 11U )
                                | ( uint16 ) ( ( uint16 ) eQEP_DIRECTON_DEPENDENT << 10U )
                                | ( uint16 ) ( ( uint16 ) 0U << 9U )
                                | ( uint16 ) ( ( uint16 ) eQEP_RISING_EDGE << 8U )
                                | ( uint16 ) ( ( uint16 ) 0U << 7U )
                                | ( uint16 ) ( ( uint16 ) eQEP_RISING_EDGE << 6U )
                                | ( uint16 ) ( ( uint16 ) eQEP_LATCH_RISING_EDGE << 4U )
                                | ( uint16 ) ( ( uint16 ) eQEP_ON_POSITION_COUNTER_READ
                                               << 2U )
                                | ( uint16 ) 0x0000U );

    /** - Setup eQEP Position Control Register
     *     - Enable / Disable Position compare shadow.
     *     - Select Position compare shadow load mode.
     *     - Select Polarity of Sync output.
     *     - Select Position compare sync output pulse width.
     */
    eqepREG1->QPOSCTL = ( uint16 ) ( ( uint16 ) ( ( uint16 ) 0U << 15U )
                                     | ( uint16 ) ( ( uint16 ) eQEP_QPOSCNT_EQ_QPSCMP
                                                    << 14U )
                                     | ( uint16 ) ( ( uint16 ) eQEP_ACTIVE_HIGH << 13U )
                                     | ( uint16 ) ( ( uint16 ) 0x000U )
                                     | ( uint16 ) 0x0000U );

    /** - Setup eQEP Capture Control Register
     *     - Select capture timer clock prescaler.
     *     - Select Unit position event prescaler.
     */
    eqepREG1->QCAPCTL = ( uint16 ) ( ( uint16 ) ( ( uint16 ) eQEP_PS_8 << 4U )
                                     | ( uint16 ) ( ( uint16 ) eQEP_PS_512 )
                                     | ( uint16 ) 0x0000U );

    /* USER CODE BEGIN (3) */
    /* USER CODE END */

    /** - Clear Interrupt Flag register  */
    eqepREG1->QCLR = ( uint16 ) 0xFFFFU;

    /** - Setup eQEP Interrupt Enable Register
     *     Enable / Diable UTO Interrupt
     *     Enable / Diable IEL Interrupt
     *     Enable / Diable SEL Interrupt
     *     Enable / Diable PCM Interrupt
     *     Enable / Diable PCR Interrupt
     *     Enable / Diable PCO Interrupt
     *     Enable / Diable PCU Interrupt
     *     Enable / Diable WTO Interrupt
     *     Enable / Diable QDC Interrupt
     *     Enable / Diable QPE Interrupt
     *     Enable / Diable PCE Interrupt
     */
    eqepREG1->QEINT = ( uint16 ) ( ( uint16 ) ( ( uint16 ) 0U << 11U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 10U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 9U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 8U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 7U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 6U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 5U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 4U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 3U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 2U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 1U ) );

    /** - Clear Capture Timer register  */
    eqepREG1->QCTMR = ( uint16 ) 0x0000U;

    /** - Clear the Capture Period regiter */
    eqepREG1->QCPRD = ( uint16 ) 0x0000U;

    /** - Clear Period Latch register */
    eqepREG1->QCPRDLAT = ( uint16 ) 0x0000U;

    /* USER CODE BEGIN (4) */
    /* USER CODE END */

    /** - Clear Position Counter register   */
    eqepREG2->QPOSCNT = 0x00000000U;

    /** - Initialize Position Counter value register   */
    eqepREG2->QPOSINIT = 0x00000000U;

    /** - Set Maximum position counter value   */
    eqepREG2->QPOSMAX = 0x00000000U;

    /** - Set the initial Position compare value   */
    eqepREG2->QPOSCMP = 0U;

    /** - Clear the time base   */
    eqepREG2->QUTMR = 0x00000000U;

    /** - Configure unit period register   */
    eqepREG2->QUPRD = ( uint32 ) 0U;

    /** - Clear Watchdog Timer register  */
    eqepREG2->QWDTMR = ( uint16 ) 0x00000000U;

    /** - Configure Watchdog Period   */
    eqepREG2->QWDPRD = ( uint16 ) 0U;

    /* USER CODE BEGIN (5) */
    /* USER CODE END */

    /** - Setup Decoder Control Register
     *     - Select Position counter Mode
     *     - Enable / Disable Sync Output
     *     - Select Sync Output Pin
     *     - Select external Clock rate ( resolution)
     *     - Enable / Disable Swap Quadrature clock input
     *     - Enable / Disable Gating of index pulse with Strobe.
     *     - Enable / Disable Negate QEPA input
     *     - Enable / Disable Negate QEPB input
     *     - Enable / Disable Negate QEPI input
     *     - Enable / Disable Negate QEPS input
     */
    eqepREG2->QDECCTL = ( uint16 ) ( ( uint16 ) ( ( uint16 ) eQEP_DIRECTION_COUNT << 14U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 13U )
                                     | ( uint16 ) ( ( uint16 ) eQEP_INDEX_PIN << 12U )
                                     | ( uint16 ) ( ( uint16 ) eQEP_RESOLUTION_1x << 11U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 10U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 9U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 8U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 7U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 6U )
                                     | ( uint16 ) ( ( uint16 ) 0U << 5U )
                                     | ( uint16 ) 0x0000U );

    /** - Setup eQEP Control Register
     *     - Select Position counter Reset Mode
     *     - Enable & Select Strobe event initialization of position counter
     *     - Enable & Select Index event initialization of position counter
     *     - Enable / Disable Software Initialization of Position counter.
     *     - Select Strobe event latch of position counter.
     *     - Select Index event latch of position counter.
     *     - Select EQEP capture Latch mode
     */
    eqepREG2
        ->QEPCTL = ( uint16 ) ( ( uint16 ) ( ( uint16 ) eQEP_MAX_POSITION << 12U )
                                | ( uint16 ) ( ( uint16 ) 0U << 11U )
                                | ( uint16 ) ( ( uint16 ) eQEP_DIRECTON_DEPENDENT << 10U )
                                | ( uint16 ) ( ( uint16 ) 0U << 9U )
                                | ( uint16 ) ( ( uint16 ) eQEP_RISING_EDGE << 8U )
                                | ( uint16 ) ( ( uint16 ) 0U << 7U )
                                | ( uint16 ) ( ( uint16 ) eQEP_RISING_EDGE << 6U )
                                | ( uint16 ) ( ( uint16 ) eQEP_LATCH_RISING_EDGE << 4U )
                                | ( uint16 ) ( ( uint16 ) eQEP_ON_POSITION_COUNTER_READ
                                               << 2U )
                                | ( uint16 ) 0x0000U );

    /** - Setup eQEP Position Control Register
     *     - Enable / Disable Position compare shadow.
     *     - Select Position compare shadow load mode.
     *     - Select Polarity of Sync output.
     *     - Select Position compare sync output pulse width.
     */
    eqepREG2->QPOSCTL = ( uint16 ) ( ( uint16 ) ( ( uint16 ) 0U << 15U )
                                     | ( uint16 ) ( ( uint16 ) eQEP_QPOSCNT_EQ_QPSCMP
                                                    << 14U )
                                     | ( uint16 ) ( ( uint16 ) eQEP_ACTIVE_HIGH << 13U )
                                     | ( uint16 ) ( ( uint16 ) 0U )
                                     | ( uint16 ) 0x0000U );

    /** - Setup eQEP Capture Control Register
     *     - Select capture timer clock prescaler.
     *     - Select Unit position event prescaler.
     */
    eqepREG2->QCAPCTL = ( uint16 ) ( ( uint16 ) ( ( uint16 ) eQEP_PS_8 << 4U )
                                     | ( uint16 ) ( ( uint16 ) eQEP_PS_512 )
                                     | ( uint16 ) 0x0000U );

    /* USER CODE BEGIN (6) */
    /* USER CODE END */

    /** - Clear Interrupt Flag register  */
    eqepREG2->QCLR = ( uint16 ) 0xFFFFU;

    /** - Setup eQEP Interrupt Enable Register
     *     Enable / Diable UTO Interrupt
     *     Enable / Diable IEL Interrupt
     *     Enable / Diable SEL Interrupt
     *     Enable / Diable PCM Interrupt
     *     Enable / Diable PCR Interrupt
     *     Enable / Diable PCO Interrupt
     *     Enable / Diable PCU Interrupt
     *     Enable / Diable WTO Interrupt
     *     Enable / Diable QDC Interrupt
     *     Enable / Diable QPE Interrupt
     *     Enable / Diable PCE Interrupt
     */
    eqepREG2->QEINT = ( uint16 ) ( ( uint16 ) ( ( uint16 ) 0U << 11U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 10U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 9U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 8U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 7U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 6U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 5U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 4U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 3U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 2U )
                                   | ( uint16 ) ( ( uint16 ) 0U << 1U ) );

    /** - Clear Capture Timer register  */
    eqepREG2->QCTMR = ( uint16 ) 0x0000U;

    /** - Clear the Capture Period regiter */
    eqepREG2->QCPRD = ( uint16 ) 0x0000U;

    /** - Clear Period Latch register */
    eqepREG2->QCPRDLAT = ( uint16 ) 0x0000U;

    /* USER CODE BEGIN (7) */
    /* USER CODE END */
}

/** @brief Clears all QEP interrupt flags
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_002 */
/* DesignId : EQEP_DesignId_002 */
/* Requirements : CONQ_QEP_SR2 */
void eqepClearAllInterruptFlags( eqepBASE_t * eqep )
{
    eqep->QCLR = 0xfffU;

    return;
} /*end of eQEP_clear_all_interrupt_flags() function */

/** @brief Clears a single interrupt flag
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEINT			Interrupt flag
 */
/* SourceId : EQEP_SourceId_003 */
/* DesignId : EQEP_DesignId_003 */
/* Requirements : CONQ_QEP_SR3 */
void eqepClearInterruptFlag( eqepBASE_t * eqep, QEINT_t QEINT_type )
{
    eqep->QCLR |= ( uint16 ) QEINT_type;

    return;
} /*end of eQEP_clear_interrupt_flag() function */

/** @brief Clears the position counter
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_004 */
/* DesignId : EQEP_DesignId_004 */
/* Requirements : CONQ_QEP_SR4 */
void eqepClearPosnCounter( eqepBASE_t * eqep )
{
    eqep->QPOSCNT = 0U;

    return;
} /*end of eQEP_clear_posn_counter() function */

/** @brief Disables all interrupts
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_005 */
/* DesignId : EQEP_DesignId_005 */
/* Requirements : CONQ_QEP_SR5 */
void eqepDisableAllInterrupts( eqepBASE_t * eqep )
{
    eqep->QEINT = 0U;

    return;
} /*end of eQEP_disable_all_interrupts () function */

/** @brief Disable capture
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_006 */
/* DesignId : EQEP_DesignId_006 */
/* Requirements : CONQ_QEP_SR6 */
void eqepDisableCapture( eqepBASE_t * eqep )
{
    eqep->QCAPCTL &= ( uint16 ) ~eQEP_QCAPCTL_CEN;

    return;
} /*end of eQEP_disable_capture () function */

/** @brief Disable gating of index pulse
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_007 */
/* DesignId : EQEP_DesignId_007 */
/* Requirements : CONQ_QEP_SR7 */
void eqepDisableGateIndex( eqepBASE_t * eqep )
{
    eqep->QDECCTL &= ( uint16 ) ~eQEP_QDECCTL_IGATE;

    return;
} /*end of eQEP_disable_gate_index () function */

/** @brief Disable individual interrupt
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEINT			Individual interrupts
 */
/* SourceId : EQEP_SourceId_008 */
/* DesignId : EQEP_DesignId_008 */
/* Requirements : CONQ_QEP_SR8 */
void eqepDisableInterrupt( eqepBASE_t * eqep, QEINT_t QEINT_type )
{
    eqep->QEINT &= ( uint16 ) ~( uint16 ) QEINT_type;

    return;
} /*end of eQEP_disable_interrupt */

/** @brief Disable position compare
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_009 */
/* DesignId : EQEP_DesignId_009 */
/* Requirements : CONQ_QEP_SR9 */
void eqepDisablePosnCompare( eqepBASE_t * eqep )
{
    eqep->QPOSCTL &= ( uint16 ) ~eQEP_QPOSCTL_PCE;

    return;
} /*end of eQEP_disable_posn_compare () function */

/** @brief Disable position compare shadowing
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_010 */
/* DesignId : EQEP_DesignId_010 */
/* Requirements : CONQ_QEP_SR10 */
void eqepDisablePosnCompareShadow( eqepBASE_t * eqep )
{
    eqep->QPOSCTL &= ( uint16 ) ~eQEP_QPOSCTL_PCSHDW;

    return;
} /*end of eQEP_disable_posn_compare_shadow () function */

/** @brief Disable output sync pulse
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_011 */
/* DesignId : EQEP_DesignId_011 */
/* Requirements : CONQ_QEP_SR11 */
void eqepDisableSyncOut( eqepBASE_t * eqep )
{
    eqep->QDECCTL &= ( uint16 ) ~eQEP_QDECCTL_SOEN;

    return;
} /*end of eQEP_disable_sync_out () function */

/** @brief Disable unit timer
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_012 */
/* DesignId : EQEP_DesignId_012 */
/* Requirements : CONQ_QEP_SR12 */
void eqepDisableUnitTimer( eqepBASE_t * eqep )
{
    eqep->QEPCTL &= ( uint16 ) ~eQEP_QEPCTL_UTE;

    return;
} /*end of eQEP_disable_unit_timer () function */

/** @brief Disable watchdog timer
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_013 */
/* DesignId : EQEP_DesignId_013 */
/* Requirements : CONQ_QEP_SR13 */
void eqepDisableWatchdog( eqepBASE_t * eqep )
{
    eqep->QEPCTL &= ( uint16 ) ~eQEP_QEPCTL_WDE;

    return;
} /*end of eQEP_disable_watchdog () function */

/** @brief Enable capture
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_014 */
/* DesignId : EQEP_DesignId_014 */
/* Requirements : CONQ_QEP_SR14 */
void eqepEnableCapture( eqepBASE_t * eqep )
{
    eqep->QCAPCTL |= eQEP_QCAPCTL_CEN;

    return;
} /*end of eQEP_enable_capture () function */

/** @brief Enable counter
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_015 */
/* DesignId : EQEP_DesignId_015 */
/* Requirements : CONQ_QEP_SR15 */
void eqepEnableCounter( eqepBASE_t * eqep )
{
    eqep->QEPCTL |= eQEP_QEPCTL_QPEN;

    return;
} /*end of eQEP_enable_counter () function */

/** @brief Enable gating of index pulse
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_016 */
/* DesignId : EQEP_DesignId_016 */
/* Requirements : CONQ_QEP_SR16 */
void eqepEnableGateIndex( eqepBASE_t * eqep )
{
    eqep->QDECCTL |= ( uint16 ) eQEP_Igate_Enable;

    return;
} /*end of eQEP_enable_gate_index () function */

/** @brief Enable individual interrupt
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEINT_type			Individual interrupts
 */
/* SourceId : EQEP_SourceId_017 */
/* DesignId : EQEP_DesignId_017 */
/* Requirements : CONQ_QEP_SR17 */
void eqepEnableInterrupt( eqepBASE_t * eqep, QEINT_t QEINT_type )
{
    eqep->QEINT |= ( uint16 ) QEINT_type;

    return;
} /*end of eQEP_enable_interrupt () function */

/** @brief Enable position compare
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_018 */
/* DesignId : EQEP_DesignId_018 */
/* Requirements : CONQ_QEP_SR18 */
void eqepEnablePosnCompare( eqepBASE_t * eqep )
{
    eqep->QPOSCTL |= eQEP_QPOSCTL_PCE;

    return;
} /*end of eQEP_enable_posn_compare () function */

/** @brief Enable position compare shadowing
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_019 */
/* DesignId : EQEP_DesignId_019 */
/* Requirements : CONQ_QEP_SR19 */
void eqepEnablePosnCompareShadow( eqepBASE_t * eqep )
{
    eqep->QPOSCTL |= eQEP_QPOSCTL_PCSHDW;

    return;
} /*end of eQEP_enable_posn_compare_shadow () function */

/** @brief Enable output sync pulse
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_020 */
/* DesignId : EQEP_DesignId_020 */
/* Requirements : CONQ_QEP_SR46 */
void eqepEnableSyncOut( eqepBASE_t * eqep )
{
    eqep->QDECCTL |= eQEP_QDECCTL_SOEN;

    return;
} /*end of eQEP_enable_sync_out () function */

/** @brief Enable unit timer
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_021 */
/* DesignId : EQEP_DesignId_021 */
/* Requirements : CONQ_QEP_SR20 */
void eqepEnableUnitTimer( eqepBASE_t * eqep )
{
    eqep->QEPCTL |= eQEP_QEPCTL_UTE;

    return;
} /*end of eQEP_enable_unit_timer () function */

/** @brief Enable watchdog timer
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_022 */
/* DesignId : EQEP_DesignId_022 */
/* Requirements : CONQ_QEP_SR21 */
void eqepEnableWatchdog( eqepBASE_t * eqep )
{
    eqep->QEPCTL |= eQEP_QEPCTL_WDE;

    return;
} /*end of eQEP_enable_watchdog () function */

/** @brief Manually force QEP interrupt
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEINT			Individual interrupt
 */
/* SourceId : EQEP_SourceId_023 */
/* DesignId : EQEP_DesignId_023 */
/* Requirements : CONQ_QEP_SR22 */
void eqepForceInterrupt( eqepBASE_t * eqep, QEINT_t QEINT_type )
{
    eqep->QFRC |= ( uint16 ) QEINT_type;

    return;
} /*end of eQEP_force_interrupt () function */

/** @brief Reads capture period latch
 *   @param[in] eqep		Handle to QEP object
 *   @return						Counter value
 */
/* SourceId : EQEP_SourceId_024 */
/* DesignId : EQEP_DesignId_024 */
/* Requirements : CONQ_QEP_SR23 */
uint16 eqepReadCapturePeriodLatch( eqepBASE_t * eqep )
{
    return eqep->QCPRDLAT;
} /*end of eQEP_read_capture_period_latch () function */

/** @brief Reads timer latch
 *   @param[in] eqep		Handle to QEP object
 *   @return						Timer value
 */
/* SourceId : EQEP_SourceId_025 */
/* DesignId : EQEP_DesignId_025 */
/* Requirements : CONQ_QEP_SR24 */
uint16 eqepReadCaptureTimerLatch( eqepBASE_t * eqep )
{
    return eqep->QCTMRLAT;
} /*end of eQEP_read_capture_timer_latch () function */

/** @brief Reads interrupt flag value
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEINT			Which interrupt to interrogate
 *   @return						Interrupt flag value
 */
/* SourceId : EQEP_SourceId_064 */
/* DesignId : EQEP_DesignId_064 */
/* Requirements : CONQ_QEP_SR25 */
uint16 eqepReadInterruptFlag( eqepBASE_t * eqep, QEINT_t QEINT_type )
{
    return ( uint16 ) ( eqep->QFLG & ( uint16 ) QEINT_type );
} /*end of eQEP_read_interrupt_flag () function */

/** @brief Reads position compare register
 *   @param[in] eqep		Handle to QEP object
 *   @return						Counter value
 */
/* SourceId : EQEP_SourceId_026 */
/* DesignId : EQEP_DesignId_026 */
/* Requirements : CONQ_QEP_SR26 */
uint32 eqepReadPosnCompare( eqepBASE_t * eqep )
{
    return eqep->QPOSCMP;
} /*end of eQEP_read_posn_compare () function */

/** @brief Reads position counter
 *   @param[in] eqep		Handle to QEP object
 *   @return						Counter value
 */
/* SourceId : EQEP_SourceId_027 */
/* DesignId : EQEP_DesignId_027 */
/* Requirements : CONQ_QEP_SR27 */
uint32 eqepReadPosnCount( eqepBASE_t * eqep )
{
    return eqep->QPOSCNT;
} /*end of eQEP_read_posn_count () function */

/** @brief Reads position counter value index pulse latch register
 *   @param[in] eqep		Handle to QEP object
 *   @return						Counter value
 */
/* SourceId : EQEP_SourceId_028 */
/* DesignId : EQEP_DesignId_028 */
/* Requirements : CONQ_QEP_SR28 */
uint32 eqepReadPosnIndexLatch( eqepBASE_t * eqep )
{
    return eqep->QPOSILAT;
} /*end of eQEP_read_posn_index_latch () function */

/** @brief Reads position counter value
 *   @param[in] eqep		Handle to QEP object
 *   @return						Counter value
 */
/* SourceId : EQEP_SourceId_029 */
/* DesignId : EQEP_DesignId_029 */
/* Requirements : CONQ_QEP_SR29 */
uint32 eqepReadPosnLatch( eqepBASE_t * eqep )
{
    return eqep->QPOSLAT;
} /*end of eQEP_read_posn_latch () function */

/** @brief Reads position strobe latch
 *   @param[in] eqep		Handle to QEP object
 *   @return						Counter value
 */
/* SourceId : EQEP_SourceId_030 */
/* DesignId : EQEP_DesignId_030 */
/* Requirements : CONQ_QEP_SR30 */
uint32 eqepReadPosnStrobeLatch( eqepBASE_t * eqep )
{
    return eqep->QPOSSLAT;
} /*end of eQEP_read_posn_strobe_latch () function */

/** @brief Reads status register
 *   @param[in] eqep		Handle to QEP object
 *   @return						Status register value
 */
/* SourceId : EQEP_SourceId_031 */
/* DesignId : EQEP_DesignId_031 */
/* Requirements : CONQ_QEP_SR31 */
uint16 eqepReadStatus( eqepBASE_t * eqep )
{
    return eqep->QEPSTS;
} /*end of eqepReadStatus () function */

/** @brief Resets counter
 *   @param[in] eqep		Handle to QEP object
 */
/* SourceId : EQEP_SourceId_032 */
/* DesignId : EQEP_DesignId_032 */
/* Requirements : CONQ_QEP_SR32 */
void eqepResetCounter( eqepBASE_t * eqep )
{
    eqep->QEPCTL &= ( uint16 ) ~eQEP_QEPCTL_QPEN;

    return;
} /*end of eqepResetCounter () function */

/** @brief Sets capture latch mode
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEPCTL_Qclm		capture latch mode
 */
/* SourceId : EQEP_SourceId_033 */
/* DesignId : EQEP_DesignId_033 */
/* Requirements : CONQ_QEP_SR33 */
void eqepSetCaptureLatchMode( eqepBASE_t * eqep, QEPCTL_Qclm_t QEPCTL_Qclm )
{
    eqep->QEPCTL &= ( uint16 ) ~eQEP_QEPCTL_QCLM;
    eqep->QEPCTL |= QEPCTL_Qclm;

    return;
} /*end of eqepSetCaptureLatchMode () function */

/** @brief Sets capture period
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] period			Capture period
 */
/* SourceId : EQEP_SourceId_034 */
/* DesignId : EQEP_DesignId_034 */
/* Requirements : CONQ_QEP_SR34 */
void eqepSetCapturePeriod( eqepBASE_t * eqep, uint16 period )
{
    eqep->QCPRD = period;

    return;
} /*end of eqepSetCapturePeriod () function */

/** @brief Sets capture pre-scaler
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QCAPCTL_Ccps		Capture pre-scaler
 */
/* SourceId : EQEP_SourceId_035 */
/* DesignId : EQEP_DesignId_035 */
/* Requirements : CONQ_QEP_SR35 */
void eqepSetCapturePrescale( eqepBASE_t * eqep, QCAPCTL_Ccps_t QCAPCTL_Ccps )
{
    eqep->QCAPCTL &= ( uint16 ) ~eQEP_QCAPCTL_CCPS;
    eqep->QCAPCTL |= QCAPCTL_Ccps;
} /*end of eqepSetCapturePrescale () function */

/** @brief Sets emulation control
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEPCTL_Freesoft	Emulation control bits
 */
/* SourceId : EQEP_SourceId_036 */
/* DesignId : EQEP_DesignId_036 */
/* Requirements : CONQ_QEP_SR36 */
void eqepSetEmuControl( eqepBASE_t * eqep, QEPCTL_Freesoft_t QEPCTL_Freesoft )
{
    eqep->QEPCTL &= ( uint16 ) ~eQEP_QEPCTL_FREESOFT;
    eqep->QEPCTL |= QEPCTL_Freesoft;

    return;
} /*end of eqepSetEmuControl () function */

/** @brief Sets external clock rate
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] eQEP_Xcr			External clock rate
 */
/* SourceId : EQEP_SourceId_037 */
/* DesignId : EQEP_DesignId_037 */
/* Requirements : CONQ_QEP_SR37 */
void eqepSetExtClockRate( eqepBASE_t * eqep, eQEP_Xcr_t eQEP_Xcr )
{
    eqep->QDECCTL &= ( uint16 ) ~eQEP_QDECCTL_XCR;
    eqep->QDECCTL |= ( uint16 ) eQEP_Xcr;

    return;
} /*end of eqepSetExtClockRate () function */

/** @brief Sets the event which initializes the counter register
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEPCTL_Iei		Index event
 */
/* SourceId : EQEP_SourceId_038 */
/* DesignId : EQEP_DesignId_038 */
/* Requirements : CONQ_QEP_SR38 */
void eqepSetIndexEventInit( eqepBASE_t * eqep, QEPCTL_Iei_t QEPCTL_Iei )
{
    eqep->QEPCTL &= ( uint16 ) ~eQEP_QEPCTL_IEI;
    eqep->QEPCTL |= ( uint16 ) QEPCTL_Iei;

    return;
} /*end of eqepSetIndexEventInit () function */

/** @brief Sets the index event which latches the position counter
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEPCTL_Iel		Latch event
 */
/* SourceId : EQEP_SourceId_039 */
/* DesignId : EQEP_DesignId_039 */
/* Requirements : CONQ_QEP_SR39 */
void eqepSetIndexEventLatch( eqepBASE_t * eqep, QEPCTL_Iel_t QEPCTL_Iel )
{
    eqep->QEPCTL &= ( uint16 ) ~eQEP_QEPCTL_IEL;
    eqep->QEPCTL |= QEPCTL_Iel;

    return;
} /*end of eqepSetIndexEventLatch */

/** @brief Sets index polarity
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] eQEP_Qip			Index polarity
 */
/* SourceId : EQEP_SourceId_040 */
/* DesignId : EQEP_DesignId_040 */
/* Requirements : CONQ_QEP_SR40 */
void eqepSetIndexPolarity( eqepBASE_t * eqep, eQEP_Qip_t eQEP_Qip )
{
    eqep->QDECCTL &= ( uint16 ) ~eQEP_QDECCTL_QIP;
    eqep->QDECCTL |= eQEP_Qip;

    return;
} /*end of eqepSetIndexPolarity () function */

/** @brief Sets max position count
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] max_count		Maximum counter value
 */
/* SourceId : EQEP_SourceId_041 */
/* DesignId : EQEP_DesignId_041 */
/* Requirements : CONQ_QEP_SR41 */
void eqepSetMaxPosnCount( eqepBASE_t * eqep, uint32 max_count )
{
    eqep->QPOSMAX = max_count;

    return;
} /*end of eqepSetMaxPosnCount () function */

/** @brief Sets output pulse width when a match occur
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] pulse_width		Pulse width value
 */
/* SourceId : EQEP_SourceId_042 */
/* DesignId : EQEP_DesignId_042 */
/* Requirements : CONQ_QEP_SR42 */
void eqepSetPosnComparePulseWidth( eqepBASE_t * eqep, uint16 pulse_width )
{
    uint16 pulse_width_masked;

    pulse_width_masked = pulse_width & 4095U;
    eqep->QPOSCTL &= ( uint16 ) ~eQEP_QPOSCTL_PCSPW;
    eqep->QPOSCTL |= pulse_width_masked;

    return;
} /*end of eqepSetPosnComparePulseWidth () function */

/** @brief Sets position compare shadow load mode
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QPOSCTL_Pcload	PC load event
 */
/* SourceId : EQEP_SourceId_043 */
/* DesignId : EQEP_DesignId_043 */
/* Requirements : CONQ_QEP_SR43 */
void eqepSetPosnCompareShadowLoad( eqepBASE_t * eqep, QPOSCTL_Pcload_t QPOSCTL_Pcload )
{
    eqep->QPOSCTL &= ( uint16 ) ~eQEP_QPOSCTL_PCLOAD;
    eqep->QPOSCTL |= ( uint16 ) QPOSCTL_Pcload;

    return;
} /*end of eqepSetPosnCompareShadowLoad () function */

/** @brief Sets position counter reset mode
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEPCTL_Pcrm		Position counter reset mode
 */
/* SourceId : EQEP_SourceId_044 */
/* DesignId : EQEP_DesignId_044 */
/* Requirements : CONQ_QEP_SR44 */
void eqepSetPosnCountResetMode( eqepBASE_t * eqep, QEPCTL_Pcrm_t QEPCTL_Pcrm )
{
    eqep->QEPCTL &= ( uint16 ) ~eQEP_QEPCTL_PCRM;
    eqep->QEPCTL |= ( uint16 ) QEPCTL_Pcrm;

    return;
} /*end of eqepSetPosnCountResetMode () function */

/** @brief Sets initial position counter value
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] init_count		initial counter value
 */
/* SourceId : EQEP_SourceId_045 */
/* DesignId : EQEP_DesignId_045 */
/* Requirements : CONQ_QEP_SR45 */
void eqepSetPosnInitCount( eqepBASE_t * eqep, uint32 init_count )
{
    eqep->QPOSINIT = init_count;

    return;
} /*end of eqepSetPosnInitCount () function */

/** @brief Selects whether index or strobe pin is used for sync output
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] eQEP_SPsel		Selected pin
 */
/* SourceId : EQEP_SourceId_046 */
/* DesignId : EQEP_DesignId_046 */
/* Requirements : CONQ_QEP_SR47 */
void eqepSetSelectSyncPin( eqepBASE_t * eqep, eQEP_Spsel_t eQEP_SPsel )
{
    eqep->QDECCTL &= ( uint16 ) ~eQEP_QDECCTL_SPSEL;
    eqep->QDECCTL |= ( uint16 ) eQEP_SPsel;

    return;
} /*end of eQEP_set_select_sync_pin () function */

/** @brief Determines if software initialization of position counter enabled
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEPCTL_Swi		Enable/disable position counter initialization
 */
/* SourceId : EQEP_SourceId_047 */
/* DesignId : EQEP_DesignId_047 */
/* Requirements : CONQ_QEP_SR48 */
void eqepSetSoftInit( eqepBASE_t * eqep, QEPCTL_Swi_t QEPCTL_Swi )
{
    eqep->QEPCTL &= ( uint16 ) ~eQEP_QEPCTL_SWI;
    eqep->QEPCTL |= ( uint16 ) QEPCTL_Swi;

    return;
} /*end of eQEP_set_soft_init () function */

/** @brief Determines strobe initialization of position counter
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEPCTL_Sei		Strobe initialization of position counter (disabled,
 * rising edge of QEPI) or rising/falling depending on direction
 */
/* SourceId : EQEP_SourceId_048 */
/* DesignId : EQEP_DesignId_048 */
/* Requirements : CONQ_QEP_SR49 */
void eqepSetStrobeEventInit( eqepBASE_t * eqep, QEPCTL_Sei_t QEPCTL_Sei )
{
    eqep->QEPCTL &= ( uint16 ) ~eQEP_QEPCTL_SEI;
    eqep->QEPCTL |= ( uint16 ) QEPCTL_Sei;

    return;
} /*end of eQEP_set_strobe_event_init () function */

/** @brief Sets up strobe latch of position counter
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEPCTL_Sel		Sets strobe latch of position counter
 */
/* SourceId : EQEP_SourceId_049 */
/* DesignId : EQEP_DesignId_049 */
/* Requirements : CONQ_QEP_SR50 */
void eqepSetStrobeEventLatch( eqepBASE_t * eqep, QEPCTL_Sel_t QEPCTL_Sel )
{
    eqep->QEPCTL &= ( uint16 ) ~eQEP_QEPCTL_SEL;
    eqep->QEPCTL |= QEPCTL_Sel;

    return;
} /*end of eQEP_set_strobe_event_latch () function */

/** @brief Sets up strobe polarity
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] eQEP_Qsp			Strobe polarity
 */
/* SourceId : EQEP_SourceId_050 */
/* DesignId : EQEP_DesignId_050 */
/* Requirements : CONQ_QEP_SR51 */
void eqepSetStrobePolarity( eqepBASE_t * eqep, eQEP_Qsp_t eQEP_Qsp )
{
    eqep->QDECCTL &= ( uint16 ) ~eQEP_QDECCTL_QSP;
    eqep->QDECCTL |= eQEP_Qsp;

    return;
} /*end of eqepSetStrobePolarity () function */

/** @brief Sets up swapping of A/B channels
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] eQEP_Swap			Swap/don't swap A/B channels
 */
/* SourceId : EQEP_SourceId_051 */
/* DesignId : EQEP_DesignId_051 */
/* Requirements : CONQ_QEP_SR52 */
void eqepSetSwapQuadInputs( eqepBASE_t * eqep, eQEP_Swap_t eQEP_Swap )
{
    eqep->QDECCTL &= ( uint16 ) ~eQEP_QDECCTL_SWAP;
    eqep->QDECCTL |= ( uint16 ) eQEP_Swap;

    return;
} /*end of eqepSetSwapQuadInputs () function */

/** @brief Sets sync output compare polarity
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QPOSCTL_Pcpol	Polarity of sync output
 */
/* SourceId : EQEP_SourceId_052 */
/* DesignId : EQEP_DesignId_052 */
/* Requirements : CONQ_QEP_SR53 */
void eqepSetSynchOutputComparePolarity( eqepBASE_t * eqep, QPOSCTL_Pcpol_t QPOSCTL_Pcpol )
{
    eqep->QPOSCTL &= ( uint16 ) ~eQEP_QPOSCTL_PCPOL;
    eqep->QPOSCTL |= ( uint16 ) QPOSCTL_Pcpol;

    return;
} /*end of eqepSetSynchOutputComparePolarity () function */

/** @brief Sets unit timer period
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] unit_period		Unit period
 */
/* SourceId : EQEP_SourceId_053 */
/* DesignId : EQEP_DesignId_053 */
/* Requirements : CONQ_QEP_SR54 */
void eqepSetUnitPeriod( eqepBASE_t * eqep, uint32 unit_period )
{
    eqep->QUPRD = unit_period;

    return;
} /*end of eqepSetUnitPeriod () function */

/** @brief Sets unit timer prescaling
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QCAPCTL_Upps		Unit timer prescaling
 */
/* SourceId : EQEP_SourceId_054 */
/* DesignId : EQEP_DesignId_054 */
/* Requirements : CONQ_QEP_SR55 */
void eqepSetUnitPosnPrescale( eqepBASE_t * eqep, QCAPCTL_Upps_t QCAPCTL_Upps )
{
    eqep->QCAPCTL &= ( uint16 ) ~eQEP_QCAPCTL_UPPS;
    eqep->QCAPCTL |= ( uint16 ) QCAPCTL_Upps;

    return;
} /*end of eqepSetUnitPosnPrescale () function */

/** @brief Sets watchdog period
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] watchdog_period	Watchdog period
 */
/* SourceId : EQEP_SourceId_055 */
/* DesignId : EQEP_DesignId_055 */
/* Requirements : CONQ_QEP_SR56 */
void eqepSetWatchdogPeriod( eqepBASE_t * eqep, uint16 watchdog_period )
{
    eqep->QWDPRD = watchdog_period;

    return;
} /*end of eqepSetWatchdogPeriod () function */

/** @brief Sets strobe event latch
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] QEPCTL_Sel	Sets strobe latch of position counter
 */
/* SourceId : EQEP_SourceId_056 */
/* DesignId : EQEP_DesignId_056 */
/* Requirements : CONQ_QEP_SR57 */
void eqepSetupStrobeEventLatch( eqepBASE_t * eqep, QEPCTL_Sel_t QEPCTL_Sel )
{
    eqep->QEPCTL &= ( uint16 ) ~eQEP_QEPCTL_SEL;
    eqep->QEPCTL |= ( uint16 ) QEPCTL_Sel;

    return;
} /*end of eqepSetupStrobeEventLatch () function */

/** @brief Sets A polarity
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] eQEP_Qap			Channel A polarity
 */
/* SourceId : EQEP_SourceId_057 */
/* DesignId : EQEP_DesignId_057 */
/* Requirements : CONQ_QEP_SR58 */
void eqepSetAPolarity( eqepBASE_t * eqep, eQEP_Qap_t eQEP_Qap )
{
    eqep->QDECCTL &= ( uint16 ) ~eQEP_QDECCTL_QAP;
    eqep->QDECCTL |= ( uint16 ) eQEP_Qap;

    return;
} /*end of eqepSetAPolarity () function */

/** @brief Sets B polarity
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] eQEP_Qbp			Channel B polarity
 */
/* SourceId : EQEP_SourceId_058 */
/* DesignId : EQEP_DesignId_058 */
/* Requirements : CONQ_QEP_SR59 */
void eqepSetBPolarity( eqepBASE_t * eqep, eQEP_Qbp_t eQEP_Qbp )
{
    eqep->QDECCTL &= ( uint16 ) ~eQEP_QDECCTL_QBP;
    eqep->QDECCTL |= ( uint16 ) eQEP_Qbp;

    return;
} /*end of eQEP_set_B_polarity () function */

/** @brief Set QEP counting mode
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] eQEP_Qsrc Sets QEP counting mode
 */
/* SourceId : EQEP_SourceId_059 */
/* DesignId : EQEP_DesignId_059 */
/* Requirements : CONQ_QEP_SR60 */
void eqepSetQEPSource( eqepBASE_t * eqep, eQEP_Qsrc_t eQEP_Qsrc )
{
    /* set the value */
    eqep->QDECCTL &= ( uint16 ) ~eQEP_QDECCTL_QSRC;
    eqep->QDECCTL |= ( uint16 ) eQEP_Qsrc;

    return;
} /*end of eQEP_set_eQEP_source () function */

/** @brief Writes a value to the position compare register
 *   @param[in] eqep		Handle to QEP object
 *   @param[in] posn				Position compare register value
 */
/* SourceId : EQEP_SourceId_060 */
/* DesignId : EQEP_DesignId_060 */
/* Requirements : CONQ_QEP_SR61 */
void eqepWritePosnCompare( eqepBASE_t * eqep, uint32 posn )
{
    eqep->QPOSCMP = posn;

    return;
} /*end of eQEP_write_posn_compare () function */

/** @fn void eqep1GetConfigValue(eqep_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *    @param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *    @param[in] type:     whether initial or current value of the configuration registers
 * need to be stored
 *                        - InitialValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *                        - CurrentValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : EQEP_SourceId_061 */
/* DesignId : EQEP_DesignId_061 */
/* Requirements : CONQ_QEP_SR64 */
void eqep1GetConfigValue( eqep_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_QPOSINIT = EQEP1_QPOSINIT_CONFIGVALUE;
        config_reg->CONFIG_QPOSMAX = EQEP1_QPOSMAX_CONFIGVALUE;
        config_reg->CONFIG_QPOSCMP = EQEP1_QPOSCMP_CONFIGVALUE;
        config_reg->CONFIG_QUPRD = EQEP1_QUPRD_CONFIGVALUE;
        config_reg->CONFIG_QWDPRD = EQEP1_QWDPRD_CONFIGVALUE;
        config_reg->CONFIG_QDECCTL = EQEP1_QDECCTL_CONFIGVALUE;
        config_reg->CONFIG_QEPCTL = EQEP1_QEPCTL_CONFIGVALUE;
        config_reg->CONFIG_QCAPCTL = EQEP1_QCAPCTL_CONFIGVALUE;
        config_reg->CONFIG_QPOSCTL = EQEP1_QPOSCTL_CONFIGVALUE;
        config_reg->CONFIG_QEINT = EQEP1_QEINT_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_QPOSINIT = eqepREG1->QPOSINIT;
        config_reg->CONFIG_QPOSMAX = eqepREG1->QPOSMAX;
        config_reg->CONFIG_QPOSCMP = eqepREG1->QPOSCMP;
        config_reg->CONFIG_QUPRD = eqepREG1->QUPRD;
        config_reg->CONFIG_QWDPRD = eqepREG1->QWDPRD;
        config_reg->CONFIG_QDECCTL = eqepREG1->QDECCTL;
        config_reg->CONFIG_QEPCTL = eqepREG1->QEPCTL;
        config_reg->CONFIG_QCAPCTL = eqepREG1->QCAPCTL;
        config_reg->CONFIG_QPOSCTL = eqepREG1->QPOSCTL;
        config_reg->CONFIG_QEINT = eqepREG1->QEINT;
    }
}

/** @fn void eqep2GetConfigValue(eqep_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *    @param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *    @param[in] type:     whether initial or current value of the configuration registers
 * need to be stored
 *                        - InitialValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *                        - CurrentValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : EQEP_SourceId_062 */
/* DesignId : EQEP_DesignId_062 */
/* Requirements : CONQ_QEP_SR65 */
void eqep2GetConfigValue( eqep_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_QPOSINIT = EQEP2_QPOSINIT_CONFIGVALUE;
        config_reg->CONFIG_QPOSMAX = EQEP2_QPOSMAX_CONFIGVALUE;
        config_reg->CONFIG_QPOSCMP = EQEP2_QPOSCMP_CONFIGVALUE;
        config_reg->CONFIG_QUPRD = EQEP2_QUPRD_CONFIGVALUE;
        config_reg->CONFIG_QWDPRD = EQEP2_QWDPRD_CONFIGVALUE;
        config_reg->CONFIG_QDECCTL = EQEP2_QDECCTL_CONFIGVALUE;
        config_reg->CONFIG_QEPCTL = EQEP2_QEPCTL_CONFIGVALUE;
        config_reg->CONFIG_QCAPCTL = EQEP2_QCAPCTL_CONFIGVALUE;
        config_reg->CONFIG_QPOSCTL = EQEP2_QPOSCTL_CONFIGVALUE;
        config_reg->CONFIG_QEINT = EQEP2_QEINT_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_QPOSINIT = eqepREG2->QPOSINIT;
        config_reg->CONFIG_QPOSMAX = eqepREG2->QPOSMAX;
        config_reg->CONFIG_QPOSCMP = eqepREG2->QPOSCMP;
        config_reg->CONFIG_QUPRD = eqepREG2->QUPRD;
        config_reg->CONFIG_QWDPRD = eqepREG2->QWDPRD;
        config_reg->CONFIG_QDECCTL = eqepREG2->QDECCTL;
        config_reg->CONFIG_QEPCTL = eqepREG2->QEPCTL;
        config_reg->CONFIG_QCAPCTL = eqepREG2->QCAPCTL;
        config_reg->CONFIG_QPOSCTL = eqepREG2->QPOSCTL;
        config_reg->CONFIG_QEINT = eqepREG2->QEINT;
    }
}

/*end of file*/
