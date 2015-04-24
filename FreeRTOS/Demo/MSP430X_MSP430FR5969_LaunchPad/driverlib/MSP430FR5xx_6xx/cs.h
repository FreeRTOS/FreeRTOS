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
// cs.h - Driver for the CS Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_CS_H__
#define __MSP430WARE_CS_H__

#include "inc/hw_memmap.h"

#if defined(__MSP430_HAS_CS__) || defined(__MSP430_HAS_SFR__)

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
// The following are values that can be passed to the clockSourceDivider
// parameter for functions: CS_initClockSignal().
//
//*****************************************************************************
#define CS_CLOCK_DIVIDER_1                                              DIVM__1
#define CS_CLOCK_DIVIDER_2                                              DIVM__2
#define CS_CLOCK_DIVIDER_4                                              DIVM__4
#define CS_CLOCK_DIVIDER_8                                              DIVM__8
#define CS_CLOCK_DIVIDER_16                                            DIVM__16
#define CS_CLOCK_DIVIDER_32                                            DIVM__32

//*****************************************************************************
//
// The following are values that can be passed to the selectClock parameter for
// functions: CS_enableClockRequest(), and CS_disableClockRequest(); the
// selectedClockSignal parameter for functions: CS_initClockSignal().
//
//*****************************************************************************
#define CS_ACLK                                                            0x01
#define CS_MCLK                                                            0x02
#define CS_SMCLK                                                           0x04
#define CS_MODOSC                                                   MODCLKREQEN

//*****************************************************************************
//
// The following are values that can be passed to the clockSource parameter for
// functions: CS_initClockSignal().
//
//*****************************************************************************
#define CS_VLOCLK_SELECT                                           SELM__VLOCLK
#define CS_DCOCLK_SELECT                                           SELM__DCOCLK
#define CS_LFXTCLK_SELECT                                         SELM__LFXTCLK
#define CS_HFXTCLK_SELECT                                         SELM__HFXTCLK
#define CS_LFMODOSC_SELECT                                       SELM__LFMODOSC
#define CS_MODOSC_SELECT                                           SELM__MODOSC

//*****************************************************************************
//
// The following are values that can be passed to the lfxtdrive parameter for
// functions: CS_turnOnLFXT(), and CS_turnOnLFXTWithTimeout().
//
//*****************************************************************************
#define CS_LFXT_DRIVE_0                                             LFXTDRIVE_0
#define CS_LFXT_DRIVE_1                                             LFXTDRIVE_1
#define CS_LFXT_DRIVE_2                                             LFXTDRIVE_2
#define CS_LFXT_DRIVE_3                                             LFXTDRIVE_3

//*****************************************************************************
//
// The following are values that can be passed to the hfxtdrive parameter for
// functions: CS_turnOnHFXT(), and CS_turnOnHFXTWithTimeout().
//
//*****************************************************************************
#define CS_HFXT_DRIVE_4MHZ_8MHZ                                     HFXTDRIVE_0
#define CS_HFXT_DRIVE_8MHZ_16MHZ                                    HFXTDRIVE_1
#define CS_HFXT_DRIVE_16MHZ_24MHZ                                   HFXTDRIVE_2
#define CS_HFXT_DRIVE_24MHZ_32MHZ                                   HFXTDRIVE_3

//*****************************************************************************
//
// The following are values that can be passed to the mask parameter for
// functions: CS_getFaultFlagStatus(), and CS_clearFaultFlag() as well as
// returned by the CS_getFaultFlagStatus() function.
//
//*****************************************************************************
#define CS_LFXTOFFG                                                    LFXTOFFG
#define CS_HFXTOFFG                                                    HFXTOFFG

//*****************************************************************************
//
// The following are values that can be passed to the dcorsel parameter for
// functions: CS_setDCOFreq().
//
//*****************************************************************************
#define CS_DCORSEL_0                                                       0x00
#define CS_DCORSEL_1                                                    DCORSEL

//*****************************************************************************
//
// The following are values that can be passed to the dcofsel parameter for
// functions: CS_setDCOFreq().
//
//*****************************************************************************
#define CS_DCOFSEL_0                                                  DCOFSEL_0
#define CS_DCOFSEL_1                                                  DCOFSEL_1
#define CS_DCOFSEL_2                                                  DCOFSEL_2
#define CS_DCOFSEL_3                                                  DCOFSEL_3
#define CS_DCOFSEL_4                                                  DCOFSEL_4
#define CS_DCOFSEL_5                                                  DCOFSEL_5
#define CS_DCOFSEL_6                                                  DCOFSEL_6

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Sets the external clock source
//!
//! This function sets the external clock sources LFXT and HFXT crystal
//! oscillator frequency values. This function must be called if an external
//! crystal LFXT or HFXT is used and the user intends to call CS_getMCLK,
//! CS_getSMCLK, CS_getACLK and CS_turnOnLFXT, CS_LFXTByPass,
//! CS_turnOnLFXTWithTimeout, CS_LFXTByPassWithTimeout, CS_turnOnHFXT,
//! CS_HFXTByPass, CS_turnOnHFXTWithTimeout, CS_HFXTByPassWithTimeout.
//!
//! \param LFXTCLK_frequency is the LFXT crystal frequencies in Hz
//! \param HFXTCLK_frequency is the HFXT crystal frequencies in Hz
//!
//! \return None
//
//*****************************************************************************
extern void CS_setExternalClockSource(uint32_t LFXTCLK_frequency,
                                      uint32_t HFXTCLK_frequency);

//*****************************************************************************
//
//! \brief Initializes clock signal
//!
//! This function initializes each of the clock signals. The user must ensure
//! that this function is called for each clock signal. If not, the default
//! state is assumed for the particular clock signal. Refer to MSP430ware
//! documentation for CS module or Device Family User's Guide for details of
//! default clock signal states.
//!
//! \param selectedClockSignal Selected clock signal
//!        Valid values are:
//!        - \b CS_ACLK
//!        - \b CS_MCLK
//!        - \b CS_SMCLK
//!        - \b CS_MODOSC
//! \param clockSource is the selected clock signal
//!        Valid values are:
//!        - \b CS_VLOCLK_SELECT
//!        - \b CS_DCOCLK_SELECT - [Not available for ACLK]
//!        - \b CS_LFXTCLK_SELECT
//!        - \b CS_HFXTCLK_SELECT - [Not available for ACLK]
//!        - \b CS_LFMODOSC_SELECT
//!        - \b CS_MODOSC_SELECT - [Not available for ACLK]
//! \param clockSourceDivider is the selected clock divider to calculate clock
//!        signal from clock source.
//!        Valid values are:
//!        - \b CS_CLOCK_DIVIDER_1 - [Default for ACLK]
//!        - \b CS_CLOCK_DIVIDER_2
//!        - \b CS_CLOCK_DIVIDER_4
//!        - \b CS_CLOCK_DIVIDER_8 - [Default for SMCLK and MCLK]
//!        - \b CS_CLOCK_DIVIDER_16
//!        - \b CS_CLOCK_DIVIDER_32
//!
//! Modified bits of \b CSCTL0 register, bits of \b CSCTL3 register and bits of
//! \b CSCTL2 register.
//!
//! \return None
//
//*****************************************************************************
extern void CS_initClockSignal(uint8_t selectedClockSignal,
                               uint16_t clockSource,
                               uint16_t clockSourceDivider);

//*****************************************************************************
//
//! \brief Initializes the LFXT crystal in low frequency mode.
//!
//! Initializes the LFXT crystal oscillator in low frequency mode. Loops until
//! all oscillator fault flags are cleared, with no timeout. See the device-
//! specific data sheet for appropriate drive settings. IMPORTANT: User must
//! call CS_setExternalClockSource function to set frequency of external clocks
//! before calling this function.
//!
//! \param lfxtdrive is the target drive strength for the LFXT crystal
//!        oscillator.
//!        Valid values are:
//!        - \b CS_LFXT_DRIVE_0
//!        - \b CS_LFXT_DRIVE_1
//!        - \b CS_LFXT_DRIVE_2
//!        - \b CS_LFXT_DRIVE_3 [Default]
//!
//! Modified bits of \b CSCTL0 register, bits of \b CSCTL5 register, bits of \b
//! CSCTL4 register and bits of \b SFRIFG1 register.
//!
//! \return None
//
//*****************************************************************************
extern void CS_turnOnLFXT(uint16_t lfxtdrive);

//*****************************************************************************
//
//! \brief Bypasses the LFXT crystal oscillator.
//!
//! Bypasses the LFXT crystal oscillator. Loops until all oscillator fault
//! flags are cleared, with no timeout. IMPORTANT: User must call
//! CS_setExternalClockSource function to set frequency of external clocks
//! before calling this function.
//!
//!
//! Modified bits of \b CSCTL0 register, bits of \b CSCTL5 register, bits of \b
//! CSCTL4 register and bits of \b SFRIFG register.
//!
//! \return None
//
//*****************************************************************************
extern void CS_bypassLFXT(void);

//*****************************************************************************
//
//! \brief Initializes the LFXT crystal oscillator in low frequency mode with
//! timeout.
//!
//! Initializes the LFXT crystal oscillator in low frequency mode with timeout.
//! Loops until all oscillator fault flags are cleared or until a timeout
//! counter is decremented and equals to zero. See the device-specific
//! datasheet for appropriate drive settings. IMPORTANT: User must call
//! CS_setExternalClockSource to set frequency of external clocks before
//! calling this function.
//!
//! \param lfxtdrive is the target drive strength for the LFXT crystal
//!        oscillator.
//!        Valid values are:
//!        - \b CS_LFXT_DRIVE_0
//!        - \b CS_LFXT_DRIVE_1
//!        - \b CS_LFXT_DRIVE_2
//!        - \b CS_LFXT_DRIVE_3 [Default]
//! \param timeout is the count value that gets decremented every time the loop
//!        that clears oscillator fault flags gets executed.
//!
//! Modified bits of \b CSCTL0 register, bits of \b CSCTL5 register, bits of \b
//! CSCTL4 register and bits of \b SFRIFG1 register.
//!
//! \return STATUS_SUCCESS or STATUS_FAIL indicating if the LFXT crystal
//!         oscillator was initialized successfully
//
//*****************************************************************************
extern bool CS_turnOnLFXTWithTimeout(uint16_t lfxtdrive,
                                     uint32_t timeout);

//*****************************************************************************
//
//! \brief Bypass the LFXT crystal oscillator with timeout.
//!
//! Bypasses the LFXT crystal oscillator with timeout. Loops until all
//! oscillator fault flags are cleared or until a timeout counter is
//! decremented and equals to zero. NOTE: User must call
//! CS_setExternalClockSource to set frequency of external clocks before
//! calling this function.
//!
//! \param timeout is the count value that gets decremented every time the loop
//!        that clears oscillator fault flags gets executed.
//!
//! Modified bits of \b CSCTL0 register, bits of \b CSCTL5 register, bits of \b
//! CSCTL4 register and bits of \b SFRIFG register.
//!
//! \return STATUS_SUCCESS or STATUS_FAIL
//
//*****************************************************************************
extern bool CS_bypassLFXTWithTimeout(uint32_t timeout);

//*****************************************************************************
//
//! \brief Stops the LFXT oscillator using the LFXTOFF bit.
//!
//!
//! Modified bits of \b CSCTL4 register.
//!
//! \return None
//
//*****************************************************************************
extern void CS_turnOffLFXT(void);

//*****************************************************************************
//
//! \brief Starts the HFXFT crystal
//!
//! Initializes the HFXT crystal oscillator, which supports crystal frequencies
//! between 0 MHz and 24 MHz, depending on the selected drive strength. Loops
//! until all oscillator fault flags are cleared, with no timeout. See the
//! device-specific data sheet for appropriate drive settings. NOTE: User must
//! call CS_setExternalClockSource to set frequency of external clocks before
//! calling this function.
//!
//! \param hfxtdrive is the target drive strength for the HFXT crystal
//!        oscillator.
//!        Valid values are:
//!        - \b CS_HFXT_DRIVE_4MHZ_8MHZ
//!        - \b CS_HFXT_DRIVE_8MHZ_16MHZ
//!        - \b CS_HFXT_DRIVE_16MHZ_24MHZ
//!        - \b CS_HFXT_DRIVE_24MHZ_32MHZ [Default]
//!
//! Modified bits of \b CSCTL5 register, bits of \b CSCTL4 register and bits of
//! \b SFRIFG1 register.
//!
//! \return None
//
//*****************************************************************************
extern void CS_turnOnHFXT(uint16_t hfxtdrive);

//*****************************************************************************
//
//! \brief Bypasses the HFXT crystal oscillator
//!
//! Bypasses the HFXT crystal oscillator, which supports crystal frequencies
//! between 0 MHz and 24 MHz. Loops until all oscillator fault flags are
//! cleared, with no timeout.NOTE: User must call CS_setExternalClockSource to
//! set frequency of external clocks before calling this function.
//!
//!
//! Modified bits of \b CSCTL5 register, bits of \b CSCTL4 register and bits of
//! \b SFRIFG register.
//!
//! \return None
//
//*****************************************************************************
extern void CS_bypassHFXT(void);

//*****************************************************************************
//
//! \brief Initializes the HFXT crystal oscillator with timeout.
//!
//! Initializes the HFXT crystal oscillator, which supports crystal frequencies
//! between 0 MHz and 24 MHz, depending on the selected drive strength. Loops
//! until all oscillator fault flags are cleared or until a timeout counter is
//! decremented and equals to zero. See the device-specific data sheet for
//! appropriate drive settings. NOTE: User must call CS_setExternalClockSource
//! to set frequency of external clocks before calling this function.
//!
//! \param hfxtdrive is the target drive strength for the HFXT crystal
//!        oscillator.
//!        Valid values are:
//!        - \b CS_HFXT_DRIVE_4MHZ_8MHZ
//!        - \b CS_HFXT_DRIVE_8MHZ_16MHZ
//!        - \b CS_HFXT_DRIVE_16MHZ_24MHZ
//!        - \b CS_HFXT_DRIVE_24MHZ_32MHZ [Default]
//! \param timeout is the count value that gets decremented every time the loop
//!        that clears oscillator fault flags gets executed.
//!
//! Modified bits of \b CSCTL5 register, bits of \b CSCTL4 register and bits of
//! \b SFRIFG1 register.
//!
//! \return STATUS_SUCCESS or STATUS_FAIL
//
//*****************************************************************************
extern bool CS_turnOnHFXTWithTimeout(uint16_t hfxtdrive,
                                     uint32_t timeout);

//*****************************************************************************
//
//! \brief Bypasses the HFXT crustal oscillator with timeout
//!
//! Bypasses the HFXT crystal oscillator, which supports crystal frequencies
//! between 0 MHz and 24 MHz. Loops until all oscillator fault flags are
//! cleared or until a timeout counter is decremented and equals to zero. NOTE:
//! User must call CS_setExternalClockSource to set frequency of external
//! clocks before calling this function.
//!
//! \param timeout is the count value that gets decremented every time the loop
//!        that clears oscillator fault flags gets executed.
//!
//! Modified bits of \b CSCTL5 register, bits of \b CSCTL4 register and bits of
//! \b SFRIFG1 register.
//!
//! \return STATUS_SUCCESS or STATUS_FAIL
//
//*****************************************************************************
extern bool CS_bypassHFXTWithTimeout(uint32_t timeout);

//*****************************************************************************
//
//! \brief Stops the HFXT oscillator using the HFXTOFF bit.
//!
//!
//! Modified bits of \b CSCTL4 register.
//!
//! \return None
//
//*****************************************************************************
extern void CS_turnOffHFXT(void);

//*****************************************************************************
//
//! \brief Enables conditional module requests
//!
//! \param selectClock selects specific request enables.
//!        Valid values are:
//!        - \b CS_ACLK
//!        - \b CS_MCLK
//!        - \b CS_SMCLK
//!        - \b CS_MODOSC
//!
//! Modified bits of \b CSCTL6 register.
//!
//! \return None
//
//*****************************************************************************
extern void CS_enableClockRequest(uint8_t selectClock);

//*****************************************************************************
//
//! \brief Disables conditional module requests
//!
//! \param selectClock selects specific request enables.
//!        Valid values are:
//!        - \b CS_ACLK
//!        - \b CS_MCLK
//!        - \b CS_SMCLK
//!        - \b CS_MODOSC
//!
//! Modified bits of \b CSCTL6 register.
//!
//! \return None
//
//*****************************************************************************
extern void CS_disableClockRequest(uint8_t selectClock);

//*****************************************************************************
//
//! \brief Gets the current CS fault flag status.
//!
//! \param mask is the masked interrupt flag status to be returned. Mask
//!        parameter can be either any of the following selection.
//!        Mask value is the logical OR of any of the following:
//!        - \b CS_LFXTOFFG - LFXT oscillator fault flag
//!        - \b CS_HFXTOFFG - HFXT oscillator fault flag
//!
//! \return Logical OR of any of the following:
//!         - \b CS_LFXTOFFG LFXT oscillator fault flag
//!         - \b CS_HFXTOFFG HFXT oscillator fault flag
//!         \n indicating the status of the masked interrupts
//
//*****************************************************************************
extern uint8_t CS_getFaultFlagStatus(uint8_t mask);

//*****************************************************************************
//
//! \brief Clears the current CS fault flag status for the masked bit.
//!
//! \param mask is the masked interrupt flag status to be returned. mask
//!        parameter can be any one of the following
//!        Mask value is the logical OR of any of the following:
//!        - \b CS_LFXTOFFG - LFXT oscillator fault flag
//!        - \b CS_HFXTOFFG - HFXT oscillator fault flag
//!
//! Modified bits of \b CSCTL5 register.
//!
//! \return None
//
//*****************************************************************************
extern void CS_clearFaultFlag(uint8_t mask);

//*****************************************************************************
//
//! \brief Get the current ACLK frequency.
//!
//! If a oscillator fault is set, the frequency returned will be based on the
//! fail safe mechanism of CS module. The user of this API must ensure that
//! CS_externalClockSourceInit API was invoked before in case LFXT or HFXT is
//! being used.
//!
//!
//! \return Current ACLK frequency in Hz
//
//*****************************************************************************
extern uint32_t CS_getACLK(void);

//*****************************************************************************
//
//! \brief Get the current SMCLK frequency.
//!
//! If a oscillator fault is set, the frequency returned will be based on the
//! fail safe mechanism of CS module. The user of this API must ensure that
//! CS_externalClockSourceInit API was invoked before in case LFXT or HFXT is
//! being used.
//!
//!
//! \return Current SMCLK frequency in Hz
//
//*****************************************************************************
extern uint32_t CS_getSMCLK(void);

//*****************************************************************************
//
//! \brief Get the current MCLK frequency.
//!
//! If a oscillator fault is set, the frequency returned will be based on the
//! fail safe mechanism of CS module. The user of this API must ensure that
//! CS_externalClockSourceInit API was invoked before in case LFXT or HFXT is
//! being used.
//!
//!
//! \return Current MCLK frequency in Hz
//
//*****************************************************************************
extern uint32_t CS_getMCLK(void);

//*****************************************************************************
//
//! \brief Turns off VLO
//!
//!
//! Modified bits of \b CSCTL4 register.
//!
//! \return None
//
//*****************************************************************************
extern void CS_turnOffVLO(void);

//*****************************************************************************
//
//! \brief Clears all the Oscillator Flags
//!
//! \param timeout is the count value that gets decremented every time the loop
//!        that clears oscillator fault flags gets executed.
//!
//! Modified bits of \b CSCTL5 register and bits of \b SFRIFG1 register.
//!
//! \return the mask of the oscillator flag status
//
//*****************************************************************************
extern uint16_t CS_clearAllOscFlagsWithTimeout(uint32_t timeout);

//*****************************************************************************
//
//! \brief Set DCO frequency
//!
//! \param dcorsel selects frequency range option.
//!        Valid values are:
//!        - \b CS_DCORSEL_0 [Default] - Low Frequency Option
//!        - \b CS_DCORSEL_1 - High Frequency Option
//! \param dcofsel selects valid frequency options based on dco frequency range
//!        selection (dcorsel)
//!        Valid values are:
//!        - \b CS_DCOFSEL_0 - Low frequency option 1MHz. High frequency option
//!           1MHz.
//!        - \b CS_DCOFSEL_1 - Low frequency option 2.67MHz. High frequency
//!           option 5.33MHz.
//!        - \b CS_DCOFSEL_2 - Low frequency option 3.33MHz. High frequency
//!           option 6.67MHz.
//!        - \b CS_DCOFSEL_3 - Low frequency option 4MHz. High frequency option
//!           8MHz.
//!        - \b CS_DCOFSEL_4 - Low frequency option 5.33MHz. High frequency
//!           option 16MHz.
//!        - \b CS_DCOFSEL_5 - Low frequency option 6.67MHz. High frequency
//!           option 20MHz.
//!        - \b CS_DCOFSEL_6 - Low frequency option 8MHz. High frequency option
//!           24MHz.
//!
//! \return None
//
//*****************************************************************************
extern void CS_setDCOFreq(uint16_t dcorsel,
                          uint16_t dcofsel);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_CS_H__
