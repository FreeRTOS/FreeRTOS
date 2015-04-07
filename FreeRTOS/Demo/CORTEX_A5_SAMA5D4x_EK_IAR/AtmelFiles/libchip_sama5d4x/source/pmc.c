/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/** \file */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <assert.h>

/*----------------------------------------------------------------------------
 *        Definition
 *----------------------------------------------------------------------------*/
#define MAX_PERI_ID  ID_L2CC

extern const PeripheralClockMaxFreq periClkMaxFreq[];
/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Get maxinum frequency clock for giving pripheral ID.
 *
 * \param id  Peripheral ID (ID_xxx).
 */
extern uint32_t PMC_GetPeriMaxFreq( uint32_t dwId )
{
    uint8_t i;
    for (i = 0; i < MAX_PERI_ID; i++) {
        if ( dwId == periClkMaxFreq[i].bPeriphID) return periClkMaxFreq[i].bMaxFrequency;
    }
    return 0;
}

/**
 * \brief Set maxinum frequency clock for giving pripheral ID.
 *
 * \param id  Peripheral ID (ID_xxx).
 * \param mck  Master clock.
 * \return Peripheral clock.
 */
extern uint32_t PMC_SetPeriMaxClock( uint32_t dwId, uint32_t mck)
{
    uint32_t maxClock;
    uint8_t i;
    /* Disable peripher clocl */
    PMC->PMC_PCR = PMC_PCR_PID(dwId) | PMC_PCR_CMD;
    maxClock = PMC_GetPeriMaxFreq(dwId);
    for ( i = 0; i < 4; i++) {
        if ( mck / (1 << i ) <= maxClock) break;
    }
    PMC->PMC_PCR = PMC_PCR_PID(dwId) | PMC_PCR_CMD | (i << PMC_PCR_DIV_Pos) | PMC_PCR_EN;
    return maxClock;
}

/**
 * \brief Enables the clock of a peripheral. The peripheral ID is used
 * to identify which peripheral is targetted.
 *
 * \note The ID must NOT be shifted (i.e. 1 << ID_xxx).
 *
 * \param id  Peripheral ID (ID_xxx).
 */
extern void PMC_EnablePeripheral( uint32_t dwId )
{
    if (dwId < 32)
    {
        if ( (PMC->PMC_PCSR0 & ((uint32_t)1 << dwId)) == ((uint32_t)1 << dwId) )
        {
         //   TRACE_DEBUG( "PMC_EnablePeripheral: clock of peripheral"  " %u is already enabled\n\r", dwId ) ;
        }
        else
        {
            PMC->PMC_PCER0 = (1 << dwId) ;
        }
    } else {
        if ( (PMC->PMC_PCSR1 & ((uint32_t)1 << ( dwId - 32))) == ((uint32_t)1 << (dwId - 32)) )
        {
           // TRACE_DEBUG( "PMC_EnablePeripheral: clock of peripheral"  " %u is already enabled\n\r", dwId ) ;
        }
        else
        {
            PMC->PMC_PCER1 = 1 << (dwId - 32) ;
        }
    }
}

/**
 * \brief Disables the clock of a peripheral. The peripheral ID is used
 * to identify which peripheral is targetted.
 *
 * \note The ID must NOT be shifted (i.e. 1 << ID_xxx).
 *
 * \param id  Peripheral ID (ID_xxx).
 */
extern void PMC_DisablePeripheral( uint32_t dwId )
{
    if (dwId < 32)
    {
        if ( (PMC->PMC_PCSR0 & ((uint32_t)1 << dwId)) != ((uint32_t)1 << dwId) )
        {
            TRACE_DEBUG("PMC_DisablePeripheral: clock of peripheral" " %u is not enabled\n\r", (unsigned int)dwId ) ;
        }
        else
        {
            PMC->PMC_PCDR0 = 1 << dwId ;
        }
    } else {
        if ( (PMC->PMC_PCSR1 & ((uint32_t)1 << (dwId - 32))) != ((uint32_t)1 << (dwId - 32)) )
        {
            TRACE_DEBUG("PMC_DisablePeripheral: clock of peripheral" " %u is not enabled\n\r", (unsigned int)dwId ) ;
        }
        else
        {
            PMC->PMC_PCDR1 = 1 << (dwId - 32) ;
        }
    }
}

/**
 * \brief Enable all the periph clock via PMC.
 */
extern void PMC_EnableAllPeripherals( void )
{
    PMC->PMC_PCER0 = 0xFFFFFFFF ;
    PMC->PMC_PCER1 = 0xFFFFFFFF ;
    TRACE_DEBUG( "Enable all periph clocks\n\r" ) ;
}

/**
 * \brief Disable all the periph clock via PMC.
 */
extern void PMC_DisableAllPeripherals( void )
{
    TRACE_DEBUG( "Disable all periph clocks\n\r" ) ;
    PMC->PMC_PCDR0 = 0xFFFFFFFF ;
    PMC->PMC_PCDR1 = 0xFFFFFFFF ;
}

/**
 * \brief Get Periph Status for the given peripheral ID.
 *
 * \param id  Peripheral ID (ID_xxx).
 */
extern uint32_t PMC_IsPeriphEnabled( uint32_t dwId )
{
    if (dwId < 32) {
        return ( PMC->PMC_PCSR0 & (1 << dwId) ) ;
    } else {
        return ( PMC->PMC_PCSR1 & (1 << (dwId - 32)) ) ;
    }
}

/**
 * \brief Select external 32K crystal.
 */
extern void PMC_SelectExt32KCrystal(void)
{ 
    volatile uint32_t count;
    SCKC->SCKC_CR = (SCKC->SCKC_CR & ~SCKC_CR_OSCSEL) | SCKC_CR_OSCSEL_XTAL;
    /* Wait 5 slow clock cycles for internal resynchronization*/
    for (count = 0; count < 0x1000; count++);
    /* wait slow clock status change for external OSC 32 kHz selection */
}

/**
 * \brief Select internal 32K crystal.
 */
extern void PMC_SelectInt32kCrystal(void)
{
    /* switch from external RC 32kHz to internal OSC 32 kHz */
    volatile uint32_t  count;
    /* switch slow clock source to internal OSC 32 kHz */
    SCKC->SCKC_CR = (SCKC->SCKC_CR & ~SCKC_CR_OSCSEL) | SCKC_CR_OSCSEL_RC;
    /* Wait 5 slow clock cycles for internal resynchronization */
    for (count = 0; count < 0x1000; count++);
    /* wait slow clock status change for internal RC 32 kHz selection */
    //   while(PMC->PMC_SR & PMC_SR_OSCSELS);
}

/**
 * \brief Select external 12M OSC.
 */
extern void PMC_SelectExt12M_Osc(void)
{ 
    /* switch from internal RC 12 MHz to external OSC 12 MHz */
    /* wait Main XTAL Oscillator stabilisation*/
    if ((PMC->CKGR_MOR & CKGR_MOR_MOSCSEL ) == CKGR_MOR_MOSCSEL) return;
    /* enable external OSC 12 MHz */
    PMC->CKGR_MOR |= CKGR_MOR_MOSCXTEN | CKGR_MOR_KEY_PASSWD; 
    /* wait Main CLK Ready */
    while(!(PMC->CKGR_MCFR & CKGR_MCFR_MAINFRDY)); 
    /* switch MAIN clock to external OSC 12 MHz*/
    PMC->CKGR_MOR |= CKGR_MOR_MOSCSEL | CKGR_MOR_KEY_PASSWD;
    /* wait MAIN clock status change for external OSC 12 MHz selection*/
    while(!(PMC->PMC_SR & PMC_SR_MOSCSELS));
    /* in case where MCK is running on MAIN CLK */
    while(!(PMC->PMC_SR & PMC_SR_MCKRDY));
}

/**
 * \brief Select internal 12M OSC.
 */
extern void PMC_SelectInt12M_Osc(void)
{
    /* switch from external OSC 12 MHz to internal RC 12 MHz*/
    /* Wait internal 12 MHz RC Startup Time for clock stabilization (software loop) */
    while(!(PMC->PMC_SR & PMC_SR_MOSCRCS));
    /* switch MAIN clock to internal RC 12 MHz */
    PMC->CKGR_MOR = (PMC->CKGR_MOR & ~CKGR_MOR_MOSCSEL) | CKGR_MOR_KEY_PASSWD;
    /* in case where MCK is running on MAIN CLK */
    while(!(PMC->PMC_SR & PMC_SR_MCKRDY));
    /* disable external OSC 12 MHz   */
    PMC->CKGR_MOR = (PMC->CKGR_MOR & ~CKGR_MOR_MOSCXTEN) | CKGR_MOR_KEY_PASSWD;
    while(!(PMC->PMC_SR & PMC_SR_MCKRDY));
}

/**
 * \brief Switch PMC from MCK to PLL clock.
 */
extern void PMC_SwitchMck2Pll(void)
{
    /* Select PLL as input clock for PCK and MCK */
    PMC->PMC_MCKR = (PMC->PMC_MCKR & ~PMC_MCKR_CSS_Msk) | PMC_MCKR_CSS_PLLA_CLK ;
    while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
}


/**
 * \brief Switch PMC from MCK to main clock.
 */
extern void PMC_SwitchMck2Main(void)
{
    /* Select Main Oscillator as input clock for PCK and MCK */
    PMC->PMC_MCKR = (PMC->PMC_MCKR & ~PMC_MCKR_CSS_Msk) | PMC_PCK_CSS_MAIN_CLK ;
    while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
}


/**
 * \brief Switch PMC from MCK to slow clock.
 */
extern uint32_t PMC_SwitchMck2Slck(void)
{
    /* Select Slow Clock as input clock for PCK and MCK */
    PMC->PMC_MCKR = (PMC->PMC_MCKR & ~PMC_MCKR_CSS_Msk) | PMC_PCK_CSS_SLOW_CLK ;
    while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
    return PMC->PMC_MCKR;
}


/**
 * \brief Configure MCK Prescaler.
 * \param prescaler prescaler value.
 */
extern void PMC_SetMckPrescaler(uint32_t prescaler)
{
    /* Change MCK Prescaler divider in PMC_MCKR register */
    PMC->PMC_MCKR = (PMC->PMC_MCKR & ~PMC_MCKR_PRES_Msk) | prescaler;
    while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
}

/**
 * \brief Configure MCK PLLA divider.
 * \param divider PLL divider value.
 */
extern void PMC_SetMckPllaDiv(uint32_t divider)
{
    if ((PMC->PMC_MCKR & PMC_MCKR_PLLADIV2) == PMC_MCKR_PLLADIV2)
    {
        if(divider == 0) {
            PMC->PMC_MCKR = (PMC->PMC_MCKR & ~PMC_MCKR_PLLADIV2);
            while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
        }
    } else {
        if(divider == PMC_MCKR_PLLADIV2) {
            PMC->PMC_MCKR = (PMC->PMC_MCKR | PMC_MCKR_PLLADIV2);
            while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
        }
    }
}

/**
 * \brief Configure MCK Divider.
 * \param divider divider value.
 */
extern void PMC_SetMckDivider(uint32_t divider)
{
    /* change MCK Prescaler divider in PMC_MCKR register */
    PMC->PMC_MCKR = (PMC->PMC_MCKR & ~PMC_MCKR_MDIV_Msk) | divider;
    while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
}

/**
 * \brief Configure PLL Register.
 * \param pll pll value.
 * \param cpcr cpcr value.
 */
extern void PMC_SetPllA(uint32_t pll, uint32_t cpcr)
{
    PMC->CKGR_PLLAR = pll;
    PMC->PMC_PLLICPR = cpcr;
    while( !(PMC->PMC_SR & PMC_SR_LOCKA) );
}

/**
 * \brief Disable PLLA Register.
 */
extern void PMC_DisablePllA(void)
{
    PMC->CKGR_PLLAR = (PMC->CKGR_PLLAR & ~CKGR_PLLAR_MULA_Msk) | CKGR_PLLAR_MULA(0);
}

