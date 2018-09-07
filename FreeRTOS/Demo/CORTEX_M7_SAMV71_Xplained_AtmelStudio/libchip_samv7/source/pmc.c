/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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

/** \addtogroup pmc_module Working with PMC
 * The PMC driver provides the Interface to configure the Power Management 
 * Controller (PMC).
 *
 *  \section Usage
 * <ul>
 *  <li> Enables/Disable the clock of a peripheral by using 
 * PMC_EnablePeripheral() and PMC_DisablePeripheral().</li>
 *  <li> Enables/Disable the clock of all peripherals by using 
 * PMC_EnableAllPeripherals() and PMC_DisableAllPeripherals().</li>
 *  <li> Get status of a peripheral using PMC_IsPeriphEnabled().</li>
 *  <li> Manage the clocks using PMC_EnableExtOsc(), PMC_DisableExtOsc(), 
 * PMC_SelectExtOsc(), PMC_SelectExtBypassOsc(), PMC_EnableIntRC4_8_12MHz(), 
 * PMC_DisableIntRC4_8_12MHz(), PMC_SetPllaClock(), PMC_SetMckSelection(), 
 * PMC_DisableAllClocks(), PMC_ConfigureMckWithPlla(), 
 * PMC_EnableXT32KFME() and PMC_ConfigurePCK2().</li>
 *
 * </ul>
 * For more accurate information, please look at the PMC section of the Datasheet.
 *
 * Related files :\n
 * \ref pmc.c\n
 * \ref pmc.h.\n
*/

 /**
 *  \file
 *
 *  \section Purpose
 *
 *  Interface for configuring and using Power Management Controller (PMC) 
 * peripherals.
 *
 */
 
/**
 * \file
 *
 * Implementation of Power Management Controller (PMC).
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/

#define MASK_STATUS0 0xFFFFFFFC
#define MASK_STATUS1 0xFFFFFFFF

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Switch MCK to PLLA clock.
 */
static void _PMC_SwitchMck2PllaClock(void)

{
	/* Select PLLA as input clock for MCK */
	PMC->PMC_MCKR = (PMC->PMC_MCKR & ~PMC_MCKR_CSS_Msk) | PMC_MCKR_CSS_PLLA_CLK ;

	/* Wait until the master clock is established */
	while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
}

/**
 * \brief Switch MCK to main clock.
 */
static void _PMC_SwitchMck2MainClock(void)
{
	/* Select Main Oscillator as input clock for MCK */
	PMC->PMC_MCKR = (PMC->PMC_MCKR & ~PMC_MCKR_CSS_Msk) | PMC_MCKR_CSS_MAIN_CLK ;

	/* Wait until the master clock is established */
	while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
	PMC->PMC_MCKR = PMC_MCKR_CSS_MAIN_CLK;
	while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
}

/**
 * \brief Switch MCK to slow clock.
 */
static void _PMC_SwitchMck2SlowClock(void)
{
	/* Select Slow Clock as input clock for MCK */
	PMC->PMC_MCKR = (PMC->PMC_MCKR & ~PMC_MCKR_CSS_Msk) | PMC_MCKR_CSS_SLOW_CLK ;

	/* Wait until the master clock is established */
	while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
}

/**
 * \brief Set prescaler for MCK.
 *
 * \param prescaler Master Clock prescaler
 */
static void _PMC_SetMckPrescaler(uint32_t prescaler)
{
	/* Change MCK Prescaler divider in PMC_MCKR register */
	PMC->PMC_MCKR = (PMC->PMC_MCKR & ~PMC_MCKR_PRES_Msk) | prescaler;

	/* Wait until the master clock is established */
	while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
}
/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Enables the clock of a peripheral. The peripheral ID is used
 * to identify which peripheral is targeted.
 *
 * \note The ID must NOT be shifted (i.e. 1 << ID_xxx).
 *
 * \param id  Peripheral ID (ID_xxx).
 */
void PMC_EnablePeripheral( uint32_t dwId )
{
	assert( dwId < 63 ) ;

	if ( dwId < 32 ) {
		if ( (PMC->PMC_PCSR0 & ((uint32_t)1 << dwId)) == ((uint32_t)1 << dwId) ) {
			TRACE_DEBUG( "PMC_EnablePeripheral: clock of peripheral" \
			" %u is already enabled\n\r", (unsigned int)dwId ) ;
		} else {
			PMC->PMC_PCER0 = 1 << dwId ;
		}
	} else {
		dwId -= 32;
		if ((PMC->PMC_PCSR1 & ((uint32_t)1 << dwId)) == ((uint32_t)1 << dwId)) {
			TRACE_DEBUG( "PMC_EnablePeripheral: clock of peripheral" \
			" %u is already enabled\n\r", (unsigned int)(dwId + 32) ) ;
		} else {
			PMC->PMC_PCER1 = 1 << dwId ;
		}
	}
}

/**
 * \brief Disables the clock of a peripheral. The peripheral ID is used
 * to identify which peripheral is targeted.
 *
 * \note The ID must NOT be shifted (i.e. 1 << ID_xxx).
 *
 * \param id  Peripheral ID (ID_xxx).
 */
void PMC_DisablePeripheral( uint32_t dwId )
{
	assert( dwId < 63 ) ;

	if ( dwId < 32 ) {
		if ( (PMC->PMC_PCSR0 & ((uint32_t)1 << dwId)) != ((uint32_t)1 << dwId) ) {
			TRACE_DEBUG("PMC_DisablePeripheral: clock of peripheral" \
			" %u is not enabled\n\r", (unsigned int)dwId ) ;
		} else {
			PMC->PMC_PCDR0 = 1 << dwId ;
		}
	} else {
		dwId -= 32 ;
		if ( (PMC->PMC_PCSR1 & ((uint32_t)1 << dwId)) != ((uint32_t)1 << dwId) ) {
			TRACE_DEBUG( "PMC_DisablePeripheral: clock of peripheral" 
				" %u is not enabled\n\r", (unsigned int)(dwId + 32) ) ;
		} else {
			PMC->PMC_PCDR1 = 1 << dwId ;
		}
	}
}

/**
 * \brief Enable all the periph clock via PMC.
 */
void PMC_EnableAllPeripherals( void )
{
	PMC->PMC_PCER0 = MASK_STATUS0 ;
	while ( (PMC->PMC_PCSR0 & MASK_STATUS0) != MASK_STATUS0 ) ;

	PMC->PMC_PCER1 = MASK_STATUS1 ;
	while ( (PMC->PMC_PCSR1 & MASK_STATUS1) != MASK_STATUS1 ) ;

	TRACE_DEBUG( "Enable all periph clocks\n\r" ) ;
}

/**
 * \brief Disable all the periph clock via PMC.
 */
void PMC_DisableAllPeripherals( void )
{
	PMC->PMC_PCDR0 = MASK_STATUS0 ;
	while ( (PMC->PMC_PCSR0 & MASK_STATUS0) != 0 ) ;

	PMC->PMC_PCDR1 = MASK_STATUS1 ;
	while ( (PMC->PMC_PCSR1 & MASK_STATUS1) != 0 ) ;

	TRACE_DEBUG( "Disable all periph clocks\n\r" ) ;
}

/**
 * \brief Get Periph Status for the given peripheral ID.
 *
 * \param id  Peripheral ID (ID_xxx).
 */
uint32_t PMC_IsPeriphEnabled( uint32_t dwId )
{
	assert( dwId < ID_PERIPH_COUNT ) ;

	if ( dwId < 32 ) {
		return ( PMC->PMC_PCSR0 & (1 << dwId) ) ;
	} else {
		return ( PMC->PMC_PCSR1 & (1 << (dwId - 32)) ) ;
	}
}


/**
 * \brief Enable external oscillator as main clock input.
 */
void PMC_EnableExtOsc(void)
{
	uint32_t   read_MOR;

	/* Before switching MAIN OSC on external crystal : enable it and don't disable
	 * at the same time RC OSC in case of if MAIN OSC is still using RC OSC
	 */

	read_MOR = PMC->CKGR_MOR;
	read_MOR &= ~CKGR_MOR_MOSCRCF_Msk;  
	/* reset MOSCRCF field in MOR register before select RC 12MHz */
	read_MOR  |= (CKGR_MOR_KEY_PASSWD 
				| CKGR_MOR_MOSCRCF_12_MHz
				| CKGR_MOR_MOSCXTEN     
				| CKGR_MOR_MOSCRCEN     
				| CKGR_MOR_MOSCXTST(DEFAUTL_MAIN_OSC_COUNT)); 
			/* enable external crystal - enable RC OSC */

	PMC->CKGR_MOR = read_MOR;

	while( !(PMC->PMC_SR & PMC_SR_MOSCRCS ) );
	/* wait end of RC oscillator stabilization */
	while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );

	read_MOR |= CKGR_MOR_MOSCSEL;
	/* select external crystal */

	PMC->CKGR_MOR = read_MOR;

	while( !(PMC->PMC_SR & PMC_SR_MOSCSELS ) ); 
	/* Wait end of Main Oscillator Selection */
	while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
}

/**
 * \brief Disable external 12MHz oscillator.
 */
void PMC_DisableExtOsc(void)
{
	uint32_t   read_MOR;

	read_MOR = PMC->CKGR_MOR;
	read_MOR &= ~CKGR_MOR_MOSCXTEN; /* disable main xtal osc */
	PMC->CKGR_MOR = CKGR_MOR_KEY_PASSWD | read_MOR;
	while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
}

/**
 * \brief Select external OSC.
 */
void PMC_SelectExtOsc(void)
{ 
	/* switch from internal RC 12 MHz to external OSC 12 MHz */
	/* wait Main XTAL Oscillator stabilisation*/
	if ((PMC->CKGR_MOR & CKGR_MOR_MOSCSEL ) == CKGR_MOR_MOSCSEL) {
		PMC_DisableIntRC4_8_12MHz();
		return;
	}
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
	PMC_DisableIntRC4_8_12MHz();
}


/**
 * \brief Select external OSC.
 */
void PMC_SelectExtBypassOsc(void)
{   
	volatile uint32_t timeout;
	if((PMC->CKGR_MOR & CKGR_MOR_MOSCXTBY) != CKGR_MOR_MOSCXTBY){
		PMC->CKGR_MOR = CKGR_MOR_KEY_PASSWD |
			CKGR_MOR_MOSCRCEN | 
			CKGR_MOR_MOSCXTST(0xFF) |
			CKGR_MOR_MOSCXTBY;
		PMC->CKGR_MOR |= CKGR_MOR_KEY_PASSWD | CKGR_MOR_MOSCSEL;
		/* wait MAIN clock status change for external OSC 12 MHz selection*/
		while(!(PMC->PMC_SR & PMC_SR_MOSCSELS));
		// Check if an external clock is provided
		for(timeout = 0; timeout<0xffff;timeout++);
		while(!(PMC->CKGR_MCFR & CKGR_MCFR_MAINFRDY));
	}
}

/**
 * \brief Enable internal 4/8/12MHz fast RC as main clock input.
 *
 * \param freqSelect fast RC frequency (FAST_RC_4MHZ, FAST_RC_8MHZ, 
 * FAST_RC_12MHZ).
 */
void PMC_EnableIntRC4_8_12MHz(uint32_t freqSelect)
{
	/* Enable Fast RC oscillator but DO NOT switch to RC now */
	PMC->CKGR_MOR |= (CKGR_MOR_KEY_PASSWD | CKGR_MOR_MOSCRCEN);

	/* Wait the Fast RC to stabilize */
	while (!(PMC->PMC_SR & PMC_SR_MOSCRCS));

	/* Change Fast RC oscillator frequency */
	PMC->CKGR_MOR = (PMC->CKGR_MOR & ~CKGR_MOR_MOSCRCF_Msk) |
		CKGR_MOR_KEY_PASSWD | freqSelect;

	/* Wait the Fast RC to stabilize */
	while (!(PMC->PMC_SR & PMC_SR_MOSCRCS));

	/* Switch to Fast RC */
	PMC->CKGR_MOR = (PMC->CKGR_MOR & ~CKGR_MOR_MOSCSEL) |
		CKGR_MOR_KEY_PASSWD;
	/* wait MAIN clock status change for Fast RC oscillator */
	while(!(PMC->PMC_SR & PMC_SR_MOSCSELS));

	/* in case where MCK is running on MAIN CLK */
	while(!(PMC->PMC_SR & PMC_SR_MCKRDY));

}

/**
 * \brief Disable internal 4/8/12MHz fast RC.
 */
void PMC_DisableIntRC4_8_12MHz(void)
{
	uint32_t   read_MOR;

	read_MOR = PMC->CKGR_MOR;

	read_MOR &= ~CKGR_MOR_MOSCRCF_Msk;   /* reset MOSCRCF field in MOR register */
	read_MOR &= ~CKGR_MOR_MOSCRCEN;      /* disable fast RC */
	PMC->CKGR_MOR = CKGR_MOR_KEY_PASSWD | read_MOR;
	while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
}

/**
 * \brief Configure PLLA clock by giving MUL and DIV.
 *        Disable PLLA when 'mul' set to 0.
 *
 * \param mul  PLL multiplier factor.
 * \param div  PLL divider factor.
 */
void PMC_SetPllaClock(uint32_t mul, uint32_t div)
{
	if (mul != 0) {
		/* Init PLL speed */
		PMC->CKGR_PLLAR = CKGR_PLLAR_ONE 
			| CKGR_PLLAR_PLLACOUNT(DEFAUTL_PLLA_COUNT)
			| CKGR_PLLAR_MULA(mul - 1)
			| CKGR_PLLAR_DIVA(div);
		/* Wait for PLL stabilization */
		while( !(PMC->PMC_SR & PMC_SR_LOCKA) );
	} else {
		PMC->CKGR_PLLAR = CKGR_PLLAR_ONE; /* disable PLL A */
	}
}

/**
 * \brief Selection of Master Clock.
 *
 * \param clockSource  Master Clock source.
 * \param prescaler    Master Clock prescaler.
 *
 * \note
 * The PMC_MCKR register must not be programmed in a single write
 * operation (see. Product Data Sheet).
 */
void PMC_SetMckSelection(uint32_t clockSource, uint32_t prescaler)
{
	switch ( clockSource ) {
	case PMC_MCKR_CSS_SLOW_CLK :
		_PMC_SwitchMck2SlowClock();
		_PMC_SetMckPrescaler(prescaler);
		break;

	case PMC_MCKR_CSS_MAIN_CLK :
		_PMC_SwitchMck2MainClock();
		_PMC_SetMckPrescaler(prescaler);
		break;

	case PMC_MCKR_CSS_PLLA_CLK :
		_PMC_SetMckPrescaler(prescaler);
		_PMC_SwitchMck2PllaClock();
		break ;
	}
}

/**
 * \brief Disable all clocks.
 */
void PMC_DisableAllClocks(void)
{
	uint32_t   read_reg;

	PMC->PMC_SCDR = PMC_SCDR_PCK0 | PMC_SCDR_PCK1 | PMC_SCDR_PCK2 | PMC_SCDR_PCK3 | 
			PMC_SCDR_PCK4 | PMC_SCDR_PCK5 | PMC_SCDR_PCK6;  /* disable PCK */

	_PMC_SwitchMck2MainClock();

	PMC->CKGR_PLLAR = PMC->CKGR_PLLAR & ~CKGR_PLLAR_MULA_Msk;   /* disable PLL A */

	_PMC_SwitchMck2SlowClock();

	read_reg  =  PMC->CKGR_MOR;
	read_reg  =  (read_reg & ~CKGR_MOR_MOSCRCEN) | CKGR_MOR_KEY_PASSWD; 
	/* disable RC OSC */

	PMC->CKGR_MOR = read_reg;

	PMC_DisableAllPeripherals(); /* disable all peripheral clocks */
}

/**
 * \brief Configure PLLA as clock input for MCK.
 *
 * \param mul        PLL multiplier factor (not shifted, don't minus 1).
 * \param div        PLL divider factor (not shifted).
 * \param prescaler  Master Clock prescaler (shifted as in register).
 */
void PMC_ConfigureMckWithPlla(uint32_t mul, uint32_t div, uint32_t prescaler)
{
	/* First, select Main OSC as input clock for MCK */
	_PMC_SwitchMck2MainClock();

	/* Then, Set PLLA clock */
	PMC_SetPllaClock(mul, div);

	/* Wait until the master clock is established for the case we already
		turn on the PLL */
	while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );

	/* Finally, select PllA as input clock for MCK */
	PMC_SetMckSelection(PMC_MCKR_CSS_PLLA_CLK, prescaler);
}


/**
 * \brief Configure PLLA as clock input for MCK.
 *
 * \param mul        PLL multiplier factor (not shifted, don't minus 1).
 * \param div        PLL divider factor (not shifted).
 * \param prescaler  Master Clock prescaler (shifted as in register).
 */
void PMC_EnableXT32KFME(void)
{

	uint32_t   read_MOR;

	/* Before switching MAIN OSC on external crystal : enable it and don't 
	disable at the same time RC OSC in case of if MAIN OSC is still using 
	RC OSC */

	read_MOR = PMC->CKGR_MOR;

	read_MOR |= (CKGR_MOR_KEY_PASSWD |CKGR_MOR_XT32KFME);  
	/* enable external crystal - enable RC OSC */

	PMC->CKGR_MOR = read_MOR;

}

/**
 * \brief Configure PLLA as clock input for MCK.
 *
 * \param mul        PLL multiplier factor (not shifted, don't minus 1).
 * \param div        PLL divider factor (not shifted).
 * \param prescaler  Master Clock prescaler (shifted as in register).
 */
void PMC_ConfigurePCK0(uint32_t MasterClk, uint32_t prescaler)
{
	PMC->PMC_SCDR = PMC_SCDR_PCK0;  /* disable PCK */

	while((PMC->PMC_SCSR)& PMC_SCSR_PCK0);
	PMC->PMC_PCK[0] = MasterClk | prescaler; 
	PMC->PMC_SCER = PMC_SCER_PCK0;
	while(!((PMC->PMC_SR) & PMC_SR_PCKRDY0));

}


/**
 * \brief Configure PLLA as clock input for MCK.
 *
 * \param mul        PLL multiplier factor (not shifted, don't minus 1).
 * \param div        PLL divider factor (not shifted).
 * \param prescaler  Master Clock prescaler (shifted as in register).
 */
void PMC_ConfigurePCK1(uint32_t MasterClk, uint32_t prescaler)
{
	PMC->PMC_SCDR = PMC_SCDR_PCK1;  /* disable PCK */

	while((PMC->PMC_SCSR)& PMC_SCSR_PCK1);
	PMC->PMC_PCK[1] = MasterClk | prescaler; 
	PMC->PMC_SCER = PMC_SCER_PCK1;
	while(!((PMC->PMC_SR) & PMC_SR_PCKRDY1));

}

/**
 * \brief Configure PLLA as clock input for MCK.
 *
 * \param mul        PLL multiplier factor (not shifted, don't minus 1).
 * \param div        PLL divider factor (not shifted).
 * \param prescaler  Master Clock prescaler (shifted as in register).
 */
void PMC_ConfigurePCK2(uint32_t MasterClk, uint32_t prescaler)
{
	PMC->PMC_SCDR = PMC_SCDR_PCK2;  /* disable PCK */

	while((PMC->PMC_SCSR)& PMC_SCSR_PCK2);
	PMC->PMC_PCK[2] = MasterClk | prescaler; 
	PMC->PMC_SCER = PMC_SCER_PCK2;
	while(!((PMC->PMC_SR) & PMC_SR_PCKRDY2));

}
