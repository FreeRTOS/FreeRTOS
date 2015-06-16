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
 
#include "samv71.h"

/* @cond 0 */
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/* @endcond */

/* %ATMEL_SYSTEM% */
/* Clock Settings (500MHz PLL VDDIO 3.3V and VDDCORE 1.2V) */
/* Clock Settings (300MHz HCLK, 150MHz MCK)=> PRESC = 1, MDIV = 2 */
#define SYS_BOARD_OSCOUNT   (CKGR_MOR_MOSCXTST(0x8U))
#define SYS_BOARD_PLLAR     (CKGR_PLLAR_ONE | CKGR_PLLAR_MULA(0x18U) | \
				CKGR_PLLAR_PLLACOUNT(0x3fU) | CKGR_PLLAR_DIVA(0x1U))

#define SYS_BOARD_MCKR      (PMC_MCKR_PRES_CLK_1 | PMC_MCKR_CSS_PLLA_CLK \
				| PMC_MCKR_MDIV_PCK_DIV2)

uint32_t SystemCoreClock = CHIP_FREQ_MAINCK_RC_4MHZ;
#define USBCLK_DIV          10

/**
 * \brief Set up the Microcontroller system.
 * Initialize the System and update the SystemFrequency variable.
 */
 void SystemInit( void )
{
	uint32_t read_MOR;
	/* Set FWS according to SYS_BOARD_MCKR configuration */
	EFC->EEFC_FMR = EEFC_FMR_FWS(5);
	
	 /* Before switching MAIN OSC on external crystal : enable it and don't 
	 * disable at the same time RC OSC in case of if MAIN OSC is still using RC
	 * OSC
	 */
	
	read_MOR = PMC->CKGR_MOR;
	 /* enable external crystal - enable RC OSC */
	read_MOR |= (CKGR_MOR_KEY_PASSWD |CKGR_MOR_XT32KFME); 
	PMC->CKGR_MOR = read_MOR;
	
	/* Select XTAL 32k instead of internal slow RC 32k for slow clock */
	if ( (SUPC->SUPC_SR & SUPC_SR_OSCSEL) != SUPC_SR_OSCSEL_CRYST )
	{
		SUPC->SUPC_CR = SUPC_CR_KEY_PASSWD | SUPC_CR_XTALSEL_CRYSTAL_SEL;
	
		while( !(SUPC->SUPC_SR & SUPC_SR_OSCSEL) );
	}
	
	/* Initialize main oscillator */
	if ( !(PMC->CKGR_MOR & CKGR_MOR_MOSCSEL) )
	{
	  PMC->CKGR_MOR = CKGR_MOR_KEY_PASSWD | SYS_BOARD_OSCOUNT
					| CKGR_MOR_MOSCRCEN | CKGR_MOR_MOSCXTEN;
	
	  while ( !(PMC->PMC_SR & PMC_SR_MOSCXTS) )
	  {
	  }
	}
	
	/* Switch to 3-20MHz Xtal oscillator */
	PMC->CKGR_MOR = CKGR_MOR_KEY_PASSWD | SYS_BOARD_OSCOUNT 
					| CKGR_MOR_MOSCRCEN | CKGR_MOR_MOSCXTEN | CKGR_MOR_MOSCSEL;
	
	while ( !(PMC->PMC_SR & PMC_SR_MOSCSELS) )
	{
	}
	
	PMC->PMC_MCKR = (PMC->PMC_MCKR & ~(uint32_t)PMC_MCKR_CSS_Msk)
					| PMC_MCKR_CSS_MAIN_CLK;

	while ( !(PMC->PMC_SR & PMC_SR_MCKRDY) )
	{
	}
   
	/* Initialize PLLA */
	PMC->CKGR_PLLAR = SYS_BOARD_PLLAR;
	while ( !(PMC->PMC_SR & PMC_SR_LOCKA) )
	{
	}
   
	/* Switch to main clock */
	PMC->PMC_MCKR = (SYS_BOARD_MCKR & ~PMC_MCKR_CSS_Msk) | PMC_MCKR_CSS_MAIN_CLK;
	while ( !(PMC->PMC_SR & PMC_SR_MCKRDY) )
	{
	}
   
	/* Switch to PLLA */
	PMC->PMC_MCKR = SYS_BOARD_MCKR;
	while ( !(PMC->PMC_SR & PMC_SR_MCKRDY) )
	{
	}
   
	SystemCoreClock = CHIP_FREQ_CPU_MAX;
}

void SystemCoreClockUpdate( void )
{
  /* Determine clock frequency according to clock register values */
	switch (PMC->PMC_MCKR & (uint32_t) PMC_MCKR_CSS_Msk)
	{
	case PMC_MCKR_CSS_SLOW_CLK: /* Slow clock */
		if ( SUPC->SUPC_SR & SUPC_SR_OSCSEL )
		{
		SystemCoreClock = CHIP_FREQ_XTAL_32K;
		}
		else
		{
		SystemCoreClock = CHIP_FREQ_SLCK_RC;
		}
		break;

	case PMC_MCKR_CSS_MAIN_CLK: /* Main clock */
		if ( PMC->CKGR_MOR & CKGR_MOR_MOSCSEL )
		{
		SystemCoreClock = CHIP_FREQ_XTAL_12M;
		}
		else
		{
		SystemCoreClock = CHIP_FREQ_MAINCK_RC_4MHZ;

			switch ( PMC->CKGR_MOR & CKGR_MOR_MOSCRCF_Msk )
			{
			case CKGR_MOR_MOSCRCF_4_MHz:
				break;

			case CKGR_MOR_MOSCRCF_8_MHz:
				SystemCoreClock *= 2U;
				break;

			case CKGR_MOR_MOSCRCF_12_MHz:
				SystemCoreClock *= 3U;
				break;

			default:
				break;
			}
		}
	break;

	case PMC_MCKR_CSS_PLLA_CLK:	/* PLLA clock */
		if ( PMC->CKGR_MOR & CKGR_MOR_MOSCSEL )
		{
			SystemCoreClock = CHIP_FREQ_XTAL_12M ;
		}
		else
		{
			SystemCoreClock = CHIP_FREQ_MAINCK_RC_4MHZ;

			switch ( PMC->CKGR_MOR & CKGR_MOR_MOSCRCF_Msk )
			{
			case CKGR_MOR_MOSCRCF_4_MHz:
				break;

			case CKGR_MOR_MOSCRCF_8_MHz:
				SystemCoreClock *= 2U;
				break;

			case CKGR_MOR_MOSCRCF_12_MHz:
				SystemCoreClock *= 3U;
				break;

			default:
				break;
			}
		}

		if ( (uint32_t) (PMC->PMC_MCKR & (uint32_t) PMC_MCKR_CSS_Msk)
						== PMC_MCKR_CSS_PLLA_CLK )
		{
			SystemCoreClock *= ((((PMC->CKGR_PLLAR) & CKGR_PLLAR_MULA_Msk)
							>> CKGR_PLLAR_MULA_Pos) + 1U);
			SystemCoreClock /= ((((PMC->CKGR_PLLAR) & CKGR_PLLAR_DIVA_Msk)
							>> CKGR_PLLAR_DIVA_Pos));
		}
	break;

	default:
	break;
	}

	if ( (PMC->PMC_MCKR & PMC_MCKR_PRES_Msk) == PMC_MCKR_PRES_CLK_3 )
	{
		SystemCoreClock /= 3U;
	}
	else
	{
		SystemCoreClock >>= ((PMC->PMC_MCKR & PMC_MCKR_PRES_Msk)
						>> PMC_MCKR_PRES_Pos);
	}
}
/**
 * Initialize flash.
 */
void system_init_flash( uint32_t ul_clk )
{
	/* Set FWS for embedded Flash access according to operating frequency */
	if ( ul_clk < CHIP_FREQ_FWS_0 )
	{
		EFC->EEFC_FMR = EEFC_FMR_FWS(0)|EEFC_FMR_CLOE;
	}
	else
	{
		if (ul_clk < CHIP_FREQ_FWS_1)
		{
		EFC->EEFC_FMR = EEFC_FMR_FWS(1)|EEFC_FMR_CLOE;
		}
		else
		{
			if (ul_clk < CHIP_FREQ_FWS_2)
			{
			EFC->EEFC_FMR = EEFC_FMR_FWS(2)|EEFC_FMR_CLOE;
			}
			else
			{
				if ( ul_clk < CHIP_FREQ_FWS_3 )
				{
					EFC->EEFC_FMR = EEFC_FMR_FWS(3)|EEFC_FMR_CLOE;
				}
				else
				{
					if ( ul_clk < CHIP_FREQ_FWS_4 )
					{
						EFC->EEFC_FMR = EEFC_FMR_FWS(4)|EEFC_FMR_CLOE;
					}
					else
					{
						EFC->EEFC_FMR = EEFC_FMR_FWS(5)|EEFC_FMR_CLOE;
					}
				}
			}
		}
	}
}

/**
 * \brief Enable full speed USB clock.
 *
 * \note The SAM3X PMC hardware interprets div as div+1. For readability the hardware div+1
 * is hidden in this implementation. Use div as div effective value.
 *
 * \param pll_id Source of the USB clock.
 * \param div Actual clock divisor. Must be superior to 0.
 */
void sysclk_enable_usb(void)
{
    /* Disable FS USB clock*/
    PMC->PMC_SCDR = PMC_SCDR_USBCLK;
    
    /* Enable PLL 480 MHz */
    PMC->CKGR_UCKR = CKGR_UCKR_UPLLEN | CKGR_UCKR_UPLLCOUNT(0xF);    
    /* Wait that PLL is considered locked by the PMC */
    while( !(PMC->PMC_SR & PMC_SR_LOCKU) );
    
    /* USB clock register: USB Clock Input is UTMI PLL */
    PMC->PMC_USB = (PMC_USB_USBS | PMC_USB_USBDIV(USBCLK_DIV - 1) );
    
    PMC->PMC_SCER = PMC_SCER_USBCLK;
}


/**
 * \brief Enable full speed USB clock.
 *
 * \note The SAM3X PMC hardware interprets div as div+1. For readability the hardware div+1
 * is hidden in this implementation. Use div as div effective value.
 *
 * \param pll_id Source of the USB clock.
 * \param div Actual clock divisor. Must be superior to 0.
 */
void sysclk_disable_usb(void)
{
    /* Disable FS USB clock*/
    PMC->PMC_SCDR = PMC_SCDR_USBCLK;
    
    /* Enable PLL 480 MHz */
    PMC->CKGR_UCKR = CKGR_UCKR_UPLLEN | CKGR_UCKR_UPLLCOUNT(0xF);    
    /* Wait that PLL is considered locked by the PMC */
    while( !(PMC->PMC_SR & PMC_SR_LOCKU) );
    
    /* USB clock register: USB Clock Input is UTMI PLL */
    PMC->PMC_USB = (PMC_USB_USBS | PMC_USB_USBDIV(USBCLK_DIV - 1) );
    

}


/* @cond 0 */
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/* @endcond */
