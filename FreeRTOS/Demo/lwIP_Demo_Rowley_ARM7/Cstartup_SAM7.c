//*----------------------------------------------------------------------------
//*         ATMEL Microcontroller Software Support  -  ROUSSET  -
//*----------------------------------------------------------------------------
//* The software is delivered "AS IS" without warranty or condition of any
//* kind, either express, implied or statutory. This includes without
//* limitation any warranty or condition with respect to merchantability or
//* fitness for any particular purpose, or against the infringements of
//* intellectual property rights of others.
//*----------------------------------------------------------------------------
//* File Name           : Cstartup_SAM7.c
//* Object              : Low level initializations written in C for IAR
//*                       tools
//* 1.0   08/Sep/04 JPP	: Creation
//* 1.10  10/Sep/04 JPP : Update AT91C_CKGR_PLLCOUNT filed
//*----------------------------------------------------------------------------


// Include the board file description
#include "Board.h"

//*----------------------------------------------------------------------------
//* \fn    AT91F_LowLevelInit
//* \brief This function performs very low level HW initialization
//*        this function can be use a Stack, depending the compilation
//*        optimization mode
//*----------------------------------------------------------------------------
void AT91F_LowLevelInit( void);
void AT91F_LowLevelInit( void )
{
 AT91PS_PMC     pPMC = AT91C_BASE_PMC;

    //* Set Flash Waite sate
	//  Single Cycle Access at Up to 30 MHz, or 40
	//  if MCK = 47923200 I have 50 Cycle for 1 useconde ( flied MC_FMR->FMCN
	    AT91C_BASE_MC->MC_FMR = ((AT91C_MC_FMCN)&(75 <<16)) | AT91C_MC_FWS_1FWS ;

    //* Watchdog Disable
        AT91C_BASE_WDTC->WDTC_WDMR= AT91C_WDTC_WDDIS;

	//* Set MCK at 47 923 200
    // 1 Enabling the Main Oscillator:
        // SCK = 1/32768 = 30.51 uSeconde
    	// Start up time = 8 * 6 / SCK = 56 * 30.51 = 1,46484375 ms
       pPMC->PMC_MOR = ((( AT91C_CKGR_OSCOUNT & (0x06 <<8)) | AT91C_CKGR_MOSCEN ));
        // Wait the startup time
        while(!(pPMC->PMC_SR & AT91C_PMC_MOSCS));
	// 2 Checking the Main Oscillator Frequency (Optional)
	// 3 Setting PLL and divider:
		// - div by 5 Fin = 3,6864 =(18,432 / 5)
		// - Mul 25+1: Fout =	95,8464 =(3,6864 *26)
		// for 96 MHz the erroe is 0.16%
		//eld out NOT USED = 0 Fi
       pPMC->PMC_PLLR = ((AT91C_CKGR_DIV & 5) |
                         (AT91C_CKGR_PLLCOUNT & (28<<8)) |
                         (AT91C_CKGR_MUL & (25<<16)));

        // Wait the startup time
        while(!(pPMC->PMC_SR & AT91C_PMC_LOCK));
	// 4. Selection of Master Clock and Processor Clock
        // select the PLL clock divided by 2
       pPMC->PMC_MCKR = AT91C_PMC_PRES_CLK_2 ;
        while(!(pPMC->PMC_SR & AT91C_PMC_MCKRDY));

        pPMC->PMC_MCKR |= AT91C_PMC_CSS_PLL_CLK ;
        while(!(pPMC->PMC_SR & AT91C_PMC_MCKRDY));
}



