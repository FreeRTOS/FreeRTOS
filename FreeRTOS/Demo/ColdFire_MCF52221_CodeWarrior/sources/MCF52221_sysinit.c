/*
 * File:		mcf52221_sysinit.c
 * Purpose:		Power-on Reset configuration of the MCF52221.
 *
 * Notes: 
 *
 */
#include "support_common.h"
#include "exceptions.h"



/********************************************************************/
static void pll_init(void)
{

   MCF_CLOCK_CCHR =0x05; // The PLL pre divider - 48MHz / 6 = 8MHz 

	/* The PLL pre-divider affects this!!! 
	 * Multiply 8Mhz reference crystal /CCHR by 10 to acheive system clock of 80Mhz
	 */

	MCF_CLOCK_SYNCR = MCF_CLOCK_SYNCR_MFD(3) | MCF_CLOCK_SYNCR_CLKSRC| MCF_CLOCK_SYNCR_PLLMODE | MCF_CLOCK_SYNCR_PLLEN ;

	while (!(MCF_CLOCK_SYNSR & MCF_CLOCK_SYNSR_LOCK))
	{
	}
}
/********************************************************************/
static void scm_init(void)
{
	/*
	 * Enable on-chip modules to access internal SRAM
	 */
	MCF_SCM_RAMBAR = (0
		| MCF_SCM_RAMBAR_BA(RAMBAR_ADDRESS)
		| MCF_SCM_RAMBAR_BDE);
}

/********************************************************************/

	/*
 * Out of reset, the low-level assembly code calls this routine to
 * initialize the mcf5206e for this board. A temporary stack has been
 * setup in the internal SRAM, and the stack pointer will be changed
 * to point to DRAM once this routine returns.
	 */
void __initialize_hardware(void)
{
	/*******************************************************
	*	Out of reset, the low-level assembly code calls this 
	*	routine to initialize the MCF52221 modules for the  
	*	M522223EVB board. 
	********************************************************/


	asm 
	{
	    /* Initialize IPSBAR */
	    move.l  #__IPSBAR,d0
	       andi.l  #0xC0000000,d0 // need to mask
	    add.l   #0x1,d0
	    move.l  d0,0x40000000

	    

	    /* Initialize FLASHBAR */
	    move.l  #__FLASHBAR,d0
	       andi.l  #0xFFF80000,d0 // need to mask
	    add.l   #0x61,d0
	    movec   d0,FLASHBAR

	}

	
	/* Set real time clock freq */
	MCF_CLOCK_RTCDR = 48000000;
	
	pll_init();
	scm_init();

	initialize_exceptions();
}



