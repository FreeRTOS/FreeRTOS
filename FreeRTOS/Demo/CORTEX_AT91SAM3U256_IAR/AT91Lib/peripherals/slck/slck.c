/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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

#if defined(at91cap9)
//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "slck.h"
#include <utility/assert.h>
#include <utility/trace.h>
#include <utility/util.h>

//------------------------------------------------------------------------------
//         Local definitions
//------------------------------------------------------------------------------

/// Start Up Time Slow Clock 32K Oscillator // see DC characteritics in Datasheet
#define T_ST_SLCK_32K_IN_MS  1200 

/// Start Up Time Slow Clock RC Oscillator  // see DC characteritics in Datasheet
#define T_ST_SLCK_RC_IN_US     75 

#define FREQ_SLCK_32K     32768 // see DC characteritics in Datasheet
#define MIN_FREQ_SLCK_RC  20000 // see DC characteritics in Datasheet

#define TIME_5_CYCLES_32K_IN_US     ((2 * 5 * 1000000) / FREQ_SLCK_32K)
#define TIME_5_CYCLES_RC_IN_US      ((2 * 5 * 1000000) / MIN_FREQ_SLCK_RC)

//------------------------------------------------------------------------------
//         Local functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Wait time in ms
//------------------------------------------------------------------------------
// not precise, depends on the compiler and on the options
static void WaitTimeInMs(unsigned int pck, unsigned int time_ms)
{
    register unsigned int i = 0;
    i = (pck / 1000) * time_ms;
    i = i / 4;    
    while(i--);
}

//------------------------------------------------------------------------------
/// Wait time in us
//------------------------------------------------------------------------------
// not precise, depends on the compiler and on the options
static void WaitTimeInUs(unsigned int pck, unsigned int time_us)
{
    volatile unsigned int i = 0;
    i = (pck / 1000000) * time_us;  
    i = i / 4;    
    while(i--);
}

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Return 1 if the slow clock is 32k
//------------------------------------------------------------------------------
unsigned char SLCK_Is32k(void)
{
    return ((*AT91C_SYS_SLCKSEL & AT91C_SLCKSEL_OSCSEL) != 0);
}

//------------------------------------------------------------------------------
/// Configure the 32kHz oscillator for the slow clock
//------------------------------------------------------------------------------
void SLCK_RCto32k(void)
{
    // Check that the master clock has a different source than slow clock. If no,
    if( (AT91C_BASE_PMC->PMC_MCKR & AT91C_PMC_CSS) == 0)
    {
        TRACE_WARNING("The master clock use the slow clock. " \
            "Not possible to change Slow clock\n\r");       
        return;
    }

    // Check that the slow clock source is RC
    if( SLCK_Is32k() )
    {
        TRACE_WARNING("The slow clock is already the external 32.768kHz crystal\n\r");             
        return;
    }    
    
    // Enable the 32,768 Hz oscillator by setting the bit OSC32EN to 1.
    *AT91C_SYS_SLCKSEL |= AT91C_SLCKSEL_OSC32EN;
    
    // Wait 32,768 Hz Startup Time for clock stabilization (software loop).    
    WaitTimeInMs(BOARD_MCK*2, T_ST_SLCK_32K_IN_MS);
    
    // Switch from internal RC to 32,768 Hz oscillator by setting the bit OSCSEL to 1.
    *AT91C_SYS_SLCKSEL |= AT91C_SLCKSEL_OSCSEL;    
    
    // Wait 5 slow clock cycles for internal resynchronization.   
    WaitTimeInUs(BOARD_MCK*2, TIME_5_CYCLES_32K_IN_US);     
    
    // Disable the RC oscillator by setting the bit RCEN to 0.    
    *AT91C_SYS_SLCKSEL &= (0xFFFFFFFF ^ AT91C_SLCKSEL_RCEN);
    
    TRACE_INFO("The slow clock is now the external 32.768kHz crystal\n\r");    
}


//------------------------------------------------------------------------------
/// Configure the RC oscillator for the slow clock
//------------------------------------------------------------------------------
void SLCK_32ktoRC(void)
{
    // Check that the master clock has a different source than slow clock.
    if( (AT91C_BASE_PMC->PMC_MCKR & AT91C_PMC_CSS) == 0)
    {
        TRACE_WARNING("The master clock use the slow clock. " \
            "Not possible to change Slow clock\n\r");             
        return;
    }
    
    // Check that the slow clock source is RC
    if( !SLCK_Is32k() )
    {
        TRACE_WARNING("The slow clock is already the internal RC oscillator\n\r");       
        return;
    }        
    
    // Enable the internal RC oscillator by setting the bit RCEN to 1
    *AT91C_SYS_SLCKSEL |= AT91C_SLCKSEL_RCEN;
    
    // Wait internal RC Startup Time for clock stabilization (software loop).
    WaitTimeInUs(BOARD_MCK*2, T_ST_SLCK_RC_IN_US);
    
    // Switch from 32768 Hz oscillator to internal RC by setting the bit OSCSEL to 0.
    *AT91C_SYS_SLCKSEL &= (0xFFFFFFFF ^ AT91C_SLCKSEL_OSCSEL);
    
    // Wait 5 slow clock cycles for internal resynchronization.
    WaitTimeInUs(BOARD_MCK*2, TIME_5_CYCLES_RC_IN_US);  
    
    // Disable the 32768 Hz oscillator by setting the bit OSC32EN to 0.   
    *AT91C_SYS_SLCKSEL &= (0xFFFFFFFF ^ AT91C_SLCKSEL_OSC32EN);
    
    TRACE_INFO("The slow clock is now the internal RC oscillator\n\r");      
}

//------------------------------------------------------------------------------
/// by pass the 32kHz oscillator
//------------------------------------------------------------------------------
void SLCK_bypass32Kosc(void)
{
    // Enable the bypass path OSC32BYP bit set to 1
    *AT91C_SYS_SLCKSEL |= AT91C_SLCKSEL_OSC32BYP;
  
    // Disable the 32,768 Hz oscillator by setting the bit OSC32EN to 0
    *AT91C_SYS_SLCKSEL &= (0xFFFFFFFF ^ AT91C_SLCKSEL_OSC32EN);     
}

//------------------------------------------------------------------------------
/// set Slow Clock Mode
//------------------------------------------------------------------------------
#define TIMEOUT             10000000
void SLCK_UtilSetSlowClockMode(unsigned int timeInSlowClockMode)
{
    unsigned int oldPll;
    unsigned int oldMck;  
    unsigned int timeout = 0;  
    
    // Save previous values for PLL A and Master Clock configuration
    oldPll = AT91C_BASE_CKGR->CKGR_PLLAR;
    oldMck = AT91C_BASE_PMC->PMC_MCKR;
     
    // Slow clock is selected for Master Clock 
    // 32kKz / 64 = 500Hz
    // PCK = 500Hz, MCK = 250 MHz
    AT91C_BASE_PMC->PMC_MCKR = AT91C_PMC_CSS_SLOW_CLK | AT91C_PMC_PRES_CLK_64 | AT91C_PMC_MDIV_2;
    timeout = 0;
    while ( !(AT91C_BASE_PMC->PMC_SR & AT91C_PMC_MCKRDY) && timeout++ < TIMEOUT);
      
    // Stop PLL A
    // MULA: PLL A Multiplier 0 = The PLL A is deactivated.
    AT91C_BASE_CKGR->CKGR_PLLAR = 0x00003f00; 
   
    // Stop Main Oscillator
    AT91C_BASE_CKGR->CKGR_MOR = AT91C_BASE_CKGR->CKGR_MOR & (~AT91C_CKGR_MOSCEN);  
    
    // Wait a while. The clock is at 500Hz...
    while( timeInSlowClockMode-- );
    // End !  
    
    // Restart Main Oscillator    
    AT91C_BASE_CKGR->CKGR_MOR = AT91C_BASE_CKGR->CKGR_MOR | (AT91C_CKGR_OSCOUNT & (0x32<<8) );
    AT91C_BASE_CKGR->CKGR_MOR = AT91C_BASE_CKGR->CKGR_MOR | (AT91C_CKGR_MOSCEN);

    // Restart PLL A
    AT91C_BASE_CKGR->CKGR_PLLAR = oldPll;        
    timeout = 0;
    while( !(AT91C_BASE_PMC->PMC_SR & AT91C_PMC_LOCKA) && timeout++ < TIMEOUT);
    
    // Selection of Master Clock MCK (so Processor Clock PCK)
    AT91C_BASE_PMC->PMC_MCKR = oldMck;  
    timeout = 0;
    while( !(AT91C_BASE_PMC->PMC_SR & AT91C_PMC_MCKRDY) && timeout++ < TIMEOUT);    
        
    // Reconfigure DBGU
    TRACE_CONFIGURE(DBGU_STANDARD, 115200, BOARD_MCK);                 
}

//------------------------------------------------------------------------------
/// get the slow clock frequency
//------------------------------------------------------------------------------
unsigned int SLCK_UtilGetFreq(void)
{
    unsigned int freq = 0;
    
    SLCK_UtilSetSlowClockMode(0);
    
    if(AT91C_BASE_PMC->PMC_MCFR & (1<<16)) {
        freq = BOARD_MAINOSC / (AT91C_BASE_PMC->PMC_MCFR & 0x0000FFFF);
        freq *= 16;        
    }
    return freq;
}

#endif //#if defined(at91cap9)