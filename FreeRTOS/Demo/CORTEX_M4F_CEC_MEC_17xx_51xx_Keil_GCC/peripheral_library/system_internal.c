/**************************************************************************//**
 * @file     system_internal.c
 * @brief    CMSIS Device System Source File for
 *           Microchip ARMCM4F Device Series
 * @version  V1.09
 * @date     27. August 2014
 *
 * @note
 *
 ******************************************************************************/
/* Copyright (c) 2011 - 2014 ARM LIMITED

   All rights reserved.
   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions are met:
   - Redistributions of source code must retain the above copyright
     notice, this list of conditions and the following disclaimer.
   - Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.
   - Neither the name of ARM nor the names of its contributors may be used
     to endorse or promote products derived from this software without
     specific prior written permission.
   *
   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
   AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
   IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
   ARE DISCLAIMED. IN NO EVENT SHALL COPYRIGHT HOLDERS AND CONTRIBUTORS BE
   LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
   CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
   SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
   INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
   CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
   ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
   POSSIBILITY OF SUCH DAMAGE.
   ---------------------------------------------------------------------------*/


/*
 * Device CMSIS header file 
 */
#include "common_lib.h"
#include "MCHP_device_header.h"


/*----------------------------------------------------------------------------
  Define clocks
 *----------------------------------------------------------------------------*/
#define __HSI             ( 48000000UL)
#define __XTAL            ( 48000000UL)    /* Oscillator frequency             */

/*
 * Core system clock is 48MHz derived from an internal oscillator
 * It may be divided down using the PCR Processor Clock Control register. 
 * Supported dividers are: 1, 2, 3, 4, 16, and 48.
 * Power on default is 4.
 */
#define __SYSTEM_CLOCK    (__XTAL)

/* !!!! Define EC_INIT_CLK_DIV for the clock divider you 
 * want the ARM CM4F core to run at !!!!
 */
#ifndef EC_INIT_CLK_DIV
#define EC_INIT_CLK_DIV (1u)
#endif

/*----------------------------------------------------------------------------
  System Core Clock Variable
 *----------------------------------------------------------------------------*/
uint32_t SystemCoreClock = __SYSTEM_CLOCK;/* System Core Clock Frequency      */


/**
 * Update SystemCoreClock variable
 *
 * @param  none
 * @return none
 *
 * @brief  Updates the SystemCoreClock with current core Clock
 *         retrieved from cpu registers.
 * @note Read the EC core clock divider from the PCR block's processor 
 * clock control register. Actual EC core frequency is 48MHz / proc_clock_control[7:0].
 */
void SystemCoreClockUpdate (void)
{
    uint32_t cpu_clk_div;
    
    SystemCoreClock = __SYSTEM_CLOCK;
    cpu_clk_div = PCR->PROC_CLK_CNTRL;
    if (cpu_clk_div) {
        SystemCoreClock = __SYSTEM_CLOCK / cpu_clk_div;
    }
}

/**
 * Initialize the system
 *
 * @param  none
 * @return none
 *
 * @brief  Setup the microcontroller system.
 *         Initialize the System.
 * @note SystemInit is usually called from early startup code before 
 * C/C++ library initialization. It is used for early hardware initialization 
 * such as clocks, FPU, debug hardware, etc.
 */
void SystemInit (void)
{
  #if (__FPU_USED == 1)
    SCB->CPACR |= ((3UL << 10*2) |                 /* set CP10 Full Access */
                   (3UL << 11*2)  );               /* set CP11 Full Access */
  #endif

#ifdef UNALIGNED_SUPPORT_DISABLE
  SCB->CCR |= SCB_CCR_UNALIGN_TRP_Msk;
#endif

  /* Program device PCR Processor Clock Control divider to set the EC core clock */
  PCR->PROC_CLK_CNTRL = (EC_INIT_CLK_DIV);
  SystemCoreClock = ( __SYSTEM_CLOCK / (EC_INIT_CLK_DIV) );
  
}
