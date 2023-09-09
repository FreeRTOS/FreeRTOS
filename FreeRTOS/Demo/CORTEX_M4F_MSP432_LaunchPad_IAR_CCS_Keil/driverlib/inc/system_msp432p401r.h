/**************************************************************************//**
* @file     system_msp432p401r.h
* @brief    CMSIS Cortex-M4F Device Peripheral Access Layer Header File for
*           MSP432P401R
* @version  V1.00
* @date     20-Oct-2015
*
* @note     View configuration instructions embedded in comments
*
******************************************************************************/
/****************************************************************************** */
/* */
/* Copyright (C) 2015 Texas Instruments Incorporated - http://www.ti.com/ */
/* */
/* Redistribution and use in source and binary forms, with or without */
/* modification, are permitted provided that the following conditions */
/* are met: */
/* */
/*  Redistributions of source code must retain the above copyright */
/*  notice, this list of conditions and the following disclaimer. */
/* */
/*  Redistributions in binary form must reproduce the above copyright */
/*  notice, this list of conditions and the following disclaimer in the */
/*  documentation and/or other materials provided with the */
/*  distribution. */
/* */
/*  Neither the name of Texas Instruments Incorporated nor the names of */
/*  its contributors may be used to endorse or promote products derived */
/*  from this software without specific prior written permission. */
/* */
/* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS */
/* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT */
/* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR */
/* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT */
/* OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, */
/* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT */
/* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, */
/* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY */
/* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT */
/* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE */
/* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. */
/* */
/****************************************************************************** */

#ifndef SYSTEM_MSP432P401R_H
    #define SYSTEM_MSP432P401R_H

    #ifdef __cplusplus
    extern "C" {
    #endif

    #include <stdint.h>

    extern uint32_t SystemCoreClock; /*!< System Clock Frequency (Core Clock)  */


/**
 * Initialize the system
 *
 * @param  none
 * @return none
 *
 * @brief  Setup the microcontroller system.
 *
 * Performs the following initialization steps:
 *     1. Enables the FPU
 *     2. Halts the WDT
 *     3. Enables all SRAM banks
 *     4. Sets up power __REGULATOR and VCORE
 *     5. Enable Flash wait states if needed
 *     6. Change MCLK to desired frequency
 *     7. Enable Flash read buffering
 */
    extern void SystemInit( void );

/**
 * Update SystemCoreClock variable
 *
 * @param  none
 * @return none
 *
 * @brief  Updates the SystemCoreClock with current core Clock
 *         retrieved from cpu registers.
 */
    extern void SystemCoreClockUpdate( void );

    #ifdef __cplusplus
}
    #endif

#endif /* SYSTEM_MSP432P401R_H */
