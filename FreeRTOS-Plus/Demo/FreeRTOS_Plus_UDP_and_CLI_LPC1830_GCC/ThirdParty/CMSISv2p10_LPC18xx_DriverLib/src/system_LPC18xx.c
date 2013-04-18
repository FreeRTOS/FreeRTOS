/*
 * Modifications for use with Code Red's toolchain - 2011/11/24
 */
/**********************************************************************
* $Id$		system_LPC18xx.c			2011-06-02
*//**
* @file		system_LPC18xx.c
* @brief	Cortex-M3 Device System Source File for NXP LPC18xx Series.
* @version	1.0
* @date		02. June. 2011
* @author	NXP MCU SW Application Team
*
* Copyright(C) 2011, NXP Semiconductor
* All rights reserved.
*
***********************************************************************
* Software that is described herein is for illustrative purposes only
* which provides customers with programming information regarding the
* products. This software is supplied "AS IS" without any warranties.
* NXP Semiconductors assumes no responsibility or liability for the
* use of the software, conveys no license or title under any patent,
* copyright, or mask work right to the product. NXP Semiconductors
* reserves the right to make changes in the software without
* notification. NXP Semiconductors also make no representation or
* warranty that such application will be suitable for the specified
* use without further testing or modification.
**********************************************************************/

#include "LPC18xx.h"
#include "lpc18xx_cgu.h"
/*----------------------------------------------------------------------------
  Define clocks
 *----------------------------------------------------------------------------*/
#define __IRC            (12000000UL)    /* IRC Oscillator frequency          */

/*----------------------------------------------------------------------------
  Clock Variable definitions
 *----------------------------------------------------------------------------*/
uint32_t SystemCoreClock = __IRC * 10UL;		/*!< System Clock Frequency (Core Clock)*/

#ifndef __CODE_RED
extern uint32_t getPC(void);
#endif

/**
 * Initialize the system
 *
 * @param  none
 * @return none
 *
 * @brief  Setup the microcontroller system.
 *         Initialize the System.
 */
void SystemInit (void)
{
#ifdef __CODE_RED
    // CodeRed startup code will modify VTOR register to match
    // when code has been linked to run from.

    // Check whether we are running from external flash
    if (SCB->VTOR == 0x1C000000)
        /*Enable Buffer for External Flash*/
        LPC_EMC->STATICCONFIG0 |= 1<<19;

    // Call clock initialisation code
    CGU_Init();

#else
	// Enable VTOR register to point to vector table
	SCB->VTOR = getPC() & 0xFFF00000;
    /*Enable Buffer for External Flash*/
    LPC_EMC->STATICCONFIG0 |= 1<<19;

#endif

}
