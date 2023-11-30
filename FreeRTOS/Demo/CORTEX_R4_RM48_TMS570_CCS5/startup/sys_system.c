/** @file system.c 
*   @brief System Driver Source File
*   @date 05.November.2010
*   @version 1.01.000
*
*   This file contains:
*   - API Funcions
*   .
*   which are relevant for the System driver.
*/

/* (c) Texas Instruments 2010, All rights reserved. */


/* Include Files */

#include "sys_system.h"

#define startupCPU_100MHZ 1

void systemInit(void)
{
    /** @b Initialize @b Flash @b Wrapper: */

    /** - Setup flash read mode, address wait states and data wait states */
#if	startupCPU_100MHZ == 1
	/* 100MHz */
    flashWREG->FRDCNTL =  0x01000000U
                       | (2U << 8U)
                       | (0U << 4U)
                       |  1U;
#else
    /* 180MHz */
    flashWREG->FRDCNTL =  0x01000000U 
                       | (3U << 8U) 
                       | (1U << 4U) 
                       |  1U;
#endif

#if 0
    /** - Setup flash bank power modes */
    flashWREG->FBFALLBACK = 0x05050000
                          | (SYS_ACTIVE << 14U)
                          | (SYS_SLEEP << 12U)
                          | (SYS_SLEEP << 10U)
                          | (SYS_SLEEP << 8U)
                          | (SYS_SLEEP << 6U)
                          | (SYS_SLEEP << 4U)
                          | (SYS_ACTIVE << 2U)
                          |  SYS_ACTIVE;

    /** @b Initialize @b Lpo: */
    {
        unsigned trim = *(volatile unsigned short *)0xF00801B4;

        if (trim != 0xFFFF)
        {
            systemREG1->LPOMONCTL = (1U << 24U)
                                  | (0U << 16U)
                                  | trim;
        }
        else
        {
            systemREG1->LPOMONCTL = (1U << 24U)
                                  | (0U << 16U)
                                  | (systemREG1->LPOMONCTL & 0xFFFF);
        }
    }
#endif

    /** @b Initialize @b Pll: */

    /** - Setup pll control register 1:
    *     - Setup reset on oscillator slip 
    *     - Setup bypass on pll slip
    *     - Setup Pll output clock divider
    *     - Setup reset on oscillator fail
    *     - Setup reference clock divider 
    *     - Setup Pll multiplier          
    */

#if	startupCPU_100MHZ == 1
	/* 100MHz */
    systemREG1->PLLCTL1 =  0x00000000U
                        |  0x20000000U
                        | (0U << 24U)
                        |  0x00000000U
                        | (5U << 16U)
                        | (74U << 8U);
#else
    /* 180Mhz */
    systemREG1->PLLCTL1 =  0x00000000U 
                        |  0x20000000U 
                        | (0U << 24U) 
                        |  0x00000000U 
                        | (5U << 16U) 
                        | (134U << 8U);
#endif

    /** - Setup pll control register 1 
    *     - Enable/Disable frequency modulation
    *     - Setup spreading rate
    *     - Setup bandwidth adjustment
    *     - Setup internal Pll output divider
    *     - Setup spreading amount
    */
    systemREG1->PLLCTL2 = 0x00000000U
                        | (255U << 22U)
                        | (7U << 12U)
                        | (1U << 9U)
                        |  61U;

    /** @b Initialize @b Clock @b Tree: */

    /** - Start clock source lock */
    systemREG1->CSDISCLR = 0x00000000U
                         | 0x00000000U 
                         | 0x00000000U 
                         | 0x00000000U 
                         | 0x00000002U; 

    /** - Wait for until clocks are locked */
    while ((systemREG1->CSVSTAT & 0x00000002U) == 0x00); /* wait for PLL */

    /** - Setup GCLK, HCLK and VCLK clock source for normal operation, power down mode and after wakeup */
    systemREG1->GHVSRC = (SYS_PLL << 24U) 
                       | (SYS_PLL << 16U) 
                       |  SYS_PLL;

    /** - Power-up all peripharals */
    pcrREG->PSPWRDWNCLR0 = 0xFFFFFFFFU;
    pcrREG->PSPWRDWNCLR1 = 0xFFFFFFFFU;
    pcrREG->PSPWRDWNCLR2 = 0xFFFFFFFFU;
    pcrREG->PSPWRDWNCLR3 = 0xFFFFFFFFU;

    /** - Setup synchronous peripheral clock dividers for VCLK1 and VCLK2 */
    systemREG1->PENA      = 0U;
    systemREG1->VCLKR     = 15U;
    systemREG1->VCLK2R    = 1U;
    systemREG1->VCLKR     = 1U;

    systemREG2->CLK2CNTRL = (1U << 8U)
                          | 1U;

    /** - Setup RTICLK1 and RTICLK2 clocks */
    /* 90MHz (180Mhz/2) */
    systemREG1->RCLKSRC = (1U << 24U)
                        | (SYS_VCLK << 16U)
                        | (1U << 8U)  
                        |  SYS_VCLK;

#if 0
    /** - Setup asynchronous peripheral clock sources for AVCLK1 and AVCLK2 */
    systemREG1->VCLKASRC = (SYS_FR_PLL << 8U)
                         |  SYS_VCLK;

    /** - Setup asynchronous peripheral clock sources for AVCLK3 and AVCLK4 */
    systemREG2->VCLKACON1 = (0U << 24U)
                          | (0U << 20U)
                          | (SYS_EXTERNAL2 << 16U)
                          | (3U << 8U)
                          | (0U << 4U)
                          |  SYS_EXTERNAL;
#endif

    /** - Enable Peripherals */
    systemREG1->PENA = 1U;

    /** @note: HCLK >= VCLK2 >= VCLK_sys */
}

