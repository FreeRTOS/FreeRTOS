/*
 * Copyright 2018 NXP.
 * All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * How to set up clock using clock driver functions:
 *
 * 1. Setup clock sources.
 *
 * 2. Setup voltage for the fastest of the clock outputs
 *
 * 3. Set up wait states of the flash.
 *
 * 4. Set up all dividers.
 *
 * 5. Set up all selectors to provide selected clocks.
 */

/* TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
!!GlobalInfo
product: Clocks v4.1
processor: LPC51U68
package_id: LPC51U68JBD64
mcu_data: ksdk2_0
processor_version: 3.0.1
board: LPCXpresso51u68
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS **********/

#include "fsl_power.h"
#include "fsl_clock.h"
#include "clock_config.h"

/*******************************************************************************
 * Definitions
 ******************************************************************************/

/*******************************************************************************
 * Variables
 ******************************************************************************/
/* System clock frequency. */
extern uint32_t SystemCoreClock;

/*******************************************************************************
 ************************ BOARD_InitBootClocks function ************************
 ******************************************************************************/
void BOARD_InitBootClocks(void)
{
    BOARD_BootClockRUN();
}

/*******************************************************************************
 ********************** Configuration BOARD_BootClockRUN ***********************
 ******************************************************************************/
/* TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
!!Configuration
name: BOARD_BootClockRUN
called_from_default_init: true
outputs:
- {id: PLL_clock.outFreq, value: 12 MHz}
- {id: SYSTICK_clock.outFreq, value: 12 MHz}
- {id: System_clock.outFreq, value: 12 MHz}
settings:
- {id: SYSCON.M_MULT.scale, value: '0', locked: true}
- {id: SYSCON.N_DIV.scale, value: '3', locked: true}
- {id: SYSCON.PLL_BYPASS.sel, value: SYSCON.SYSPLLCLKSEL}
- {id: SYSCON.SYSPLLCLKSEL.sel, value: SYSCON.fro_12m}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS **********/

/*******************************************************************************
 * Variables for BOARD_BootClockRUN configuration
 ******************************************************************************/
/*******************************************************************************
 * Code for BOARD_BootClockRUN configuration
 ******************************************************************************/
void BOARD_BootClockRUN(void)
{
    /*!< Set up the clock sources */
    /*!< Set up FRO */
    POWER_DisablePD(kPDRUNCFG_PD_FRO_EN); /*!< Ensure FRO is on  */
    CLOCK_SetupFROClocking(12000000U);    /*!< Set up FRO to the 12 MHz, just for sure */
    CLOCK_AttachClk(kFRO12M_to_MAIN_CLK); /*!< Switch to FRO 12MHz first to ensure we can change voltage without
                                             accidentally being below the voltage for current speed */
    POWER_SetVoltageForFreq(
        12000000U); /*!< Set voltage for the one of the fastest clock outputs: System clock output */
    CLOCK_SetFLASHAccessCyclesForFreq(12000000U); /*!< Set FLASH wait states for core */

    /*!< Set up PLL */
    CLOCK_AttachClk(kFRO12M_to_SYS_PLL); /*!< Switch PLL clock source selector to FRO12M */
    const pll_setup_t pllSetup = {.syspllctrl   = SYSCON_SYSPLLCTRL_UPLIMOFF_MASK | SYSCON_SYSPLLCTRL_BYPASS_MASK,
                                  .syspllndec   = SYSCON_SYSPLLNDEC_NDEC(1U),
                                  .syspllpdec   = SYSCON_SYSPLLPDEC_PDEC(2U),
                                  .syspllssctrl = {0x0U, (SYSCON_SYSPLLSSCTRL1_MD(0U) | (uint32_t)(kSS_MF_512) |
                                                          (uint32_t)(kSS_MR_K0) | (uint32_t)(kSS_MC_NOC))},
                                  .pllRate      = 12000000U,
                                  .flags        = PLL_SETUPFLAG_POWERUP};
    CLOCK_SetPLLFreq(&pllSetup); /*!< Configure PLL to the desired values */

    /* PLL in Fractional/Spread spectrum mode */
    /* SYSTICK is used for waiting for PLL stabilization */

    CLOCK_SetClkDiv(kCLOCK_DivSystickClk, 0U, true);  /*!< Reset SysTick divider counter and halt it */
    CLOCK_SetClkDiv(kCLOCK_DivSystickClk, 3U, false); /*!< Set SysTick divider to value 3 */
    SysTick->LOAD = 27999UL;                          /*!< Set SysTick count value */
    SysTick->VAL  = 0UL;                              /*!< Reset current count value */
    SysTick->CTRL = SysTick_CTRL_ENABLE_Msk;          /*!< Enable SYSTICK */
    while ((SysTick->CTRL & SysTick_CTRL_COUNTFLAG_Msk) != SysTick_CTRL_COUNTFLAG_Msk)
    {
    }                    /*!< Waiting for PLL stabilization */
    SysTick->CTRL = 0UL; /*!< Stop SYSTICK */

    /*!< Set up dividers */
    CLOCK_SetClkDiv(kCLOCK_DivAhbClk, 1U, false);     /*!< Set AHBCLKDIV divider to value 1 */
    CLOCK_SetClkDiv(kCLOCK_DivSystickClk, 0U, true);  /*!< Reset SYSTICKCLKDIV divider counter and halt it */
    CLOCK_SetClkDiv(kCLOCK_DivSystickClk, 1U, false); /*!< Set SYSTICKCLKDIV divider to value 1 */

    /*!< Set up clock selectors - Attach clocks to the peripheries */
    CLOCK_AttachClk(kFRO12M_to_MAIN_CLK); /*!< Switch MAIN_CLK to FRO12M */
    /*!< Set SystemCoreClock variable. */
    SystemCoreClock = BOARD_BOOTCLOCKRUN_CORE_CLOCK;
}

/*******************************************************************************
 ******************** Configuration BOARD_BootClockFRO12M **********************
 ******************************************************************************/
/* TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
!!Configuration
name: BOARD_BootClockFRO12M
outputs:
- {id: SYSTICK_clock.outFreq, value: 12 MHz}
- {id: System_clock.outFreq, value: 12 MHz}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS **********/

/*******************************************************************************
 * Variables for BOARD_BootClockFRO12M configuration
 ******************************************************************************/
/*******************************************************************************
 * Code for BOARD_BootClockFRO12M configuration
 ******************************************************************************/
void BOARD_BootClockFRO12M(void)
{
    /*!< Set up the clock sources */
    /*!< Set up FRO */
    POWER_DisablePD(kPDRUNCFG_PD_FRO_EN); /*!< Ensure FRO is on  */
    CLOCK_SetupFROClocking(12000000U);    /*!< Set up FRO to the 12 MHz, just for sure */
    CLOCK_AttachClk(kFRO12M_to_MAIN_CLK); /*!< Switch to FRO 12MHz first to ensure we can change voltage without
                                             accidentally being below the voltage for current speed */
    POWER_SetVoltageForFreq(
        12000000U); /*!< Set voltage for the one of the fastest clock outputs: System clock output */
    CLOCK_SetFLASHAccessCyclesForFreq(12000000U); /*!< Set FLASH wait states for core */

    /*!< Set up dividers */
    CLOCK_SetClkDiv(kCLOCK_DivAhbClk, 1U, false);     /*!< Set AHBCLKDIV divider to value 1 */
    CLOCK_SetClkDiv(kCLOCK_DivSystickClk, 0U, true);  /*!< Reset SYSTICKCLKDIV divider counter and halt it */
    CLOCK_SetClkDiv(kCLOCK_DivSystickClk, 1U, false); /*!< Set SYSTICKCLKDIV divider to value 1 */

    /*!< Set up clock selectors - Attach clocks to the peripheries */
    CLOCK_AttachClk(kFRO12M_to_MAIN_CLK); /*!< Switch MAIN_CLK to FRO12M */
    /*!< Set SystemCoreClock variable. */
    SystemCoreClock = BOARD_BOOTCLOCKFRO12M_CORE_CLOCK;
}

/*******************************************************************************
 ******************* Configuration BOARD_BootClockFROHF48M *********************
 ******************************************************************************/
/* TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
!!Configuration
name: BOARD_BootClockFROHF48M
outputs:
- {id: SYSTICK_clock.outFreq, value: 48 MHz}
- {id: System_clock.outFreq, value: 48 MHz}
settings:
- {id: SYSCON.MAINCLKSELA.sel, value: SYSCON.fro_hf}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS **********/

/*******************************************************************************
 * Variables for BOARD_BootClockFROHF48M configuration
 ******************************************************************************/
/*******************************************************************************
 * Code for BOARD_BootClockFROHF48M configuration
 ******************************************************************************/
void BOARD_BootClockFROHF48M(void)
{
    /*!< Set up the clock sources */
    /*!< Set up FRO */
    POWER_DisablePD(kPDRUNCFG_PD_FRO_EN); /*!< Ensure FRO is on  */
    CLOCK_SetupFROClocking(12000000U);    /*!< Set up FRO to the 12 MHz, just for sure */
    CLOCK_AttachClk(kFRO12M_to_MAIN_CLK); /*!< Switch to FRO 12MHz first to ensure we can change voltage without
                                             accidentally being below the voltage for current speed */
    POWER_SetVoltageForFreq(
        48000000U); /*!< Set voltage for the one of the fastest clock outputs: System clock output */
    CLOCK_SetFLASHAccessCyclesForFreq(48000000U); /*!< Set FLASH wait states for core */

    CLOCK_SetupFROClocking(48000000U); /*!< Set up high frequency FRO output to selected frequency */

    /*!< Set up dividers */
    CLOCK_SetClkDiv(kCLOCK_DivAhbClk, 1U, false);     /*!< Set AHBCLKDIV divider to value 1 */
    CLOCK_SetClkDiv(kCLOCK_DivSystickClk, 0U, true);  /*!< Reset SYSTICKCLKDIV divider counter and halt it */
    CLOCK_SetClkDiv(kCLOCK_DivSystickClk, 1U, false); /*!< Set SYSTICKCLKDIV divider to value 1 */

    /*!< Set up clock selectors - Attach clocks to the peripheries */
    CLOCK_AttachClk(kFRO_HF_to_MAIN_CLK); /*!< Switch MAIN_CLK to FRO_HF */
    /*!< Set SystemCoreClock variable. */
    SystemCoreClock = BOARD_BOOTCLOCKFROHF48M_CORE_CLOCK;
}

/*******************************************************************************
 ******************* Configuration BOARD_BootClockFROHF96M *********************
 ******************************************************************************/
/* TEXT BELOW IS USED AS SETTING FOR TOOLS *************************************
!!Configuration
name: BOARD_BootClockFROHF96M
outputs:
- {id: SYSTICK_clock.outFreq, value: 96 MHz}
- {id: System_clock.outFreq, value: 96 MHz}
settings:
- {id: SYSCON.MAINCLKSELA.sel, value: SYSCON.fro_hf}
sources:
- {id: SYSCON.fro_hf.outFreq, value: 96 MHz}
 * BE CAREFUL MODIFYING THIS COMMENT - IT IS YAML SETTINGS FOR TOOLS **********/

/*******************************************************************************
 * Variables for BOARD_BootClockFROHF96M configuration
 ******************************************************************************/
/*******************************************************************************
 * Code for BOARD_BootClockFROHF96M configuration
 ******************************************************************************/
void BOARD_BootClockFROHF96M(void)
{
    /*!< Set up the clock sources */
    /*!< Set up FRO */
    POWER_DisablePD(kPDRUNCFG_PD_FRO_EN); /*!< Ensure FRO is on  */
    CLOCK_SetupFROClocking(12000000U);    /*!< Set up FRO to the 12 MHz, just for sure */
    CLOCK_AttachClk(kFRO12M_to_MAIN_CLK); /*!< Switch to FRO 12MHz first to ensure we can change voltage without
                                             accidentally being below the voltage for current speed */
    POWER_SetVoltageForFreq(
        96000000U); /*!< Set voltage for the one of the fastest clock outputs: System clock output */
    CLOCK_SetFLASHAccessCyclesForFreq(96000000U); /*!< Set FLASH wait states for core */

    CLOCK_SetupFROClocking(96000000U); /*!< Set up high frequency FRO output to selected frequency */

    /*!< Set up dividers */
    CLOCK_SetClkDiv(kCLOCK_DivAhbClk, 1U, false);     /*!< Set AHBCLKDIV divider to value 1 */
    CLOCK_SetClkDiv(kCLOCK_DivSystickClk, 0U, true);  /*!< Reset SYSTICKCLKDIV divider counter and halt it */
    CLOCK_SetClkDiv(kCLOCK_DivSystickClk, 1U, false); /*!< Set SYSTICKCLKDIV divider to value 1 */

    /*!< Set up clock selectors - Attach clocks to the peripheries */
    CLOCK_AttachClk(kFRO_HF_to_MAIN_CLK); /*!< Switch MAIN_CLK to FRO_HF */
    /*!< Set SystemCoreClock variable. */
    SystemCoreClock = BOARD_BOOTCLOCKFROHF96M_CORE_CLOCK;
}
