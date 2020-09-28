/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No 
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all 
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, 
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM 
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES 
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS 
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of 
* this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : mcu_clocks.c
* Description  : Contains clock specific routines
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 08.10.2019 1.00     First Release
*         : 10.12.2019 1.01     Removed unnecessary processing from the clock_source_select fucntion.
*         : 17.12.2019 1.02     Fixed warning of clock_source_select function with IAR compiler.
*         : 14.02.2020 1.03     Fixed warning of clock_source_select function with CCRX and IAR compiler.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "platform.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define BSP_PRV_CKSEL_LOCO            (0x0)
#define BSP_PRV_CKSEL_HOCO            (0x1)
#define BSP_PRV_CKSEL_MAIN_OSC        (0x2)
#define BSP_PRV_CKSEL_SUBCLOCK        (0x3)
#define BSP_PRV_CKSEL_PLL             (0x4)

#define BSP_PRV_NORMALIZE_X10  (10)   /* used to avoid floating point arithmetic */

/* This macro runs or stops the low-speed on-chip oscillator(LOCO).
   If the following conditions are satisfied, LOCO will operate.
   1. System clock source is LOCO.
   2. Clock output enable and CLKOUT source is LOCO.
 */
#if (BSP_CFG_CLOCK_SOURCE == 0) \
     || ((BSP_CFG_CLKOUT_OUTPUT == 1) && (BSP_CFG_CLKOUT_SOURCE == 0))
    #define BSP_PRV_LOCO_CLK_OPERATING    (1)    /* LOCO is operating. */
#else
    #define BSP_PRV_LOCO_CLK_OPERATING    (0)    /* LOCO is stopped. */
#endif

/* This macro runs or stops the high-speed on-chip oscillator(HOCO).
   If the following conditions are satisfied, HOCO will operate.
   1. System clock source is HOCO.
   2. System clock source is PLL circuit. PLL source is HOCO.
   3. PHY clock source is PLL circuit. PLL source is HOCO.
   4. PHY clock source is PPLL circuit. PPLL source is HOCO.
   5. Clock output enable and clock output source is HOCO.
   6. Clock output enable and clock output source is PLL circuit. PLL source is HOCO.
   7. Clock output enable and clock output source is PPLL circuit. PPLL source is HOCO.
 */
#if (BSP_CFG_CLOCK_SOURCE == 1) \
     || ((BSP_CFG_CLOCK_SOURCE == 4) && (BSP_CFG_PLL_SRC == 1)) \
     || ((BSP_CFG_PHY_CLOCK_SOURCE == 0) && (BSP_CFG_PLL_SRC == 1)) \
     || ((BSP_CFG_PHY_CLOCK_SOURCE == 1) && (BSP_CFG_PLL_SRC == 1)) \
     || ((BSP_CFG_CLKOUT_OUTPUT == 1) && (BSP_CFG_CLKOUT_SOURCE == 1)) \
     || ((BSP_CFG_CLKOUT_OUTPUT == 1) && (BSP_CFG_CLKOUT_SOURCE == 4) && (BSP_CFG_PLL_SRC == 1)) \
     || ((BSP_CFG_CLKOUT_OUTPUT == 1) && (BSP_CFG_CLKOUT_SOURCE == 6) && (BSP_CFG_PLL_SRC == 1))
    #define BSP_PRV_HOCO_CLK_OPERATING    (1)    /* HOCO is operating. */
#else
    #define BSP_PRV_HOCO_CLK_OPERATING    (0)    /* HOCO is stopped. */
#endif

/* This macro runs or stops the Main-clock oscillator.
   If the following conditions are satisfied, Main-clock oscillator will operate.
   1. System clock source is Main-clock oscillator.
   2. System clock source is PLL circuit. PLL source is Main-clock oscillator.
   3. USB clock source is PPLL circuit. PPLL source is Main-clock oscillator.
   4. PHY clock source is PLL circuit. PLL source is Main-clock oscillator.
   5. PHY clock source is PPLL circuit. PPLL source is Main-clock oscillator.
   6. Clock output enable and clock output source is Main-clock oscillator.
   7. Clock output enable and clock output source is PLL circuit. PLL source is Main-clock oscillator.
   8. Clock output enable and clock output source is PPLL circuit. PPLL source is Main-clock oscillator.
 */
#if (BSP_CFG_CLOCK_SOURCE == 2) \
     || ((BSP_CFG_CLOCK_SOURCE == 4) && (BSP_CFG_PLL_SRC == 0)) \
     || ((BSP_CFG_USB_CLOCK_SOURCE == 3) && (BSP_CFG_PLL_SRC == 0)) \
     || ((BSP_CFG_PHY_CLOCK_SOURCE == 0) && (BSP_CFG_PLL_SRC == 0)) \
     || ((BSP_CFG_PHY_CLOCK_SOURCE == 1) && (BSP_CFG_PLL_SRC == 0)) \
     || ((BSP_CFG_CLKOUT_OUTPUT == 1) && (BSP_CFG_CLKOUT_SOURCE == 2)) \
     || ((BSP_CFG_CLKOUT_OUTPUT == 1) && (BSP_CFG_CLKOUT_SOURCE == 4) && (BSP_CFG_PLL_SRC == 0)) \
     || ((BSP_CFG_CLKOUT_OUTPUT == 1) && (BSP_CFG_CLKOUT_SOURCE == 6) && (BSP_CFG_PLL_SRC == 0))
    #define BSP_PRV_MAIN_CLK_OPERATING    (1)    /* Main-clock oscillator is operating. */
#else
    #define BSP_PRV_MAIN_CLK_OPERATING    (0)    /* Main-clock oscillator is stopped. */
#endif

/* This macro runs or stops the Sub-clock oscillator.
   If the following conditions are satisfied, Sub-clock oscillator will operate.
   1. System clock source is Sub-clock oscillator.
   2. Clock output enable and clock output source is Sub-clock oscillator.
 */
#if (BSP_CFG_CLOCK_SOURCE == 3) \
     || ((BSP_CFG_CLKOUT_OUTPUT == 1) && (BSP_CFG_CLKOUT_SOURCE == 3))
    #define BSP_PRV_SUB_CLK_OPERATING    (1)    /* Sub-clock oscillator is operating. */
#else /* Clock source is not Sub-clock oscillator. */
    #define BSP_PRV_SUB_CLK_OPERATING    (0)    /* Sub-clock oscillator is stopped. */
#endif

/* This macro runs or stops the PLL circuit.
   If the following conditions are satisfied, PLL circuit will operate.
   1. System clock source is PLL circuit.
   2. PHY clock source is PLL circuit.
   3. Clock output enable and clock output source is PLL circuit.
 */
#if (BSP_CFG_CLOCK_SOURCE == 4) \
     || (BSP_CFG_PHY_CLOCK_SOURCE == 0) \
     || ((BSP_CFG_CLKOUT_OUTPUT == 1) && (BSP_CFG_CLKOUT_SOURCE == 4))
    #define BSP_PRV_PLL_CLK_OPERATING    (1)    /* PLL circuit is operating. */
#else /* PLL is not used as clock source. */
    #define BSP_PRV_PLL_CLK_OPERATING    (0)    /* PLL circuit is stopped. */
#endif

/* This macro runs or stops the PPLL circuit.
   If the following conditions are satisfied, PPLL circuit will operate.
   1. USB clock source is PPLL circuit.
   2. PHY clock source is PPLL circuit.
   3. Clock output enable and clock output source is PPLL circuit.
 */
#if (BSP_CFG_USB_CLOCK_SOURCE == 3) \
     || (BSP_CFG_PHY_CLOCK_SOURCE == 1) \
     || ((BSP_CFG_CLKOUT_OUTPUT == 1) && (BSP_CFG_CLKOUT_SOURCE == 6))
    #define BSP_PRV_PPLL_CLK_OPERATING    (1)    /* PPLL circuit is operating. */
#else /* PPLL is not used for USB clock. */
    #define BSP_PRV_PPLL_CLK_OPERATING    (0)    /* PPLL circuit is stopped. */
#endif

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global variables (to be accessed by other files)
***********************************************************************************************************************/

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
/* When using the user startup program, disable the following code. */
#if BSP_CFG_STARTUP_DISABLE == 0
static void operating_frequency_set(void);
static void clock_source_select(void);
#if BSP_CFG_CLKOUT_OUTPUT != 0
/* CLKOUT initial configuration function declaration */
static void bsp_clkout_initial_configure(void);
#endif /* BSP_CFG_CLKOUT_OUTPUT != 0 */
#endif /* BSP_CFG_STARTUP_DISABLE == 0 */

/***********************************************************************************************************************
* Function Name: get_iclk_freq_hz
* Description  : Return the current ICLK frequency in Hz.  Called by R_BSP_GetIClkFreqHz().
*                The system clock source can be changed at any time via SYSTEM.SCKCR3.BIT.CKSEL, so in order to
*                determine the ICLK frequency we need to first find the current system clock source and then,
*                in some cases where the clock source can be configured for multiple frequencies, calculate the
*                frequency at which it is currently running.
* Arguments    : None
* Return Value : uint32_t - the iclk frequency in Hz
***********************************************************************************************************************/
uint32_t get_iclk_freq_hz(void)
{
    uint32_t sys_clock_src_freq;
    uint32_t pll_multiplier;
    uint32_t pll_source_freq;
    uint32_t hoco_frequency[3] = {16000000, 18000000, 20000000};

    /* Casting is valid because it matches the type to the retern value. */
    uint8_t  cksel = (uint8_t)SYSTEM.SCKCR3.BIT.CKSEL;

    switch (cksel)
    {
        case BSP_PRV_CKSEL_LOCO:
            sys_clock_src_freq = BSP_LOCO_HZ;
            break;

        case BSP_PRV_CKSEL_HOCO:

            /* Set HOCO frequency. */
            sys_clock_src_freq = hoco_frequency[SYSTEM.HOCOCR2.BIT.HCFRQ];
            break;

        case BSP_PRV_CKSEL_MAIN_OSC:
            sys_clock_src_freq = BSP_CFG_XTAL_HZ;
            break;

        case BSP_PRV_CKSEL_SUBCLOCK:
            sys_clock_src_freq = BSP_SUB_CLOCK_HZ;
            break;

        case BSP_PRV_CKSEL_PLL:

            /* The RX72N have two possible sources for the PLL */

            /* Casting is valid because it matches the type to the retern value. */
            pll_multiplier = ((((uint32_t)(SYSTEM.PLLCR.BIT.STC + 1)) * BSP_PRV_NORMALIZE_X10) / 2);

            /* Default to the MAIN OSC as the PLL source */
            pll_source_freq = BSP_CFG_XTAL_HZ;

            /* If 1 then the HOCO is the PLL source */
            if (0x1 == SYSTEM.PLLCR.BIT.PLLSRCSEL)
            {
                /* Set HOCO frequency. */
                pll_source_freq = hoco_frequency[SYSTEM.HOCOCR2.BIT.HCFRQ];
            }

            /* Casting is valid because it matches the type to the retern value. */
            sys_clock_src_freq = ((pll_source_freq / (((uint32_t)(SYSTEM.PLLCR.BIT.PLIDIV + 1)) * BSP_PRV_NORMALIZE_X10)) * pll_multiplier);
            break;

        default:

            /* Should never arrive here. Use the Main OSC freq as a default... */
            sys_clock_src_freq = BSP_CFG_XTAL_HZ;
            break;
    }

    /* Finally, divide the system clock source frequency by the currently set ICLK divider to get the ICLK frequency */
    return (sys_clock_src_freq / (uint32_t)(1 << SYSTEM.SCKCR.BIT.ICK));
} /* End of function get_iclk_freq_hz() */

/* When using the user startup program, disable the following code. */
#if BSP_CFG_STARTUP_DISABLE == 0

/***********************************************************************************************************************
* Function name: mcu_clock_setup
* Description  : Contains clock functions called at device restart.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void mcu_clock_setup(void)
{
    /* Switch to high-speed operation */
    operating_frequency_set();

#if BSP_CFG_CLKOUT_OUTPUT != 0
    bsp_clkout_initial_configure();
#endif /* BSP_CFG_CLKOUT_OUTPUT != 0 */
} /* End of function mcu_clock_setup() */

/***********************************************************************************************************************
* Function name: operating_frequency_set
* Description  : Configures the clock settings for each of the device clocks
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
static void operating_frequency_set (void)
{
    /* Used for constructing value to write to SCKCR, SCKCR2, and SCKCR3 registers. */
    uint32_t tmp_clock = 0;
    uint32_t tmp_restore_clock = 0;

    /* Protect off. */
    SYSTEM.PRCR.WORD = 0xA50B;

    /* Select the clock based upon user's choice. */
    clock_source_select();

    /* Figure out setting for FCK bits. */
#if   BSP_CFG_FCK_DIV == 1
    /* Do nothing since FCK bits should be 0. */
#elif BSP_CFG_FCK_DIV == 2
    tmp_clock |= 0x10000000;
#elif BSP_CFG_FCK_DIV == 4
    tmp_clock |= 0x20000000;
#elif BSP_CFG_FCK_DIV == 8
    tmp_clock |= 0x30000000;
#elif BSP_CFG_FCK_DIV == 16
    tmp_clock |= 0x40000000;
#elif BSP_CFG_FCK_DIV == 32
    tmp_clock |= 0x50000000;
#elif BSP_CFG_FCK_DIV == 64
    tmp_clock |= 0x60000000;
#else
    #error "Error! Invalid setting for BSP_CFG_FCK_DIV in r_bsp_config.h"
#endif

    /* Figure out setting for ICK bits. */
#if   BSP_CFG_ICK_DIV == 1
    /* Do nothing since ICK bits should be 0. */
#elif BSP_CFG_ICK_DIV == 2
    tmp_clock |= 0x01000000;
#elif BSP_CFG_ICK_DIV == 4
    tmp_clock |= 0x02000000;
#elif BSP_CFG_ICK_DIV == 8
    tmp_clock |= 0x03000000;
#elif BSP_CFG_ICK_DIV == 16
    tmp_clock |= 0x04000000;
#elif BSP_CFG_ICK_DIV == 32
    tmp_clock |= 0x05000000;
#elif BSP_CFG_ICK_DIV == 64
    tmp_clock |= 0x06000000;
#else
    #error "Error! Invalid setting for BSP_CFG_ICK_DIV in r_bsp_config.h"
#endif

    /* Figure out setting for BCK bits. */
#if   BSP_CFG_BCK_DIV == 1
    /* Do nothing since BCK bits should be 0. */
#elif BSP_CFG_BCK_DIV == 2
    tmp_clock |= 0x00010000;
#elif BSP_CFG_BCK_DIV == 3
    tmp_clock |= 0x00090000;
#elif BSP_CFG_BCK_DIV == 4
    tmp_clock |= 0x00020000;
#elif BSP_CFG_BCK_DIV == 8
    tmp_clock |= 0x00030000;
#elif BSP_CFG_BCK_DIV == 16
    tmp_clock |= 0x00040000;
#elif BSP_CFG_BCK_DIV == 32
    tmp_clock |= 0x00050000;
#elif BSP_CFG_BCK_DIV == 64
    tmp_clock |= 0x00060000;
#else
    #error "Error! Invalid setting for BSP_CFG_BCK_DIV in r_bsp_config.h"
#endif

    /* Configure PSTOP1 bit for BCLK output. */
#if BSP_CFG_BCLK_OUTPUT == 0
    /* Set PSTOP1 bit */
    tmp_clock |= 0x00800000;
#elif BSP_CFG_BCLK_OUTPUT == 1
    /* Clear PSTOP1 bit */
    tmp_clock &= ~0x00800000;
#elif BSP_CFG_BCLK_OUTPUT == 2
    /* Clear PSTOP1 bit */
    tmp_clock &= ~0x00800000;
    /* Set BCLK divider bit */
    SYSTEM.BCKCR.BIT.BCLKDIV = 1;

    /* Dummy read and compare. cf."5. I/O Registers", "(2) Notes on writing to I/O registers" in User's manual.
       This is done to ensure that the register has been written before the next register access. The RX has a 
       pipeline architecture so the next instruction could be executed before the previous write had finished.
    */
    if(1 ==  SYSTEM.BCKCR.BIT.BCLKDIV)
    {
        R_BSP_NOP();
    }
#else
    #error "Error! Invalid setting for BSP_CFG_BCLK_OUTPUT in r_bsp_config.h"
#endif

    /* Figure out setting for PCKA bits. */
#if   BSP_CFG_PCKA_DIV == 1
    /* Do nothing since PCKA bits should be 0. */
#elif BSP_CFG_PCKA_DIV == 2
    tmp_clock |= 0x00001000;
#elif BSP_CFG_PCKA_DIV == 4
    tmp_clock |= 0x00002000;
#elif BSP_CFG_PCKA_DIV == 8
    tmp_clock |= 0x00003000;
#elif BSP_CFG_PCKA_DIV == 16
    tmp_clock |= 0x00004000;
#elif BSP_CFG_PCKA_DIV == 32
    tmp_clock |= 0x00005000;
#elif BSP_CFG_PCKA_DIV == 64
    tmp_clock |= 0x00006000;
#else
    #error "Error! Invalid setting for BSP_CFG_PCKA_DIV in r_bsp_config.h"
#endif

    /* Figure out setting for PCKB bits. */
#if   BSP_CFG_PCKB_DIV == 1
    /* Do nothing since PCKB bits should be 0. */
#elif BSP_CFG_PCKB_DIV == 2
    tmp_clock |= 0x00000100;
#elif BSP_CFG_PCKB_DIV == 4
    tmp_clock |= 0x00000200;
#elif BSP_CFG_PCKB_DIV == 8
    tmp_clock |= 0x00000300;
#elif BSP_CFG_PCKB_DIV == 16
    tmp_clock |= 0x00000400;
#elif BSP_CFG_PCKB_DIV == 32
    tmp_clock |= 0x00000500;
#elif BSP_CFG_PCKB_DIV == 64
    tmp_clock |= 0x00000600;
#else
    #error "Error! Invalid setting for BSP_CFG_PCKB_DIV in r_bsp_config.h"
#endif

    /* Figure out setting for PCKC bits. */
#if   BSP_CFG_PCKC_DIV == 1
    /* Do nothing since PCKA bits should be 0. */
#elif BSP_CFG_PCKC_DIV == 2
    tmp_clock |= 0x00000010;
#elif BSP_CFG_PCKC_DIV == 4
    tmp_clock |= 0x00000020;
#elif BSP_CFG_PCKC_DIV == 8
    tmp_clock |= 0x00000030;
#elif BSP_CFG_PCKC_DIV == 16
    tmp_clock |= 0x00000040;
#elif BSP_CFG_PCKC_DIV == 32
    tmp_clock |= 0x00000050;
#elif BSP_CFG_PCKC_DIV == 64
    tmp_clock |= 0x00000060;
#else
    #error "Error! Invalid setting for BSP_CFG_PCKC_DIV in r_bsp_config.h"
#endif

    /* Figure out setting for PCKD bits. */
#if   BSP_CFG_PCKD_DIV == 1
    /* Do nothing since PCKD bits should be 0. */
#elif BSP_CFG_PCKD_DIV == 2
    tmp_clock |= 0x00000001;
#elif BSP_CFG_PCKD_DIV == 4
    tmp_clock |= 0x00000002;
#elif BSP_CFG_PCKD_DIV == 8
    tmp_clock |= 0x00000003;
#elif BSP_CFG_PCKD_DIV == 16
    tmp_clock |= 0x00000004;
#elif BSP_CFG_PCKD_DIV == 32
    tmp_clock |= 0x00000005;
#elif BSP_CFG_PCKD_DIV == 64
    tmp_clock |= 0x00000006;
#else
    #error "Error! Invalid setting for BSP_CFG_PCKD_DIV in r_bsp_config.h"
#endif

    /* To change the ICLK frequency from less than 70 MHz to 70 MHz or higher such that the ratio of the frequency 
       after the change to that before the change is greater than four, start by setting the frequency to one quarter 
       of the intended frequency, wait for 3 us, and then change it to the intended frequency.
       (Refer User's Manual: 9.10.7 Notes on Changing the ICLK Frequency.) */
    /* Confirm whether to change ICLK frequency from less than 70 MHz to 70 MHz or higher. */
    if(BSP_ICLK_HZ >= BSP_MCU_ICLK_FREQ_THRESHOLD)
    {
        /* The clock source after reset is LOCO. The frequency of LOCO is 240 kHz.
           When the target clock frequency is 70 MHz or higher, it always exceeds 4 times the current clock frequency.
           Therefore, this process does not check whether the target clock frequency exceeds 4 times the current 
           clock frequency. */

        /* Backup of tmp_clock */
        tmp_restore_clock = tmp_clock;

        /* Clear the setting for ICK and BCK bits. */
        tmp_clock &= 0xF0F0FFFF;
#if   BSP_CFG_ICK_DIV == 1
        /* Set ICK and BCK bits to divide by 4. */
        tmp_clock |= 0x02020000;
#elif BSP_CFG_ICK_DIV == 2
        /* Set ICK and BCK bits to divide by 8. */
        tmp_clock |= 0x03030000;
#endif
    }

    /* Set SCKCR register. */
    SYSTEM.SCKCR.LONG = tmp_clock;

    /* Dummy read and compare. cf."5. I/O Registers", "(2) Notes on writing to I/O registers" in User's manual.
       This is done to ensure that the register has been written before the next register access. The RX has a 
       pipeline architecture so the next instruction could be executed before the previous write had finished.
    */
    if(tmp_clock ==  SYSTEM.SCKCR.LONG)
    {
        R_BSP_NOP();
    }

    /* Re-init tmp_clock to use to set SCKCR2. */
    tmp_clock = 0;

    /* Figure out setting for UCK bits. */
#if   BSP_CFG_UCK_DIV == 2
    tmp_clock |= 0x00000011;
#elif BSP_CFG_UCK_DIV == 3
    tmp_clock |= 0x00000021;
#elif BSP_CFG_UCK_DIV == 4
    tmp_clock |= 0x00000031;
#elif BSP_CFG_UCK_DIV == 5
    tmp_clock |= 0x00000041;
#else
    #error "Error! Invalid setting for BSP_CFG_UCK_DIV in r_bsp_config.h"
#endif

    /* Set SCKCR2 register. */
    SYSTEM.SCKCR2.WORD = (uint16_t)tmp_clock;

    /* Dummy read and compare. cf."5. I/O Registers", "(2) Notes on writing to I/O registers" in User's manual.
       This is done to ensure that the register has been written before the next register access. The RX has a 
       pipeline architecture so the next instruction could be executed before the previous write had finished.
    */
    if((uint16_t)tmp_clock ==  SYSTEM.SCKCR2.WORD)
    {
        R_BSP_NOP();
    }

    /* Choose clock source. Default for r_bsp_config.h is PLL. */
    tmp_clock = ((uint16_t)BSP_CFG_CLOCK_SOURCE) << 8;

    /* Casting is valid because it matches the type to the retern value. */
    SYSTEM.SCKCR3.WORD = (uint16_t)tmp_clock;

    /* Dummy read and compare. cf."5. I/O Registers", "(2) Notes on writing to I/O registers" in User's manual.
       This is done to ensure that the register has been written before the next register access. The RX has a 
       pipeline architecture so the next instruction could be executed before the previous write had finished.
    */
    if((uint16_t)tmp_clock ==  SYSTEM.SCKCR3.WORD)
    {
        R_BSP_NOP();
    }

    /* Set ICLK frequency to target ICLK. */
    if(BSP_ICLK_HZ >= BSP_MCU_ICLK_FREQ_THRESHOLD)
    {
        /* Wait for 3 us. */
        R_BSP_SoftwareDelay((uint32_t)3, BSP_DELAY_MICROSECS);

        /* Set SCKCR register. */
        SYSTEM.SCKCR.LONG = tmp_restore_clock;

        /* Dummy read and compare. cf."5. I/O Registers", "(2) Notes on writing to I/O registers" in User's manual.
           This is done to ensure that the register has been written before the next register access. The RX has a 
           pipeline architecture so the next instruction could be executed before the previous write had finished.
         */
        if(tmp_restore_clock == SYSTEM.SCKCR.LONG)
        {
            R_BSP_NOP();
        }
    }

#if BSP_PRV_LOCO_CLK_OPERATING == 0
    /* We can now turn LOCO off since it is not going to be used. */
    SYSTEM.LOCOCR.BYTE = 0x01;

    /* Wait for five the LOCO cycles */
    /* 5 count of LOCO : (1000000/216000)*5 = 23.148148148us
       23 + 2 = 25us ("+2" is overhead cycle) */
    R_BSP_SoftwareDelay((uint32_t)25, BSP_DELAY_MICROSECS);
#endif

    /* Protect on. */
    SYSTEM.PRCR.WORD = 0xA500;
} /* End of function operating_frequency_set() */

/***********************************************************************************************************************
* Function name: clock_source_select
* Description  : Enables and disables clocks as chosen by the user. This function also implements the delays
*                needed for the clocks to stabilize.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
static void clock_source_select (void)
{
    volatile uint8_t i;
    volatile uint8_t dummy;
#if (BSP_PRV_SUB_CLK_OPERATING == 1) || (BSP_CFG_RTC_ENABLE == 1)
    uint8_t tmp;
#endif
    volatile uint16_t tmp_packcr;

    /* Main clock will be not oscillate in software standby or deep software standby modes. */
    SYSTEM.MOFCR.BIT.MOFXIN = 0;

    /* Set the oscillation source of the main clock oscillator. */
    SYSTEM.MOFCR.BIT.MOSEL = BSP_CFG_MAIN_CLOCK_SOURCE;

#if BSP_PRV_HOCO_CLK_OPERATING == 1
    /* HOCO is chosen. Start it operating if it is not already operating. */
    if (1 == SYSTEM.HOCOCR.BIT.HCSTP)
    {
        /* Turn on power to HOCO. */
        SYSTEM.HOCOPCR.BYTE = 0x00;

        /* Stop HOCO. */
        SYSTEM.HOCOCR.BYTE = 0x01;

        /* WAIT_LOOP */
        while(1 == SYSTEM.OSCOVFSR.BIT.HCOVF)
        {
            /* The delay period needed is to make sure that the HOCO has stopped. */
            R_BSP_NOP();
        }

        /* Set HOCO frequency. */
        #if   (BSP_CFG_HOCO_FREQUENCY == 0)
        SYSTEM.HOCOCR2.BYTE = 0x00;         //16MHz
        #elif (BSP_CFG_HOCO_FREQUENCY == 1)
        SYSTEM.HOCOCR2.BYTE = 0x01;         //18MHz
        #elif (BSP_CFG_HOCO_FREQUENCY == 2)
        SYSTEM.HOCOCR2.BYTE = 0x02;         //20MHz
        #else
            #error "Error! Invalid setting for BSP_CFG_HOCO_FREQUENCY in r_bsp_config.h"
        #endif

        /* HOCO is chosen. Start it operating. */
        SYSTEM.HOCOCR.BYTE = 0x00;

        /* Dummy read and compare. cf."5. I/O Registers", "(2) Notes on writing to I/O registers" in User's manual.
           This is done to ensure that the register has been written before the next register access. The RX has a 
           pipeline architecture so the next instruction could be executed before the previous write had finished.
         */
        if(0x00 ==  SYSTEM.HOCOCR.BYTE)
        {
            R_BSP_NOP();
        }
    }

    /* WAIT_LOOP */
    while(0 == SYSTEM.OSCOVFSR.BIT.HCOVF)
    {
        /* The delay period needed is to make sure that the HOCO has stabilized. */
        R_BSP_NOP();
    }
#else /* (BSP_PRV_HOCO_CLK_OPERATING == 0) */
    /* If HOCO is already operating, it doesn't stop. */
    if (1 == SYSTEM.HOCOCR.BIT.HCSTP)
    {
        /* Turn off power to HOCO. */
        SYSTEM.HOCOPCR.BYTE = 0x01;
    }
    else
    {
        /* WAIT_LOOP */
        while(0 == SYSTEM.OSCOVFSR.BIT.HCOVF)
        {
            /* The delay period needed is to make sure that the HOCO has stabilized. */
            R_BSP_NOP();
        }
    }
#endif /* BSP_PRV_HOCO_CLK_OPERATING == 1 */

#if BSP_PRV_MAIN_CLK_OPERATING == 1
    /* Main clock oscillator is chosen. Start it operating. */

    /* If the main oscillator is >10MHz then the main clock oscillator forced oscillation control register (MOFCR) must
       be changed. */
    if (BSP_CFG_XTAL_HZ > 20000000)
    {
        /* 20 - 24MHz. */
        SYSTEM.MOFCR.BIT.MODRV2 = 0;
    }
    else if (BSP_CFG_XTAL_HZ > 16000000)
    {
        /* 16 - 20MHz. */
        SYSTEM.MOFCR.BIT.MODRV2 = 1;
    }
    else if (BSP_CFG_XTAL_HZ > 8000000)
    {
        /* 8 - 16MHz. */
        SYSTEM.MOFCR.BIT.MODRV2 = 2;
    }
    else
    {
        /* 8MHz. */
        SYSTEM.MOFCR.BIT.MODRV2 = 3;
    }

    /* Set the oscillation stabilization wait time of the main clock oscillator. */
#if BSP_CFG_MAIN_CLOCK_SOURCE == 0 /* Resonator */
    SYSTEM.MOSCWTCR.BYTE = BSP_CFG_MOSC_WAIT_TIME;
#elif BSP_CFG_MAIN_CLOCK_SOURCE == 1 /* External oscillator input */
    SYSTEM.MOSCWTCR.BYTE = 0x00;
#else
    #error "Error! Invalid setting for BSP_CFG_MAIN_CLOCK_SOURCE in r_bsp_config.h"
#endif

    /* Set the main clock to operating. */
    SYSTEM.MOSCCR.BYTE = 0x00;

    /* Dummy read and compare. cf."5. I/O Registers", "(2) Notes on writing to I/O registers" in User's manual.
       This is done to ensure that the register has been written before the next register access. The RX has a 
       pipeline architecture so the next instruction could be executed before the previous write had finished.
     */
    if(0x00 ==  SYSTEM.MOSCCR.BYTE)
    {
        R_BSP_NOP();
    }

    /* WAIT_LOOP */
    while(0 == SYSTEM.OSCOVFSR.BIT.MOOVF)
    {
        /* The delay period needed is to make sure that the Main clock has stabilized. */
        R_BSP_NOP();
    }
#else /* (BSP_PRV_MAIN_CLK_OPERATING == 0) */
    /* Main clock is stopped after reset. */
#endif /* BSP_PRV_MAIN_CLK_OPERATING == 1 */

    /* Sub-clock setting. */

    /* Cold start setting */
    if (0 == SYSTEM.RSTSR1.BIT.CWSF)
    {
        /* Stop the sub-clock oscillator */
        /* RCR4 - RTC Control Register 4
        b7:b1    Reserved - The write value should be 0.
        b0       RCKSEL   - Count Source Select - Sub-clock oscillator is selected. */
        RTC.RCR4.BIT.RCKSEL = 0;

        /* WAIT_LOOP */
        for (i = 0; i < 4; i++)
        {
            /* dummy read four times */
            dummy = RTC.RCR4.BYTE;
        }

        /* Confirm that the written */
        if (0 != RTC.RCR4.BIT.RCKSEL)
        {
            R_BSP_NOP();
        }

        /* RCR3 - RTC Control Register 3
        b7:b4    Reserved - The write value should be 0.
        b3:b1    RTCDV    - Sub-clock oscillator Drive Ability Control.
        b0       RTCEN    - Sub-clock oscillator is stopped. */
        RTC.RCR3.BIT.RTCEN = 0;

        /* WAIT_LOOP */
        for (i = 0; i < 4; i++)
        {
            /* dummy read four times */
            dummy = RTC.RCR3.BYTE;
        }

        /* Confirm that the written */
        if (0 != RTC.RCR3.BIT.RTCEN)
        {
            R_BSP_NOP();
        }

        /* SOSCCR - Sub-Clock Oscillator Control Register
        b7:b1    Reserved - The write value should be 0.
        b0       SOSTP    - Sub-clock oscillator Stop - Sub-clock oscillator is stopped. */
        SYSTEM.SOSCCR.BYTE = 0x01;

        /* Dummy read and compare. cf."5. I/O Registers", "(2) Notes on writing to I/O registers" in User's manual.
           This is done to ensure that the register has been written before the next register access. The RX has a 
           pipeline architecture so the next instruction could be executed before the previous write had finished.
         */
        if (0x01 != SYSTEM.SOSCCR.BYTE)
        {
            R_BSP_NOP();
        }

        /* WAIT_LOOP */
        while (0 != SYSTEM.OSCOVFSR.BIT.SOOVF)
        {        
            /* The delay period needed is to make sure that the sub-clock has stopped. */
            R_BSP_NOP();
        }

#if (BSP_PRV_SUB_CLK_OPERATING == 1) || (BSP_CFG_RTC_ENABLE == 1)
        /* Set the drive capacity of the sub-clock oscillator */
        #if   (BSP_CFG_SOSC_DRV_CAP == 0) /* Standard CL */
            tmp = 0x06;
        #elif (BSP_CFG_SOSC_DRV_CAP == 1) /* Low CL */
            tmp = 0x01;
        #else
            #error "Error! Invalid setting for BSP_CFG_SOSC_DRV_CAP in r_bsp_config.h"
        #endif

        /* Set the Sub-Clock Oscillator Drive Capacity Control. */
        RTC.RCR3.BIT.RTCDV = tmp;

        /* WAIT_LOOP */
        for (i = 0; i < 4; i++)
        {
            /* dummy read four times */
            dummy = RTC.RCR3.BYTE;
        }

        /* Confirm that the written */
        if (tmp != RTC.RCR3.BIT.RTCDV)
        {
            R_BSP_NOP();
        }

        /* Set wait time until the sub-clock oscillator stabilizes */
        /* SOSCWTCR - Sub-Clock Oscillator Wait Control Register
        b7:b5    Reserved - The write value should be 0.
        b4:b0    SSTS - Sub-Clock Oscillator Waiting Time - Waiting time is 2.044ms(the maximum value of fLOCO). */
        SYSTEM.SOSCWTCR.BYTE = BSP_CFG_SOSC_WAIT_TIME;

        /* Operate the Sub-clock oscillator */
        SYSTEM.SOSCCR.BYTE = 0x00;

        /* Dummy read and compare. cf."5. I/O Registers", "(2) Notes on writing to I/O registers" in User's manual.
           This is done to ensure that the register has been written before the next register access. The RX has a 
           pipeline architecture so the next instruction could be executed before the previous write had finished.
         */
        if (0x00 != SYSTEM.SOSCCR.BYTE)
        {
            R_BSP_NOP();
        }

        /* WAIT_LOOP */
        while (1 != SYSTEM.OSCOVFSR.BIT.SOOVF)
        {
            /* The delay period needed is to make sure that the sub-clock  has stabilized. */
            R_BSP_NOP();
        }
#endif /* (BSP_PRV_SUB_CLK_OPERATING == 1) || (BSP_CFG_RTC_ENABLE == 1) */

#if BSP_CFG_RTC_ENABLE == 1
        /* ---- Set wait time until the sub-clock oscillator stabilizes ---- */
        SYSTEM.SOSCWTCR.BYTE = 0x00;

        /* ---- Operate the sub-clock oscillator ---- */
        RTC.RCR3.BIT.RTCEN = 1;

        /* WAIT_LOOP */
        for (i = 0; i < 4; i++)
        {
             /* dummy read four times */
             dummy = RTC.RCR3.BIT.RTCEN;
        }

        /* Confirm that the written value can be read correctly. */
        if (1 != RTC.RCR3.BIT.RTCEN)
        {
            R_BSP_NOP();
        }
#endif

#if (BSP_PRV_SUB_CLK_OPERATING == 1) || (BSP_CFG_RTC_ENABLE == 1)
        /* Wait for six the sub-clock cycles */
        /* 6 count of sub-clock : (1000000/32768)*6=183.10546875us
           In the case of LOCO frequency is 264kHz : 183.10546875/(1000000/264000)=48.33984375cycle
           (48.33984375+2)*(1000000/240000)=209.7493489583333us ("+2" is overhead cycle) */
        R_BSP_SoftwareDelay((uint32_t)210, BSP_DELAY_MICROSECS);
#endif

#if (BSP_PRV_SUB_CLK_OPERATING == 1) && (BSP_CFG_RTC_ENABLE == 0)
        /* Stop prescaler and counter */
        /* RCR2 - RTC Control Register 2
        b7  CNTMD - Count Mode Select - The calendar count mode.
        b6  HR24  - Hours Mode - The RTC operates in 24-hour mode.
        b5  AADJP - Automatic Adjustment Period Select - The RADJ.ADJ[5:0] setting value is adjusted from 
                                                           the count value of the prescaler every 10 seconds.
        b4  AADJE - Automatic Adjustment Enable - Automatic adjustment is enabled.
        b3  RTCOE - RTCOUT Output Enable - RTCOUT output enabled.
        b2  ADJ30 - 30-Second Adjustment - 30-second adjustment is executed.
        b1  RESET - RTC Software Reset - The prescaler and the target registers for RTC software reset are initialized.
        b0  START - start - Prescaler is stopped. */
        RTC.RCR2.BYTE &= 0x7E;

        /* WAIT_LOOP */
        while (0 != RTC.RCR2.BIT.START)
        {
            /* Confirm that the written value can be read correctly. */
             R_BSP_NOP();
        }

        /* RTC Software Reset */
        RTC.RCR2.BIT.RESET = 1;

        /* WAIT_LOOP */
        while (0 != RTC.RCR2.BIT.RESET)
        {
            /* Confirm that the written value can be read correctly. */
            R_BSP_NOP();
        }

        /* An alarm interrupt request is disabled */
        /* RCR1 - RTC Control Register 1
        b7:b4  PES   - Periodic Interrupt Select - These bits specify the period for the periodic interrupt.
        b3     RTCOS - RTCOUT Output Select - RTCOUT outputs 1 Hz.
        b2     PIE   - Periodic Interrupt Enable - A periodic interrupt request is disabled.
        b1     CIE   - Carry Interrupt Enable - A carry interrupt request is disabled.
        b0     AIE   - Alarm Interrupt Enable - An alarm interrupt request is disabled. */
        RTC.RCR1.BYTE &= 0xF8;

        /* Wait for one the sub-clock cycles */
        /* 1 count of sub-clock : (1000000/32768)=30.517578125us
           In the case of LOCO frequency is 264kHz : 30.517578125/(1000000/264000)=8.056640625cycle
           (8.056640625+2)*(1000000/240000)=41.902669270833us ("+2" is overhead cycle) */
        R_BSP_SoftwareDelay((uint32_t)42, BSP_DELAY_MICROSECS);

        /* Confirm that the written value can be read correctly. */
        if (0x00 != (RTC.RCR1.BYTE & 0x07))
        {
            R_BSP_NOP();
        }
#endif /* (BSP_PRV_SUB_CLK_OPERATING == 1) && (BSP_CFG_RTC_ENABLE == 0) */
    }
    /* Warm start setting */
    else
    {
#if (BSP_PRV_SUB_CLK_OPERATING == 1) || ((BSP_PRV_SUB_CLK_OPERATING == 0) && (BSP_CFG_RTC_ENABLE == 0))
        /* SOSCCR - Sub-Clock Oscillator Control Register
        b7:b1    Reserved - The write value should be 0.
        b0       SOSTP    - Sub-clock oscillator Stop - Sub-clock oscillator is stopped. */
        SYSTEM.SOSCCR.BYTE = 0x01;

        /* Dummy read and compare. cf."5. I/O Registers", "(2) Notes on writing to I/O registers" in User's manual.
           This is done to ensure that the register has been written before the next register access. The RX has a 
           pipeline architecture so the next instruction could be executed before the previous write had finished.
         */
        if (0x01 != SYSTEM.SOSCCR.BYTE)
        {
            R_BSP_NOP();
        }

        /* WAIT_LOOP */
        while (0 != SYSTEM.OSCOVFSR.BIT.SOOVF)
        {
            /* Confirm that the Sub clock stopped. */
            R_BSP_NOP();
        }
#endif

#if BSP_PRV_SUB_CLK_OPERATING == 1
        /* Set wait time until the sub-clock oscillator stabilizes */
        /* SOSCWTCR - Sub-Clock Oscillator Wait Control Register
        b7:b5    Reserved - The write value should be 0.
        b4:b0    SSTS - Sub-Clock Oscillator Waiting Time - Waiting time is 2.044ms(the maximum value of fLOCO). */
        SYSTEM.SOSCWTCR.BYTE = BSP_CFG_SOSC_WAIT_TIME;

        /* Operate the Sub-clock oscillator */
        SYSTEM.SOSCCR.BYTE = 0x00;

        /* Dummy read and compare. cf."5. I/O Registers", "(2) Notes on writing to I/O registers" in User's manual.
           This is done to ensure that the register has been written before the next register access. The RX has a 
           pipeline architecture so the next instruction could be executed before the previous write had finished.
         */
        if (0x00 != SYSTEM.SOSCCR.BYTE)
        {
            R_BSP_NOP();
        }
#endif

#if (BSP_PRV_SUB_CLK_OPERATING == 1) || (BSP_CFG_RTC_ENABLE == 1)
        /* WAIT_LOOP */
        while (1 != SYSTEM.OSCOVFSR.BIT.SOOVF)
        {
            /* The delay period needed is to make sure that the sub-clock  has stabilized. */
            R_BSP_NOP();
        }
#endif

#if BSP_CFG_RTC_ENABLE == 1
        /* ---- Set wait time until the sub-clock oscillator stabilizes ---- */
        SYSTEM.SOSCWTCR.BYTE = 0x00;
#endif
    }

#if (BSP_CFG_PHY_CLOCK_SOURCE == 1) || (BSP_CFG_USB_CLOCK_SOURCE == 3)
    /* initialize */
    tmp_packcr = SYSTEM.PACKCR.WORD;

#if BSP_CFG_PHY_CLOCK_SOURCE == 1
    /* Set value of OUTCKSEL bit. */
    tmp_packcr |= 0x0010;
#endif

#if BSP_CFG_USB_CLOCK_SOURCE == 3
    /* Set value of UPLLSEL bit. */
    tmp_packcr |= 0x1000;
#endif

    /* Set value to PACLCR register. */
    SYSTEM.PACKCR.WORD = tmp_packcr;
#endif

#if (BSP_PRV_PLL_CLK_OPERATING == 1) || (BSP_PRV_PPLL_CLK_OPERATING == 1)
    /* Set PLL clock source. */
    #if BSP_CFG_PLL_SRC == 0
    /* Clear PLL clock source if PLL clock source is Main clock. */
    SYSTEM.PLLCR.BIT.PLLSRCSEL = 0;
    #else
    /* Set PLL clock source if PLL clock source is HOCO clock. */
    SYSTEM.PLLCR.BIT.PLLSRCSEL = 1;
    #endif
#endif

#if BSP_PRV_PLL_CLK_OPERATING == 1

    /* Set PLL Input Divisor. */
    SYSTEM.PLLCR.BIT.PLIDIV = BSP_CFG_PLL_DIV - 1;

    /* Set PLL Multiplier. */
    SYSTEM.PLLCR.BIT.STC = ((uint8_t)((float)BSP_CFG_PLL_MUL * 2.0)) - 1;

    /* Set the PLL to operating. */
    SYSTEM.PLLCR2.BYTE = 0x00;

    /* WAIT_LOOP */
    while(0 == SYSTEM.OSCOVFSR.BIT.PLOVF)
    {
        /* The delay period needed is to make sure that the PLL has stabilized. */
        R_BSP_NOP();
    }
#else
    /* PLL is stopped after reset. */
#endif

#if BSP_PRV_PPLL_CLK_OPERATING == 1
    /* Set PPLL Input Divisor. */
    SYSTEM.PPLLCR.BIT.PPLIDIV = BSP_CFG_PPLL_DIV - 1;

    /* Set PPLL Multiplier. */
    SYSTEM.PPLLCR.BIT.PPLSTC = ((uint8_t)((float)BSP_CFG_PPLL_MUL * 2.0)) - 1;

    /* Set the PPLL to operating. */
    SYSTEM.PPLLCR2.BYTE = 0x00;

    /* WAIT_LOOP */
    while(0 == SYSTEM.OSCOVFSR.BIT.PPLOVF)
    {
        /* The delay period needed is to make sure that the PPLL has stabilized. */
        R_BSP_NOP();
    }

    /* Set PPLCK Input Divisor. */
    SYSTEM.PPLLCR3.BIT.PPLCK = BSP_CFG_PPLCK_DIV - 1;
#endif

    /* LOCO is saved for last since it is what is running by default out of reset. This means you do not want to turn
       it off until another clock has been enabled and is ready to use. */
#if BSP_PRV_LOCO_CLK_OPERATING == 1
    /* LOCO is chosen. This is the default out of reset. */
#else
    /* LOCO is not chosen but it cannot be turned off yet since it is still being used. */
#endif

    /* RX72N has a MEMWAIT register which controls the cycle waiting for access to code flash memory.
       It is set as zero coming out of reset. We only want to set this if we are > 120 MHz.
     */
    if (BSP_ICLK_HZ > BSP_MCU_MEMWAIT_FREQ_THRESHOLD)
    {
        /* Set MEMWAIT */
        SYSTEM.MEMWAIT.BYTE = 0x01;

        /* Dummy read and compare. cf."5. I/O Registers", "(2) Notes on writing to I/O registers" in User's manual.
           This is done to ensure that the register has been written before the next register access. The RX has a 
           pipeline architecture so the next instruction could be executed before the previous write had finished.
        */
        if(0x01 == SYSTEM.MEMWAIT.BYTE)
        {
            R_BSP_NOP();
        }
    }
} /* End of function clock_source_select() */

#if BSP_CFG_CLKOUT_OUTPUT != 0
/***********************************************************************************************************************
* Function name: bsp_clkout_initial_configure
* Description  : Configures the CLKOUT initial settings
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
static void bsp_clkout_initial_configure(void)
{
    /* Protect off. */
    SYSTEM.PRCR.WORD = 0xA50B;

    /* Set the CLKOUT Output Divisor Select. */
    SYSTEM.CKOCR.BIT.CKODIV = BSP_CFG_CLKOUT_DIV;

    /* Set the CLKOUT Output Source Select. */
    SYSTEM.CKOCR.BIT.CKOSEL = BSP_CFG_CLKOUT_SOURCE;
#if BSP_CFG_CLKOUT_OUTPUT == 1

    /* Set the CLKOUT Output Stop Control. */
    SYSTEM.CKOCR.BIT.CKOSTP = 0;
#elif BSP_CFG_CLKOUT_OUTPUT == 0
    /* do nothing */
#else
    #error "Error! Invalid setting for BSP_CFG_CLKOUT_OUTPUT in r_bsp_config.h"
#endif
    /* Protect on. */
    SYSTEM.PRCR.WORD = 0xA500;
} /* End of function bsp_clkout_initial_configure() */
#endif /* BSP_CFG_CLKOUT_OUTPUT != 0 */

#endif /* BSP_CFG_STARTUP_DISABLE == 0 */

