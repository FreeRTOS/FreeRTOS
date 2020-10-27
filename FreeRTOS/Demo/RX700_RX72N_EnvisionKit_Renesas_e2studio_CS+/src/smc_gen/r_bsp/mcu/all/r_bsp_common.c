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
* Copyright (C) 2013 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : r_bsp_common.c
* Description  : Implements functions that apply to all r_bsp boards and MCUs.
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 06.05.2013 1.00     First Release
*         : 26.03.2014 1.10     Added R_BSP_SoftwareDelay() function
*         : 03.09.2014 1.20     Corrected R_BSP_SoftwareDelay() timing when using an RX64M
*         : 30.09.2015 1.30     Added RX23T
*         : 01.02.2016 1.40     Added RX24T
*                               Changed the value of the following macro definition.
*                               - OVERHEAD_CYCLES
*                               - OVERHEAD_CYCLES_64
*         : 29.02.2016 1.50     Added RX230
*         : 01.10.2016 1.60     Added RX65N
*         : 22.08.2016 1.70     Added RX24U
*         : 15.05.2017 1.80     Changed method of selecting the number of CPU cycles required to execute 
*                               the delayWait() loop.
*         : 27.07.2018 1.90     Changed the value of the following macro definition, because added RX66T.
*                               - CPU_CYCLES_PER_LOOP
*         : 28.02.2019 2.00     Deleted the following definition. 
*                               (The following definition moved to the common file (mcu_info.h).)
*                               - CPU_CYCLES_PER_LOOP
*                               Added support for GNUC and ICCRX.
*                               Fixed coding style.
*                               Renamed following macro definitions.
*                               - BSP_PRV_OVERHEAD_CYCLES
*                               - BSP_PRV_OVERHEAD_CYCLES_64
*                               - BSP_PRV_CKSEL_LOCO
*                               Renamed following function.
*                               - delay_wait
*         : 26.07.2019 2.01     Modified comment of API function to Doxygen style.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Get information about current board and MCU. */
#include "platform.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define BSP_PRV_OVERHEAD_CYCLES        (2)    /* R_BSP_SoftwareDelay() overhead per call */
#define BSP_PRV_OVERHEAD_CYCLES_64     (2)    /* R_BSP_SoftwareDelay() overhead per call using 64-bit ints */

#define BSP_PRV_CKSEL_LOCO             (0x0)  /* SCKCR3 register setting for LOCO */

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global variables (to be accessed by other files)
***********************************************************************************************************************/

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/

/**********************************************************************************************************************
 * Function Name: R_BSP_GetVersion
 ******************************************************************************************************************//**
 * @brief Returns the current version of the r_bsp.
 * @return Version of the r_bsp.
 * @details This function will return the version of the currently installed r_bsp. The version number is encoded 
 * where the top 2 bytes are the major version number and the bottom 2 bytes are the minor version number. For 
 * example, Version 4.25 would be returned as 0x00040019.
 */
uint32_t R_BSP_GetVersion (void)
{
    /* These version macros are defined in platform.h. */
    return ((((uint32_t)R_BSP_VERSION_MAJOR) << 16) | (uint32_t)R_BSP_VERSION_MINOR);
} /* End of function R_BSP_GetVersion() */


/***********************************************************************************************************************
* Function Name: delay_wait
* Description  : This asm loop executes a known number (5) of CPU cycles. If a value of '4' is passed
*                in as an argument, then this function would consume 20 CPU cycles before returning.
* Arguments    : loop_cnt - A single 32-bit value is provided as the number of loops to execute.
* Return Value : None
***********************************************************************************************************************/
R_BSP_PRAGMA_STATIC_INLINE_ASM(delay_wait)
void delay_wait (unsigned long loop_cnt)
{
    R_BSP_ASM_INTERNAL_USED(loop_cnt)
    R_BSP_ASM_BEGIN
    R_BSP_ASM(    BRA.B   R_BSP_ASM_LAB_NEXT(0)     )
    R_BSP_ASM(    NOP                               )
    R_BSP_ASM_LAB(0:                                )
    R_BSP_ASM(    NOP                               )
    R_BSP_ASM(    SUB     #01H, R1                  )
    R_BSP_ASM(    BNE.B   R_BSP_ASM_LAB_PREV(0)     )
    R_BSP_ASM_END
} /* End of function delay_wait() */


/**********************************************************************************************************************
 * Function Name: R_BSP_GetIClkFreqHz
 ******************************************************************************************************************//**
 * @brief Returns the system clock frequency.
 * @return System clock frequency specified by the r_bsp.
 * @details This function returns the system clock frequency. For example, when the system clock is set to 120 MHz in 
 * r_bsp_config_h and the r_bsp has completed to specify the clock setting, then even if the user changed the system 
 * clock frequency to 60 MHz, the return value is '60000000'.
 */
uint32_t R_BSP_GetIClkFreqHz(void)
{
    return get_iclk_freq_hz();  // Get the MCU specific ICLK frequency
} /* End of function R_BSP_GetIClkFreqHz() */


/**********************************************************************************************************************
 * Function Name: R_BSP_SoftwareDelay
 ******************************************************************************************************************//**
 * @brief Delay the specified duration in units and return.
 * @param[in] delay The number of 'units' to delay.
 * @param[in] units The 'base' for the units specified.
 * @retval true True if delay executed.
 * @retval false False if delay/units combination resulted in overflow/underflow.
 * @details This is function that may be called for all MCU targets to implement a specific wait time.
 * The actual delay time is plus the overhead at a specified duration. The overhead changes under the influence of 
 * the compiler, operating frequency and ROM cache. When the operating frequency is low, or the specified duration in 
 * units of microsecond level, please note that the error becomes large.
 */
bool R_BSP_SoftwareDelay(uint32_t delay, bsp_delay_units_t units)
{
    volatile uint32_t iclk_rate;
    volatile uint32_t delay_cycles;
    volatile uint32_t loop_cnt;
    volatile uint64_t delay_cycles_64;
    volatile uint64_t loop_cnt_64;

#ifdef BSP_CFG_PARAM_CHECKING_ENABLE
    if ((BSP_DELAY_MICROSECS != units) && (BSP_DELAY_MILLISECS != units) && (BSP_DELAY_SECS != units))
    {
        return(false);
    }
#endif

    iclk_rate = R_BSP_GetIClkFreqHz();  /* Get the current ICLK frequency */

    /*
     * In order to handle all possible combinations of delay/ICLK it is necessary to use 64-bit
     * integers (not all MCUs have floating point support). However, there is no native hw support
     * for 64 bit integers so it requires many more clock cycles. This is not an issue if the
     * requested delay is long enough and the ICLK is fast, but for delays in the low microseconds
     * and/or a slow ICLK we use 32 bit integers to reduce the overhead cycles of this function
     * by approximately a third and stand the best chance of achieving the requested delay.
     */
    if ( (BSP_DELAY_MICROSECS == units) &&
         (delay <= (0xFFFFFFFFUL / iclk_rate)) )  /* Ensure (iclk_rate * delay) will not exceed 32 bits */
    {
        delay_cycles = ((iclk_rate * delay) / units);

        if (delay_cycles > BSP_PRV_OVERHEAD_CYCLES)
        {
            delay_cycles -= BSP_PRV_OVERHEAD_CYCLES;
        }
        else
        {
            delay_cycles = 0;
        }

        loop_cnt = delay_cycles / CPU_CYCLES_PER_LOOP;

        if (0 == loop_cnt)
        {
            /* The requested delay is too large/small for the current ICLK. Return false which
             * also results in the minimum possible delay. */
            return(false);
        }
    }
    else
    {
        /* Casting is valid because it matches the type to the right side or argument. */
        delay_cycles_64 = (((uint64_t)iclk_rate * (uint64_t)delay) / units);

        if (delay_cycles_64 > BSP_PRV_OVERHEAD_CYCLES_64)
        {
            delay_cycles_64 -= BSP_PRV_OVERHEAD_CYCLES_64;
        }
        else
        {
            delay_cycles = 0;
        }

        loop_cnt_64 = delay_cycles_64 / CPU_CYCLES_PER_LOOP;

        if ((loop_cnt_64 > 0xFFFFFFFFUL) || (0 == loop_cnt_64))
        {
            /* The requested delay is too large/small for the current ICLK. Return false which
             * also results in the minimum possible delay. */
            return(false);
        }

        /* Casting is valid because it matches the type to the right side or argument. */
        loop_cnt = (uint32_t)loop_cnt_64;
    }

    delay_wait(loop_cnt);

    return(true);
} /* End of function R_BSP_SoftwareDelay() */

