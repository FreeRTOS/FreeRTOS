
/******************************************************************************
*
* alt_watchdog.c - API for the Altera SoC FPGA watchdog timers.
*
******************************************************************************/

/******************************************************************************
*
* Copyright 2013 Altera Corporation. All Rights Reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*
* 1. Redistributions of source code must retain the above copyright notice,
* this list of conditions and the following disclaimer.
*
* 2. Redistributions in binary form must reproduce the above copyright notice,
* this list of conditions and the following disclaimer in the documentation
* and/or other materials provided with the distribution.
*
* 3. The name of the author may not be used to endorse or promote products
* derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
* OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
* INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
* CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
* IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
* OF SUCH DAMAGE.
*
******************************************************************************/

/******************************************************************************
*
* The Altera SoC FPGA has six watchdog timers, two are local to the MPU
* themselves, and the other four are accessable to either MPU.
*
******************************************************************************/

#include <stdint.h>
#include <stdbool.h>
#include "socal/hps.h"
#include "socal/socal.h"
#include "socal/alt_rstmgr.h"
#include "socal/alt_l4wd.h"
#include "socal/alt_tmr.h"
#include "hwlib.h"
#include "alt_mpu_registers.h"
#include "alt_watchdog.h"
#include "alt_clock_manager.h"


    /* Useful constants and utilities */

bool cpu_wdog_in_gpt_mode(void)
{
    return !(alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET) & WDOG_WDT_MODE);
}

static inline bool cpu_wdog_in_wdt_mode(void)
{
    return (alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET) & WDOG_WDT_MODE);
}


/* This value must be written to the Counter Restart Register of the
 * peripheral watchdog timers to restart them. */
#define WDOG_RESET_KEY          0x00000076

#define ALT_WDOG_RST_WIDTH      8                       /* 8 or more MPU clock cycles */


inline static void alt_wdog_wait(void* reg, uint32_t cnt)
{
    for (; cnt ; cnt--)
    {
        (void) alt_read_word(reg);
    }
}


/****************************************************************************************/
/* Initialize the watchdog timer module before use                                      */
/****************************************************************************************/

ALT_STATUS_CODE alt_wdog_init(void)
{
    // put watchdog timer modules into system manager reset if not already there
    alt_wdog_uninit();
    // release L4 watchdog timer modules from system reset (w/ four instruction-cycle delay)
    alt_clrbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_L4WD0_SET_MSK |
            ALT_RSTMGR_PERMODRST_L4WD1_SET_MSK);

    // release *both* ARM watchdog timer modules from system reset (if in reset)
    // does not put either one into watchdog timer mode
    alt_clrbits_word(ALT_RSTMGR_MPUMODRST_ADDR, ALT_RSTMGR_MPUMODRST_WDS_SET_MSK);
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* Return the local ARM watchdog timer back to general-purpose timer mode               */
/****************************************************************************************/

void alt_ARM_wdog_gpt_mode_set(void)
{
    while (alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET) & WDOG_WDT_MODE)
    {
        alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_DISABLE_REG_OFFSET, WDOG_DISABLE_VAL0);
        alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_DISABLE_REG_OFFSET, WDOG_DISABLE_VAL1);
    }
}


/****************************************************************************************/
/* Set the local ARM watchdog timer to watchdog timer mode                              */
/****************************************************************************************/

void alt_ARM_wdog_wdog_mode_set(void)
{
    alt_setbits_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET, WDOG_WDT_MODE);
}


/****************************************************************************************/
/* Uninitialize the watchdog timer module & return to reset state                        */
/****************************************************************************************/

ALT_STATUS_CODE alt_wdog_uninit(void)
{
    // put L4 watchdog modules into system manager reset
    alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR,
            ALT_RSTMGR_PERMODRST_L4WD0_SET_MSK | ALT_RSTMGR_PERMODRST_L4WD1_SET_MSK);

        // using the system manager bit to reset the ARM watchdog timer
        // resets *both* ARM watchdog timers, which is often not advisable,
        // so we reset the local ARM watchdog timer manually:

        // first, stop the ARM watchdog timer & disable interrupt
    alt_clrbits_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET, WDOG_TMR_ENABLE | WDOG_INT_EN);
        // reset load and counter registers
    alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_LOAD_REG_OFFSET, 0);
        // clear any pending reset and interrupt status
    alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_RSTSTAT_REG_OFFSET, WDOG_RST_STAT_BIT);
    alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_INTSTAT_REG_OFFSET, WDOG_INT_STAT_BIT);
        // return ARM watchdog timer to (initial) general-purpose timer mode
    alt_ARM_wdog_gpt_mode_set();
        // now write zeros to the control register significant bitfields
        // and then verify that all significant bitfields return zero
    alt_clrbits_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET,
            (WDOG_PS_MASK | WDOG_WDT_MODE | WDOG_INT_EN | WDOG_AUTO_RELOAD | WDOG_TMR_ENABLE));
    if (alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET)
            & (WDOG_PS_MASK | WDOG_WDT_MODE | WDOG_INT_EN | WDOG_AUTO_RELOAD | WDOG_TMR_ENABLE))
    {
        return ALT_E_ERROR;
    }
    return ALT_E_SUCCESS;

}


/****************************************************************************************/
/* Stops the specified watchdog timer.                                                  */
/****************************************************************************************/

ALT_STATUS_CODE alt_wdog_stop(ALT_WDOG_TIMER_t tmr_id)
{
    ALT_STATUS_CODE         ret = ALT_E_BAD_ARG;    // return value
    uint32_t                config;                 // the current configuration
    uint32_t                loadreg;                // current restart value


    if (tmr_id == ALT_WDOG_CPU)
    {
        alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET,
                (alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET) & ~WDOG_TMR_ENABLE));
        ret = ALT_E_SUCCESS;
    }

    // these timers can only be reset by using a system manager reset
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        config = alt_read_word(ALT_L4WD0_WDT_CR_ADDR);      // read current timer mode
        loadreg = alt_read_word(ALT_L4WD0_WDT_TORR_ADDR);   // read timer restart values
        alt_write_word(ALT_RSTMGR_PERMODRST_ADDR,
                alt_read_word(ALT_RSTMGR_PERMODRST_ADDR) | ALT_RSTMGR_PERMODRST_L4WD0_SET_MSK);
                        // assert reset & wait
        alt_wdog_wait(ALT_RSTMGR_PERMODRST_ADDR, ALT_WDOG_RST_WIDTH);
        alt_write_word(ALT_RSTMGR_PERMODRST_ADDR,
                alt_read_word(ALT_RSTMGR_PERMODRST_ADDR) & ALT_RSTMGR_PERMODRST_L4WD0_CLR_MSK);
                        // release peripheral reset signal by clearing bit
        alt_write_word(ALT_L4WD0_WDT_TORR_ADDR, loadreg);   // restore timer restart value
        alt_write_word(ALT_L4WD0_WDT_CR_ADDR, config & ALT_TMR_TMR1CTLREG_TMR1_EN_CLR_MSK);
                          // restore previous timer mode except timer isn't started
        ret = ALT_E_SUCCESS;
    }
    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        config = alt_read_word(ALT_L4WD1_WDT_CR_ADDR);      // read current timer mode
        loadreg = alt_read_word(ALT_L4WD1_WDT_TORR_ADDR);   // read timer restart values
        alt_write_word(ALT_RSTMGR_PERMODRST_ADDR,
                alt_read_word(ALT_RSTMGR_PERMODRST_ADDR) | ALT_RSTMGR_PERMODRST_L4WD1_SET_MSK);
                        // assert reset & wait
        alt_write_word(ALT_RSTMGR_PERMODRST_ADDR,
                alt_read_word(ALT_RSTMGR_PERMODRST_ADDR) & ALT_RSTMGR_PERMODRST_L4WD1_CLR_MSK);
                         // release peripheral reset signal by clearing bit
        alt_write_word(ALT_L4WD1_WDT_TORR_ADDR, loadreg);   // restore timer restart value
        alt_write_word(ALT_L4WD1_WDT_CR_ADDR, config & ALT_TMR_TMR1CTLREG_TMR1_EN_CLR_MSK);
                          // restore previous timer mode except timer isn't started
        ret = ALT_E_SUCCESS;
    }
    return  ret;
}

/****************************************************************************************/
/* Start the specified watchdog timer.                                                  */
/****************************************************************************************/

ALT_STATUS_CODE alt_wdog_start(ALT_WDOG_TIMER_t tmr_id)
{
    ALT_STATUS_CODE     ret = ALT_E_BAD_ARG;    // return value
    uint32_t            regdata;                // data


    if (tmr_id == ALT_WDOG_CPU)
    {
        regdata = alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET);
        alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET, regdata | WDOG_TMR_ENABLE);
        ret = ALT_E_SUCCESS;
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        regdata = alt_read_word(ALT_L4WD0_WDT_CR_ADDR);
        alt_write_word(ALT_L4WD0_WDT_CR_ADDR, regdata | ALT_L4WD_CR_WDT_EN_SET_MSK);
        ret = ALT_E_SUCCESS;
    }
    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        regdata = alt_read_word(ALT_L4WD1_WDT_CR_ADDR);
        alt_write_word(ALT_L4WD1_WDT_CR_ADDR, regdata | ALT_L4WD_CR_WDT_EN_SET_MSK);
        ret = ALT_E_SUCCESS;
    }
    return  ret;
}


/****************************************************************************************/
/* Returns whether the specified watchdog timer is currently running or not.            */
/****************************************************************************************/

bool alt_wdog_tmr_is_enabled(ALT_WDOG_TIMER_t tmr_id)
{
    bool      ret = false;          // return value


    if (tmr_id == ALT_WDOG_CPU)
    {
        ret = alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET) & WDOG_TMR_ENABLE;
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        ret = alt_read_word(ALT_L4WD0_WDT_CR_ADDR) & ALT_L4WD_CR_WDT_EN_SET_MSK;
    }

    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        ret = alt_read_word(ALT_L4WD1_WDT_CR_ADDR) & ALT_L4WD_CR_WDT_EN_SET_MSK;
    }
    return  ret;
}


/****************************************************************************************/
/*  Reloads the counter countdown value and restarts the watchdog timer. User can reset */
/*  the timer at any time before timeout. Also known as kicking, petting, feeding,      */
/* waking, or walking the watchdog. Inherently clears the interrupt as well.            */
/****************************************************************************************/

ALT_STATUS_CODE alt_wdog_reset(ALT_WDOG_TIMER_t tmr_id)
{
    uint32_t                regdata;        // data read


    if (tmr_id == ALT_WDOG_CPU)
    {
        regdata = alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_LOAD_REG_OFFSET);
        alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_LOAD_REG_OFFSET, regdata);
                // verify operation when we have hardware,
                // the ARM documentation is somewhat vague here

        if (cpu_wdog_in_wdt_mode())
        {
            alt_write_word((CPU_WDTGPT_TMR_BASE + WDOG_RSTSTAT_REG_OFFSET), WDOG_RST_STAT_BIT);
                      // depending on current mode, clear the reset bit or...
        }
        else
        {
            alt_write_word((CPU_WDTGPT_TMR_BASE + WDOG_INTSTAT_REG_OFFSET), WDOG_INT_STAT_BIT);
                      // ...clear the interrupt status bit by writing one to it
        }
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        alt_write_word(ALT_L4WD0_WDT_CRR_ADDR, WDOG_RESET_KEY);
            //restarts the counter, also clears the watchdog timer interrupt
    }
    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        alt_write_word(ALT_L4WD1_WDT_CRR_ADDR, WDOG_RESET_KEY);
            //restarts the counter, also clears the watchdog timer interrupt
    }
    else {return  ALT_E_BAD_ARG; }
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* Sets the countdown value of the specified timer.                                     */
/****************************************************************************************/

ALT_STATUS_CODE alt_wdog_counter_set(ALT_WDOG_TIMER_t tmr_id, uint32_t val)
{
    ALT_STATUS_CODE         ret = ALT_E_BAD_ARG;    // return value
    uint32_t                regdata;                // returned data


    if (tmr_id == ALT_WDOG_CPU)
    {
        alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_LOAD_REG_OFFSET, val);
        ret = ALT_E_SUCCESS;
        // the ARM documentation is somewhat vague here, but it looks like it should be
        // possible to rewrite this value while counter is running, and that it works in
        // watchdog mode as well as timer mode. Verify operation when we have hardware.
    }
    else if (val <= ALT_WDOG_TIMEOUT2G)
    {
        if (tmr_id == ALT_WDOG0)
        {
            // set regular timeout value
            regdata = alt_read_word(ALT_L4WD0_WDT_TORR_ADDR);
            alt_write_word(ALT_L4WD0_WDT_TORR_ADDR, (regdata & ALT_L4WD_TORR_TOP_CLR_MSK) | val);
            ret = ALT_E_SUCCESS;
        }
        else if (tmr_id == ALT_WDOG1)
        {
            // set regular timeout value
            regdata = alt_read_word(ALT_L4WD1_WDT_TORR_ADDR);
            alt_write_word(ALT_L4WD1_WDT_TORR_ADDR, (regdata & ALT_L4WD_TORR_TOP_CLR_MSK) | val);
            ret = ALT_E_SUCCESS;
        }
        else if (tmr_id == ALT_WDOG0_INIT)
        {
            // set initial timeout value
            regdata = alt_read_word(ALT_L4WD0_WDT_TORR_ADDR);
            regdata = (regdata & ALT_L4WD_TORR_TOP_INIT_CLR_MSK) |
                    (val << ALT_L4WD_TORR_TOP_INIT_LSB);
            alt_write_word(ALT_L4WD0_WDT_TORR_ADDR, regdata);
            ret = ALT_E_SUCCESS;
        }
        else if (tmr_id == ALT_WDOG1_INIT)
        {
            // set initial timeout value
            regdata = alt_read_word(ALT_L4WD1_WDT_TORR_ADDR);
            regdata = (regdata & ALT_L4WD_TORR_TOP_INIT_CLR_MSK) |
                    (val << ALT_L4WD_TORR_TOP_INIT_LSB);
            alt_write_word(ALT_L4WD1_WDT_TORR_ADDR, regdata);
            ret = ALT_E_SUCCESS;
        }
    }
    return  ret;
}


/****************************************************************************************/
/* Returns the current counter value of the specified timer.                            */
/****************************************************************************************/

uint32_t alt_wdog_counter_get_current(ALT_WDOG_TIMER_t tmr_id)
{
    uint32_t     ret = 0;           // return value

    if (tmr_id == ALT_WDOG_CPU)
    {
        ret = alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CNTR_REG_OFFSET);
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        ret = alt_read_word(ALT_L4WD0_WDT_CCVR_ADDR);
    }
    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        ret = alt_read_word(ALT_L4WD1_WDT_CCVR_ADDR);
    }
    return ret;
}


/****************************************************************************************/
/* Returns the current counter value of the specified timer, as measured in             */
/* milliseconds. For ALT_CPU_WATCHDOG, this includes the effects of the prescaler       */
/* setting.                                                                             */
/****************************************************************************************/

uint32_t alt_wdog_counter_get_curtime_millisecs(ALT_WDOG_TIMER_t tmr_id)
{
    uint32_t        time = 0;           // return value
    uint64_t        bigtime;            // temp for math
    alt_freq_t      freq;               // clock frequency
    ALT_CLK_t       clk;                // clock ID

    if (tmr_id == ALT_WDOG_CPU)
    {
        clk = ALT_CLK_MPU_PERIPH;
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG1) ||
            (tmr_id == ALT_WDOG0_INIT) || (tmr_id == ALT_WDOG1_INIT))
    {
        clk = ALT_CLK_OSC1;
    }
    else { return time; }

    if ((alt_clk_freq_get(clk, &freq) == ALT_E_SUCCESS) && (freq != 0))
    {                               // get clock frequency & test
        time = alt_wdog_counter_get_current(tmr_id);    // get current counter value
        if (time != 0)
        {
            bigtime = (uint64_t) time;
                  // the current time period is not counted, only whole periods are counted
            if (tmr_id == ALT_WDOG_CPU)
            {
                bigtime *= (uint64_t) (alt_wdog_core_prescaler_get() + 1);
            }
            bigtime *= ALT_MILLISECS_IN_A_SEC;
            bigtime /= freq;          // cycles-per-second becomes milliseconds-per-cycle
            time = (bigtime > (uint64_t) UINT32_MAX) ? 0 : (uint32_t) bigtime;
        }
    }
    return  time;
}


// see the return value range calculations below at alt_wdog_counter_get_inittime_millisecs().

/****************************************************************************************/
/* Returns the initial counter value of the specified timer as a 32-bit integer         */
/* value. This is the value that will be reloaded when the timer is reset or restarted. */
/* For the timers where this value is set as an encoded powers-of-two between 15 and    */
/* 31, the value is converted into the equivalent binary value before returning it. For */
/* ALT_CPU_WATCHDOG, the returned value does not include the effects of the prescaler   */
/* setting                                                                              */
/****************************************************************************************/

uint32_t alt_wdog_counter_get_init(ALT_WDOG_TIMER_t tmr_id)
{
    uint32_t                ret = 0;        //    value to return

    if (tmr_id == ALT_WDOG_CPU)
    {
        ret = alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_LOAD_REG_OFFSET);
    }
    else if (tmr_id == ALT_WDOG0)
    {
        ret = ALT_L4WD_TORR_TOP_GET(alt_read_word(ALT_L4WD0_WDT_TORR_ADDR));
        ret = (ret >  ALT_L4WD_TORR_TOP_E_TMO2G) ? 0 : ALT_TWO_TO_POW16 << ret;
    }
    else if (tmr_id == ALT_WDOG1)
    {
        ret = ALT_L4WD_TORR_TOP_GET(alt_read_word(ALT_L4WD1_WDT_TORR_ADDR));
        ret = (ret >  ALT_L4WD_TORR_TOP_E_TMO2G) ? 0 : ALT_TWO_TO_POW16 << ret;
    }
    else if (tmr_id == ALT_WDOG0_INIT)
    {
        ret = ALT_L4WD_TORR_TOP_INIT_GET(alt_read_word(ALT_L4WD0_WDT_TORR_ADDR));
        ret = (ret >  ALT_L4WD_TORR_TOP_INIT_E_TMO2G) ? 0 : ALT_TWO_TO_POW16 << ret;
    }
    else if (tmr_id == ALT_WDOG1_INIT)
    {
        ret = ALT_L4WD_TORR_TOP_INIT_GET(alt_read_word(ALT_L4WD1_WDT_TORR_ADDR));
        ret = (ret >  ALT_L4WD_TORR_TOP_INIT_E_TMO2G) ? 0 : ALT_TWO_TO_POW16 << ret;
    }
    return  ret;
}


/****************************************************************************************/
/* Returns the initial value of the specified timer in nanoseconds. This is the         */
/* value that will be reloaded when the timer is reset or restarted. For                */
/* ALT_CPU_WATCHDOG, this includes the effects of the prescaler setting.  This call     */
/* returns a more precise result than alt_wdog_counter_get_inittime_millisecs(), but    */
/* as an unsigned 64-bit integer.                                                       */
/****************************************************************************************/

uint64_t alt_wdog_counter_get_inittime_nanosecs(ALT_WDOG_TIMER_t tmr_id)
{
    uint64_t    time = 0;
    alt_freq_t  freq;
    ALT_CLK_t   clk;

    if (tmr_id == ALT_WDOG_CPU)
    {
        clk = ALT_CLK_MPU_PERIPH;
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG1) ||
            (tmr_id == ALT_WDOG0_INIT) || (tmr_id == ALT_WDOG1_INIT))
    {
        clk = ALT_CLK_OSC1;
    }
    else { return time; }            // zero always indicates an error for an init time

    if ((alt_clk_freq_get(clk, &freq) == ALT_E_SUCCESS) && (freq != 0))
    {                               // get clock frequency & test
        time = (uint64_t) alt_wdog_counter_get_init(tmr_id);     // get reset value
        if (time != 0)
        {
            time += 1;
            if (tmr_id == ALT_WDOG_CPU)
            {
                time *= (uint64_t) (alt_wdog_core_prescaler_get() + 1);
            }
            time *= ALT_NANOSECS_IN_A_SEC;
            time /= freq;              // cycles-per-second becomes nanoseconds per cycle
        }
    }

    return  time;
}


/*  For reviewers:
 * minimum clock divider for ALT_CPU_WATCHDOG is 1
 * maximum clock divider for ALT_CPU_WATCHDOG is ((0xFFFF FFFF + 1) x (0x0000 0100) = 0x0000 0100 0000 0000)
 * multiply that by the number of nanoseconds in a second (1,000,000,000)
 *                              = 1,099,511,627,776,000,000,000 (0x9ACA 0000 0000 0000)
 * so the countdown time with the slowest mpu_peripheral clock (2.5 MHz) =
 *                              400 nS to 439,804.6511104 seconds (0x0001 9000 0000 0000 nS)
 * and with the fastest mpu_peripheral clock (200 MHz) =
 *                              5 nS to 5,497,558,138,880 nanoseconds ( 0x0000 0500 0000 0000 nS)
 *
 * minimum clock divider for peripheral watchdogs is 2**16 = (65,536 = 0x00010000)
 * maximum clock divider for peripheral watchdogs is 2**31 = (2,147,483,648 = 0x8000 0000)
 * multiply that by the number of nanoseconds in a second (1,000,000,000) =
 *              4,096,000,000,000 (0x0000 03B9 ACA0 0000) to 2,147,483,648,000,000,000 (0x1DCD 6500 0000 0000)
 * so the countdown time with the slowest l4_sp_clk (625 kHz) =
 *              6,553,600 nS (0x0064 0000) to 3,435,973,836,800 nS (0x0000 0320 0000 0000 nS)
 * and with the fastest l4_sp_clk (100 MHz) =
 *              40,960 ns (0xA000) to 21,474,836,480 nS (0x0000 0005 0000 0000 nS)
 */

/****************************************************************************************/
/* Returns the initial value of the specified timer in milliseconds. This is the        */
/* value that will be reloaded when the timer is reset or restarted. For                */
/* ALT_CPU_WATCHDOG, this includes the effects of the prescaler setting. This call      */
/* returns a 32-bit unsigned integer, though is less precise than                       */
/* alt_wdog_counter_get_inittime_nanosecs().                                            */
/****************************************************************************************/

uint32_t alt_wdog_counter_get_inittime_millisecs(ALT_WDOG_TIMER_t tmr_id)
{
    uint32_t        time = 0;
    alt_freq_t      freq;
    ALT_CLK_t       clk;
    uint64_t        bigtime;

    if (tmr_id == ALT_WDOG_CPU)
    {
        clk = ALT_CLK_MPU_PERIPH;
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG1) ||
            (tmr_id == ALT_WDOG0_INIT) || (tmr_id == ALT_WDOG1_INIT))
    {
        clk = ALT_CLK_OSC1;
    }
    else { return time; }                             // must be an invalid tmr_id

    if ((alt_clk_freq_get(clk, &freq) == ALT_E_SUCCESS) && (freq != 0))
    {                               // get clock frequency & test
        time = alt_wdog_counter_get_init(tmr_id);    // get reset value
        if (time != 0)
        {
            bigtime = ((uint64_t) time) + 1;
            if (tmr_id == ALT_WDOG_CPU)         // the only watchdog with a prescaler
            {
                bigtime *= (uint64_t) (alt_wdog_core_prescaler_get() + 1);
            }
            bigtime *= ALT_MILLISECS_IN_A_SEC;                         // scale value
            bigtime /= freq;              // cycles-per-second becomes milliseconds per cycle
            time = (bigtime > (uint64_t) UINT32_MAX) ? 0 : (uint32_t) bigtime;
        }
    }
    return  time;
}


/*  For reviewers:
 * minimum clock divider for ALT_CPU_WATCHDOG is 1
 * maximum clock divider for ALT_CPU_WATCHDOG is ((0xFFFF FFFF + 1) x (0x0000 0100) = 0x0000 0100 0000 0000)
 * multiply that by the number of milliseconds in a second (1,000)
 *                    = 1,000 (0x3e8) to 1,099,511,627,776,000 (0x0003 E800 0000 0000)
 * so the countdown time with the slowest mpu_peripheral clock (2.5 MHz) =
 *                      0 mS to 439,804.6511104 seconds (0x1A36 E2EB mS)
 * and with the fastest mpu_peripheral clock (200 MHz) =
 *                      0 mS to 5,497.55813888 seconds ( 0x0053 E2D6 mS)
 *
 * minimum clock divider for peripheral watchdogs is 2**16 = (65,536 = 0x00010000)
 * maximum clock divider for peripheral watchdogs is 2**31 = (2,147,483,648 = 0x8000 0000)
 * multiply that by the number of milliseconds in a second (1,000) =
 *              65,536,000 (0x3E8 0000) to 2,147,483,648,000 (0x01F4 0000 0000)
 * so the countdown time with the slowest l4_sp_clk (625 kHz) =
 *                  104 mS (0x0068) to 3,435,973 mS (0x0034 6DC5 mS)
 * and with the fastest l4_sp_clk (100 MHz) = 0 mS to 21,474 mS (0x0000 53E2 mS)
 */

/****************************************************************************************/
/* Sets the value of the CPU watchdog timer ALT_CPU_WATCHDOG prescaler.                 */
/****************************************************************************************/

ALT_STATUS_CODE alt_wdog_core_prescaler_set(uint32_t val)
{
    ALT_STATUS_CODE     ret = ALT_E_BAD_ARG;            // return value
    uint32_t            regdata;

    if (val <= WDOG_PS_MAX)
    {
        if (alt_wdog_tmr_is_enabled(ALT_WDOG_CPU))
        {
            ret = ALT_E_ERROR;
        }
        else
        {
            regdata = alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET);
            alt_write_word((CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET),
                    (regdata & ~WDOG_PS_MASK) | (val << WDOG_PS_SHIFT));
            ret = ALT_E_SUCCESS;
        }
    }
    return  ret;
}


/****************************************************************************************/
/* Returns the value of the prescaler of the CPU core watchdog timer.                   */
/****************************************************************************************/

uint32_t alt_wdog_core_prescaler_get(void)
{
    return  (alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET) &
                    WDOG_PS_MASK) >> WDOG_PS_SHIFT;
}


/****************************************************************************************/
/* Returns the maximum possible counter value of the specified timer as a 32-bit value. */
/* For the timers where this value is encoded (as powers-of-two between 15 and 31), the */
/* encoded value is converted into the equivalent binary value before returning it.     */
/* This does not include the effects of the prescaler available for ALT_CPU_WATCHDOG.   */
/****************************************************************************************/

uint32_t alt_wdog_counter_get_max(ALT_WDOG_TIMER_t tmr_id)
{
    uint32_t                ret = 0;        // return value

    if (tmr_id == ALT_WDOG_CPU)
    {
        ret = WDOG_TMR_MAX;
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG1)
            || (tmr_id == ALT_WDOG0_INIT) || (tmr_id == ALT_WDOG1_INIT))
    {
        ret = ((uint32_t) ALT_TWO_TO_POW16) << ALT_WDOG_TIMEOUT2G;
    }

    return  ret;
}


/****************************************************************************************/
/* Returns the maximum possible delay time of the specified timer specified in          */
/* nanoseconds. For ALT_CPU_WATCHDOG, this includes the prescaler setting. This call    */
/* returns a more precise reading of the counter than                                   */
/* alt_wdog_counter_get_max_millisecs(), though in an unsigned 64-bit integer.          */
/****************************************************************************************/

uint64_t alt_wdog_counter_get_max_nanosecs(ALT_WDOG_TIMER_t tmr_id)
{
    uint64_t    time = 0;
    alt_freq_t  freq;
    ALT_CLK_t   clk;

    if (tmr_id == ALT_WDOG_CPU)
    {
        clk = ALT_CLK_MPU_PERIPH;
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG1) ||
            (tmr_id == ALT_WDOG0_INIT) || (tmr_id == ALT_WDOG1_INIT))
    {
        clk = ALT_CLK_OSC1;
    }
    else { return time; }

    if ((alt_clk_freq_get(clk, &freq) == ALT_E_SUCCESS) && (freq != 0))
    {                    // get clock frequency & test
        time = (uint64_t) alt_wdog_counter_get_max(tmr_id);     // get maximum reset value
        if (time != 0)
        {
            time += 1;
            if (tmr_id == ALT_WDOG_CPU)
            {
                time *= (WDOG_PS_MAX + 1);          // maximum prescaler
            }
            time *= ALT_NANOSECS_IN_A_SEC;
            time /= freq;               //cycles-per-second becomes nanoseconds-per-cycle
        }
    }
    return  time;
}



/****************************************************************************************/
/* Returns the maximum possible delay time of the specified timer specified in          */
/* milliseconds. For ALT_CPU_WATCHDOG, this includes the prescaler setting. This call   */
/* returns a 32-bit unsigned integer, though is less precise than                       */
/* alt_wdog_counter_get_max_nanosecs().                                                 */
/****************************************************************************************/

uint32_t alt_wdog_counter_get_max_millisecs(ALT_WDOG_TIMER_t tmr_id)
{
    uint32_t        time = 0;
    alt_freq_t      freq;
    ALT_CLK_t       clk;
    uint64_t        bigtime;

    if (tmr_id == ALT_WDOG_CPU)
    {
        clk = ALT_CLK_MPU_PERIPH;
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG1) ||
            (tmr_id == ALT_WDOG0_INIT) || (tmr_id == ALT_WDOG1_INIT))
    {
        clk = ALT_CLK_OSC1;
    }
    else { return time; }

    if ((alt_clk_freq_get(clk, &freq) == ALT_E_SUCCESS) && (freq != 0))
    {                   // get clock frequency & test
        time = alt_wdog_counter_get_max(tmr_id);     // get reset value
        if (time != 0)
        {
            bigtime = ((uint64_t) time) + 1;
            if (tmr_id == ALT_WDOG_CPU)
            {
                bigtime *= (WDOG_PS_MAX + 1);           // maximum prescaler
            }
            bigtime *= ALT_MILLISECS_IN_A_SEC;
            bigtime /= freq;              //cycles-per-second becomes milliseconds-per-cycle
            time = (bigtime > (uint64_t) UINT32_MAX) ? 0 : (uint32_t) bigtime;
        }
    }
    return  time;
}


/****************************************************************************************/
/* Disables the interrupt of the specified watchdog timer module. If the watchdog timer */
/* is one of the watchdog timers that can be used in general-purpose mode, and if the   */
/* timer is in general-purpose timer mode, disable the interrupt.                       */
/****************************************************************************************/

ALT_STATUS_CODE alt_wdog_int_disable(ALT_WDOG_TIMER_t tmr_id)
{
    ALT_STATUS_CODE         ret = ALT_E_BAD_ARG;            // return value

    if (tmr_id == ALT_WDOG_CPU)
    {
        if (cpu_wdog_in_wdt_mode())
        {
            ret = ALT_E_ERROR;
        }
        else
        {
            alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET,
                  (alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET) & ~WDOG_INT_EN));
            ret = ALT_E_SUCCESS;
        }
    }
            // returns an error for the other four watchdog timers
            // since their interrupts cannot be disabled
            // (this could change in v13.1)
    return  ret;
}


/****************************************************************************************/
/* Sets/enables the interrupt of the specified watchdog timer module. If the watchdog   */
/* timer is one of the watchdog timers that can be used in general-purpose mode, and    */
/* if the timer is in general-purpose timer mode, enable the interrupt.                 */
/****************************************************************************************/

ALT_STATUS_CODE alt_wdog_int_enable(ALT_WDOG_TIMER_t tmr_id)
{
    ALT_STATUS_CODE         ret = ALT_E_BAD_ARG;            // return value

    if (tmr_id == ALT_WDOG_CPU)
    {
        if (cpu_wdog_in_wdt_mode())
        {
            ret = ALT_E_ERROR;
        }
        else
        {
            alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET,
                  (alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET) | WDOG_INT_EN));
            ret = ALT_E_SUCCESS;
        }
    }
    return  ret;
                // other watchdog timers always have interrupt enabled if they are running
}


/****************************************************************************************/
/* Returns the status of the interrupt of the specified watchdog timer module but does  */
/* not clear it. Return TRUE if the interrupt of the specified general purpose timer    */
/* module is pending and FALSE otherwise.                                               */
/****************************************************************************************/

bool alt_wdog_int_is_pending(ALT_WDOG_TIMER_t tmr_id)
{
    bool        ret = false;            //return value

    if ((tmr_id == ALT_WDOG_CPU) && cpu_wdog_in_gpt_mode())
    {
        ret = alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_INTSTAT_REG_OFFSET) & WDOG_INT_STAT_BIT;
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        ret = alt_read_word(ALT_L4WD0_WDT_STAT_ADDR) & ALT_L4WD_STAT_WDT_STAT_SET_MSK;
    }
    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        ret = alt_read_word(ALT_L4WD1_WDT_STAT_ADDR) & ALT_L4WD_STAT_WDT_STAT_SET_MSK;
    }
    return ret;
}


/****************************************************************************************/
/* Returns the state of the interrupt of the specified watchdog timer module. If the    */
/* watchdog timer is one of the watchdog timers that can be used in general-purpose     */
/* mode, and if the timer is in general-purpose timer mode, returns TRUE if the         */
/* interrupt of the specified general purpose timer module is enabled and FALSE if      */
/* disabled. If the timer is not in general-purpose timer mode, returns TRUE, as        */
/* watchdog interrupts are always enabled.                                              */
/****************************************************************************************/

bool alt_wdog_int_is_enabled(ALT_WDOG_TIMER_t tmr_id)
{
    bool        ret = false;            //return value

    if (tmr_id == ALT_WDOG_CPU)
    {
        ret = alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET) &
                    (WDOG_INT_EN | WDOG_WDT_MODE);
            // if in watchdog mode OR if in general purpose timer mode
            // AND the interrupt is enabled
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        ret = alt_read_word(ALT_L4WD0_WDT_CR_ADDR) & ALT_L4WD_CR_WDT_EN_SET_MSK;
        // if these timers are running, their interrupt is enabled
    }
    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        ret = alt_read_word(ALT_L4WD1_WDT_CR_ADDR) & ALT_L4WD_CR_WDT_EN_SET_MSK;
            // if these timers are running, their interrupt is enabled
    }
    return ret;
}


/****************************************************************************************/
/* Clears the pending status of the interrupt of the specified watchdog timer module.   */
/****************************************************************************************/

ALT_STATUS_CODE alt_wdog_int_clear(ALT_WDOG_TIMER_t tmr_id)
{


    if (tmr_id == ALT_WDOG_CPU)
    {
        alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_INTSTAT_REG_OFFSET, WDOG_INT_STAT_BIT);
             // clear int by writing to status bit
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        (void) alt_read_word(ALT_L4WD0_WDT_EOI_ADDR);
            // clear int by reading from end-of-interrupt register
            // adding the void cast tells armcc not to throw a error for this usage
    }
    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        (void) alt_read_word(ALT_L4WD1_WDT_EOI_ADDR);
            // clear int by reading from end-of-interrupt register
    }
    else {return  ALT_E_ERROR; }
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* Returns the status of the interrupt of the specified watchdog timer module and also  */
/* clears it. Return TRUE if the interrupt of the specified general purpose timer       */
/* module is pending and FALSE otherwise.                                               */
/****************************************************************************************/

bool alt_wdog_int_if_pending_clear(ALT_WDOG_TIMER_t tmr_id)
{
    uint32_t                ret = false;    //    value to return


    if (tmr_id == ALT_WDOG_CPU)
    {
        ret = (alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_INTSTAT_REG_OFFSET) & WDOG_INT_STAT_BIT);
        if (ret)
        {
            alt_write_word(CPU_WDTGPT_TMR_BASE + WDOG_INTSTAT_REG_OFFSET, WDOG_INT_STAT_BIT);
            // clear int by writing to status bit
        }
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        ret = alt_read_word(ALT_L4WD0_WDT_STAT_ADDR) & ALT_L4WD_STAT_WDT_STAT_SET_MSK;
        if (ret)
        {
            (void) alt_read_word(ALT_L4WD0_WDT_EOI_ADDR);
                // clear int by reading from end-of-interrupt register
                // adding the void cast tells armcc not to throw a error for this usage

       }
    }
    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        ret = alt_read_word(ALT_L4WD1_WDT_STAT_ADDR) & ALT_L4WD_STAT_WDT_STAT_SET_MSK;

        if (ret)
        {
            (void) alt_read_word(ALT_L4WD1_WDT_EOI_ADDR);
                    // clear int by reading from end-of-interrupt register
        }
    }

    return  ret;
}


/****************************************************************************************/
/* Sets the timeout response mode of the specified watchdog timer. For ALT_WATCHDOG0,   */
/* ALT_WATCHDOG1, \b ALT_WATCHDOG0_INITIAL or \b ALT_WATCHDOG1_INITIAL, the options     */
/* are to generate a system reset or to generate an interrupt and then generate a       */
/* system reset if the interrupt is not cleared by the next time the watchdog timer     */
/* counter rolls over. For ALT_CPU_WATCHDOG, the options are to trigger an interrupt    */
/* request (with the result set in the interrupt manager) or a reset request (with the  */
/* result set in the reset manager) plus two more options available when it is used     */
/* as a general-purpose timer.                                                          */
/****************************************************************************************/

ALT_STATUS_CODE alt_wdog_response_mode_set(ALT_WDOG_TIMER_t tmr_id, ALT_WDOG_RESET_TYPE_t type)
{
    ALT_STATUS_CODE         ret = ALT_E_BAD_ARG;        // return value
    uint32_t                regdata;                    // register data


    if (tmr_id == ALT_WDOG_CPU)
    {
        regdata = alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET);
        if (type == ALT_WDOG_TIMER_MODE_ONESHOT)
        {
            alt_write_word((CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET), regdata & ~WDOG_AUTO_RELOAD);
            ret = ALT_E_SUCCESS;
        }
        else if (type == ALT_WDOG_TIMER_MODE_FREERUN)
        {
            alt_write_word((CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET), regdata | WDOG_AUTO_RELOAD);
            ret = ALT_E_SUCCESS;
        }
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        regdata = alt_read_word(ALT_L4WD0_WDT_CR_ADDR);
        if (type == ALT_WDOG_WARM_RESET)
        {
            alt_write_word(ALT_L4WD0_WDT_CR_ADDR, regdata & ALT_L4WD_CR_RMOD_CLR_MSK);
            ret = ALT_E_SUCCESS;
        }
        else if (type == ALT_WDOG_INT_THEN_RESET)
        {
            alt_write_word(ALT_L4WD0_WDT_CR_ADDR, regdata | ALT_L4WD_CR_RMOD_SET_MSK);
            ret = ALT_E_SUCCESS;
        }
    }
    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        regdata = alt_read_word(ALT_L4WD1_WDT_CR_ADDR);
        if (type == ALT_WDOG_WARM_RESET)
        {
            alt_write_word(ALT_L4WD1_WDT_CR_ADDR, regdata & ALT_L4WD_CR_RMOD_CLR_MSK);
            ret = ALT_E_SUCCESS;
        }
        else if (type == ALT_WDOG_INT_THEN_RESET)
        {
            alt_write_word(ALT_L4WD1_WDT_CR_ADDR, regdata | ALT_L4WD_CR_RMOD_SET_MSK);
            ret = ALT_E_SUCCESS;
        }
    }
    return  ret;            // rejects a bad tmr_id argument/type argument combination
}


/****************************************************************************************/
/* Returns the response mode of the specified timer.                                    */
/****************************************************************************************/

int32_t alt_wdog_response_mode_get(ALT_WDOG_TIMER_t tmr_id)
{
    int32_t             ret = ALT_E_BAD_ARG;     // return value
    uint32_t            regdata;                 // read value


    if (tmr_id == ALT_WDOG_CPU)
    {
        regdata = alt_read_word(CPU_WDTGPT_TMR_BASE + WDOG_CTRL_REG_OFFSET);
        ret = (regdata & WDOG_AUTO_RELOAD) ? ALT_WDOG_TIMER_MODE_FREERUN : ALT_WDOG_TIMER_MODE_ONESHOT;
    }
    else if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        regdata = alt_read_word(ALT_L4WD0_WDT_CR_ADDR);
        ret = (regdata & ALT_L4WD_CR_RMOD_SET_MSK) ? ALT_WDOG_INT_THEN_RESET : ALT_WDOG_WARM_RESET;
    }
    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        regdata = alt_read_word(ALT_L4WD1_WDT_CR_ADDR);
        ret = (regdata & ALT_L4WD_CR_RMOD_SET_MSK) ? ALT_WDOG_INT_THEN_RESET : ALT_WDOG_WARM_RESET;
    }

    return  ret;
}



/****************************************************************************************/
/* Returns the component code of the watchdog timer module. Only valid for              */
/* ALT_WATCHDOG0, ALT_WATCHDOG1, ALT_WATCHDOG0_INITIAL or ALT_WATCHDOG1_INITIAL.        */
/****************************************************************************************/

uint32_t alt_wdog_compcode_get(ALT_WDOG_TIMER_t tmr_id)
{
    uint32_t    component = 0;                  // component code of the module

    if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        component = alt_read_word(ALT_L4WD0_WDT_COMP_TYPE_ADDR);
    }
    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        component = alt_read_word(ALT_L4WD1_WDT_COMP_TYPE_ADDR);

    }
    return  component;
}


/****************************************************************************************/
/* Returns the version code of the watchdog timer module. Only valid for ALT_WATCHDOG0, */
/* ALT_WATCHDOG1, ALT_WATCHDOG0_INITIAL or ALT_WATCHDOG1_INITIAL.                       */
/****************************************************************************************/

uint32_t alt_wdog_ver_get(ALT_WDOG_TIMER_t tmr_id)
{
    uint32_t    ver = 0;                  // revision code of the module

    if ((tmr_id == ALT_WDOG0) || (tmr_id == ALT_WDOG0_INIT))
    {
        ver = alt_read_word(ALT_L4WD0_WDT_COMP_VER_ADDR);
    }
    else if ((tmr_id == ALT_WDOG1) || (tmr_id == ALT_WDOG1_INIT))
    {
        ver = alt_read_word(ALT_L4WD1_WDT_COMP_VER_ADDR);

    }
    return  ver;
}


/****************************************************************************************/


