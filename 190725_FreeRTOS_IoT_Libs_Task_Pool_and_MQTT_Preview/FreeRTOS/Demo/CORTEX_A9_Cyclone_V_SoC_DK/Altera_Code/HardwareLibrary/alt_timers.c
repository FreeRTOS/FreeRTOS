
/******************************************************************************
*
* alt_timers.c - API for the Altera SoC general purpose timers.
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
* The SoC FPGA has nine general purpose timers. Seven timers are available
* to each CPU.
*
* There are four types of timers available:
* - Four general-purpose countdown timers available to CPU0, CPU1, or the FPGA
* - Each CPU has a private GP countdown timer available only to itself
* - Each CPU has a watchdog timer that can work in GP timer countdown mode
* - One continuous-countup global timer with compare capabilities available to
*   both CPUs and to the FPGA
*
* Each type has a somewhat different HW interface. This API presents the same
* external interface for each.
*
******************************************************************************/


#include    <stdint.h>
#include    <stdbool.h>
#include    "socal/hps.h"
#include    "socal/socal.h"
#include    "socal/alt_tmr.h"
#include    "socal/alt_rstmgr.h"
#include    "hwlib.h"
#include    "alt_mpu_registers.h"
#include    "alt_timers.h"
#include    "alt_clock_manager.h"                    // for getting clock bus frequency
#include    "alt_watchdog.h"
#include    "alt_globaltmr.h"


extern bool cpu_wdog_in_gpt_mode(void);
extern bool alt_globaltmr_is_running(void);
#define     alt_globaltmr_remain_get64()   (alt_globaltmr_comp_get64() - alt_globaltmr_get64())


/****************************************************************************************/
/* alt_gpt_all_tmr_uninit() uninitializes the general-purpose timer modules             */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpt_all_tmr_uninit(void)
{
        // put the L4 general-purpose timer modules into system manager reset
    alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR,
            ALT_RSTMGR_PERMODRST_OSC1TMR0_SET_MSK | ALT_RSTMGR_PERMODRST_OSC1TMR1_SET_MSK
            | ALT_RSTMGR_PERMODRST_SPTMR0_SET_MSK | ALT_RSTMGR_PERMODRST_SPTMR1_SET_MSK);

        // put the local ARM private timer into reset manually
    alt_clrbits_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET,
            CPU_PRIV_TMR_ENABLE | CPU_PRIV_TMR_INT_EN);
        // reset load and counter registers
    alt_write_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_LOAD_REG_OFFSET, 0);
        // clear any pending interrupts
    alt_write_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_INT_STATUS_REG_OFFSET, CPU_PRIV_TMR_INT_STATUS);
        // now write zeros to the control register significant bitfields
    alt_clrbits_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET,
            (CPU_PRIV_TMR_ENABLE | CPU_PRIV_TMR_AUTO_RELOAD | CPU_PRIV_TMR_INT_EN
            | CPU_PRIV_TMR_PS_MASK));

    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* alt_gpt_all_tmr_init() initializes the general-purpose timer modules                 */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpt_all_tmr_init(void)
{
        // put general-purpose timer modules into system manager reset if not already there
    alt_gpt_all_tmr_uninit();
        // release general-purpose timer modules from system reset (w/ two-instruction delay)
    alt_clrbits_word(ALT_RSTMGR_PERMODRST_ADDR,
            ALT_RSTMGR_PERMODRST_OSC1TMR0_SET_MSK | ALT_RSTMGR_PERMODRST_OSC1TMR1_SET_MSK
            | ALT_RSTMGR_PERMODRST_SPTMR0_SET_MSK | ALT_RSTMGR_PERMODRST_SPTMR1_SET_MSK);

        // nothing to do for the local ARM private timer
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/*  alt_gpt_tmr_stop() stops the countdown or countup of the specified timer.           */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpt_tmr_stop(ALT_GPT_TIMER_t tmr_id)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;      // Return value
    uint32_t            regmask;                // data mask
    volatile uint32_t   *regaddr;               // register address


    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)               // Global Timer
    {
        ret = alt_globaltmr_stop();
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)  // Local watchdog Timer for this CPU, if it is in gpt mode
    {
        if (cpu_wdog_in_gpt_mode())             // Is local watchdog timer in general-purpose timer mode?
        {
            ret = alt_wdog_stop(ALT_WDOG_CPU);
        }
    }
    else
    {
        if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR) // Local Private Timer for this CPU
        {
            regaddr = (volatile uint32_t *) (CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET);
            regmask = ~CPU_PRIV_TMR_ENABLE;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR0)   // Timer 0 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR0_TMR1CTLREG_ADDR;
            regmask = ALT_TMR_TMR1CTLREG_TMR1_EN_CLR_MSK;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)   // Timer 1 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR1_TMR1CTLREG_ADDR;
            regmask = ALT_TMR_TMR1CTLREG_TMR1_EN_CLR_MSK;
        }
        else if (tmr_id == ALT_GPT_SP_TMR0)     // Timer 0 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR0_TMR1CTLREG_ADDR;
            regmask = ALT_TMR_TMR1CTLREG_TMR1_EN_CLR_MSK;
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)     // Timer 1 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR1_TMR1CTLREG_ADDR;
            regmask = ALT_TMR_TMR1CTLREG_TMR1_EN_CLR_MSK;
        }
        else { return ALT_E_BAD_ARG; }          // none of the above

        alt_write_word(regaddr, alt_read_word(regaddr) & regmask);
        ret = ALT_E_SUCCESS;
    }
    return ret;
}


/****************************************************************************************/
/*  alt_gpt_tmr_start() starts the countdown or countup of the specified timer.         */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpt_tmr_start(ALT_GPT_TIMER_t tmr_id)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;          // Return value
    uint32_t            regmask;                    // data mask
    volatile uint32_t   *regaddr;                   // register address


    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)           // Global Timer
    {
        ret = alt_globaltmr_start();
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)      // Local watchdog Timer for this CPU, if it is in gpt mode
    {
        if (cpu_wdog_in_gpt_mode())                 // Is local watchdog timer in general-purpose timer mode?
        {
            ret = alt_wdog_start(ALT_WDOG_CPU);
        }
    }
    else
    {
        if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)     // Local Private Timer for this CPU
        {
            regaddr = (volatile uint32_t *) (CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET);
            regmask = CPU_PRIV_TMR_ENABLE;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR0)       // Timer 0 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR0_TMR1CTLREG_ADDR;
            regmask = ALT_TMR_TMR1CTLREG_TMR1_EN_SET_MSK;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)       // Timer 1 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR1_TMR1CTLREG_ADDR;
            regmask = ALT_TMR_TMR1CTLREG_TMR1_EN_SET_MSK;
        }
        else if (tmr_id == ALT_GPT_SP_TMR0)         // Timer 0 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR0_TMR1CTLREG_ADDR;
            regmask = ALT_TMR_TMR1CTLREG_TMR1_EN_SET_MSK;
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)         // Timer 1 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR1_TMR1CTLREG_ADDR;
            regmask = ALT_TMR_TMR1CTLREG_TMR1_EN_SET_MSK;
        }
        else { return ALT_E_BAD_ARG; }              // none of the above

        alt_write_word(regaddr, alt_read_word(regaddr) | regmask);
        ret = ALT_E_SUCCESS;
    }
    return ret;
}


/****************************************************************************************/
/* alt_gpt_tmr_is_running() checks and returns the status of the specified timer,       */
/* i.e. whether running or not.                                                         */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpt_tmr_is_running(ALT_GPT_TIMER_t tmr_id)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;  // Return value
    uint32_t            regdata;            // temp value to read
    uint32_t            regmask;            // data mask
    volatile uint32_t   *regaddr;           // register address


    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)           // Global Timer
    {
        ret = (alt_globaltmr_is_comp_mode() && alt_globaltmr_is_running())
                        ? ALT_E_TRUE : ALT_E_FALSE;
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)      // Local watchdog Timer for this CPU
    {
        ret = (alt_wdog_tmr_is_enabled(ALT_WDOG_CPU)) ? ALT_E_TRUE : ALT_E_FALSE;
    }
    else
    {
        if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)     // Local Private Timer for this CPU
        {
            regaddr = (volatile uint32_t *) (CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET);
            regmask = CPU_PRIV_TMR_ENABLE;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR0)       //Timer 0 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR0_TMR1CTLREG_ADDR;
            regmask = ALT_TMR_TMR1CTLREG_TMR1_EN_SET_MSK;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)       //Timer 1 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR1_TMR1CTLREG_ADDR;
            regmask = ALT_TMR_TMR1CTLREG_TMR1_EN_SET_MSK;
        }
        else if (tmr_id == ALT_GPT_SP_TMR0)         //Timer 0 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR0_TMR1CTLREG_ADDR;
            regmask = ALT_TMR_TMR1CTLREG_TMR1_EN_SET_MSK;
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)         //Timer 1 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR1_TMR1CTLREG_ADDR;
            regmask = ALT_TMR_TMR1CTLREG_TMR1_EN_SET_MSK;
        }
        else { return ALT_E_BAD_ARG; }              // none of the above

        regdata = alt_read_word(regaddr);
        ret = (regdata & regmask) ? ALT_E_TRUE : ALT_E_FALSE;
    }
    return ret;
}


/****************************************************************************************/
/* alt_gpt_tmr_reset() just stops and restarts the specified timer, causing it to       */
/* reset and start its count over again.                                                */
 /****************************************************************************************/

ALT_STATUS_CODE alt_gpt_tmr_reset(ALT_GPT_TIMER_t tmr_id)
{
    ALT_STATUS_CODE     ret = ALT_E_SUCCESS;

    if (alt_gpt_tmr_is_running(tmr_id)) { ret = alt_gpt_tmr_stop(tmr_id); }
                // stop the timer
    if (ret == ALT_E_SUCCESS) { ret = alt_gpt_tmr_start(tmr_id); }
                // restart timer again from the beginning
    if (ret == ALT_E_SUCCESS) { ret = alt_gpt_int_clear_pending(tmr_id); }
               // clear out any pending interrupts for this timer

    return    ret;
}


/****************************************************************************************/
/* alt_gpt_counter_set() sets the value of the specified timer. If the timer is         */
/* currently running, it is stopped first.                                              */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpt_counter_set(ALT_GPT_TIMER_t tmr_id, uint32_t val)
{
    ALT_STATUS_CODE      ret = ALT_E_ERROR;           // Return value
    volatile uint32_t    *regaddr;                    // register address


    if (alt_gpt_tmr_is_running(tmr_id))
    {
        alt_gpt_tmr_stop(tmr_id);               // If timer is currently running, stop it
    }

    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)       // Global Timer
    {
        ret = alt_globaltmr_autoinc_set(val);
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)  // Local watchdog Timer for this CPU, if it is in gpt mode
    {
        ret = alt_wdog_counter_set(ALT_WDOG_CPU, (ALT_WDOG_TIMEOUT_t) val);
    }
    else
    {
        if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR) // Local Private Timer for this CPU
        {
            regaddr = (volatile uint32_t *) (CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_LOAD_REG_OFFSET);
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR0)   // Timer 0 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR0_TMR1LDCOUNT_ADDR;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)   // Timer 1 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR1_TMR1LDCOUNT_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR0)     // Timer 0 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR0_TMR1LDCOUNT_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)     // Timer 1 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR1_TMR1LDCOUNT_ADDR;
        }
        else { return ALT_E_BAD_ARG; }          // none of the above

        alt_write_word(regaddr, val);
        ret = ALT_E_SUCCESS;
    }
    return    ret;
}


/****************************************************************************************/
/* alt_gpt_counter_get() returns the current value of the specified timer, whether      */
/* running or not. Note that the global timer counts up and for the global timer, this  */
/* function does NOT return a value that indicates how long until the next interrupt.   */
/****************************************************************************************/

 uint32_t alt_gpt_counter_get(ALT_GPT_TIMER_t tmr_id)
{
    uint32_t            ret = 0;                // value to return
    volatile uint32_t   *regaddr;               // register address


    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)       // Global Timer
    {
        ret = alt_globaltmr_counter_get_low32();
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)  // Local watchdog Timer for this CPU
    {
        ret = alt_wdog_counter_get_current(ALT_WDOG_CPU);
    }
    else
    {
        if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR) // Local Private Timer for this CPU
        {
            regaddr = (volatile uint32_t *) (CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CNTR_REG_OFFSET);
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR0)   // Timer 0 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR0_TMR1CURVAL_ADDR;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)   // Timer 1 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR1_TMR1CURVAL_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR0)     // Timer 0 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR0_TMR1CURVAL_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)     // Timer 1 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR1_TMR1CURVAL_ADDR;
        }
        else { return 0; }                      // none of the above

        ret = alt_read_word(regaddr);
    }
    return ret;
}


/****************************************************************************************/
/* alt_gpt_curtime_get_kernl() is the basis of the next four functions.                   */
/****************************************************************************************/

static uint32_t alt_gpt_curtime_get_kernl(ALT_GPT_TIMER_t tmr_id, uint32_t mult)
{
     uint64_t           bigtime;                // r2 & r3
     uint32_t           time = 0;               // value to return
     ALT_CLK_t          clk = ALT_CLK_UNKNOWN;
     uint32_t           pres, freq;
     volatile uint32_t  *regaddr;               // register address



     pres = alt_gpt_prescaler_get(tmr_id);
     if (pres <= UINT8_MAX)
     {
         if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)      // Global Timer
         {
             bigtime = alt_globaltmr_remain_get64();
             clk = ALT_CLK_MPU_PERIPH;
         }
         else
         {
             if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR) // Local watchdog Timer for this CPU
             {
                 time = alt_wdog_counter_get_current(ALT_WDOG_CPU);
                 clk = ALT_CLK_MPU_PERIPH;
             }
             else
             {
                 if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)    // Local Private Timer for this CPU
                 {
                     regaddr = (volatile uint32_t *) (CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CNTR_REG_OFFSET);
                     clk = ALT_CLK_MPU_PERIPH;
                 }
                 else if (tmr_id == ALT_GPT_OSC1_TMR0)      // Timer 0 on the OSC1 bus
                 {
                     regaddr = (volatile uint32_t *) ALT_OSC1TMR0_TMR1CURVAL_ADDR;
                     clk = ALT_CLK_OSC1;
                 }
                 else if (tmr_id == ALT_GPT_OSC1_TMR1)      // Timer 1 on the OSC1 bus
                 {
                     regaddr = (volatile uint32_t *) ALT_OSC1TMR1_TMR1CURVAL_ADDR;
                     clk = ALT_CLK_OSC1;
                 }
                 else if (tmr_id == ALT_GPT_SP_TMR0)        // Timer 0 on the SP bus
                 {
                     regaddr = (volatile uint32_t *) ALT_SPTMR0_TMR1CURVAL_ADDR;
                     clk = ALT_CLK_L4_SP;
                }
                 else if (tmr_id == ALT_GPT_SP_TMR1)        // Timer 1 on the SP bus
                 {
                     regaddr = (volatile uint32_t *) ALT_SPTMR1_TMR1CURVAL_ADDR;
                     clk = ALT_CLK_L4_SP;
                 }
                 else { return 0; }                      // none of the above

                 time = alt_read_word(regaddr);
             }
             bigtime = (uint64_t) time;
         }

         if (alt_clk_freq_get(clk, &freq) == ALT_E_SUCCESS)
         {
             bigtime *= (pres + 1);
                 // ARM can usually do a 32x64 bit multiply faster than a 64x64 bit multiply
             bigtime *= mult;
             bigtime /= freq;
                 // remaining count divided by cycles-per-second becomes seconds,
                 // milliseconds, microseconds, or nanoseconds remaining
             time = (bigtime > UINT32_MAX) ? 0xFFFFFFFF : (uint32_t) bigtime;
         }
     }
     return time;
}


/****************************************************************************************/
/* alt_gpt_curtime_get() returns the current time until the specified timer counts      */
/* down to zero, measured in seconds.                                                   */
/****************************************************************************************/

uint32_t alt_gpt_curtime_get(ALT_GPT_TIMER_t tmr_id)
{
    return alt_gpt_curtime_get_kernl(tmr_id, 1);
}


/****************************************************************************************/
/* alt_gpt_curtime_get() returns the current time until the specified timer counts      */
/* down to zero, measured in milliseconds.                                              */
/****************************************************************************************/

uint32_t alt_gpt_curtime_millisecs_get(ALT_GPT_TIMER_t tmr_id)
{
    return alt_gpt_curtime_get_kernl(tmr_id, ALT_MILLISECS_IN_A_SEC);
}


/****************************************************************************************/
/* alt_gpt_curtime_get() returns the current time until the specified timer counts      */
/* down to zero, measured in microseconds.                                              */
/****************************************************************************************/

uint32_t alt_gpt_curtime_microsecs_get(ALT_GPT_TIMER_t tmr_id)
{
    return alt_gpt_curtime_get_kernl(tmr_id, ALT_MICROSECS_IN_A_SEC);
}


/****************************************************************************************/
/* alt_gpt_curtime_get() returns the current time until the specified timer counts      */
/* down to zero, measured in microseconds.                                              */
/****************************************************************************************/

uint32_t alt_gpt_curtime_nanosecs_get(ALT_GPT_TIMER_t tmr_id)
{
    return alt_gpt_curtime_get_kernl(tmr_id, ALT_NANOSECS_IN_A_SEC);
}


/****************************************************************************************/
/* alt_gpt_counter_get() returns the value that the specified timer would reset to,     */
/* independent of the current value of the counter.                                     */
/****************************************************************************************/

 uint32_t alt_gpt_reset_value_get(ALT_GPT_TIMER_t tmr_id)
{
    uint32_t            ret = 0;                // Return value
    volatile uint32_t   *regaddr;               // register address


    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)           // Global Timer
    {
        ret = alt_globaltmr_autoinc_get();          // The equivalent of the reset value
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)      // Local watchdog Timer for this CPU
    {
        ret = alt_wdog_counter_get_init(ALT_WDOG_CPU);
    }
    else
    {
        if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)     // Local Private Timer for this CPU
        {
            regaddr = (volatile uint32_t *) (CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_LOAD_REG_OFFSET);
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR0)       // Timer 0 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR0_TMR1LDCOUNT_ADDR;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)       // Timer 1 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR1_TMR1LDCOUNT_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR0)         // Timer 0 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR0_TMR1LDCOUNT_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)         // Timer 1 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR1_TMR1LDCOUNT_ADDR;
        }
        else { return ret;}                         // none of the above

        ret = alt_read_word(regaddr);
    }
    return ret;
}


/****************************************************************************************/
/* alt_gpt_maxcounter_get() returns the maximum possible value that the specified timer */
/* could be set to reset or restart to.                                                 */
/****************************************************************************************/

uint32_t alt_gpt_maxcounter_get(ALT_GPT_TIMER_t tmr_id)
{
    uint32_t    ret = 0;                    // Return value

    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)           // Global Timer
    {
        ret = GLOBALTMR_MAX;
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)      // Local watchdog Timer for this CPU, if it is in gpt mode
    {
        ret = alt_wdog_counter_get_max(ALT_WDOG_CPU);
    }
    else if ((tmr_id == ALT_GPT_CPU_PRIVATE_TMR)    // Local Private Timer for this CPU
            || (tmr_id == ALT_GPT_OSC1_TMR0)        // Timer 0 on the OSC1 bus
            || (tmr_id == ALT_GPT_OSC1_TMR1)        // Timer 1 on the OSC1 bus
            || (tmr_id == ALT_GPT_SP_TMR0)          // Timer 0 on the SP bus
            || (tmr_id == ALT_GPT_SP_TMR1))         // Timer 1 on the SP bus
    {
        ret = CPU_PRIV_TMR_MAX;
    }
    return    ret;
}


/****************************************************************************************/
/* alt_gpt_prescaler_set() sets the value of the prescaler field of the specified       */
/* timer, which is one less than the actual counter value. Valid input = 0-255 and any  */
/* larger value causes an error. It also throws an error if the timer is currently      */
/* running.                                                                             */
/****************************************************************************************/

 ALT_STATUS_CODE alt_gpt_prescaler_set(ALT_GPT_TIMER_t tmr_id, uint32_t val)
{
    ALT_STATUS_CODE         ret = ALT_E_ERROR;      // value to return
    uint32_t                regdata;

    if ((tmr_id == ALT_GPT_CPU_GLOBAL_TMR) && (val <= GLOBALTMR_PS_MAX))    // Global Timer
    {
        ret = alt_globaltmr_prescaler_set(val);
    }
    else if ((tmr_id == ALT_GPT_CPU_WDTGPT_TMR) && (val <= WDOG_PS_MAX))
    {                                       // Local watchdog Timer for this CPU
        ret = alt_wdog_core_prescaler_set(val);
    }
    else if ((tmr_id == ALT_GPT_CPU_PRIVATE_TMR)  && (val <= CPU_PRIV_TMR_PS_MAX))
    {                       // Local Private Timer for this CPU
        regdata = alt_read_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET);
        regdata = (regdata & ~CPU_PRIV_TMR_PS_MASK) | (val << CPU_PRIV_TMR_PS_SHIFT);
        // Replace existing bitfield
        alt_write_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET,
                       regdata);
        ret = ALT_E_SUCCESS;
    }
        else { ret = ALT_E_BAD_ARG; }               // the other timers don't have a prescaler
    return ret;
}


/****************************************************************************************/
/* alt_gpt_prescaler_get() returns the value of the prescaler setting of the specified  */
/* timer, which is one less than the actual scaler value. Valid output = 0-255.         */
/****************************************************************************************/

 uint32_t alt_gpt_prescaler_get(ALT_GPT_TIMER_t tmr_id)
{
    uint32_t        ret = 0;                        // value to return
    uint32_t        regdata;                        // value to read

    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)           // Global Timer
    {
        ret = alt_globaltmr_prescaler_get();
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)
    {                   // Local watchdog Timer for this CPU, gpt mode doesn't matter
        ret = alt_wdog_core_prescaler_get();
    }
    else if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)    // Local Private Timer for this CPU
    {
        regdata = alt_read_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET);
        ret = (regdata & CPU_PRIV_TMR_PS_MASK) >> CPU_PRIV_TMR_PS_SHIFT;
    }
    return ret;                                     // Returns zero for the other timers
}


 /****************************************************************************************/
/* alt_gpt_freq_get() returns the integer portion of the frequency that the             */
/* selected timer will rollover at, measured in Hertz.                                  */
/****************************************************************************************/

uint32_t alt_gpt_freq_get(ALT_GPT_TIMER_t tmr_id)
{
    uint32_t        freq = 0;                   // return value
    uint64_t        divd, bigfreq;              // math
    ALT_CLK_t       clk;                        // clock type


    if ((tmr_id == ALT_GPT_CPU_GLOBAL_TMR) || (tmr_id == ALT_GPT_CPU_WDTGPT_TMR) || (tmr_id == ALT_GPT_CPU_PRIVATE_TMR))
    {
        clk = ALT_CLK_MPU_PERIPH;
    }
        /* Peripheral timers */
    else if ((tmr_id == ALT_GPT_OSC1_TMR0) || (tmr_id == ALT_GPT_OSC1_TMR1))
    {
        clk = ALT_CLK_OSC1;
    }
    else if ((tmr_id == ALT_GPT_SP_TMR0) || (tmr_id == ALT_GPT_SP_TMR1))
    {
        clk = ALT_CLK_L4_SP;
    }
    else { return freq; }

    if (alt_clk_freq_get(clk, &freq) == ALT_E_SUCCESS)
    {
        bigfreq = (uint64_t) freq;
        divd = ((((uint64_t) alt_gpt_reset_value_get(tmr_id)) + 1) *
                    ((uint64_t) (alt_gpt_prescaler_get(tmr_id) + 1)));
            // Convert the reset value to 64-bit before the addition to avoid a potential
            // rollover to zero. But add one to the prescaler value before the conversion
            // to 64-bit -- no potential for rollover  and integer addition is faster

        bigfreq /= divd;
        freq = (bigfreq > UINT32_MAX) ? 0 : (uint32_t) bigfreq;
    }
    else { freq = 0; }
    return freq;
}


/****************************************************************************************/
/* alt_gpt_time_get_kernl() is the root function of the next three functions            */
/* definitions.                                                                         */
/****************************************************************************************/

static uint32_t alt_gpt_time_get_kernl(ALT_GPT_TIMER_t tmr_id, uint32_t mult)
{
    uint32_t            freq, time = 0;
    uint64_t            bigtime;
    ALT_CLK_t           clk;


    if ((tmr_id == ALT_GPT_CPU_GLOBAL_TMR) || (tmr_id == ALT_GPT_CPU_WDTGPT_TMR) || (tmr_id == ALT_GPT_CPU_PRIVATE_TMR))
    {
        clk = ALT_CLK_MPU_PERIPH;
    }
        /* Peripheral timers */
    else if ((tmr_id == ALT_GPT_OSC1_TMR0) || (tmr_id == ALT_GPT_OSC1_TMR1))
    {
        clk = ALT_CLK_OSC1;
    }
    else if ((tmr_id == ALT_GPT_SP_TMR0) || (tmr_id == ALT_GPT_SP_TMR1))
    {
        clk = ALT_CLK_L4_SP;
    }
    else { return time; }

    if (alt_clk_freq_get(clk, &freq) == ALT_E_SUCCESS)
    {
        bigtime = ((((uint64_t) alt_gpt_reset_value_get(tmr_id)) + 1) *
                            ((uint64_t) (alt_gpt_prescaler_get(tmr_id) + 1)));
                // Convert the reset value to 64-bit before the addition to avoid a potential
                // rollover to zero. But add one to the prescaler value before the conversion
                // to 64-bit -- no potential for rollover and integer addition is faster

        bigtime *= (uint64_t) mult;
        bigtime /= (uint64_t) freq;
        time = (bigtime > UINT32_MAX) ? 0xFFFFFFFF : (uint32_t) bigtime;
    }
    return time;
}


/****************************************************************************************/
/* alt_gpt_time_get() returns the currently-selected timeout period of the selected     */
/* timer, measured in seconds.                                                          */
/****************************************************************************************/

uint32_t alt_gpt_time_get(ALT_GPT_TIMER_t tmr_id)
{
    return alt_gpt_time_get_kernl(tmr_id, 1);
}

/****************************************************************************************/
/* alt_gpt_time_get() returns the currently-selected timeout period of the selected     */
/* timer, measured in milliseconds.                                                     */
/****************************************************************************************/

uint32_t alt_gpt_time_millisecs_get(ALT_GPT_TIMER_t tmr_id)
{
    return alt_gpt_time_get_kernl(tmr_id, ALT_MILLISECS_IN_A_SEC);
}


/****************************************************************************************/
/* alt_gpt_time_get() returns the currently-selected timeout period of the selected     */
/* timer, measured in microseconds.                                                     */
/****************************************************************************************/

uint32_t alt_gpt_time_microsecs_get(ALT_GPT_TIMER_t tmr_id)
{
    return alt_gpt_time_get_kernl(tmr_id, ALT_MICROSECS_IN_A_SEC);
}


/****************************************************************************************/
/* alt_gpt_maxtime_get_kernl() is the basis for the next two functions                  */
/****************************************************************************************/

static uint32_t alt_gpt_maxtime_get_kernl(ALT_GPT_TIMER_t tmr_id, uint32_t mult)
{
    uint32_t            time = 0;
    uint32_t            freq;
    uint64_t            bigtime;
    ALT_CLK_t           clk;


    if ((tmr_id == ALT_GPT_CPU_GLOBAL_TMR) || (tmr_id == ALT_GPT_CPU_WDTGPT_TMR) || (tmr_id == ALT_GPT_CPU_PRIVATE_TMR))
    {
        clk = ALT_CLK_MPU_PERIPH;
    }
        /* Peripheral timers */
    else if ((tmr_id == ALT_GPT_OSC1_TMR0) || (tmr_id == ALT_GPT_OSC1_TMR1))
    {
        clk = ALT_CLK_OSC1;
    }
    else if ((tmr_id == ALT_GPT_SP_TMR0) || (tmr_id == ALT_GPT_SP_TMR1))
    {
        clk = ALT_CLK_L4_SP;
    }
    else { return time; }

    if (alt_clk_freq_get(clk, &freq) == ALT_E_SUCCESS)
    {
        bigtime = (((uint64_t) alt_gpt_maxcounter_get(tmr_id)) + 1)
                                * ((uint64_t) (alt_gpt_prescaler_get(tmr_id) + 1));
        bigtime *= (uint64_t) mult;                 //scale the output
        bigtime /= (uint64_t) freq;
        time = (bigtime > UINT32_MAX) ? 0xFFFFFFFF : (uint32_t) bigtime;
    }
    return time;
}


/****************************************************************************************/
/* alt_gpt_maxtime_get() returns the maximum available timeout period of the selected   */
/* timer, measured in seconds.                                                          */
/****************************************************************************************/

uint32_t alt_gpt_maxtime_get(ALT_GPT_TIMER_t tmr_id)
{
    return alt_gpt_maxtime_get_kernl(tmr_id, 1);
}


/****************************************************************************************/
/* alt_gpt_maxtime_millisecs_get() returns the maximum available timeout period of the  */
/* selected timer, measured in milliseconds.                                            */
/****************************************************************************************/

uint32_t alt_gpt_maxtime_millisecs_get(ALT_GPT_TIMER_t tmr_id)
{
    return alt_gpt_maxtime_get_kernl(tmr_id, ALT_MILLISECS_IN_A_SEC);
}


/****************************************************************************************/
/* alt_gpt_int_disable() disables the interrupt of the specified timer. It returns a    */
/* status code showing the result of the operation.                                     */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpt_int_disable(ALT_GPT_TIMER_t tmr_id)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;          // Return value
    volatile uint32_t   *regaddr;                   // register address


    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)               // Global Timer
    {
        ret = alt_globaltmr_int_disable();
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)          // Local watchdog Timer for this CPU, if it is in gpt mode
    {
        ret = alt_wdog_int_disable(ALT_WDOG_CPU);
    }
    else if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)        // Local Private Timer for this CPU
    {
        alt_write_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET,
                alt_read_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET) & ~CPU_PRIV_TMR_INT_EN);
        ret = ALT_E_SUCCESS;
    }
    else
    {
        if (tmr_id == ALT_GPT_OSC1_TMR0)                // Timer 0 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR0_TMR1CTLREG_ADDR;

        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)           // Timer 1 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR1_TMR1CTLREG_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR0)             // Timer 0 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR0_TMR1CTLREG_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)             // Timer 1 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR1_TMR1CTLREG_ADDR;
        }
        else { return    ALT_E_BAD_ARG; }               // none of the above

        alt_write_word(regaddr, alt_read_word(regaddr) | ALT_TMR_TMR1CTLREG_TMR1_INT_MSK_SET_MSK);
        ret = ALT_E_SUCCESS;
    }
    alt_gpt_int_clear_pending(tmr_id);                  // Clear any pending ints
    return    ret;
}


/****************************************************************************************/
/* alt_gpt_int_enable() enables the interrupt of the specified timer. It returns a      */
/* status code showing the result of the operation.                                     */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpt_int_enable(ALT_GPT_TIMER_t tmr_id)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;  // Return value
    volatile uint32_t   *regaddr;           // register address


    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)           // Global Timer
    {
        ret = alt_globaltmr_int_enable();
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)      // Local watchdog Timer for this CPU
    {
        if (cpu_wdog_in_gpt_mode())                 // Is watchdog in general-purpose timer mode?
        {
            ret = alt_wdog_int_enable(ALT_WDOG_CPU);
        }
    }
    else if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)    // Local Private Timer for this CPU
    {
        alt_write_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET,
                alt_read_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET) | CPU_PRIV_TMR_INT_EN);
        ret = ALT_E_SUCCESS;
    }
    else
    {
        if (tmr_id == ALT_GPT_OSC1_TMR0)            // Timer 0 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR0_TMR1CTLREG_ADDR;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)       // Timer 1 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR1_TMR1CTLREG_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR0)         // Timer 0 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR0_TMR1CTLREG_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)         // Timer 1 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR1_TMR1CTLREG_ADDR;
        }
        else { return    ALT_E_BAD_ARG; }           // none of the above

        alt_write_word(regaddr, alt_read_word(regaddr) & ALT_TMR_TMR1CTLREG_TMR1_INT_MSK_CLR_MSK);
        ret = ALT_E_SUCCESS;
    }
    return    ret;
}


/****************************************************************************************/
/* alt_gpt_int_is_enabled() returns whether or not the interrupt of the specified       */
/* timer is enabled or not.                                                             */
/****************************************************************************************/

bool alt_gpt_int_is_enabled(ALT_GPT_TIMER_t tmr_id)
{
    bool                ret = false;            // Return value
    volatile uint32_t   *regaddr;               // register address


    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)       // Global Timer
    {
        ret = alt_globaltmr_int_is_enabled();
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)  // Local watchdog Timer for this CPU
    {
        if (cpu_wdog_in_gpt_mode())             // Is watchdog timer in gpt mode?
        {
            ret = alt_wdog_int_is_enabled(ALT_WDOG_CPU);
        }
    }
    if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)     // Local Private Timer for this CPU
    {
        ret = alt_read_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET) & CPU_PRIV_TMR_INT_EN;
    }
    else
    {
        if (tmr_id == ALT_GPT_OSC1_TMR0)        // Timer 0 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR0_TMR1CTLREG_ADDR;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)   // Timer 1 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR1_TMR1CTLREG_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR0)     // Timer 0 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR0_TMR1CTLREG_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)     // Timer 1 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR1_TMR1CTLREG_ADDR;
        }
        else { return ret; }                    // none of the above

        ret = (alt_read_word(regaddr) & ALT_TMR_TMR1CTLREG_TMR1_INT_MSK_SET_MSK) ? false : true;
                    // this is inverted from the private timer above
    }
    return ret;
}


/****************************************************************************************/
/* alt_gpt_int_clear_pending() clears the interrupt of the specified timer.             */
/****************************************************************************************/


ALT_STATUS_CODE alt_gpt_int_clear_pending(ALT_GPT_TIMER_t tmr_id)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;          // Return status

    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)                   // Global Timer
    {
        ret = alt_globaltmr_int_clear_pending();
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)      // Local watchdog Timer for this CPU, if it is in gpt mode
    {
        if (cpu_wdog_in_gpt_mode())                 // Is local watchdog timer in general-purpose timer mode?
        {
            ret = alt_wdog_int_clear(ALT_WDOG_CPU);
        }
    }
    else
    {
        if (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)      // Local Private Timer for this CPU
        {
            alt_write_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_INT_STATUS_REG_OFFSET, CPU_PRIV_TMR_INT_STATUS);
                        // Clear interrupt status bit by writing 0x00000001 to register
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR0)       // Timer 0 on the OSC1 bus
        {
            (void) alt_read_word(ALT_OSC1TMR0_TMRSEOI_ADDR);
                // Clear Osc1 Timer 0 interrupts by reading the timers EOI register
                // adding the void cast tells armcc not to throw a error for this usage
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)       // Timer 1 on the OSC1 bus
        {
            (void) alt_read_word(ALT_OSC1TMR1_TMRSEOI_ADDR);
                // Clear Osc1 Timer 1 interrupts by reading the timers EOI register
        }
        else if (tmr_id == ALT_GPT_SP_TMR0)         // Timer 0 on the SP bus
        {
            (void) alt_read_word(ALT_SPTMR0_TMRSEOI_ADDR);
                // Clear SP Timer 0 interrupts by reading the timers EOI register
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)         // Timer 1 on the SP bus
        {
            (void) alt_read_word(ALT_SPTMR1_TMRSEOI_ADDR);
                // Clear SP Timer 1 interrupts by reading the timers EOI register
        }
        else { return ALT_E_BAD_ARG; }              // none of the above

        ret = ALT_E_SUCCESS;
    }
    return    ret;
}


/****************************************************************************************/
/* alt_gpt_int_is_pending() returns whether or not the interrupt of the specified       */
/* timer is pending or not.                                                             */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpt_int_is_pending(ALT_GPT_TIMER_t tmr_id)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;      // Return status
    uint32_t            regmask;                // data mask
    volatile uint32_t   *regaddr;               // register address

    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)           // Global Timer
    {
        ret = alt_globaltmr_int_is_pending();
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)      // Local watchdog Timer for this CPU
    {
        if (cpu_wdog_in_gpt_mode())
        {
            ret = alt_wdog_int_is_pending(ALT_WDOG_CPU);
        }
    }
    else
    {
        if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)     // Local Private Timer for this CPU
        {
            regaddr = (uint32_t *) (CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_INT_STATUS_REG_OFFSET);
            regmask = CPU_PRIV_TMR_INT_STATUS;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR0)       // Timer 0 on the OSC1 bus
        {
            regaddr = (uint32_t *) ALT_OSC1TMR0_TMR1INTSTAT_ADDR;
            regmask = ALT_TMR_TMR1INTSTAT_TMR1INTSTAT_SET_MSK;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)       // Timer 1 on the OSC1 bus
        {
            regaddr = (uint32_t *) ALT_OSC1TMR1_TMR1INTSTAT_ADDR;
            regmask = ALT_TMR_TMR1INTSTAT_TMR1INTSTAT_SET_MSK;
        }
        else if (tmr_id == ALT_GPT_SP_TMR0)         // Timer 0 on the SP bus
        {
            regaddr = (uint32_t *) ALT_SPTMR0_TMR1INTSTAT_ADDR;
            regmask = ALT_TMR_TMR1INTSTAT_TMR1INTSTAT_SET_MSK;
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)         // Timer 1 on the SP bus
        {
            regaddr = (uint32_t *) ALT_SPTMR1_TMR1INTSTAT_ADDR;
            regmask = ALT_TMR_TMR1INTSTAT_TMR1INTSTAT_SET_MSK;
        }
        else { return    ALT_E_BAD_ARG; }           // none of the above

        ret = (alt_read_word(regaddr) & regmask) ? ALT_E_TRUE : ALT_E_FALSE;

    }
    return    ret;
}


/****************************************************************************************/
/* alt_gpt_int_if_pending_clear() clears the interrupt of the specified timer and also  */
/* returns whether it was pending before being cleared or not.                          */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpt_int_if_pending_clear(ALT_GPT_TIMER_t tmr_id)
{
    ALT_STATUS_CODE     ret = ALT_E_FALSE;              // Return status

    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)           // Global Timer
    {
        ret = alt_globaltmr_int_if_pending_clear();
    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)      // Local watchdog Timer for this CPU
    {
        if (cpu_wdog_in_gpt_mode())
        {
            ret = alt_wdog_int_if_pending_clear(ALT_WDOG_CPU);
        }
        else { ret = ALT_E_ERROR; }
    }
    else if (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)     // Local Private Timer for this CPU
    {
        if (alt_read_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_INT_STATUS_REG_OFFSET) & CPU_PRIV_TMR_INT_STATUS)                // Faster to avoid the read if possible
        {
            alt_write_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_INT_STATUS_REG_OFFSET, CPU_PRIV_TMR_INT_STATUS);
                         // Clear interrupt status bit by writing 0x00000001 to register
            ret = ALT_E_TRUE;
        }
    }
    else
    {
        if (tmr_id == ALT_GPT_OSC1_TMR0)            // Timer 0 on the OSC1 bus
        {
            if (alt_read_word(ALT_OSC1TMR0_TMR1INTSTAT_ADDR) & ALT_TMR_TMR1INTSTAT_TMR1INTSTAT_SET_MSK)
            {
                (void) alt_read_word(ALT_OSC1TMR0_TMR1EOI_ADDR);
                    // Clear Osc1 Timer 0 interrupts by reading the timer1 EOI register
                // adding the void cast tells armcc not to throw a error for this usage
                ret = ALT_E_TRUE;
            }
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)       // Timer 1 on the OSC1 bus
        {
            if (alt_read_word(ALT_OSC1TMR1_TMR1INTSTAT_ADDR) & ALT_TMR_TMR1INTSTAT_TMR1INTSTAT_SET_MSK)
            {
                (void) alt_read_word(ALT_OSC1TMR1_TMR1EOI_ADDR);
                    // Clear Osc1 Timer 1 interrupts by reading the timer1 EOI register
                ret = ALT_E_TRUE;
            }

        }
        else if (tmr_id == ALT_GPT_SP_TMR0)         // Timer 0 on the SP bus
        {
            if (alt_read_word(ALT_SPTMR0_TMR1INTSTAT_ADDR) & ALT_TMR_TMR1INTSTAT_TMR1INTSTAT_SET_MSK)
            {
                 (void) alt_read_word(ALT_SPTMR0_TMR1EOI_ADDR);
                    // Clear SP Timer 0 interrupts by reading the timer1 EOI register
                ret = ALT_E_TRUE;
            }
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)         // Timer 1 on the SP bus
        {
            if (alt_read_word(ALT_SPTMR1_TMR1INTSTAT_ADDR) & ALT_TMR_TMR1INTSTAT_TMR1INTSTAT_SET_MSK)
            {
                (void) alt_read_word(ALT_SPTMR1_TMR1EOI_ADDR);
                // Clear SP Timer 1 interrupts by reading the timer1 EOI register
                ret = ALT_E_TRUE;
            }
        }
        else { ret = ALT_E_BAD_ARG; }               // none of the above
    }
    return    ret;
}


/****************************************************************************************/
/* alt_gpt_mode_set() sets the reset mode (rollover or oneshot) of the specified timer. */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpt_mode_set(ALT_GPT_TIMER_t tmr_id, ALT_GPT_RESTART_MODE_t mode)
{
    int32_t             ret = ALT_E_ERROR;      // Return value
    uint32_t            regdata;                // value to read
    volatile uint32_t   *regaddr;               // register address


    if ((mode == ALT_GPT_RESTART_MODE_ONESHOT) || (mode == ALT_GPT_RESTART_MODE_PERIODIC))
    {
        if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)                   // Global Timer
        {
            if (mode == ALT_GPT_RESTART_MODE_PERIODIC)
            {
                ret = alt_globaltmr_autoinc_mode_start();
            }
            else
            {
                ret = alt_globaltmr_autoinc_mode_stop();
            }
        }
        else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)      // Local watchdog Timer for this CPU
        {
            ret = alt_wdog_response_mode_set(ALT_WDOG_CPU,
                    (mode == ALT_GPT_RESTART_MODE_ONESHOT) ? ALT_WDOG_TIMER_MODE_ONESHOT : ALT_WDOG_TIMER_MODE_FREERUN);
        }
        else if  (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)    // Local Private Timer for this CPU
        {
            regdata = alt_read_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET);
            regdata = (mode == ALT_GPT_RESTART_MODE_PERIODIC) ?
                    regdata | CPU_PRIV_TMR_AUTO_RELOAD : regdata & ~CPU_PRIV_TMR_AUTO_RELOAD;
            alt_write_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET, regdata);
            ret = ALT_E_SUCCESS;
        }
        else
        {
            if (tmr_id == ALT_GPT_OSC1_TMR0)            // Timer 0 on the OSC1 bus
            {
                regaddr = (volatile uint32_t *) ALT_OSC1TMR0_TMR1CTLREG_ADDR;
            }
            else if (tmr_id == ALT_GPT_OSC1_TMR1)       // Timer 1 on the OSC1 bus
            {
                regaddr = (volatile uint32_t *) ALT_OSC1TMR1_TMR1CTLREG_ADDR;
            }
            else if (tmr_id == ALT_GPT_SP_TMR0)         // Timer 0 on the SP bus
            {
                regaddr = (volatile uint32_t *) ALT_SPTMR0_TMR1CTLREG_ADDR;
            }
            else if (tmr_id == ALT_GPT_SP_TMR1)         // Timer 1 on the SP bus
            {
                regaddr = (volatile uint32_t *) ALT_SPTMR1_TMR1CTLREG_ADDR;
            }
            else { return    ALT_E_BAD_ARG; }           // none of the above

            regdata = alt_read_word(regaddr);
            regdata =  (mode == ALT_GPT_RESTART_MODE_ONESHOT) ?
                    regdata & ALT_TMR_TMR1CTLREG_TMR1_MOD_CLR_MSK :
                    regdata | ALT_TMR_TMR1CTLREG_TMR1_MOD_SET_MSK;
                    // Peripheral timers are opposite polarity as the private timer
            alt_write_word(regaddr, regdata);
            ret = ALT_E_SUCCESS;
        }
    }
    else { ret = ALT_E_BAD_ARG; }

    return    ret;
}


/****************************************************************************************/
/* alt_gpt_mode_get() returns the mode setting of the specified timer.                  */
/****************************************************************************************/

int32_t alt_gpt_mode_get(ALT_GPT_TIMER_t tmr_id)
{
    int32_t             ret = ALT_E_BAD_ARG;        // Return value
    volatile uint32_t   *regaddr;                   // register address


    if (tmr_id == ALT_GPT_CPU_GLOBAL_TMR)           // Global Timer
    {
        ret = alt_globaltmr_is_autoinc_mode() ? ALT_GPT_RESTART_MODE_PERIODIC : ALT_GPT_RESTART_MODE_ONESHOT;

    }
    else if (tmr_id == ALT_GPT_CPU_WDTGPT_TMR)      // Local watchdog Timer for this CPU
    {
        ret = alt_wdog_response_mode_get(ALT_WDOG_CPU);

        ret = (ret == ALT_WDOG_TIMER_MODE_ONESHOT) ? ALT_GPT_RESTART_MODE_ONESHOT :
                (ret == ALT_WDOG_TIMER_MODE_FREERUN) ? ALT_GPT_RESTART_MODE_PERIODIC : ALT_E_ERROR;
                        // enumeration conversion
    }
    else if (tmr_id == ALT_GPT_CPU_PRIVATE_TMR)     // Local Private Timer for this CPU
        {
            ret = (alt_read_word(CPU_PRIVATE_TMR_BASE + CPU_PRIV_TMR_CTRL_REG_OFFSET) & CPU_PRIV_TMR_AUTO_RELOAD)
                    ? ALT_GPT_RESTART_MODE_PERIODIC : ALT_GPT_RESTART_MODE_ONESHOT;
        }
    else
    {
        if (tmr_id == ALT_GPT_OSC1_TMR0)            // Timer 0 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR0_TMR1CTLREG_ADDR;
        }
        else if (tmr_id == ALT_GPT_OSC1_TMR1)       // Timer 1 on the OSC1 bus
        {
            regaddr = (volatile uint32_t *) ALT_OSC1TMR1_TMR1CTLREG_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR0)         // Timer 0 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR0_TMR1CTLREG_ADDR;
        }
        else if (tmr_id == ALT_GPT_SP_TMR1)         // Timer 1 on the SP bus
        {
            regaddr = (volatile uint32_t *) ALT_SPTMR1_TMR1CTLREG_ADDR;
        }
        else { return ret; }                        // none of the above

        ret = (alt_read_word(regaddr) & ALT_TMR_TMR1CTLREG_TMR1_MOD_SET_MSK)
                ? ALT_GPT_RESTART_MODE_PERIODIC : ALT_GPT_RESTART_MODE_ONESHOT;
    }
    return    ret;
}




