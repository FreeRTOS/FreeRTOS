/*! \file
 *  Altera - Module Description
 */

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

#ifndef __ALT_GPT_H__
#define __ALT_GPT_H__

#include <stdint.h>
#include <stdbool.h>
#include "hwlib.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */


/******************************************************************************/
/*! \addtogroup GPT_MGR The General Purpose Timer Manager API
 *
 *  There are nine on-chip general purpose timers. Seven timers are available
 *  to each CPU.\n\n
 *  There are four types of timers available:
 *     - Four general-purpose countdown timers available to CPU0, CPU1, or the
 *     FPGA.\n
 *     - Each CPU has a private GP countdown timer available only to itself.\n
 *     - Each CPU has a watchdog timer  available only to itself that can work in
 *     GP timer countdown mode.\n
 *     - One continuous-countup global timer with compare capabilities available to
 *     both CPUs and the FPGA.\n\n
 *     Each type has a somewhat different HW interface This API presents the same
 *     external interface for each.
 *
 * @{
 */

/******************************************************************************/
/*!
 * This type definition enumerates the names of the timers
 * managed by the General Purpose Timers Manager.
 */
typedef enum ALT_GPT_TIMER_e
{
     /*!
      * \b CPU_GLOBAL_TMR - CPU Core Global timer - There is one 64-bit
      * continuously incrementing counter for all CPU cores that is clocked
      * by PERIPHCLK. CPU_GLOBAL_TMR selects the comparator value, compare
      * enable, autoincrement value, autoincrement enable, and interrupt
      * enable for the CPU this code is running on.
      */
    ALT_GPT_CPU_GLOBAL_TMR,

    /*!
     * \b CPU_PRIVATE_TMR - CPU Core 32-bit Private Timer - The private timer
     * for the CPU this code is running on. Clocked by PERIPHCLK. Counts
     * down to zero and can either stop or restart.
     */
    ALT_GPT_CPU_PRIVATE_TMR,

    /*!
     * \b CPU_WDTGPT_TMR - CPU Core 32-bit Watchdog Timer - The watchdog
     * timer can be used as a general-purpose timer by calling
     * alt_wdt_response_mode_set() to put the watchdog timer in general-purpose
     * timer mode. It is recommended that programmers use the other available
     * timers first before using the watchdog timer as there is more software
     * overhead involved in using the watchdog timer in this mode. This enum is
     * for the core watchdog timer of the CPU this code is running on. Counts
     * down to zero and can either stop or restart.
     */
    ALT_GPT_CPU_WDTGPT_TMR,

    /* Peripheral Timers */
    /* OSC1 Clock Group */
    /*!
     * \b osc1_timer0 - 32-bit timer connected to the L4_OSC1 bus clocked by
     * osc1_clk. Counts down to zero and can either stop or restart.
     */
    ALT_GPT_OSC1_TMR0,

    /*!
     * \b osc1_timer1 - 32-bit timer connected to the L4_OSC1 bus clocked by
     * osc1_clk. Counts down to zero and can either stop or restart.
     */
    ALT_GPT_OSC1_TMR1,

    /* L4_SP Clock Group */
    /*!
     * \b sp_timer0 - 32-bit timer connected to the L4_SP bus clocked by
     * l4_sp_clk. Counts down to zero and can either stop or restart.
     */
    ALT_GPT_SP_TMR0,

    /*!
     * \b sp_timer1 - 32-bit timer connected to the L4_SP bus clocked by
     * l4_sp_clk. Counts down to zero and can either stop or restart.
     */
    ALT_GPT_SP_TMR1

}  ALT_GPT_TIMER_t;


/*!
 * This type definition enumerates the possible rollover or restart modes
 * of the general purpose timers.
 */
typedef enum ALT_GPT_RESTART_MODE_e
{
     /*!
     * \b ONE-SHOT \b MODE - \b CPU_PRIVATE_TMR,
     * \b OSC1_TMR0, \b OSC1_TMR1, \b SP_TMR0, and \b SP_TMR1
     * count down from the value set with alt_gpt_counter_set() to
     * zero, trigger an interrupt and stop.\n
     * The global timer \b CPU_GLOBAL_TMR counts up to the next compare value
     * set by the compare value, triggers an interrupt and stops
     * comparing.
     */
     ALT_GPT_RESTART_MODE_ONESHOT,

    /*!
     * \b USER-SUPPLIED \b COUNT - For \b CPU_PRIVATE_TMR,  \b OSC1_TMR0,
     * \b OSC1_TMR1, \b SP_TMR0, and \b SP_TMR1, the timer counts down
     * to zero and then resets to a value previously set using
     * alt_gpt_counter_set() and continues counting.\n
     * \b CPU_GLOBAL_TMR counts up to the comparator value, then adds
     * the value set in alt_gpt_counter_set() to the comparator value and
     * continues counting.
     */
     ALT_GPT_RESTART_MODE_PERIODIC

} ALT_GPT_RESTART_MODE_t;


/******************************************************************************/
/*! \addtogroup GPT_STATUS Enable, Disable, and Status
 *
 * This functional group handles enabling, disabling, and reading the
 * current enable state of the general purpose timers and the global timer.
 *
 * @{
 */
/******************************************************************************/
/*! Uninitialize all of the general-purpose timer modules
 *
 */
ALT_STATUS_CODE alt_gpt_all_tmr_uninit(void);

/******************************************************************************/
/*! Initialize all of the general-purpose timer modules
 *
 */
ALT_STATUS_CODE alt_gpt_all_tmr_init(void);

/******************************************************************************/
/*!
 * Stop and disable the specified general purpose timer or global timer.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Tried to stop an invalid timer.
 */
ALT_STATUS_CODE alt_gpt_tmr_stop(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Enable and start the specified general purpose timer or global timer.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Tried to start an invalid timer.
 */
ALT_STATUS_CODE alt_gpt_tmr_start(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Returns whether the specified timer is currently running or not.
 * For the free-running 64-bit global timer, returns whether its comparison
 * mode is enabled or not.
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      ALT_E_TRUE      The timer is currently enabled and running.
 * \retval      ALT_E_FALSE     The timer is currently disabled and stopped.
 * \retval      ALT_E_BAD_ARG   Tried to access an invalid timer.
 */
ALT_STATUS_CODE alt_gpt_tmr_is_running(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Restarts the specified general purpose timer with its original value. If
 * used for the global timer, it updates the comparator value with the sum of
 * the auto-increment value and the current global timer value and enables
 * comparison mode.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Tried to access an invalid timer.
 */
ALT_STATUS_CODE alt_gpt_tmr_reset(ALT_GPT_TIMER_t tmr_id);


/*! @} */
/******************************************************************************/
/*! \addtogroup GPT_COUNTER Counters Interface
 *
 * This functional group handles setting and reading the general purpose
 * timer counters and the global timer.
 *
 * @{
 * */
/******************************************************************************/
/*!
 * For tmr_id = \b CPU_PRIVATE_TMR, \b OSC1_TMR0, \b
 * OSC1_TMR1, \b SP_TMR0, or \b SP_TMR1, sets the countdown value of the
 * specified timer and the value that the counter will reset to (in rollover
 * mode) or if restarted (in one-shot mode). It does not automatically start
 * the counter. \n For tmr_id = \b CPU_GLOBAL_TMR,
 * this function sets the auto-increment value instead, which is similar in
 * function to setting the reset value of the other timers. The effect of this
 * function is identical to using alt_globaltmr_autoinc_set().
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \param       val
 *              The 32-bit counter value to load.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_gpt_counter_set(ALT_GPT_TIMER_t tmr_id,
        uint32_t val);

/******************************************************************************/
/*!
 * For tmr_id = \b CPU_PRIVATE_TMR, \b OSC1_TMR0, \b
 * OSC1_TMR1, \b SP_TMR0, or \b SP_TMR1, returns the current counter value of
 * the specified timer. \n For tmr_id = \b CPU_GLOBAL_TMR, returns the 32
 * low-order bits of the counter and is identical to the result returned by
 * alt_globaltmr_counter_get_low32(). Use alt_globaltmr_get() to obtain the full
 * 64-bit timer value.
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 *
 * \retval      uint32_t     The current 32-bit counter value.
 */
uint32_t alt_gpt_counter_get(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * For tmr_id = \b CPU_PRIVATE_TMR, \b OSC1_TMR0, \b
 * OSC1_TMR1, \b SP_TMR0, or \b SP_TMR1, returns the counter value that is
 * set to be reloaded when the specified timer hits zero. \n
 * For tmr_id =  \b CPU_GLOBAL_TMR, returns the value that will
 * autoincrement the comparator value, which defines the time until the next
 * comparator interrupt is triggered.  This is similar in function to the
 * reset value of the other timers. It is identical to the result returned by
 * alt_globaltmr_autoinc_get(). \n The value returned does not take into
 * CPU_PRIVATE_TMR and  \b CPU_GLOBAL_TMR. The prescaler value may be obtained
 * with alt_gpt_prescaler_get().
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 *
 * \retval      uint32_t    The reset counter value currently set.
 * \retval      0           An error occurred.
 */
uint32_t alt_gpt_reset_value_get(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Returns the maximum counter value available for the specified
 * timer. Valid for \b CPU_PRIVATE_TMR, \b OSC1_TMR0,
 * \b OSC1_TMR1, \b SP_TMR0, \b SP_TMR1, and \b CPU_GLOBAL_TMR. \n
 * The value returned does not factor in the value of the clock prescaler
 * available for \b CPU_PRIVATE_TMR and \b CPU_GLOBAL_TMR.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 *
 * \retval      uint32_t    The maximum counter value available for this timer.
 * \retval      0           An error occurred.
 *
 */
uint32_t alt_gpt_maxcounter_get(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Sets the clock prescaler value of the specified timer. Valid for \b
 * CPU_PRIVATE_TMR and \b CPU_GLOBAL_TMR. Returns an error
 * if called with a tmr_id of \b OSC1_TMR0,
 * \b OSC1_TMR1, \b SP_TMR0, or \b SP_TMR1 since they have no prescaler.
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \param       val
 *              The 32-bit prescaler value to load. Valid range is 1-256.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_gpt_prescaler_set(ALT_GPT_TIMER_t tmr_id,
        uint32_t val);

/******************************************************************************/
/*!
 * Returns the clock prescaler value of the specified timer. Valid for \b
 * CPU_PRIVATE_TMR and \b CPU_GLOBAL_TMR. Returns one if
 * called with a tmr_id of \b OSC1_TMR0, \b
 * OSC1_TMR1, \b SP_TMR0, or \b SP_TMR1 since they have no prescaler.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      uint32_t    The prescaler value. Valid range is 1-256.
 *                             Zero indicates an error.
 */
uint32_t alt_gpt_prescaler_get(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Returns the integer portion of the current countdown frequency of the
 * specified timer.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      unint32_t    The integer portion of the repeat frequency of the
 *                             given timer, measured in Hertz (cycles per second).
 */
uint32_t alt_gpt_freq_get(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Returns the current period of the specified timer measured in seconds.
 * If the result is less than 64, alt_gpt_millisecs_get() will give a more
 * precise result.
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      uint32_t      The current period of the given timer, measured
 *                         in seconds.
 */
uint32_t alt_gpt_time_get(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Returns the current period of the specified timer measured in milliseconds.
 *
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      uint32_t      The current period of the given timer, measured
 *                         in milliseconds. Returns 0 if result cannot fit
 *                         in 32 bits. alt_gpt_time_get() can be used to
 *                         obtain measurements of longer periods.
 *                         alt_gpt_microsecs_get() can be used to obtain
 *                         more precise measurements of shorter periods.
 */
uint32_t alt_gpt_time_millisecs_get(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Returns the current period of the specified timer measured in milliseconds.
 *
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      uint32_t      The current period of the given timer, measured
 *                         in microseconds. Returns 0 if result cannot fit
 *                         in 32 bits. alt_gpt_millisecs_get() and
 *                         alt_gpt_time_get() can be used to obtain
 *                         measurements of longer periods.
 */
uint32_t alt_gpt_time_microsecs_get(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Returns the current time until the specified timer counts
 * down to zero, measured in seconds.
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 *
 * \retval      uint32_t     The current 32-bit counter value.
 */
uint32_t alt_gpt_curtime_get(ALT_GPT_TIMER_t tmr_id);


/******************************************************************************/
/*!
 * Returns the current time until the specified timer counts
 * down to zero, measured in milliseconds. \n Returns 0xFFFFFFFF if the value
 * is too large to be expressed in 32 bits.
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 *
 * \retval      uint32_t     The current 32-bit counter value.
 */
uint32_t alt_gpt_curtime_millisecs_get(ALT_GPT_TIMER_t tmr_id);


/******************************************************************************/
/*!
 * Returns the current time until the specified timer counts
 * down to zero, measured in microseconds. \n Returns  0xFFFFFFFF if the value
 * is too large to be expressed in 32 bits.
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 *
 * \retval      uint32_t     The current 32-bit counter value.
 */
uint32_t alt_gpt_curtime_microsecs_get(ALT_GPT_TIMER_t tmr_id);


/******************************************************************************/
/*!
 * Returns the current time until the specified timer counts
 * down to zero, measured in nanoseconds. \n Returns  0xFFFFFFFF if the value
 * is too large to be expressed in 32 bits.
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 *
 * \retval      uint32_t     The current 32-bit counter value.
 */
uint32_t alt_gpt_curtime_nanosecs_get(ALT_GPT_TIMER_t tmr_id);


/******************************************************************************/
/*!
 * Returns the maximum available period of the specified
 * timer measured in seconds.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      uint32_t      The maximum period of the given timer, measured
 *                         in seconds. Returns 0 if result cannot fit
 *                         in 32 bits.
 */
uint32_t alt_gpt_maxtime_get(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Returns the maximum available period of the specified
 * timer measured in milliseconds.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      uint32_t      The maximum period of the given timer, measured
 *                         in milliseconds. Returns 0 if result cannot fit
 *                         in 32 bits.
 */
uint32_t alt_gpt_maxtime_millisecs_get(ALT_GPT_TIMER_t tmr_id);

/*! @} */

/******************************************************************************/
/*! \addtogroup GPT_INT Interrupts
 * This functional group handles managing, setting, clearing, and disabling
 * the interrupts of the general purpose timers and the global timer.
 * @{  */
/******************************************************************************/
/*!
 * Disables the interrupt from the specified general purpose timer or
 * global timer module.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_gpt_int_disable(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Enables the interrupt of the specified general purpose timer or global
 * timer module.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_gpt_int_enable(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Return \b TRUE if the interrupt of the specified timer module is enabled
 * and \b FALSE if the interrupt is disabled or masked.
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      TRUE            The timer interrupt is currently enabled.
 * \retval      FALSE           The timer interrupt is currently disabled.
 */
bool alt_gpt_int_is_enabled(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Clear the pending interrupt status of the specified timer module.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_gpt_int_clear_pending(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Read the state (pending or not) of the interrupt of the specified timer
 * module without changing the interrupt state.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      ALT_E_TRUE            The timer interrupt is currently pending.
 * \retval      ALT_E_FALSE           The timer interrupt is not currently pending.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_gpt_int_is_pending(ALT_GPT_TIMER_t tmr_id);

/******************************************************************************/
/*!
 * Read the state of the interrupt of the specified general purpose timer
 * module and if the interrupt is set, clear it.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      ALT_E_TRUE            The timer interrupt is currently pending.
 * \retval      ALT_E_FALSE           The timer interrupt is not currently pending.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_gpt_int_if_pending_clear(ALT_GPT_TIMER_t tmr_id);
/*! @} */

/******************************************************************************/
/*! \addtogroup GPT_MODE Mode Control
 * This functional group handles setting and reading the operational mode of
 * the general purpose timers. The module version ID read function is also
 * located here.
 * @{
 */
/******************************************************************************/
/*!
 * Sets the mode of the specified timer, the behavior that occurs when either
 * the general-purpose timer counts down to zero or when the the global timer
 * reaches its comparator value.
 *
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \param       mode
 *              \b GPT_RESTART_MODE_ONESHOT - To select one-shot mode for
 *              the timer.
 * \n           \b GPT_RESTART_MODE_PERIODIC - To select free-run mode for
 *              the timer.
 *
 * \internal
 *   The HHP HPS Timer NPP states that the value of the counter (Timer1LoadCount
 *   register) must be set to 0xFFFFFFFF before changing this setting to free-
 *   running mode (and timer must be disabled). The relevent L4 peripheral
 *   document does not mention the requirement to write 0xFFFFFFFF to the
 *   Timer1LoadCount register though.
 * \endinternal
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_gpt_mode_set(ALT_GPT_TIMER_t tmr_id,
        ALT_GPT_RESTART_MODE_t mode);

/******************************************************************************/
/*!
 * Reads the mode of the specified timer.
 *
 * \param       tmr_id
 *              The timer identifier.
 *
 * \retval      GPT_RESTART_MODE_ONESHOT    Timer is set to one-shot mode.
 * \retval      GPT_RESTART_MODE_PERIODIC   Counter value is set to a
 *                                              user-defined value.
 * \retval      ALT_E_BAD_ARG               Invalid input argument.
 */
int32_t alt_gpt_mode_get(ALT_GPT_TIMER_t tmr_id);

/*! @} */
/*! @} */
/*! @} */
/*! @} */

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALT_GPT_H__ */
