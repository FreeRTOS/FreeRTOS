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

#ifndef __ALT_GBLTMR_H__
#define __ALT_GBLTMR_H__

#include <stdint.h>
#include <stdbool.h>
#include "hwlib.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */


/******************************************************************************/
/*! \addtogroup GBLTMR_MGR The Global Timer Manager API
 *
 * This functional group handles setting and reading various parameters of the
 * global 64-bit incrementing counter. There is one 64-bit continuously
 * incrementing counter for all CPU cores and it is clocked by PERIPHCLK.
 * This section manages the comparator value, compare enable,
 * auto-increment value, auto-increment enable, and interrupt enable for the
 * CPU that this code is running on (referenced as \b CPU_GLOBAL_TMR).
 * @{
 */
/******************************************************************************/
/*! Uninitialize the Global timer module
 *
 */
ALT_STATUS_CODE alt_globaltmr_uninit(void);

/******************************************************************************/
/*! Initialize the Global timer module
 *
 */
ALT_STATUS_CODE alt_globaltmr_init(void);

/******************************************************************************/
/*!
 * Stops the global timer counter compare function for this CPU and disables
 * its interrupt. It does
 * not stop the global timer itself. This function is identical to calling
 * \b alt_gpt_tmr_stop() with a tmr_id of \b CPU_GLOBAL_TMR.
 *
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_globaltmr_stop(void);

/******************************************************************************/
/*!
 * Starts the global timer compare function for this CPU, enables its interrupt
 * function and, if free-running mode is selected also enables its
 * auto-increment function. If the global timer is not yet running, it starts
 * the timer. This function is identical to calling \b alt_gpt_tmr_start()
 * with a tmr_id of \b CPU_GLOBAL_TMR.
 *
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_globaltmr_start(void);

/******************************************************************************/
/*!
 * Returns the current counter value of the 64-bit global timer.
 *
 *
 * \param       highword
 *              Location used to return the most significant 32-bit word of
 *              the current global timer count.
 * \param       lowword
 *              Location used to return the least significant 32-bit word
 *              of the current global timer count.
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_globaltmr_get(uint32_t* highword, uint32_t* lowword);

/******************************************************************************/
/*!
 * Returns the current counter value of the 64-bit global timer. This function
 * is identical to alt_globaltmr_get() except that the value is returned as a
 * 64-bit unsigned integer rather than as two 32-bit words.
 *
 *
 *
 * \retval      uint64_t
 *              The current value of the 64-bit counter.
 */
uint64_t alt_globaltmr_get64(void);

/******************************************************************************/
/*!
 * Returns the 32 low-order bits of the global timer. This
 * is identical to calling \b alt_gpt_counter_get() with a tmr_id equal
 * to \b CPU_GLOBAL_TMR. Use alt_globaltmr_get()  or alt_globaltmr_get64() to
 * obtain the full 64-bit timer value.
 *
 *
 *
 * \retval      uint32_t The current 32-bit counter value.
 */
uint32_t alt_globaltmr_counter_get_low32(void);

/******************************************************************************/
/*!
 * Returns the 32 higher-order bits of the global timer. Use alt_globaltmr_get()
 * or alt_globaltmr_get64() to obtain the full 64-bit timer value.
 *
 *
 *
 * \retval      uint32_t The current 32-bit counter value.
 */
uint32_t alt_globaltmr_counter_get_hi32(void);

/******************************************************************************/
/*!
 * Sets the value of the 64-bit global timer comparator for this CPU. The
 * global timer increments its count and when it reaches this value or above,
 * it triggers the following actions. If the interrupt is enabled, it forwards
 * an interrupt request to the core. If free-run mode is selected, it adds the
 * auto-increment value to the value of the global counter and the resulting
 * sum is saved as the new comparator value.
 *
 *
 * \param       highword
 *              The 32 MSBits of the new comparator value.
 * \param       loword
 *              The 32 LSBits of the new comparator value.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_globaltmr_comp_set(uint32_t highword, uint32_t loword);

/******************************************************************************/
/*!
 * Sets the value of the 64-bit global timer comparator for this CPU. The
 * global timer increments its count and when it reaches this value or above,
 * it triggers the following actions. If the interrupt is enabled, it forwards
 * an interrupt request to the core. If free-run mode is selected, it adds the
 * auto-increment value to the value of the global counter and the resulting
 * sum is saved as the new comparator value.
 *
 *
 * \param       compval
 *              The new comparator value to set.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_globaltmr_comp_set64(uint64_t compval);

/******************************************************************************/
/*!
 * Returns the current 64-bit global timer comparator value  for this CPU. The
 * global timer increments its count and when it reaches this value or above,
 * it triggers the following actions. If the interrupt is enabled, it forwards
 * an interrupt request to the core. If free-run mode is selected, it adds the
 * auto-increment value to the value of the global counter and the resulting
 * sum is saved as the new comparator value. This value will increase by the
 * auto-increment value each time the global timer reaches the comparator
 * value.
 *
 *
 * \param       highword
 *              Pointer to location to store the 32 MSBits of the comparator value.
 * \param       lowword
 *              Pointer to location to store the 32 LSBits of the comparator value.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_globaltmr_comp_get(uint32_t *highword, uint32_t *lowword);

/******************************************************************************/
/*!
 * Returns the current 64-bit global timer comparator value  for this CPU. The
 * global timer increments its count and when it reaches this value or above,
 * it triggers the following actions. If the interrupt is enabled, it forwards
 * an interrupt request to the core. If free-run mode is selected, it adds the
 * auto-increment value to the value of the global counter and the resulting
 * sum is saved as the new comparator value. This value will increase by the
 * auto-increment value each time the global timer reaches the comparator
 * value. This function is identical to alt_globaltmr_comp_get() except that the
 * value is returned in a 64-bit unsigned integer rather than as two 32-bit
 * words.
 *
 *
 * \retval      uint64_t
 *              The 64-bit value of the global timer comparator.
 */
uint64_t alt_globaltmr_comp_get64(void);


/******************************************************************************/
/*!
 * Enables the comparison function of the global timer for this CPU.
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_globaltmr_comp_mode_start(void);

/******************************************************************************/
/*!
 * Disables the comparison function of the global timer for this CPU.
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_globaltmr_comp_mode_stop(void);

/******************************************************************************/
/*!
 * Returns the comparison mode selection of the global
 * timer for this CPU.
 *
 *
 * \retval      FALSE           Comparison mode is not enabled.
 * \retval      TRUE            Comparison mode is enabled.
 */
bool alt_globaltmr_is_comp_mode(void);


/******************************************************************************/
/*!
 * Returns the clock prescaler value of the global timer.
 *
 *
 * \retval      uint32_t    The prescaler value. Valid range is 0-255.
 *                          Actual clock divisor ratio is this number plus one.
 */
uint32_t alt_globaltmr_prescaler_get(void);


/******************************************************************************/
/*!
 * Sets the clock prescaler value of the global timer.
 *
 *
 * \param       val
 *              The 8-bit prescaler value to load. Valid range is 0-255.
 *              Actual clock divisor ratio is this number plus one.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_globaltmr_prescaler_set(uint32_t val);

/******************************************************************************/
/*!
 * Sets a 32-bit global timer auto-increment value in the global
 * timer block for this CPU. The global timer continually increments its count
 * and when it reaches the value set in the comparator register or above, if
 * both comparison and free-run modes are selected, it adds the value set by this
 * function to the comparator value and saves it as the new comparator value.
 * This count then sets the time delay until the next global timer compare
 * value is reached.
 *
 *
 * \param       inc
 *              Auto-increment value to set.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_globaltmr_autoinc_set(uint32_t inc);

/******************************************************************************/
/*!
 * Returns the global timer auto-increment value for this CPU. When the global
 * timer reaches the comparator value, if both comparison and free-run modes
 * are selected this value is added to the previous comparator value and saved
 * as the new comparator value.
 *
 *
 * \retval      uint32_t
 *              The current comparator auto-increment value.
 */
uint32_t alt_globaltmr_autoinc_get(void);

/******************************************************************************/
/*!
 * Enables the auto-increment function of the global timer for this CPU.
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_globaltmr_autoinc_mode_start(void);

/******************************************************************************/
/*!
 * Disables the auto-increment function of the global timer for this CPU.
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_globaltmr_autoinc_mode_stop(void);

/******************************************************************************/
/*!
 * Returns the auto-increment selection of the global timer for this CPU.
 *
 *
 * \retval      FALSE           Auto-increment mode is not enabled.
 * \retval      TRUE            Auto-increment mode is enabled.
 */
bool alt_globaltmr_is_autoinc_mode(void);

/******************************************************************************/
/*!
 * Returns the maximum counter value available for \b CPU_GLOBAL_TMR. \n
 * The value returned does not factor in the value of the clock prescaler.
 *
 *
 *
 *
 * \retval      uint32_t    The maximum counter value available for this timer.
 * \retval      0           An error occurred.
 *
 */
uint32_t alt_globaltmr_maxcounter_get(void);

/******************************************************************************/
/*!
 * Disables the interrupt from the global timer module. Identical to calling
 * alt_gpt_int_disable() with tmr_id of \b CPU_GLOBAL_TMR.
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_globaltmr_int_disable(void);

/******************************************************************************/

#if 0
/*!
 *
 * Enables the interrupt of the global timer
 * module. Identical to calling alt_gpt_int_enable() with tmr_id of
 * \b CPU_GLOBAL_TMR. If global timer is not already running, this function
 * returns an error.
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_globaltmr_int_enable(void);

#else
/*!
 *
 * Enables the interrupt of the global timer
 * module. Identical to calling alt_gpt_int_enable() with tmr_id of
 * \b CPU_GLOBAL_TMR. If global timer is not already running, this function
 * attempts to start it.
 *
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_globaltmr_int_enable(void);

#endif

/******************************************************************************/
/*!
 * Return \b TRUE if the interrupt of the global timer module is enabled
 * and \b FALSE if the interrupt is disabled or masked. Identical to calling
 * alt_gpt_int_is_enabled() with tmr_id of
 * \b CPU_GLOBAL_TMR.
 *
 * \internal - note that there's more to this than just enabling the
 * interrupt and clearing the status.
 * \endinternal
 *
 *
 * \retval      TRUE            The timer interrupt is currently enabled.
 * \retval      FALSE           The timer interrupt is currently disabled.
 */
bool alt_globaltmr_int_is_enabled(void);

/******************************************************************************/
/*!
 * Clear the pending interrupt status of the global timer module. Identical to
 * calling alt_gpt_int_clear_pending() with tmr_id of
 * \b CPU_GLOBAL_TMR.
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_globaltmr_int_clear_pending(void);

/******************************************************************************/
/*!
 * Read the state (pending or not) of the interrupt of the global timer
 * module without changing the interrupt state. Identical to
 * calling alt_gpt_int_is_pending() with tmr_id of
 * \b CPU_GLOBAL_TMR.
 *
 *
 *
 * \retval      TRUE            The timer interrupt is currently pending.
 * \retval      FALSE           The timer interrupt is not currently pending.
 */
bool alt_globaltmr_int_is_pending(void);

/******************************************************************************/
/*!
 * Read the state of the interrupt of the global timer
 * module and if the interrupt is set, clear it. Identical to
 * calling alt_gpt_int_is_pending_and_clear()  with tmr_id of
 * \b CPU_GLOBAL_TMR.
 *
 *
 *
 * \retval      TRUE            The timer interrupt was pending.
 * \retval      FALSE           The timer interrupt was not pending.
 */
bool alt_globaltmr_int_if_pending_clear(void);

/*! @} */
/*! @} */
/*! @} */

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALT_GBLTMR_H__ */
