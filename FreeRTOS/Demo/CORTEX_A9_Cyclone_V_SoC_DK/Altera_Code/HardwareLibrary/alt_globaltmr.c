
/******************************************************************************
*
* alt_globaltmr.c - API for the Altera SoC FPGA global timer.
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



#include    <stdlib.h>
#include    <stdint.h>
#include    <stdbool.h>
#include    "socal/hps.h"
#include    "socal/socal.h"
#include    "hwlib.h"
#include    "alt_mpu_registers.h"
#include    "alt_globaltmr.h"
#include    "alt_clock_manager.h"                    // for getting clock bus frequency



/************************************************************************************************************/

/************************************************************************************************************/
/*  The global timer is common to both ARM CPUs and also to the FPGA fabric.There is no good way to know what
    effect halting the global timer might have on the other ARM CPU. It was decided that once the global
    timer was started, there should not be a way included in this API to halt it. It is possible to achieve
    much of the same effect by disabling the global timer comparison functionality instead. The global timer
    has hardware that can automatically add the count value to the current value of the global timer when
    the timer reaches the comparison value.
*/
/************************************************************************************************************/



/*************************************************************************************************************
 * alt_globaltmr_is_running() is an internal function, not published in the API.
 * It checks and returns the state of the enable bit of the global timer but doesn't check the comparison
 * mode bit.
*************************************************************************************************************/

bool alt_globaltmr_is_running(void)
{
    return alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET) & GLOBALTMR_ENABLE_BIT;
}


/****************************************************************************************/
/* alt_globaltmr_uninit() uninitializes the global timer modules                        */
/****************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_uninit(void)
{
    alt_clrbits_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET,
                GLOBALTMR_COMP_ENABLE_BIT | GLOBALTMR_INT_ENABLE_BIT |
                GLOBALTMR_AUTOINC_ENABLE_BIT);
            // do NOT clear the global timer enable bit or prescaler setting
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_COMP_LO_REG_OFFSET, 0);
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_COMP_HI_REG_OFFSET, 0);
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_AUTOINC_REG_OFFSET, 0);
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_INT_STAT_REG_OFFSET, GLOBALTMR_INT_STATUS_BIT);
                /* clear any interrupts by writing one to sticky bit */
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* alt_globaltmr_init() initializes the global timer module                             */
/****************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_init(void)
{
    alt_globaltmr_uninit();
    alt_setbits_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET, GLOBALTMR_ENABLE_BIT);
    return ALT_E_SUCCESS;
}

/*************************************************************************************************************
 * alt_globaltmr_stop() doesn't actually stop the global timer, instead it stops the virtual representation
 * of the global timer as a typical countdown timer. The timer will no longer compare the global timer value
 * to the global timer compare value, will not auto-increment the comparator value, and will not set the
 * interrupt.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_stop(void)
{
    uint32_t        regdata;                // value to read & write

    regdata = alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET);
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET, regdata & ~GLOBALTMR_COMP_ENABLE_BIT);
    return ALT_E_SUCCESS;
}


/*************************************************************************************************************
 * alt_globaltmr_start() sets the comparison mode of the global timer, allowing it to be used as a typical
 * countdown timer. If auto-increment mode is enabled, it will operate as a free-running timer.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_start(void)
{
    uint32_t        regdata;                // value to read & write

    regdata = alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET);
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET, regdata | (GLOBALTMR_COMP_ENABLE_BIT | GLOBALTMR_ENABLE_BIT));
    return ALT_E_SUCCESS;
}


/*************************************************************************************************************
 * alt_globaltmr_get() returns the current value of the 64-bit global timer as two unsigned 32-bit quantities.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_get(uint32_t* highword, uint32_t* loword)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;
    uint32_t            hi, lo, temp;                   // temporary variables
    uint32_t            cnt = 3;                        // Timeout counter, do 3 tries

    if ((highword == NULL) || (loword == NULL)) { ret = ALT_E_BAD_ARG; }
    else
    {
        hi = alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CNTR_HI_REG_OFFSET);
        do {
            temp = hi;
            lo = alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CNTR_LO_REG_OFFSET);
            hi = alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CNTR_HI_REG_OFFSET);
        }  while ((temp != hi) && (cnt--));             // has the high-order word read the same twice yet?
                       // note that if the first condition is true, cnt is neither tested nor decremented

        if (cnt) {
            *highword = hi;
            *loword = lo;
            ret = ALT_E_SUCCESS;
        }
    }
    return ret;
}


/*************************************************************************************************************
 * alt_globaltmr_get64() returns the current value of the global timer as an unsigned 64-bit quantity.
*************************************************************************************************************/

uint64_t  alt_globaltmr_get64(void)
{

    uint64_t        ret = 0;                    // zero a very unlikely value for this timer
    uint32_t        hi, lo, temp;               // temporary variables
    uint32_t        cnt = 3;                    // Timeout counter, do 3 tries

    hi = alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CNTR_HI_REG_OFFSET);
    do {
        temp = hi;
        lo = alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CNTR_LO_REG_OFFSET);
        hi = alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CNTR_HI_REG_OFFSET);
    }  while ((temp != hi) && (cnt--));             // has the high-order word read the same twice yet?
                        // note that if the first condition is true, cnt is neither tested nor decremented

    if (cnt)
    {
        ret = (uint64_t) hi;
        ret = (ret << (sizeof(uint32_t)*8)) | lo;
    }
    return ret;
}


/*************************************************************************************************************
 * alt_globaltmr_counter_get_low32() returns the least-significant 32 bits of the current global timer value.
*************************************************************************************************************/

uint32_t alt_globaltmr_counter_get_low32(void)
{
    return alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CNTR_LO_REG_OFFSET);

}


/*************************************************************************************************************
 * alt_globaltmr_counter_get_hi32() returns the most-significant 32 bits of the current global timer value.
*************************************************************************************************************/

uint32_t alt_globaltmr_counter_get_hi32(void)
{
    return alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CNTR_HI_REG_OFFSET);
}


/*************************************************************************************************************
 * alt_globaltmr_comp_set() writes the 64-bit comparator register with two 32-bit words.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_comp_set(uint32_t highword, uint32_t loword)
{
    bool                was_comping = false;
    ALT_STATUS_CODE     ret = ALT_E_ERROR;

    if (alt_globaltmr_is_comp_mode())                   // necessary to prevent a spurious interrupt
    {
        was_comping = true;
        ret = alt_globaltmr_comp_mode_stop();
        if (ret != ALT_E_SUCCESS)   { return ret; }
    }
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_COMP_LO_REG_OFFSET, loword);
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_COMP_HI_REG_OFFSET, highword);
    ret = ALT_E_SUCCESS;

    if (was_comping)  { ret = alt_globaltmr_comp_mode_start(); }
                // If global timer was in comparison mode before, re-enable it before returning
    return    ret;
}


/*************************************************************************************************************
 * alt_globaltmr_comp_set64() writes the 64-bit comparator register with the supplied 64-bit value.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_comp_set64(uint64_t compval)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;
    bool                was_comping = false;

    if (alt_globaltmr_is_comp_mode())
    {
        was_comping = true;
        ret = alt_globaltmr_comp_mode_stop();
        if (ret != ALT_E_SUCCESS)   { return ret; }
    }

    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_COMP_LO_REG_OFFSET, (uint32_t) (compval & UINT32_MAX));
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_COMP_HI_REG_OFFSET,
                (uint32_t) ((compval >> (sizeof(uint32_t)*8)) & UINT32_MAX));
    ret = ALT_E_SUCCESS;

    if (was_comping)  { ret = alt_globaltmr_comp_mode_start(); }
                                // If global timer was in comparison mode before, re-enable it
    return    ret;
}


/*************************************************************************************************************
 * alt_globaltmr_comp_get() returns the 64 bits of the current global timer comparator value via two
 * uint32_t pointers.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_comp_get(uint32_t *hiword, uint32_t *loword)
{
    if ((hiword == NULL) || (loword == NULL)) {return ALT_E_ERROR; }
    *loword = alt_read_word(GLOBALTMR_BASE + GLOBALTMR_COMP_LO_REG_OFFSET);
    *hiword = alt_read_word(GLOBALTMR_BASE + GLOBALTMR_COMP_HI_REG_OFFSET);
    /* no need to read these multiple times since the register is not expected to change mid-read */
    return    ALT_E_SUCCESS;
}


/*************************************************************************************************************
 * alt_globaltmr_comp_get64() returns all 64 bits of the current global timer comparator value.
*************************************************************************************************************/

uint64_t alt_globaltmr_comp_get64(void)
{
    uint64_t        ret;

    ret = ((uint64_t) alt_read_word(GLOBALTMR_BASE + GLOBALTMR_COMP_HI_REG_OFFSET)) << (sizeof(uint32_t)*8);
    ret = ret | ((uint64_t) alt_read_word(GLOBALTMR_BASE + GLOBALTMR_COMP_LO_REG_OFFSET));
    return ret;
}


/*************************************************************************************************************
 *  alt_globaltmr_remain_get64() returns a 64-bit quantity that represents the difference between the
 *  current comparator value and the current global timer value. If the comparator register was updated by
 *  the autoincrement circuitry (and the global timer has not subsequently crossed over the comparator
 *  value a second time), this difference will always be expressable in 32 bits. If the user has manually
 *  set the comparator value, however, this may not be true and more than 32 bits may be required to express
 *  the difference.
*************************************************************************************************************/

#define alt_globaltmr_remain_get64()   (alt_globaltmr_comp_get64() - alt_globaltmr_get64())



/*************************************************************************************************************
 *  alt_globaltmr_remain_get() returns a 32-bit quantity that represents the difference between the
 *  current comparator value and the current global timer value. If the comparator register was updated by
 *  the autoincrement circuitry (and the global timer has not subsequently crossed over the comparator
 *  value a second time), this difference will always be expressable in 32 bits. If the user has manually
 *  set the comparator value, however, this may not be true and more than 32 bits may be required to express
 *  the difference.
*************************************************************************************************************/

uint32_t alt_globaltmr_remain_get(void)
{
    return (uint32_t) (alt_globaltmr_comp_get64() - alt_globaltmr_get64());
}


/*************************************************************************************************************
 * alt_globaltmr_comp_mode_start() sets the comparison enable bit of the global timer, enabling
 * comparison mode operation.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_comp_mode_start(void)
{
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET,
                alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET) | GLOBALTMR_COMP_ENABLE_BIT);
    return ALT_E_SUCCESS;
}


/*************************************************************************************************************
 * alt_globaltmr_comp_mode_stop() clears the comparison enable bit of the global timer, disabling
 * comparison mode operation.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_comp_mode_stop(void)
{
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET,
                alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET) & ~GLOBALTMR_COMP_ENABLE_BIT);
    return ALT_E_SUCCESS;
}


/*************************************************************************************************************
 * alt_globaltmr_is_comp_mode() checks and returns the state of the comparison enable bit of the global timer.
*************************************************************************************************************/

bool alt_globaltmr_is_comp_mode(void)
{
    return alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET) & GLOBALTMR_COMP_ENABLE_BIT;
}


/*************************************************************************************************************
 * alt_globaltmr_prescaler_get() returns the value of the prescaler setting of the global timer, which is one
 * less than the actual counter divisor. Valid output = 0-255.
*************************************************************************************************************/

uint32_t alt_globaltmr_prescaler_get(void)
{
    return (alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET) & GLOBALTMR_PS_MASK) >> GLOBALTMR_PS_SHIFT;
}


/*************************************************************************************************************
 * alt_globaltmr_prescaler_set() sets the prescaler value of the global timer, which is one
 * less than the actual counter divisor.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_prescaler_set(uint32_t val)
{
    // It is not defined in the ARM global timer spec if the prescaler can be rewritten while
    //the global timer is counting or not. This is how we find out:
    uint32_t        regdata;

    if (val > UINT8_MAX) return ALT_E_BAD_ARG;
    regdata = alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET) & ~GLOBALTMR_PS_MASK;
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET, regdata | (val << GLOBALTMR_PS_SHIFT));
    return ALT_E_SUCCESS;
}


/*************************************************************************************************************
 * alt_globaltmr_autoinc_set() safely writes a value to the auto-increment register of the global timer.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_autoinc_set(uint32_t inc)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;
    bool                was_comping = false;

    if (alt_globaltmr_is_comp_mode())
    {
        was_comping = true;
        ret = alt_globaltmr_comp_mode_stop();
                            // if timer is currently in comparison mode, disable comparison mode
        if (ret != ALT_E_SUCCESS)   { return ret; }
    }

    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_AUTOINC_REG_OFFSET, inc);
    ret = ALT_E_SUCCESS;

    if (was_comping)  { ret = alt_globaltmr_comp_mode_start(); }
                      // If global timer was in comparison mode before, re-enable it
    return    ret;
}


/*************************************************************************************************************
 * alt_globaltmr_autoinc_get() returns the value of the auto-increment register of the global timer.
*************************************************************************************************************/

uint32_t alt_globaltmr_autoinc_get(void)
{
    return alt_read_word(GLOBALTMR_BASE + GLOBALTMR_AUTOINC_REG_OFFSET);
}


/*************************************************************************************************************
 * alt_globaltmr_autoinc_mode_start() sets the auto-increment enable bit of the global timer, putting it into
 * auto-increment or periodic timer mode.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_autoinc_mode_start(void)
{
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET,
            alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET) | GLOBALTMR_AUTOINC_ENABLE_BIT);
    return ALT_E_SUCCESS;
}


/*************************************************************************************************************
 * alt_globaltmr_autoinc_mode_stop() clears the auto-increment enable bit of the global timer, putting it into
 * one-shot timer mode.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_autoinc_mode_stop(void)
{
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET,
            alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET) & ~GLOBALTMR_AUTOINC_ENABLE_BIT);
    return ALT_E_SUCCESS;
}


/*************************************************************************************************************
 * alt_globaltmr_is_autoinc_mode() checks and returns the state of the auto-increment enable bit of the global
 * timer.
*************************************************************************************************************/

bool alt_globaltmr_is_autoinc_mode(void)
{
    return alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET) & GLOBALTMR_AUTOINC_ENABLE_BIT;
}


/*************************************************************************************************************
 * alt_globaltmr_maxcounter_get() returns the maximum possible auto-increment value of the global timer.
*************************************************************************************************************/

uint32_t alt_globaltmr_maxcounter_get(void)
{
    return GLOBALTMR_MAX;
}


/*************************************************************************************************************
 * alt_globaltmr_int_disable() clears the interrupt enable bit of the global timer.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_int_disable(void)
{
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET,
            alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET) & ~GLOBALTMR_INT_ENABLE_BIT);
    return ALT_E_SUCCESS;
}


/*************************************************************************************************************
 * alt_globaltmr_int_enable() sets the interrupt enable bit of the global timer, allowing the timer to throw an
 * interrupt when the global timer value is greater than the comparator value. If the global timer has not
 * yet been started, it tries to start it first.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_int_enable(void)
{
    if (!alt_globaltmr_is_running())                        // Is gbl timer running?
    {
        if ( alt_globaltmr_start() != ALT_E_SUCCESS)   { return ALT_E_ERROR; }
    }
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET,
            alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET) | GLOBALTMR_INT_ENABLE_BIT);
    return ALT_E_SUCCESS;
}


/*************************************************************************************************************
 * alt_globaltmr_int_is_enabled() checks and returns the state of the interrupt bit of the global timer.
*************************************************************************************************************/

bool alt_globaltmr_int_is_enabled(void)
{
    return alt_read_word(GLOBALTMR_BASE + GLOBALTMR_CTRL_REG_OFFSET) & GLOBALTMR_INT_ENABLE_BIT;
}


/*************************************************************************************************************
 * alt_globaltmr_int_clear_pending() clears the status of the interrupt pending bit of the global timer.
*************************************************************************************************************/

ALT_STATUS_CODE alt_globaltmr_int_clear_pending(void)
{
    alt_write_word(GLOBALTMR_BASE + GLOBALTMR_INT_STAT_REG_OFFSET, GLOBALTMR_INT_STATUS_BIT);
                /* clear interrupt sticky bit by writing one to it */
    return    ALT_E_SUCCESS;
}


/*************************************************************************************************************
 * alt_globaltmr_int_is_pending() checks and returns the status of the interrupt pending bit of the global
 * timer.
*************************************************************************************************************/

bool alt_globaltmr_int_is_pending(void)
{
    return alt_read_word(GLOBALTMR_BASE + GLOBALTMR_INT_STAT_REG_OFFSET) & GLOBALTMR_INT_STATUS_BIT;
}


/*************************************************************************************************************
 * alt_globaltmr_int_if_pending_clear() checks and returns the status of the interrupt pending bit of the global
 * timer. If the interrupt pending bit is set, this function also clears it.
*************************************************************************************************************/

bool alt_globaltmr_int_if_pending_clear(void)
{
    bool                ret;

    ret = alt_read_word(GLOBALTMR_BASE + GLOBALTMR_INT_STAT_REG_OFFSET) & GLOBALTMR_INT_STATUS_BIT;
    if (ret)
    {
        alt_write_word(GLOBALTMR_BASE + GLOBALTMR_INT_STAT_REG_OFFSET, GLOBALTMR_INT_STATUS_BIT);
    }          //clear int by writing to sticky bit

    return  ret;
}

