/*****************************************************************************
* © 2015 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
******************************************************************************

Version Control Information (Perforce)
******************************************************************************
$Revision: #1 $ 
$DateTime: 2016/09/22 08:03:49 $ 
$Author: pramans $
Last Change:	Updated for tabs
******************************************************************************/
/** @file btimer_perphl.c
* \brief Basic Timer Peripheral Source file
* \author jvasanth
* 
* This file implements the Basic Timer Peripheral functions  
******************************************************************************/

/** @defgroup Basic_Timer
 *  @{
 */

#include "common_lib.h"
#include "btimer.h"

/** Basic Timer Instance base addresses */
static TIMER0_Type * const btmr_inst[BTIMER_MAX_INSTANCE] = {
    MEC2016_TIMER0,
    MEC2016_TIMER1,
    MEC2016_TIMER2,
    MEC2016_TIMER3,
    MEC2016_TIMER4,
    MEC2016_TIMER5
};

/* ---------------------------------------------------------------------- */
/*           Functions to set and read Timer Counter Register             */
/* ---------------------------------------------------------------------- */

/** Sets timer counter
 * @param btimer_id Basic Timer ID
 * @param count	- 32-bit counter  
 */
void p_btimer_count_set(uint8_t btimer_id, uint32_t count)
{
    btmr_inst[btimer_id]->COUNT = count;					
}

/** Read the timer counter
 * @param btimer_id Basic Timer ID
 * @return count	- 32-bit counter  
 */
uint32_t p_btimer_count_get(uint8_t btimer_id)
{	
    return btmr_inst[btimer_id]->COUNT;	
}

/* ---------------------------------------------------------------------- */
/*                   Function to program the Preload                      */
/* ---------------------------------------------------------------------- */

/** Sets preload for the counter
 * @param btimer_id Basic Timer ID
 * @param preload_count	- 32-bit pre-load value 
 */
void p_btimer_preload_set(uint8_t btimer_id, uint32_t preload_count)
{
    btmr_inst[btimer_id]->PRE_LOAD = preload_count;	
}

/* ---------------------------------------------------------------------- */
/*                Functions for basic timer interrupts                    */
/* ---------------------------------------------------------------------- */

/** Reads the interrupt status bit in the timer block
 * @param btimer_id Basic Timer ID 
 * @return status - 1 if interrupt status set, else 0
 */
uint8_t p_btimer_int_status_get(uint8_t btimer_id)
{
    return (uint8_t)(btmr_inst[btimer_id]->STATUS);
}

/** Clears interrupt status bit in the timer block
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_int_status_clr(uint8_t btimer_id)
{
    // Write 1 to clear
    btmr_inst[btimer_id]->STATUS = 1;
}

/** Sets interrupt enable bit in the timer block
 * @param btimer_id Basic Timer ID  
 */
void p_btimer_int_enable_set(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->INT_EN = 1;
}

/** Clears interrupt enable bit for the timer block
 * @param btimer_id Basic Timer ID  
 */
void p_btimer_int_enable_clr(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->INT_EN = 0;
}

/* ---------------------------------------------------------------------- */
/*                Functions for Control Register                          */
/* ---------------------------------------------------------------------- */

/** Writes the control register 32-bits
 * @param btimer_id Basic Timer ID
 * @param value	- 32-bit value to program
 */
void p_btimer_ctrl_write(uint8_t btimer_id, uint32_t value)
{		
    btmr_inst[btimer_id]->CONTROL.w = value;
}

/** Reads the control register 
 * @param btimer_id Basic Timer ID
 * @return uint32_t	- 32-bit value
 */
uint32_t p_btimer_ctrl_read(uint8_t btimer_id)
{		
    uint32_t retVal;

    retVal = btmr_inst[btimer_id]->CONTROL.w;

    return retVal;
}

/** Sets enable bit in the control register
 * @param btimer_id Basic Timer ID
 */
void p_btimer_ctrl_enable_set(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] |= BTIMER_CNTL_ENABLE;
}

/** Clears enable bit in the control register
 * @param btimer_id Basic Timer ID
 */
void p_btimer_ctrl_enable_clr(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] &= ~BTIMER_CNTL_ENABLE;
}

/** Sets counter direction bit in the control register
 * @param btimer_id Basic Timer ID
 */
void p_btimer_ctrl_counter_dir_set(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] |= BTIMER_CNTL_COUNT_UP;
}

/** Clears counter direction bit in the control register
 * @param btimer_id Basic Timer ID
 */
void p_btimer_ctrl_counter_dir_clr(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] &= ~BTIMER_CNTL_COUNT_UP;
}

/** Sets auto restart bit in the control register
 * @param btimer_id Basic Timer ID
 */
void p_btimer_ctrl_auto_restart_set(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] |= BTIMER_CNTL_AUTO_RESTART;
}

/** Clears auto resetart bit in the control register
 * @param btimer_id Basic Timer ID
 */
void p_btimer_ctrl_auto_restart_clr(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] &= ~BTIMER_CNTL_AUTO_RESTART;
}

/** Sets soft reset bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_soft_reset_set(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] |= BTIMER_CNTL_SOFT_RESET;
}

/** Read Soft Reset bit 
 * @param btimer_id Basic Timer ID
 * @return 0 if soft reset status bit cleared; else non-zero value
 */
uint8_t p_btimer_ctrl_soft_reset_sts_get(uint8_t btimer_id)
{		
    return (btmr_inst[btimer_id]->CONTROL.b[0] & BTIMER_CNTL_SOFT_RESET);
}

/** Sets start bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_start_set(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] |= BTIMER_CNTL_START;
}

/** Read start bit in the control register
 * @param btimer_id Basic Timer ID 
 * @return 0 if start bit not set; else non-zero value
 */
uint8_t p_btimer_ctrl_start_get(uint8_t btimer_id)
{		
    return (btmr_inst[btimer_id]->CONTROL.b[0] & BTIMER_CNTL_START);
}

/** Clears start bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_start_clr(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] &= ~BTIMER_CNTL_START;
}

/** Sets reload bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_reload_set(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] |= BTIMER_CNTL_RELOAD;
}

/** Clears reload bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_reload_clr(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] &= ~BTIMER_CNTL_RELOAD;
}

/** Sets halt bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_halt_set(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] |= BTIMER_CNTL_HALT;
}

/** Clears halt bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_halt_clr(uint8_t btimer_id)
{		
    btmr_inst[btimer_id]->CONTROL.b[0] &= ~BTIMER_CNTL_HALT;
}

/** Sets prescale value
 * @param btimer_id Basic Timer ID
 * @param prescaler	- 16-bit pre-scale value 
 */
void p_btimer_ctrl_prescale_set(uint8_t btimer_id, uint16_t prescaler)
{		
    btmr_inst[btimer_id]->CONTROL.h[1] = prescaler;
}


/* end btimer_perphl.c */

/**   @} //Peripheral Basic_Timer
 */

