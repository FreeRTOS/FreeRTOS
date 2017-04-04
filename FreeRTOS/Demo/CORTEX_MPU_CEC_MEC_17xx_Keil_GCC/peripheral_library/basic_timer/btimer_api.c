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
/** @file btimer_api.c
* \brief Basic Timer APIs Source file
* \author jvasanth
* 
* This file implements the Basic Timer API functions  
******************************************************************************/

/** @defgroup Basic_Timer
 *  @{
 */

#include "common_lib.h"
#include "btimer.h"
#include "..\pcr\pcr.h"
//#include "..\interrupt\ecia.h"

/** Basic Timer Sleep Registers & Bit Positions */
static const uint32_t btmr_pcr_id[BTIMER_MAX_INSTANCE] = {
    PCR_BTIMER0,
    PCR_BTIMER1,
    PCR_BTIMER2,
    PCR_BTIMER3,
    PCR_BTIMER4,
    PCR_BTIMER5
};

#ifdef PLIB_BTIMER_CHECK_ID

/** Local helper that checks if logical Timer ID is valid.  
 * @param btimer_id Basic Timer ID 
 * @return uint8_t Non-zero(VALID), 0(Invalid)
 */
static uint8_t btmr_valid(uint8_t btimer_id)
{
    if ( btimer_id < (PID_BTIMER_MAX ) ) {
        return true;
    }
    return false;
}

#else


/** This version of tmr_valid skips checking always returning 1.  
 *  Compiler may optimize it out.
 * @param btimer_id Basic Timer ID 
 * @return uint8_t 1(VALID) 
 */
static uint8_t btmr_valid(uint8_t btimer_id) { return 1; }

#endif


/* ---------------------------------------------------------------------- */
/*                 Basic Timer Intitialization function                   */
/* ---------------------------------------------------------------------- */

/** Initialize specified timer
 * @param btimer_id Basic Timer ID
 * @param tmr_cntl Logical flags for Timer Control
 * @param initial_count Initial Count
 * @param preload_count Preload Count
 * @note Performs a soft reset of the timer before configuration 
 */
void btimer_init(uint8_t btimer_id, 
               uint16_t tmr_cntl,
               uint16_t prescaler,
               uint32_t initial_count,
               uint32_t preload_count)
{    
	 uint32_t value;    

    if (btmr_valid(btimer_id)) {
			
        btimer_reset(btimer_id); 
        
        // Ungate timer clocks and program prescale
        value = ((uint32_t)prescaler << 16) + (BTIMER_CNTL_ENABLE);			  
        p_btimer_ctrl_write(btimer_id, value);
    
        // Program Preload & initial counter value
        p_btimer_preload_set(btimer_id, preload_count);
        p_btimer_count_set(btimer_id, initial_count);			
        
        // Program control register, interrupt enable, and clear status
        if (tmr_cntl & BTIMER_COUNT_UP) {					
            p_btimer_ctrl_counter_dir_set(btimer_id);            
        }
        if (tmr_cntl & BTIMER_AUTO_RESTART) {
            p_btimer_ctrl_auto_restart_set(btimer_id);             
        }        
        if (tmr_cntl & BTIMER_INT_EN) {					
            p_btimer_int_enable_set(btimer_id); // enable first
            p_btimer_int_status_clr(btimer_id); // clear status          
        }
    }
}

/* ---------------------------------------------------------------------- */
/*          Functions to program and read the Basic Timer Counter         */
/* ---------------------------------------------------------------------- */

/** Program timer's counter register.
 * @param btimer_id Basic Timer ID
 * @param count new counter value 
 * @note Timer hardware may implement a 16-bit or 32-bit 
 *       hardware counter. If the timer is 16-bit only the lower
 *       16-bits of the count paramter are used.
 */
void btimer_count_set(uint8_t btimer_id, uint32_t count)
{
    if ( btmr_valid(btimer_id) ) {       
			
        p_btimer_count_set(btimer_id, count);        
    }
}

/** Return current value of timer's count register.
 * @param btimer_id Basic Timer ID. 
 * @return uint32_t timer count may be 32 or 16 bits depending 
 *         upon the hardware.  Timers 0-3 are 16-bit
 *         and Timers 4-5 are 32-bit.
 */
uint32_t btimer_count_get(uint8_t btimer_id)
{    
    uint32_t cnt;
    
    cnt = 0ul;
    if ( btmr_valid(btimer_id) ) {        
			
        cnt = p_btimer_count_get(btimer_id);        
    }
    
    return cnt;
}

/* ---------------------------------------------------------------------- */
/*          Function to reload counter from Preload Register              */
/* ---------------------------------------------------------------------- */

/** Force timer to reload counter from preload 
 * register.  
 * @param btimer_id Basic Timer ID. 
 * @note Hardware will only reload counter if timer is running. 
 */
void btimer_reload(uint8_t btimer_id)
{
    if ( btmr_valid(btimer_id) ) {        
			
        if (p_btimer_ctrl_start_get(btimer_id)) //Check if timer is running
        {
                p_btimer_ctrl_reload_set(btimer_id);
        }
    }
}

/* ---------------------------------------------------------------------- */
/*           Functions for stopping and starting the basic Timer          */
/* ---------------------------------------------------------------------- */

/** Start timer counting.
 * @param btimer_id Basic Timer ID.
 */
void btimer_start(uint8_t btimer_id)
{
    if ( btmr_valid(btimer_id) ) {
            
        p_btimer_ctrl_start_set(btimer_id);
    }
}

/** Stop timer. 
 * @param btimer_id Basic Timer ID. 
 * @note When a stopped timer is started again it will reload 
 *       the count register from preload value.
 */
void btimer_stop(uint8_t btimer_id)
{
    if ( btmr_valid(btimer_id) ) {        
			
        p_btimer_ctrl_start_clr(btimer_id);			
        
    }
}

/** Return state of timer's START bit. 
 * @param btimer_id Basic Timer ID. 
 * @return uint8_t 0(timer not started), 1 (timer started)
 */
uint8_t btimer_is_started(uint8_t btimer_id)
{ 
    uint8_t sts;
    
    sts = 0;
    if ( btmr_valid(btimer_id) ) {	  
 			
        if (p_btimer_ctrl_start_get(btimer_id))	
        {
            sts = 1;
        }					
    }
    return sts;
}

/* ---------------------------------------------------------------------- */
/*                Function to perform basic timer soft reset              */
/* ---------------------------------------------------------------------- */

/** Peform soft reset of specified timer. 
 * @param btimer_id Basic Timer ID 
 * @note Soft reset set all registers to POR values.
 * Spins 256 times waiting on hardware to clear reset bit. 
 */
void btimer_reset(uint8_t btimer_id)
{   
    uint32_t wait_cnt;
    uint8_t soft_reset_sts;

    if (btmr_valid(btimer_id)) {      
		 
        p_btimer_ctrl_soft_reset_set(btimer_id);    

        wait_cnt = 256ul;
        do {
            soft_reset_sts = p_btimer_ctrl_soft_reset_sts_get(btimer_id);
            
            if (0 == soft_reset_sts){          
                break;
            }
        } 
        while ( wait_cnt-- ); 
    }      
}

/* ---------------------------------------------------------------------- */
/*                Functions to halt/unhalt the timer counting             */
/* ---------------------------------------------------------------------- */

/** Halt timer counting with no reload on unhalt.   
 * @param btimer_id Basic Timer ID. 
 * @note A halted timer will not reload the count register when 
 *       unhalted, it will continue counting from the current
 *       count value.
 */
void btimer_halt(uint8_t btimer_id)
{
    if ( btmr_valid(btimer_id) ) {
 			
        p_btimer_ctrl_halt_set(btimer_id);        
    }
}

/** Unhalt timer counting. 
 * @param btimer_id Basic Timer ID.
 */
void btimer_unhalt(uint8_t btimer_id)
{
    if ( btmr_valid(btimer_id) ) { 
			
        p_btimer_ctrl_halt_clr(btimer_id);
    }
}

/* ---------------------------------------------------------------------- */
/*                Functions for Basic Timer interrupt                     */
/* ---------------------------------------------------------------------- */

/** Enable specified timer's interrupt from the block. 
 * @param btimer_id Basic Timer ID.
 * @param ien Non-zero enable interrupt in timer block, 0 
 *            disable.
 */
void btimer_interrupt_enable(uint8_t btimer_id, uint8_t ien)
{    
    if (btmr_valid(btimer_id)) {      
			
        p_btimer_int_enable_set(btimer_id);

        if (ien) {
             p_btimer_int_enable_set(btimer_id);
        } else {
             p_btimer_int_enable_clr(btimer_id);
        }
    }
}

/** Read Timer interrupt status and clear if set 
 * @param btimer_id Basic Timer ID. 
 * @return uint8_t 1 (Timer interrupt status set) else 0. 
 * @note If timer interrupt status is set then clear it before 
 *       returning.
 */
uint8_t btimer_interrupt_status_get_clr(uint8_t btimer_id)
{    
    uint8_t sts;

    sts = 0;
    if (btmr_valid(btimer_id)) {        
				
				sts = p_btimer_int_status_get(btimer_id);
        if (sts) {
					p_btimer_int_status_clr(btimer_id);            
        }
    }
    return sts;
}

#if 0 //Temporary disable until interrupt module

/* ---------------------------------------------------------------------- */
/*                Functions for Basic Timer GIRQ                          */
/* ---------------------------------------------------------------------- */

/** Enables GIRQ enable bit for the timer 
 * @param btimer_id Basic Timer ID.
 */
void btimer_girq_enable_set(uint8_t btimer_id)
{
    if (btmr_valid(btimer_id))
    {
        //Note: Bit Position is same as Timer ID			
        p_ecia_girq_enable_set(BTIMER_GIRQ, btimer_id);
    }		
}

/** Clears GIRQ enable bit for the timer 
 * @param btimer_id Basic Timer ID.
 */
void btimer_girq_enable_clr(uint8_t btimer_id)
{	
    if (btmr_valid(btimer_id))
    {			
        //Note: Bit Position is same as Timer ID			
        p_ecia_girq_enable_clr(BTIMER_GIRQ, btimer_id);
    }	
		
}

/** Returns GIRQ source bit for the timer 
 * @param btimer_id Basic Timer ID.
 * @return uint8_t 0(src bit not set), Non-zero (src bit set)
 */
uint8_t btimer_girq_src_get(uint8_t btimer_id)
{
    uint8_t retVal;

    retVal = 0;
    if (btmr_valid(btimer_id))
    {
        //Note: Bit Position is same as Timer ID			
        retVal = p_ecia_girq_source_get(BTIMER_GIRQ, btimer_id);			
    }

    return retVal;
}

/** Clears GIRQ source bit for the timer 
 * @param btimer_id Basic Timer ID.
 */
void btimer_girq_src_clr(uint8_t btimer_id)
{
    if (btmr_valid(btimer_id))
    {
        //Note: Bit Position is same as Timer ID			
        p_ecia_girq_source_clr(BTIMER_GIRQ, btimer_id);				
    }			
}

/** Returns GIRQ result bit for the timer 
 * @param btimer_id Basic Timer ID.
 * @return uint8_t 0(result bit not set), Non-zero (result bit set)
 */
uint8_t btimer_girq_result_get(uint8_t btimer_id)
{
    uint8_t retVal;

    retVal = 0;
    if (btmr_valid(btimer_id))
    {
        //Note: Bit Position is same as Timer ID			
        retVal = p_ecia_girq_result_get(BTIMER_GIRQ, btimer_id);			
    }

    return retVal;			
}
#endif

/* ---------------------------------------------------------------------- */
/*                Functions for Basic Timer Sleep                         */
/* ---------------------------------------------------------------------- */

/** Enable/Disable clock gating on idle of a timer  
 * @param btimer_id Basic Timer ID.
 * @param sleep_en 1 = Sleep enable, 0 = Sleep disable
 */
void btimer_sleep(uint8_t btimer_id, uint8_t sleep_en)
{
    uint32_t pcr_blk_id;
		
    if ( btmr_valid(btimer_id) ) 
    {				
        pcr_blk_id = btmr_pcr_id[btimer_id];			
			
        pcr_sleep_enable(pcr_blk_id, sleep_en);        
    }
}

/** Returns clk required status for the timer block
 * @param btimer_id Basic Timer ID.
 * @return Non-zero if clk required, else 0
 */
uint32_t btimer_clk_reqd_sts_get(uint8_t btimer_id)
{
    uint32_t retVal;
    uint32_t pcr_blk_id;
    	
    retVal = 0ul;   
    if ( btmr_valid(btimer_id) ) 
    {			
        pcr_blk_id = btmr_pcr_id[btimer_id];
        
        retVal = pcr_clock_reqd_status_get(pcr_blk_id);			       
    }
		
    return retVal;
}

/** Enable/Disable reset on sleep for the timer block 
 * @param btimer_id Basic Timer ID.
 * @param reset_en 1 to enable, 0 to disable
 */
void btimer_reset_on_sleep(uint8_t btimer_id, uint8_t reset_en)
{
    uint32_t pcr_blk_id;   
    
    if ( btmr_valid(btimer_id) ) 
    {			
        pcr_blk_id = btmr_pcr_id[btimer_id];
    
        pcr_reset_enable(pcr_blk_id, reset_en);			
    }
}

/* end btimer_api.c */

/**   @} //Peripheral Basic_Timer
 */
