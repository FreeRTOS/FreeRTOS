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
$DateTime: 2015/12/17 01:09:00 $ 
$Author: snakka $
Last Change: Updated for peripheral functions prefix p_
******************************************************************************/
/** @file btimer_perphl.c
* \brief Hibernation Timer API Source file
* \author jvasanth
* 
* This file implements Hibernation Timer APIs   
******************************************************************************/

/** @defgroup Hibernation_Timer
 *  @{
 */

#include "common_lib.h"
#include "htimer.h"

#ifdef PLIB_HTIMER_CHECK_ID

/** Local helper that checks if logical Timer ID is valid.  
 * @param htimer_id Hibernation Timer ID 
 * @return uint8_t Non-zero(VALID), 0(Invalid)
 */
static uint8_t htmr_valid(uint8_t htimer_id)
{
    if ( htimer_id < (PID_HTIMER_MAX ) ) {
        return 1;
    }
    return 0;
}

#else


/** This version of tmr_valid skips checking always returning 1.  
 *  Compiler may optimize it out.
 * @param htimer_id Hibernation Timer ID
 * @return uint8_t 1(VALID) 
 */
static uint8_t htmr_valid(uint8_t htimer_id) { return 1; }

#endif


/** Enables hibernation timer
 * @param htimer_id Hibernation Timer ID
 * @param preload_value	- 16-bit preload value 
 * @param resolution_mode 0 - resolution of 30.5us per LSB, 
 *        1 - resolution of 0.125s per LSB
 */
void htimer_enable(uint8_t htimer_id, uint16_t preload_value, uint8_t resolution_mode)
{
    if (htmr_valid(htimer_id)) 
    {
        p_htimer_preload_set(htimer_id, preload_value);
        
        p_htimer_resolution_set(htimer_id, resolution_mode);
    }        
}

/** Disables the hibernation timer by programming the prelaod value as 0
 * @param htimer_id Hibernation Timer ID 
 */
void htimer_disable(uint8_t htimer_id)
{    
    if (htmr_valid(htimer_id)) 
    {
        p_htimer_preload_set(htimer_id, 0);
    }        
}

/** Reloads new preload value for the hibernation timer
 * @param htimer_id Hibernation Timer ID
 * @param reload_value	- 16-bit preload value 
 */
void htimer_reload(uint8_t htimer_id, uint16_t reload_value)
{    
    if ( htmr_valid(htimer_id)) 
    {
        p_htimer_preload_set(htimer_id, reload_value);
    }        
}

/* end htimer_api.c */

/**   @} //APIs Hibernation_Timer
 */

