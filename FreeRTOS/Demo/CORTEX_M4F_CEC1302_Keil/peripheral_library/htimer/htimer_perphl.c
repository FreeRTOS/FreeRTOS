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
* \brief Hibernation Timer Peripheral Source file
* \author jvasanth
* 
* This file implements Hibernation Timer Peripheral functions  
******************************************************************************/

/** @defgroup Hibernation_Timer
 *  @{
 */

#include "common_lib.h"
#include "htimer.h"

/** Hibernation Timer Instance base addresses */
static HTM_Type * const htmr_inst[HTIMER_MAX_INSTANCE] = {
    CEC1302_HTM    
};

/** Sets hibernation timer preload value
 * @param htimer_id Hibernation Timer ID
 * @param preload_value	- 16-bit preload value 
 * @note Setting the preload with a non-zero value starts 
 * the hibernation timer to down count. Setting the preload 
 * to 0 disables the hibernation counter
 */
void p_htimer_preload_set(uint8_t htimer_id, uint16_t preload_value)
{
    htmr_inst[htimer_id]->PRELOAD = preload_value;					
}

/** Sets hibernation timer resolution
 * @param htimer_id Hibernation Timer ID
 * @param resolution_mode 0 - resolution of 30.5us per LSB, 
 *        1 - resolution of 0.125s per LSB
 */
void p_htimer_resolution_set(uint8_t htimer_id, uint8_t resolution_mode)
{
    htmr_inst[htimer_id]->CONTROL = resolution_mode;    
}

/** Returns the Hibernation Timer current count value
 * @param htimer_id Hibernation Timer ID
 * @return 16-bit count value 
 */
uint16_t p_htimer_count_get(uint8_t htimer_id)
{
    uint16_t htimer_count;
    
    htimer_count = htmr_inst[htimer_id]->COUNT;
    
    return htimer_count;
}

/*_RB_ Added by RB. */
uint16_t p_htimer_preload_get(uint8_t htimer_id)
{
    return htmr_inst[htimer_id]->PRELOAD;
}


/* end htimer_perphl.c */

/**   @} //Peripheral Hibernation_Timer
 */

