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
Last Change:  Updated for peripheral functions prefix p_
******************************************************************************/
/** @file btimer.h
* \brief Hibernation Timer Peripheral Header file
* \author jvasanth
* 
* This file is the header file for Hibernation Timer Peripheral 
******************************************************************************/

/** @defgroup Hibernation_Timer
 *  @{
 */

#ifndef _HTIMER_H
#define _HTIMER_H

/******************************************************************************/
/**  Logical Timer ID for APIs.
 * This is the timer IDs passed to Hibernation Timer function calls 
 *******************************************************************************/
enum _PID_HTIMER_
{
	PID_HTIMER_0,	
	PID_HTIMER_MAX	
};

#define HTIMER_MAX_INSTANCE			PID_HTIMER_MAX

/* -------------------------------------------------------------------- */
/*                Hibernation Timer APIs                                */
/* -------------------------------------------------------------------- */
/** Enables hibernation timer
 * @param htimer_id Hibernation Timer ID
 * @param preload_value	- 16-bit preload value 
 * @param resolution_mode 0 - resolution of 30.5us per LSB, 
 *        1 - resolution of 0.125s per LSB
 */
void htimer_enable(uint8_t htimer_id, uint16_t preload_value, uint8_t resolution_mode);

/** Disables the hibernation timer by programming the prelaod value as 0
 * @param htimer_id Hibernation Timer ID 
 */
void htimer_disable(uint8_t htimer_id);


/** Reloads new preload value for the hibernation timer
 * @param htimer_id Hibernation Timer ID
 * @param reload_value	- 16-bit preload value 
 */
void htimer_reload(uint8_t htimer_id, uint16_t reload_value);


/* -------------------------------------------------------------------- */
/*             Hibernation Timer Peripheral Functions                   */
/* -------------------------------------------------------------------- */
/** Sets hibernation timer preload value
 * @param htimer_id Hibernation Timer ID
 * @param preload_value	- 16-bit preload value 
 */
void p_htimer_preload_set(uint8_t htimer_id, uint16_t preload_value);

/*_RB_ Added by RB. */
uint16_t p_htimer_preload_get(uint8_t htimer_id);

/** Sets hibernation timer resolution
 * @param htimer_id Hibernation Timer ID
 * @param resolution_mode 0 - resolution of 30.5us per LSB, 
 *        1 - resolution of 0.125s per LSB
 */
void p_htimer_resolution_set(uint8_t htimer_id, uint8_t resolution_mode);


/** Returns the Hibernation Timer current count value
 * @param htimer_id Hibernation Timer ID
 * @return 16-bit count value 
 */
uint16_t p_htimer_count_get(uint8_t htimer_id);


#endif // #ifndef _HTIMER_H

/* end htimer.h */

/**   @} //Peripherals Hibernation_Timer
 */

