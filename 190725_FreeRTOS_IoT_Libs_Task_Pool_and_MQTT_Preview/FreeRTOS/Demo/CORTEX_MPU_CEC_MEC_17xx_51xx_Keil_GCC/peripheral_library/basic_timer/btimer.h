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
Last Change:	Updated with unit testing feedbacks
******************************************************************************/
/** @file btimer.h
* \brief Basic Timer Peripheral Header file
* \author jvasanth
* 
* This file is the header file for Basic Timer Peripheral 
******************************************************************************/

/** @defgroup Basic_Timer
 *  @{
 */

#ifndef _BTIMER_H
#define _BTIMER_H

/******************************************************************************/
/**  Logical Timer ID for APIs.
 * This is the timer IDs passed to Basic Timer API function calls 
 *******************************************************************************/
enum _PID_BTIMER_
{
	PID_BTIMER_0,
	PID_BTIMER_1,
	PID_BTIMER_2,
	PID_BTIMER_3,
	PID_BTIMER_4,
	PID_BTIMER_5,
	PID_BTIMER_MAX	
};

/* ---------------------------------------------------------------------- */
/*                    Logical flags for Timer Control                     */
/* ---------------------------------------------------------------------- */
//This is for tmr_cntl parameter in btimer_init function
#define BTIMER_AUTO_RESTART     			     (0x08u)
#define BTIMER_ONE_SHOT         			     (0u)
#define BTIMER_COUNT_UP         			     (0x04u)
#define BTIMER_COUNT_DOWN       			     (0u)
#define BTIMER_INT_EN           			     (0x01u)
#define BTIMER_NO_INT           			     (0u)
/* ---------------------------------------------------------------------- */


//Timer Block Hardware Bits and Masks
#define BTIMER_CNTL_HALT                   (0x80UL)
#define BTIMER_CNTL_RELOAD                 (0x40UL)
#define BTIMER_CNTL_START                  (0x20UL)
#define BTIMER_CNTL_SOFT_RESET             (0x10UL)
#define BTIMER_CNTL_AUTO_RESTART           (0x08UL)
#define BTIMER_CNTL_COUNT_UP               (0x04UL)
#define BTIMER_CNTL_ENABLE                 (0x01UL)

#define BTIMER_CNTL_HALT_BIT               (7U)
#define BTIMER_CNTL_RELOAD_BIT             (6U)
#define BTIMER_CNTL_START_BIT              (5U)
#define BTIMER_CNTRL_SOFT_RESET_BIT        (4U)
#define BTIMER_CNTL_AUTO_RESTART_BIT       (3U)
#define BTIMER_CNTL_COUNT_DIR_BIT          (2U)
#define BTIMER_CNTL_ENABLE_BIT             (0U)

#define BTIMER_GIRQ													MEC_GIRQ23_ID
#define BTIMER_MAX_INSTANCE									PID_BTIMER_MAX


/* ---------------------------------------------------------------------- */
/*            API - Basic Timer Intitialization function                  */
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
               uint32_t preload_count);

/* ---------------------------------------------------------------------- */
/*  API -   Functions to program and read the Basic Timer Counter         */
/* ---------------------------------------------------------------------- */
/** Program timer's counter register.
 * @param btimer_id Basic Timer ID
 * @param count new counter value 
 * @note Timer hardware may implement a 16-bit or 32-bit 
 *       hardware counter. If the timer is 16-bit only the lower
 *       16-bits of the count paramter are used.
 */
void btimer_count_set(uint8_t btimer_id, uint32_t count);

/** Return current value of timer's count register.
 * @param btimer_id Basic Timer ID. 
 * @return uint32_t timer count may be 32 or 16 bits depending 
 *         upon the hardware.  Timers 0-3 are 16-bit
 *         and Timers 4-5 are 32-bit.
 */
uint32_t btimer_count_get(uint8_t btimer_id);

/* ---------------------------------------------------------------------- */
/*  API -   Function to reload counter from Preload Register              */
/* ---------------------------------------------------------------------- */
/** Force timer to reload counter from preload 
 * register.  
 * @param btimer_id Basic Timer ID. 
 * @note Hardware will only reload counter if timer is running. 
 */
void btimer_reload(uint8_t btimer_id);

/* ---------------------------------------------------------------------- */
/*  API -    Functions for stopping and starting the basic Timer          */
/* ---------------------------------------------------------------------- */
/** Start timer counting.
 * @param btimer_id Basic Timer ID.
 */
void btimer_start(uint8_t btimer_id);

/** Stop timer. 
 * @param btimer_id Basic Timer ID. 
 * @note When a stopped timer is started again it will reload 
 *       the count register from preload value.
 */
void btimer_stop(uint8_t btimer_id);

/** Return state of timer's START bit. 
 * @param btimer_id Basic Timer ID. 
 * @return uint8_t 0(timer not started), 1 (timer started)
 */
uint8_t btimer_is_started(uint8_t btimer_id);

/* ---------------------------------------------------------------------- */
/*  API -         Function to perform basic timer soft reset              */
/* ---------------------------------------------------------------------- */
/** Peform soft reset of specified timer. 
 * @param btimer_id Basic Timer ID 
 * @note Soft reset set all registers to POR values.
 * Spins 256 times waiting on hardware to clear reset bit. 
 */
void btimer_reset(uint8_t btimer_id);

/* ---------------------------------------------------------------------- */
/*   API -        Functions to halt/unhalt the timer counting             */
/* ---------------------------------------------------------------------- */
/** Halt timer counting with no reload on unhalt.   
 * @param btimer_id Basic Timer ID. 
 * @note A halted timer will not reload the count register when 
 *       unhalted, it will continue counting from the current
 *       count value.
 */
void btimer_halt(uint8_t btimer_id);

/** Unhalt timer counting. 
 * @param btimer_id Basic Timer ID.
 */
void btimer_unhalt(uint8_t btimer_id);

/* ---------------------------------------------------------------------- */
/*   API -        Functions for Basic Timer interrupt                     */
/* ---------------------------------------------------------------------- */
/** Enable specified timer's interrupt from the block. 
 * @param btimer_id Basic Timer ID.
 * @param ien Non-zero enable interrupt in timer block, 0 
 *            disable.
 */
void btimer_interrupt_enable(uint8_t btimer_id, uint8_t ien);

/** Read Timer interrupt status and clear if set 
 * @param btimer_id Basic Timer ID. 
 * @return uint8_t 1 (Timer interrupt status set) else 0. 
 * @note If timer interrupt status is set then clear it before 
 *       returning.
 */
uint8_t btimer_interrupt_status_get_clr(uint8_t btimer_id);

/* ---------------------------------------------------------------------- */
/*  API -         Functions for Basic Timer GIRQ                          */
/* ---------------------------------------------------------------------- */
/** Enables GIRQ enable bit for the timer 
 * @param btimer_id Basic Timer ID.
 */
void btimer_girq_enable_set(uint8_t btimer_id);

/** Clears GIRQ enable bit for the timer 
 * @param btimer_id Basic Timer ID.
 */
void btimer_girq_enable_clr(uint8_t btimer_id);

/** Returns GIRQ source bit for the timer 
 * @param btimer_id Basic Timer ID.
 * @return uint8_t 0(src bit not set), Non-zero (src bit set)
 */
uint8_t btimer_girq_src_get(uint8_t btimer_id);

/** Clears GIRQ source bit for the timer 
 * @param btimer_id Basic Timer ID.
 */
void btimer_girq_src_clr(uint8_t btimer_id);

/** Returns GIRQ result bit for the timer 
 * @param btimer_id Basic Timer ID.
 * @return uint8_t 0(result bit not set), Non-zero (result bit set)
 */
uint8_t btimer_girq_result_get(uint8_t btimer_id);

/* ---------------------------------------------------------------------- */
/*  API -         Functions for Basic Timer Sleep                         */
/* ---------------------------------------------------------------------- */
/** Enable/Disable clock gating on idle of a timer  
 * @param btimer_id Basic Timer ID.
 * @param sleep_en 1 = Sleep enable, 0 = Sleep disable
 */
void btimer_sleep(uint8_t btimer_id, uint8_t sleep_en);

/** Returns clk required status for the timer block
 * @param btimer_id Basic Timer ID.
 * @return Non-zero if clk required, else 0
 */
uint32_t btimer_clk_reqd_sts_get(uint8_t btimer_id);

/** Enable/Disable reset on sleep for the timer block 
 * @param btimer_id Basic Timer ID.
 * @param reset_en 1 to enable, 0 to disable
 */
void btimer_reset_on_sleep(uint8_t btimer_id, uint8_t reset_en);

/* ---------------------------------------------------------------------- */
/* Peripheral Function - Functions to set and read Timer Counter Register */
/* ---------------------------------------------------------------------- */
/** Sets timer counter
 * @param btimer_id Basic Timer ID
 * @param count	- 32-bit counter  
 */
void p_btimer_count_set(uint8_t btimer_id, uint32_t count);

/** Read the timer counter
 * @param btimer_id Basic Timer ID
 * @return count	- 32-bit counter  
 */
uint32_t p_btimer_count_get(uint8_t btimer_id);


/* ---------------------------------------------------------------------- */
/* Peripheral Function - Function to program the Preload                  */
/* ---------------------------------------------------------------------- */
/** Sets preload for the counter
 * @param btimer_id Basic Timer ID
 * @param preload_count	- 32-bit pre-load value 
 */
void p_btimer_preload_set(uint8_t btimer_id, uint32_t preload_count);

/* ---------------------------------------------------------------------- */
/* Peripheral Functions - Functions for basic timer interrupts            */
/* ---------------------------------------------------------------------- */
/** Reads the interrupt status bit in the timer block
 * @param btimer_id Basic Timer ID 
 * @return status - 1 if interrupt status set, else 0
 */
uint8_t p_btimer_int_status_get(uint8_t btimer_id);

/** Clears interrupt status bit in the timer block
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_int_status_clr(uint8_t btimer_id);

/** Sets interrupt enable bit in the timer block
 * @param btimer_id Basic Timer ID  
 */
void p_btimer_int_enable_set(uint8_t btimer_id);

/** Clears interrupt enable bit for the timer block
 * @param btimer_id Basic Timer ID  
 */
void p_btimer_int_enable_clr(uint8_t btimer_id);

/* ---------------------------------------------------------------------- */
/* Peripheral Functions - Functions for Control Register                  */
/* ---------------------------------------------------------------------- */
/** Writes the control register 32-bits
 * @param btimer_id Basic Timer ID
 * @param value	- 32-bit value to program
 */
void p_btimer_ctrl_write(uint8_t btimer_id, uint32_t value);

/** Reads the control register 
 * @param btimer_id Basic Timer ID
 * @return uint32_t	- 32-bit value
 */
uint32_t p_btimer_ctrl_read(uint8_t btimer_id);

/** Clears enable bit in the control register
 * @param btimer_id Basic Timer ID
 */
void p_btimer_ctrl_enable_set(uint8_t btimer_id);

/** Clears enable bit in the control register
 * @param btimer_id Basic Timer ID
 */
void p_btimer_ctrl_enable_clr(uint8_t btimer_id);

/** Sets counter direction bit in the control register
 * @param btimer_id Basic Timer ID
 */
void p_btimer_ctrl_counter_dir_set(uint8_t btimer_id);

/** Clears counter direction bit in the control register
 * @param btimer_id Basic Timer ID
 */
void p_btimer_ctrl_counter_dir_clr(uint8_t btimer_id);

/** Sets auto restart bit in the control register
 * @param btimer_id Basic Timer ID
 */
void p_btimer_ctrl_auto_restart_set(uint8_t btimer_id);

/** Clears auto resetart bit in the control register
 * @param btimer_id Basic Timer ID
 */
void p_btimer_ctrl_auto_restart_clr(uint8_t btimer_id);

/** Sets soft reset bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_soft_reset_set(uint8_t btimer_id);

/** Read Soft Reset bit 
 * @param btimer_id Basic Timer ID
 * @return 0 if soft reset status bit cleared; else non-zero value
 */
uint8_t p_btimer_ctrl_soft_reset_sts_get(uint8_t btimer_id);

/** Sets start bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_start_set(uint8_t btimer_id);

/** Read start bit in the control register
 * @param btimer_id Basic Timer ID 
 * @return 0 if start bit not set; else non-zero value
 */
uint8_t p_btimer_ctrl_start_get(uint8_t btimer_id);

/** Clears start bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_start_clr(uint8_t btimer_id);

/** Sets reload bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_reload_set(uint8_t btimer_id);

/** Clears reload bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_reload_clr(uint8_t btimer_id);

/** Sets halt bit in the control register
 * @param btimer_id Basic Timer ID 
 */
void p_btimer_ctrl_halt_set(uint8_t btimer_id);

/** Clears halt bit in the control register
 * @param btimer_id Basic Timer ID 
 */

void p_btimer_ctrl_halt_clr(uint8_t btimer_id);

/** Sets prescale value
 * @param btimer_id Basic Timer ID
 * @param prescaler	- 16-bit pre-scale value 
 */
void p_btimer_ctrl_prescale_set(uint8_t btimer_id, uint16_t prescaler);


#endif // #ifndef _BTIMER_H

/* end btimer_perphl.c */

/**   @} //Peripherals Basic_Timer
 */

