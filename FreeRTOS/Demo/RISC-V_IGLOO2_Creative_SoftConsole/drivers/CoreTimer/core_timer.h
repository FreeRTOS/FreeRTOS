/*******************************************************************************
 * (c) Copyright 2007-2015 Microsemi SoC Products Group. All rights reserved.
 * 
 * CoreTimer public API.
 * 
 * SVN $Revision: 7967 $
 * SVN $Date: 2015-10-09 18:48:26 +0530 (Fri, 09 Oct 2015) $
 */
#ifndef CORE_TIMER_H_
#define CORE_TIMER_H_

#include "cpu_types.h"

/***************************************************************************//**
 * The following definitions are used to select the CoreTimer driver operating
 * mode. They allow selecting continuous or one-shot mode.
 * 1. Continuous Mode
 * In continuous mode the timer's counter is decremented from the load value 
 * until it reaches zero. The timer counter is automatically reloaded, with the
 * load value, upon reaching zero. An interrupt is generated every time the
 * counter reaches zero if interrupt is enabled.
 * This mode is typically used to generate an interrupt at constant time
 * intervals.
 * 2. One-shot mode: 
 * In one-shot mode, the counter decrements from the load value and until it
 * reaches zero. An interrupt can be generated, if enabled, when the counter
 * reaches zero. The timer's counter must be reloaded to begin counting down
 * again.
 */
#define TMR_CONTINUOUS_MODE		0
#define TMR_ONE_SHOT_MODE		1

/***************************************************************************//**
 * The following definitions are used to configure the CoreTimer prescaler.
 * The prescaler is used to divide down the clock used to decrement the
 * CoreTimer counter. It can be configure to divide the clock by 2, 4, 8,
 * 16, 32, 64, 128, 256, 512, or 1024.
 */
#define PRESCALER_DIV_2			0
#define PRESCALER_DIV_4			1
#define PRESCALER_DIV_8			2
#define PRESCALER_DIV_16		3
#define PRESCALER_DIV_32		4
#define PRESCALER_DIV_64		5
#define PRESCALER_DIV_128		6
#define PRESCALER_DIV_256		7
#define PRESCALER_DIV_512		8
#define PRESCALER_DIV_1024		9

/***************************************************************************//**
 * There should be one instance of this structure for each instance of CoreTimer
 * in your system. The function TMR_init() initializes this structure. It is
 * used to identify the various CoreTimer hardware instances in your system.
 * An initialized timer instance structure should be passed as first parameter to
 * CoreTimer driver functions to identify which CoreTimer instance should perform
 * the requested operation.
 * Software using this driver should only need to create one single instance of 
 * this data structure for each hardware timer instance in the system.
 */
typedef struct __timer_instance_t
{
	addr_t base_address;
} timer_instance_t;

/***************************************************************************//**
 * The function TMR_init() initializes the data structures and sets relevant
 * CoreTimer registers. This function will prepare the Timer for use in a given
 * hardware/software configuration. It should be called before any other Timer
 * API functions.
 * The timer will not start counting down immediately after this function is
 * called. It is necessary to call TMR_start() to start the timer decrementing.
 * The CoreTimer interrupt is disabled as part of this function.
 *
 * @param this_timer    Pointer to a timer_instance_t structure holding all 
 *                      relevant data associated with the target timer hardware
 * 						instance. This pointer will be used to identify the
 * 						target CoreTimer hardware instance in subsequent calls
 * 						to the CoreTimer functions.
 * @param address       Base address in the processor's memory map of the 
 *                      registers of the CoreTimer instance being initialized.
 * @param mode          This parameter is used to select the operating mode of
 * 						the timer driver. This can be either TMR_CONTINUOUS_MODE
 * 						or TMR_ONE_SHOT_MODE.
 * @param prescale    	This parameter is used to select the prescaler divider
 * 						used to divide down the clock used to decrement the
 * 						timer’s counter. This can be set using one of the 
 * 						PRESCALER_DIV_<n> definitions, where <n> is the
 * 						divider’s value.  
 * @param load_value	This parameter is used to set the timer’s load value
 * 						from which the CoreTimer counter will decrement.
 * 						In Continuous mode, this value will be used to reload 
 * 						the timer’s counter whenever it reaches zero.
 */
void
TMR_init
(
	timer_instance_t * this_timer,
	addr_t address,
	uint8_t mode,
	uint32_t prescale,
	uint32_t load_value
);

/***************************************************************************//**
 * The function TMR_start() enables the timer to start counting down.
 * This function only needs to be called once after the timer has been
 * initialized through a call to TMR_init(). It does not need to be called after
 * each call to TMR_reload() when the timer is used in one-shot mode.
 *
 * @param this_timer    Pointer to a timer_instance_t structure holding all 
 *                      relevant data associated with the target timer hardware
 * 						instance. This pointer is used to identify the target
 * 						CoreTimer hardware instance.
 */
void
TMR_start
(
    timer_instance_t * this_timer
);

/***************************************************************************//**
 * The function TMR_stop() stops the timer counting down. It can be used to 
 * stop interrupts from being generated when continuous mode is used and
 * interrupts must be paused from being generated.
 *
 * @param this_timer    Pointer to a timer_instance_t structure holding all 
 *                      relevant data associated with the target timer hardware
 * 						instance. This pointer is used to identify the target
 * 						CoreTimer hardware instance.
 */
void
TMR_stop
(
    timer_instance_t * this_timer
);

/***************************************************************************//**
 * The function TMR_enable_int() enables the timer interrupt. A call to this
 * function will allow the interrupt signal coming out of CoreTimer to be
 * asserted. 
 *
 * @param this_timer    Pointer to a timer_instance_t structure holding all 
 *                      relevant data associated with the target timer hardware
 * 						instance. This pointer is used to identify the target
 * 						CoreTimer hardware instance.
 */
void
TMR_enable_int
(
    timer_instance_t * this_timer
);

/***************************************************************************//**
 * The function TMR_clear_int() clears the timer interrupt. This function should
 * be called within the interrupt handler servicing interrupts from the timer.
 * Failure to clear the timer interrupt will result in the interrupt signal
 * generating from CoreTimer to remain asserted. This assertion may cause the
 * interrupt service routine to be continuously called, causing the system to
 * lock up.
 *
 * @param this_timer    Pointer to a timer_instance_t structure holding all 
 *                      relevant data associated with the target timer hardware
 * 						instance. This pointer is used to identify the target
 * 						CoreTimer hardware instance.
 */
void
TMR_clear_int
(
    timer_instance_t * this_timer
);

/***************************************************************************//**
 * The TMR_current_value() function returns the current value of the counter.
 *
 * @param this_timer    Pointer to a timer_instance_t structure holding all 
 *                      relevant data associated with the target timer hardware
 * 						instance. This pointer is used to identify the target
 * 						CoreTimer hardware instance.
 *
 * @return              Returns the current value of the timer counter value.
 */
uint32_t
TMR_current_value
(
    timer_instance_t * this_timer
);

/***************************************************************************//**
 * The TMR_reload() function is used in one-shot mode. It reloads the timer
 * counter with the values passed as parameter. This will result in an interrupt
 * being generated when the timer counter reaches 0 if interrupt is enabled.
 * 
 * @param this_timer    Pointer to a timer_instance_t structure holding all 
 *                      relevant data associated with the target timer hardware
 * 						instance. This pointer is used to identify the target
 * 						CoreTimer hardware instance.
 * @param load_value	This parameter sets the value from which the CoreTimer
 * 						counter will decrement. 
 */
void TMR_reload
(
	timer_instance_t * this_timer,
	uint32_t load_value
);
	
#endif /* CORE_TIMER_H_ */
