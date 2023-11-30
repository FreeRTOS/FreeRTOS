/*******************************************************************************
 * (c) Copyright 2007-2015 Microsemi SoC Products Group. All rights reserved.
 * 
 * CoreTimer driver implementation.
 * 
 * SVN $Revision: 7967 $
 * SVN $Date: 2015-10-09 18:48:26 +0530 (Fri, 09 Oct 2015) $
 */

#include "core_timer.h"
#include "coretimer_regs.h"
#include "hal.h"
#include "hal_assert.h"

#ifndef NDEBUG
static timer_instance_t* NULL_timer_instance;
#endif

/***************************************************************************//**
 * TMR_init()
 * See "core_timer.h" for details of how to use this function.
 */
void 
TMR_init
(
	timer_instance_t * this_timer,
	addr_t address,
	uint8_t mode,
	uint32_t prescale,
	uint32_t load_value
)
{
	HAL_ASSERT( this_timer != NULL_timer_instance )
	HAL_ASSERT( prescale <= PRESCALER_DIV_1024 )
	HAL_ASSERT( load_value != 0 )
    
    this_timer->base_address = address;

    /* Disable interrupts. */
    HAL_set_32bit_reg_field( address, InterruptEnable,0 );

    /* Disable timer. */
    HAL_set_32bit_reg_field( address, TimerEnable, 0 );

    /* Clear pending interrupt. */
    HAL_set_32bit_reg( address, TimerIntClr, 1 );

    /* Configure prescaler and load value. */	
    HAL_set_32bit_reg( address, TimerPrescale, prescale );
    HAL_set_32bit_reg( address, TimerLoad, load_value );

    /* Set the interrupt mode. */
    if ( mode == TMR_CONTINUOUS_MODE )
    {
        HAL_set_32bit_reg_field( address, TimerMode, 0 );
    }
    else
    {
        /* TMR_ONE_SHOT_MODE */
        HAL_set_32bit_reg_field( address, TimerMode, 1 );
    }
}

/***************************************************************************//**
 * TMR_start()
 * See "core_timer.h" for details of how to use this function.
 */
void
TMR_start
(
    timer_instance_t * this_timer
)
{
	HAL_ASSERT( this_timer != NULL_timer_instance )
    
    HAL_set_32bit_reg_field( this_timer->base_address, TimerEnable, 1 );
}

/***************************************************************************//**
 * TMR_stop()
 * See "core_timer.h" for details of how to use this function.
 */
void
TMR_stop
(
    timer_instance_t * this_timer
)
{
	HAL_ASSERT( this_timer != NULL_timer_instance )
    
    HAL_set_32bit_reg_field( this_timer->base_address, TimerEnable, 0 );
}


/***************************************************************************//**
 * TMR_enable_int()
 * See "core_timer.h" for details of how to use this function.
 */
void
TMR_enable_int
(
    timer_instance_t * this_timer
)
{
	HAL_ASSERT( this_timer != NULL_timer_instance )
    
    HAL_set_32bit_reg_field( this_timer->base_address, InterruptEnable, 1 );
}

/***************************************************************************//**
 * TMR_clear_int()
 * See "core_timer.h" for details of how to use this function.
 */
void
TMR_clear_int
(
    timer_instance_t * this_timer
)
{
	HAL_ASSERT( this_timer != NULL_timer_instance )
    
    HAL_set_32bit_reg( this_timer->base_address, TimerIntClr, 0x01 );
}

/***************************************************************************//**
 * TMR_current_value()
 * See "core_timer.h" for details of how to use this function.
 */
uint32_t
TMR_current_value
(
    timer_instance_t * this_timer
)
{
	uint32_t value = 0;
	HAL_ASSERT( this_timer != NULL_timer_instance )
    
    value = HAL_get_32bit_reg( this_timer->base_address, TimerValue );
    
	return value;
}

/***************************************************************************//**
 * TMR_reload()
 * See "core_timer.h" for details of how to use this function.
 */
void TMR_reload
(
	timer_instance_t * this_timer,
	uint32_t load_value
)
{
	HAL_ASSERT( this_timer != NULL_timer_instance )
	HAL_ASSERT( load_value != 0 )
	
	HAL_set_32bit_reg(this_timer->base_address, TimerLoad, load_value );
}

