/*******************************************************************************
 * (c) Copyright 2009-2015 Microsemi SoC Products Group.  All rights reserved.
 * 
 * CoreI2C driver interrupt control.
 * 
 * SVN $Revision: 7984 $
 * SVN $Date: 2015-10-12 12:07:40 +0530 (Mon, 12 Oct 2015) $
 */
#include "hal.h"
#include "hal_assert.h"
#include "core_i2c.h"
#include "riscv_hal.h"


#define I2C_IRQn					    External_29_IRQn

/*------------------------------------------------------------------------------
 * This function must be modified to enable interrupts generated from the
 * CoreI2C instance identified as parameter.
 */
void I2C_enable_irq( i2c_instance_t * this_i2c )
{
	PLIC_EnableIRQ(I2C_IRQn);
//    HAL_ASSERT(0)
}

/*------------------------------------------------------------------------------
 * This function must be modified to disable interrupts generated from the
 * CoreI2C instance identified as parameter.
 */
void I2C_disable_irq( i2c_instance_t * this_i2c )
{
	PLIC_DisableIRQ(I2C_IRQn);
//    HAL_ASSERT(0)
}
