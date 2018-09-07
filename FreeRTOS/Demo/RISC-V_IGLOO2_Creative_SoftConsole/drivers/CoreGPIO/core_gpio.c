/*******************************************************************************
 * (c) Copyright 2008-2015 Microsemi SoC Products Group. All rights reserved.
 * 
 * CoreGPIO bare metal driver implementation.
 *
 * SVN $Revision: 7964 $
 * SVN $Date: 2015-10-09 18:26:53 +0530 (Fri, 09 Oct 2015) $
 */
#include "core_gpio.h"
#include "hal.h"
#include "hal_assert.h"
#include "coregpio_regs.h"

/*-------------------------------------------------------------------------*//**
 *
 */
#define GPIO_INT_ENABLE_MASK        (uint32_t)0x00000008UL
#define OUTPUT_BUFFER_ENABLE_MASK   0x00000004UL


#define NB_OF_GPIO  32

#define CLEAR_ALL_IRQ32     (uint32_t)0xFFFFFFFF
#define CLEAR_ALL_IRQ16     (uint16_t)0xFFFF
#define CLEAR_ALL_IRQ8      (uint8_t)0xFF

/*-------------------------------------------------------------------------*//**
 * GPIO_init()
 * See "core_gpio.h" for details of how to use this function.
 */
void GPIO_init
(
    gpio_instance_t *   this_gpio,
    addr_t              base_addr,
    gpio_apb_width_t    bus_width
)
{
    uint8_t i = 0;
    addr_t cfg_reg_addr = base_addr;
    
    this_gpio->base_addr = base_addr;
    this_gpio->apb_bus_width = bus_width;
    
    /* Clear configuration. */
    for( i = 0, cfg_reg_addr = base_addr; i < NB_OF_GPIO; ++i )
    {
        HW_set_8bit_reg( cfg_reg_addr, 0 );
        cfg_reg_addr += 4;
    }
    /* Clear any pending interrupts */
    switch( this_gpio->apb_bus_width )
    {
        case GPIO_APB_32_BITS_BUS:
            HAL_set_32bit_reg( this_gpio->base_addr, IRQ, CLEAR_ALL_IRQ32 );
            break;
            
        case GPIO_APB_16_BITS_BUS:
            HAL_set_16bit_reg( this_gpio->base_addr, IRQ0, (uint16_t)CLEAR_ALL_IRQ16 );
            HAL_set_16bit_reg( this_gpio->base_addr, IRQ1, (uint16_t)CLEAR_ALL_IRQ16 );
            break;
            
        case GPIO_APB_8_BITS_BUS:
            HAL_set_8bit_reg( this_gpio->base_addr, IRQ0, (uint8_t)CLEAR_ALL_IRQ8 );
            HAL_set_8bit_reg( this_gpio->base_addr, IRQ1, (uint8_t)CLEAR_ALL_IRQ8 );
            HAL_set_8bit_reg( this_gpio->base_addr, IRQ2, (uint8_t)CLEAR_ALL_IRQ8 );
            HAL_set_8bit_reg( this_gpio->base_addr, IRQ3, (uint8_t)CLEAR_ALL_IRQ8 );
            break;
            
        default:
            HAL_ASSERT(0);
            break;
    }
}

/*-------------------------------------------------------------------------*//**
 * GPIO_config
 * See "core_gpio.h" for details of how to use this function.
 */
void GPIO_config
(
    gpio_instance_t *   this_gpio,
    gpio_id_t           port_id,
    uint32_t            config
)
{
    HAL_ASSERT( port_id < NB_OF_GPIO );
    
    if ( port_id < NB_OF_GPIO )
    {
        uint32_t cfg_reg_addr = this_gpio->base_addr;
        cfg_reg_addr += (port_id * 4);
        HW_set_32bit_reg( cfg_reg_addr, config );
        
        /*
         * Verify that the configuration was correctly written. Failure to read
         * back the expected value may indicate that the GPIO port was configured
         * as part of the hardware flow and cannot be modified through software.
         * It may also indicate that the base address passed as parameter to
         * GPIO_init() was incorrect.
         */
        HAL_ASSERT( HW_get_32bit_reg( cfg_reg_addr ) == config );
    }
}

/*-------------------------------------------------------------------------*//**
 * GPIO_set_outputs
 * See "core_gpio.h" for details of how to use this function.
 */
void GPIO_set_outputs
(
    gpio_instance_t *   this_gpio,
    uint32_t            value
)
{
    switch( this_gpio->apb_bus_width )
    {
        case GPIO_APB_32_BITS_BUS:
            HAL_set_32bit_reg( this_gpio->base_addr, GPIO_OUT, value );
            break;
            
        case GPIO_APB_16_BITS_BUS:
            HAL_set_16bit_reg( this_gpio->base_addr, GPIO_OUT0, (uint16_t)value );
            HAL_set_16bit_reg( this_gpio->base_addr, GPIO_OUT1, (uint16_t)(value >> 16) );
            break;
            
        case GPIO_APB_8_BITS_BUS:
            HAL_set_8bit_reg( this_gpio->base_addr, GPIO_OUT0, (uint8_t)value );
            HAL_set_8bit_reg( this_gpio->base_addr, GPIO_OUT1, (uint8_t)(value >> 8) );
            HAL_set_8bit_reg( this_gpio->base_addr, GPIO_OUT2, (uint8_t)(value >> 16) );
            HAL_set_8bit_reg( this_gpio->base_addr, GPIO_OUT3, (uint8_t)(value >> 24) );
            break;
            
        default:
            HAL_ASSERT(0);
            break;
    }
    
    /*
     * Verify that the output register was correctly written. Failure to read back
     * the expected value may indicate that some of the GPIOs may not exist due to
     * the number of GPIOs selected in the CoreGPIO hardware flow configuration.
     * It may also indicate that the base address or APB bus width passed as
     * parameter to the GPIO_init() function do not match the hardware design.
     */
    HAL_ASSERT( GPIO_get_outputs( this_gpio ) == value );
}

/*-------------------------------------------------------------------------*//**
 * GPIO_get_inputs
 * See "core_gpio.h" for details of how to use this function.
 */
uint32_t GPIO_get_inputs
(
    gpio_instance_t *   this_gpio
)
{
    uint32_t gpio_in = 0;
    
    switch( this_gpio->apb_bus_width )
    {
        case GPIO_APB_32_BITS_BUS:
            gpio_in = HAL_get_32bit_reg( this_gpio->base_addr, GPIO_IN );
            break;
            
        case GPIO_APB_16_BITS_BUS:
            gpio_in |= HAL_get_16bit_reg( this_gpio->base_addr, GPIO_IN0 );
            gpio_in |= (HAL_get_16bit_reg( this_gpio->base_addr, GPIO_IN1 ) << 16);
            break;
            
        case GPIO_APB_8_BITS_BUS:
            gpio_in |= HAL_get_8bit_reg( this_gpio->base_addr, GPIO_IN0 );
            gpio_in |= (HAL_get_8bit_reg( this_gpio->base_addr, GPIO_IN1 ) << 8);
            gpio_in |= (HAL_get_8bit_reg( this_gpio->base_addr, GPIO_IN2 ) << 16);
            gpio_in |= (HAL_get_8bit_reg( this_gpio->base_addr, GPIO_IN3 ) << 24);
            break;
            
        default:
            HAL_ASSERT(0);
            break;
    }
    
    return gpio_in;
}

/*-------------------------------------------------------------------------*//**
 * GPIO_get_outputs
 * See "core_gpio.h" for details of how to use this function.
 */
uint32_t GPIO_get_outputs
(
    gpio_instance_t *   this_gpio
)
{
    uint32_t gpio_out = 0;
    
    switch( this_gpio->apb_bus_width )
    {
        case GPIO_APB_32_BITS_BUS:
            gpio_out = HAL_get_32bit_reg( this_gpio->base_addr, GPIO_OUT );
            break;
            
        case GPIO_APB_16_BITS_BUS:
            gpio_out |= HAL_get_16bit_reg( this_gpio->base_addr, GPIO_OUT0 );
            gpio_out |= (HAL_get_16bit_reg( this_gpio->base_addr, GPIO_OUT1 ) << 16);
            break;
            
        case GPIO_APB_8_BITS_BUS:
            gpio_out |= HAL_get_16bit_reg( this_gpio->base_addr, GPIO_OUT0 );
            gpio_out |= (HAL_get_16bit_reg( this_gpio->base_addr, GPIO_OUT1 ) << 8);
            gpio_out |= (HAL_get_16bit_reg( this_gpio->base_addr, GPIO_OUT2 ) << 16);
            gpio_out |= (HAL_get_16bit_reg( this_gpio->base_addr, GPIO_OUT3 ) << 24);
            break;
            
        default:
            HAL_ASSERT(0);
            break;
    }
    
    return gpio_out;
}

/*-------------------------------------------------------------------------*//**
 * GPIO_set_output
 * See "core_gpio.h" for details of how to use this function.
 */
void GPIO_set_output
(
    gpio_instance_t *   this_gpio,
    gpio_id_t           port_id,
    uint8_t             value
)
{
    HAL_ASSERT( port_id < NB_OF_GPIO );
    
            
    switch( this_gpio->apb_bus_width )
    {
        case GPIO_APB_32_BITS_BUS:
            {
                uint32_t outputs_state;
                
                outputs_state = HAL_get_32bit_reg( this_gpio->base_addr, GPIO_OUT );
                if ( 0 == value )
                {
                    outputs_state &= ~(1 << port_id);
                }
                else
                {
                    outputs_state |= 1 << port_id;
                }
                HAL_set_32bit_reg( this_gpio->base_addr, GPIO_OUT, outputs_state );
                
                /*
                 * Verify that the output register was correctly written. Failure to read back
                 * the expected value may indicate that some of the GPIOs may not exist due to
                 * the number of GPIOs selected in the CoreGPIO hardware flow configuration.
                 * It may also indicate that the base address or APB bus width passed as
                 * parameter to the GPIO_init() function do not match the hardware design.
                 */
                HAL_ASSERT( HAL_get_32bit_reg( this_gpio->base_addr, GPIO_OUT ) == outputs_state );
            }
            break;
            
        case GPIO_APB_16_BITS_BUS:
            {
                uint16_t outputs_state;
                uint32_t gpio_out_reg_addr = this_gpio->base_addr + GPIO_OUT_REG_OFFSET + ((port_id >> 4) * 4);
                
                outputs_state = HW_get_16bit_reg( gpio_out_reg_addr );
                if ( 0 == value )
                {
                    outputs_state &= ~(1 << (port_id & 0x0F));
                }
                else
                {
                    outputs_state |= 1 << (port_id & 0x0F);
                }
                HW_set_16bit_reg( gpio_out_reg_addr, outputs_state );
                
                /*
                 * Verify that the output register was correctly written. Failure to read back
                 * the expected value may indicate that some of the GPIOs may not exist due to
                 * the number of GPIOs selected in the CoreGPIO hardware flow configuration.
                 * It may also indicate that the base address or APB bus width passed as
                 * parameter to the GPIO_init() function do not match the hardware design.
                 */
                HAL_ASSERT( HW_get_16bit_reg( gpio_out_reg_addr ) == outputs_state );
            }
            break;
            
        case GPIO_APB_8_BITS_BUS:
            {
                uint8_t outputs_state;
                uint32_t gpio_out_reg_addr = this_gpio->base_addr + GPIO_OUT_REG_OFFSET + ((port_id >> 3) * 4);
                
                outputs_state = HW_get_8bit_reg( gpio_out_reg_addr );
                if ( 0 == value )
                {
                    outputs_state &= ~(1 << (port_id & 0x07));
                }
                else
                {
                    outputs_state |= 1 << (port_id & 0x07);
                }
                HW_set_8bit_reg( gpio_out_reg_addr, outputs_state );
                
                /*
                 * Verify that the output register was correctly written. Failure to read back
                 * the expected value may indicate that some of the GPIOs may not exist due to
                 * the number of GPIOs selected in the CoreGPIO hardware flow configuration.
                 * It may also indicate that the base address or APB bus width passed as
                 * parameter to the GPIO_init() function do not match the hardware design.
                 */
                HAL_ASSERT( HW_get_8bit_reg( gpio_out_reg_addr ) == outputs_state );
            }
            break;
            
        default:
            HAL_ASSERT(0);
            break;
    }
}

/*-------------------------------------------------------------------------*//**
 * GPIO_drive_inout
 * See "core_gpio.h" for details of how to use this function.
 */
void GPIO_drive_inout
(
    gpio_instance_t *   this_gpio,
    gpio_id_t           port_id,
    gpio_inout_state_t  inout_state
)
{
    uint32_t config;
    uint32_t cfg_reg_addr = this_gpio->base_addr;
    
    HAL_ASSERT( port_id < NB_OF_GPIO );

    switch( inout_state )
    {
        case GPIO_DRIVE_HIGH:
            /* Set output high */
            GPIO_set_output( this_gpio, port_id, 1 );
            
            /* Enable output buffer */
            cfg_reg_addr = this_gpio->base_addr + (port_id * 4);
            config = HW_get_8bit_reg( cfg_reg_addr );
            config |= OUTPUT_BUFFER_ENABLE_MASK;
            HW_set_8bit_reg( cfg_reg_addr, config );
            break;
            
        case GPIO_DRIVE_LOW:
            /* Set output low */
            GPIO_set_output( this_gpio, port_id, 0 );
            
            /* Enable output buffer */
            cfg_reg_addr = this_gpio->base_addr + (port_id * 4);
            config = HW_get_8bit_reg( cfg_reg_addr );
            config |= OUTPUT_BUFFER_ENABLE_MASK;
            HW_set_8bit_reg( cfg_reg_addr, config );
            break;
            
        case GPIO_HIGH_Z:
            /* Disable output buffer */
            cfg_reg_addr = this_gpio->base_addr + (port_id * 4);
            config = HW_get_8bit_reg( cfg_reg_addr );
            config &= ~OUTPUT_BUFFER_ENABLE_MASK;
            HW_set_8bit_reg( cfg_reg_addr, config );
            break;
            
        default:
            HAL_ASSERT(0);
            break;
    }
}

/*-------------------------------------------------------------------------*//**
 * GPIO_enable_irq
 * See "core_gpio.h" for details of how to use this function.
 */
void GPIO_enable_irq
(
    gpio_instance_t *   this_gpio,
    gpio_id_t           port_id
)
{
    uint32_t cfg_value;
    uint32_t cfg_reg_addr = this_gpio->base_addr;
   
    HAL_ASSERT( port_id < NB_OF_GPIO );
    
    if ( port_id < NB_OF_GPIO )
    {
        cfg_reg_addr += (port_id * 4);
        cfg_value = HW_get_8bit_reg( cfg_reg_addr );
        cfg_value |= GPIO_INT_ENABLE_MASK;
        HW_set_8bit_reg( cfg_reg_addr, cfg_value );
    }
}

/*-------------------------------------------------------------------------*//**
 * GPIO_disable_irq
 * See "core_gpio.h" for details of how to use this function.
 */
void GPIO_disable_irq
(
    gpio_instance_t *   this_gpio,
    gpio_id_t           port_id
)
{
    uint32_t cfg_value;
    uint32_t cfg_reg_addr = this_gpio->base_addr;
   
    HAL_ASSERT( port_id < NB_OF_GPIO );
    
    if ( port_id < NB_OF_GPIO )
    {
        cfg_reg_addr += (port_id * 4);
        cfg_value = HW_get_8bit_reg( cfg_reg_addr );
        cfg_value &= ~GPIO_INT_ENABLE_MASK;
        HW_set_8bit_reg( cfg_reg_addr, cfg_value );
    }
}

/*-------------------------------------------------------------------------*//**
 * GPIO_clear_irq
 * See "core_gpio.h" for details of how to use this function.
 */
void GPIO_clear_irq
(
    gpio_instance_t *   this_gpio,
    gpio_id_t           port_id
)
{
    uint32_t irq_clr_value = ((uint32_t)1) << ((uint32_t)port_id);
    
    switch( this_gpio->apb_bus_width )
    {
        case GPIO_APB_32_BITS_BUS:
            HAL_set_32bit_reg( this_gpio->base_addr, IRQ, irq_clr_value );
            break;
            
        case GPIO_APB_16_BITS_BUS:
            HAL_set_16bit_reg( this_gpio->base_addr, IRQ0, irq_clr_value );
            HAL_set_16bit_reg( this_gpio->base_addr, IRQ1, irq_clr_value >> 16 );
            break;
            
        case GPIO_APB_8_BITS_BUS:
            HAL_set_8bit_reg( this_gpio->base_addr, IRQ0, irq_clr_value );
            HAL_set_8bit_reg( this_gpio->base_addr, IRQ1, irq_clr_value >> 8 );
            HAL_set_8bit_reg( this_gpio->base_addr, IRQ2, irq_clr_value >> 16 );
            HAL_set_8bit_reg( this_gpio->base_addr, IRQ3, irq_clr_value >> 24 );
            break;
            
        default:
            HAL_ASSERT(0);
            break;
    }
}

