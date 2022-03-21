/*******************************************************************************
 * Copyright 2019-2020 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 * 
 * PolarFire SoC microprocessor subsystem GPIO bare metal driver implementation.
 *
 * This driver is based on SmartFusion2 MSS GPIO driver v2.1.102
 *
 */

#include <drivers/mss/mss_gpio/mss_gpio.h>
#include "mpfs_hal/mss_hal.h"

#ifdef __cplusplus
extern "C" {
#endif 

/*-------------------------------------------------------------------------*//**
 * Defines.
 */
#define GPIO_INT_ENABLE_MASK                ((uint32_t)0x00000008)
#define OUTPUT_BUFFER_ENABLE_MASK           ((uint32_t)0x00000004)

/*These constants define the number of GPIO bits available on each GPIO
 * hardware block*/
#define NB_OF_GPIO_GPIO0                    ((uint32_t)14)
#define NB_OF_GPIO_GPIO1                    ((uint32_t)24)
#define NB_OF_GPIO_GPIO2                    ((uint32_t)32)

/*This constant indicates the total number of GPIO interrupt inputs at the PLIC
 * (includes the direct and non-direct GPIO interrupts)*/
#define NB_OF_GPIO_INTR                     ((uint32_t)41)

/*-------------------------------------------------------------------------*//**
 * Lookup table of GPIO interrupt number indexed on GPIO ID.
 * The GPIO interrupts are multiplexed. Total GPIO interrupts are 41.
 * 41 = (14 from GPIO0 + 24 from GPIO1 + 3 non direct interrupts)
 * GPIO2 interrupts are not available by default. Setting the corresponding bit
 * in GPIO_INTERRUPT_FAB_CR(31:0) will enable GPIO2(31:0) corresponding
 * interrupt on PLIC.
 *
 * PLIC       GPIO_INTERRUPT_FAB_CR
                0               1
    0       GPIO0 bit 0     GPIO2 bit 0
    1       GPIO0 bit 1     GPIO2 bit 1
    .
    .
    12      GPIO0 bit 12    GPIO2 bit 12
    13      GPIO0 bit 13    GPIO2 bit 13
    14      GPIO1 bit 0     GPIO2 bit 14
    15      GPIO1 bit 1     GPIO2 bit 15
    .
    .
    .
    30      GPIO1 bit 16    GPIO2 bit 30
    31      GPIO1 bit 17    GPIO2 bit 31
    32          GPIO1 bit 18
    33          GPIO1 bit 19
    34          GPIO1 bit 20
    35          GPIO1 bit 21
    36          GPIO1 bit 22
    37          GPIO1 bit 23
    38  Or of all GPIO0 interrupts who do not have a direct connection enabled
    39  Or of all GPIO1 interrupts who do not have a direct connection enabled
    40  Or of all GPIO2 interrupts who do not have a direct connection enabled
 *
 */
static const PLIC_IRQn_Type g_gpio_irqn_lut[NB_OF_GPIO_INTR] =
{
    GPIO0_BIT0_or_GPIO2_BIT0_PLIC_0,
    GPIO0_BIT1_or_GPIO2_BIT1_PLIC_1,
    GPIO0_BIT2_or_GPIO2_BIT2_PLIC_2,
    GPIO0_BIT3_or_GPIO2_BIT3_PLIC_3,
    GPIO0_BIT4_or_GPIO2_BIT4_PLIC_4,
    GPIO0_BIT5_or_GPIO2_BIT5_PLIC_5,
    GPIO0_BIT6_or_GPIO2_BIT6_PLIC_6,
    GPIO0_BIT7_or_GPIO2_BIT7_PLIC_7,
    GPIO0_BIT8_or_GPIO2_BIT8_PLIC_8,
    GPIO0_BIT9_or_GPIO2_BIT9_PLIC_9,
    GPIO0_BIT10_or_GPIO2_BIT10_PLIC_10,
    GPIO0_BIT11_or_GPIO2_BIT11_PLIC_11,
    GPIO0_BIT12_or_GPIO2_BIT12_PLIC_12,
    GPIO0_BIT13_or_GPIO2_BIT13_PLIC_13,

    GPIO1_BIT0_or_GPIO2_BIT14_PLIC_14,
    GPIO1_BIT1_or_GPIO2_BIT15_PLIC_15,
    GPIO1_BIT2_or_GPIO2_BIT16_PLIC_16,
    GPIO1_BIT3_or_GPIO2_BIT17_PLIC_17,
    GPIO1_BIT4_or_GPIO2_BIT18_PLIC_18,
    GPIO1_BIT5_or_GPIO2_BIT19_PLIC_19,
    GPIO1_BIT6_or_GPIO2_BIT20_PLIC_20,
    GPIO1_BIT7_or_GPIO2_BIT21_PLIC_21,
    GPIO1_BIT8_or_GPIO2_BIT22_PLIC_22,
    GPIO1_BIT9_or_GPIO2_BIT23_PLIC_23,
    GPIO1_BIT10_or_GPIO2_BIT24_PLIC_24,
    GPIO1_BIT11_or_GPIO2_BIT25_PLIC_25,
    GPIO1_BIT12_or_GPIO2_BIT26_PLIC_26,
    GPIO1_BIT13_or_GPIO2_BIT27_PLIC_27,
    GPIO1_BIT14_or_GPIO2_BIT28_PLIC_28,
    GPIO1_BIT15_or_GPIO2_BIT29_PLIC_29,
    GPIO1_BIT16_or_GPIO2_BIT30_PLIC_30,
    GPIO1_BIT17_or_GPIO2_BIT31_PLIC_31,

    GPIO1_BIT18_PLIC_32,
    GPIO1_BIT19_PLIC_33,
    GPIO1_BIT20_PLIC_34,
    GPIO1_BIT21_PLIC_35,
    GPIO1_BIT22_PLIC_36,
    GPIO1_BIT23_PLIC_37,

    GPIO0_NON_DIRECT_PLIC,
    GPIO1_NON_DIRECT_PLIC,
    GPIO2_NON_DIRECT_PLIC
};

/*-------------------------------------------------------------------------*//**
 * Local functions
 */
static uint8_t gpio_number_validate(GPIO_TypeDef const * gpio, mss_gpio_id_t gpio_idx);

/*-------------------------------------------------------------------------*//**
 * MSS_GPIO_init
 * See "mss_gpio.h" for details of how to use this function.
 */
void
MSS_GPIO_init
(
    GPIO_TypeDef * gpio
)
{
    /* clear all pending interrupts*/
    gpio->GPIO_IRQ = 0xFFFFFFFFU;
}

/*-------------------------------------------------------------------------*//**
 * MSS_GPIO_config
 * See "mss_gpio.h" for details of how to use this function.
 */
void MSS_GPIO_config
(
    GPIO_TypeDef * gpio,
    mss_gpio_id_t port_id,
    uint32_t config
)
{
    if (0U == gpio_number_validate(gpio, port_id))
    {
        gpio->GPIO_CFG[port_id] = config;
    }
    else
    {
        ASSERT(0); /*LDRA warning*/
    }
}

/*-------------------------------------------------------------------------*//**
 * MSS_GPIO_config_byte
 * See "mss_gpio.h" for details of how to use this function.
 */
void MSS_GPIO_config_byte
(
    GPIO_TypeDef * gpio,
    mss_gpio_byte_num_t byte_num,
    uint32_t config
)
{
    if (((GPIO0_LO == gpio) || (GPIO0_HI == gpio)) &&
                                                 (byte_num >= MSS_GPIO_BYTE_1))
    {
        ASSERT(0);
    }
    else if (((GPIO1_LO == gpio) || (GPIO1_HI == gpio)) &&
                                                  (byte_num > MSS_GPIO_BYTE_2))
    {
        ASSERT(0);
    }
    else if (((GPIO2_LO == gpio) || (GPIO2_HI == gpio)) &&
                                                  (byte_num > MSS_GPIO_BYTE_3))
    {
        ASSERT(0);
    }
    else
    {
        gpio->GPIO_CFG_BYTE[byte_num] = config;
    }
}

/*-------------------------------------------------------------------------*//**
 * MSS_GPIO_config_all
 * See "mss_gpio.h" for details of how to use this function.
 */
void MSS_GPIO_config_all
(
    GPIO_TypeDef * gpio,
    uint32_t config
)
{
    gpio->GPIO_CFG_ALL = config;
}

/*-------------------------------------------------------------------------*//**
 * MSS_GPIO_set_output
 * See "mss_gpio.h" for details of how to use this function.
 */
void MSS_GPIO_set_output
(
    GPIO_TypeDef * gpio,
    mss_gpio_id_t port_id,
    uint8_t value
)
{
    uint32_t gpio_setting;
    
    if (0U == gpio_number_validate(gpio, port_id))
    {
        /* Setting the bit in GPIO_SET_BITS (offset 0xA4) sets the corresponding
         * output port.
         * Setting the bit in GPIO_CLR_BITS (offset 0xA0) clears the
         * corresponding output port.*/

        if (value > 0u)
        {
            gpio->GPIO_SET_BITS = ((uint32_t)0x01 << port_id);
        }
        else
        {
            gpio->GPIO_CLR_BITS = ((uint32_t)0x01 << port_id);
        }
    }
    else
    {
        ASSERT(0); /*LDRA warning*/
    }
}

/*-------------------------------------------------------------------------*//**
 * MSS_GPIO_drive_inout
 * See "mss_gpio.h" for details of how to use this function.
 */
void MSS_GPIO_drive_inout
(
    GPIO_TypeDef * gpio,
    mss_gpio_id_t port_id,
    mss_gpio_inout_state_t inout_state
)
{
    uint32_t outputs_state;
    uint32_t config;
    
    if (0U == gpio_number_validate(gpio, port_id))
    {
        switch (inout_state)
        {
            case MSS_GPIO_DRIVE_HIGH:
                /* Set output high */
                gpio->GPIO_SET_BITS = ((uint32_t)1 << port_id);

                /* Enable output buffer */
                config = gpio->GPIO_CFG[port_id];
                config |= OUTPUT_BUFFER_ENABLE_MASK;
                gpio->GPIO_CFG[port_id] = config;
            break;

            case MSS_GPIO_DRIVE_LOW:
                /* Set output low */
                gpio->GPIO_CLR_BITS = (uint32_t)1 << port_id;
                /* Enable output buffer */
                config = gpio->GPIO_CFG[port_id];
                config |= OUTPUT_BUFFER_ENABLE_MASK;
                gpio->GPIO_CFG[port_id] = config;
            break;

            case MSS_GPIO_HIGH_Z:
                /* Disable output buffer */
                config = gpio->GPIO_CFG[port_id];
                config &= ~OUTPUT_BUFFER_ENABLE_MASK;
                gpio->GPIO_CFG[port_id] = config;
            break;

            default:
                ASSERT(0);
            break;
        }
    }
    else
    {
        ASSERT(0); /*LDRA warning*/
    }
}

/*-------------------------------------------------------------------------*//**
 * MSS_GPIO_enable_irq
 * See "mss_gpio.h" for details of how to use this function.
 */
void MSS_GPIO_enable_irq
(
    GPIO_TypeDef * gpio,
    mss_gpio_id_t port_id
)
{
    uint32_t cfg_value;

    if (0U == gpio_number_validate(gpio, port_id))
    {
        cfg_value = gpio->GPIO_CFG[(uint8_t)port_id];
        gpio->GPIO_CFG[(uint8_t)port_id] = (cfg_value | GPIO_INT_ENABLE_MASK);

        if ((GPIO0_LO == gpio) || (GPIO0_HI == gpio))
        {
            PLIC_EnableIRQ(g_gpio_irqn_lut[port_id]);
        }
        else if ((GPIO1_LO == gpio) || (GPIO1_HI == gpio))
        {
            PLIC_EnableIRQ(g_gpio_irqn_lut[port_id +
                                           GPIO1_BIT0_or_GPIO2_BIT14_PLIC_14]);
        }
        else if ((GPIO2_LO == gpio) || (GPIO2_HI == gpio))
        {
            PLIC_EnableIRQ(g_gpio_irqn_lut[port_id]);
        }
        else
        {
            ASSERT(0); /*LDRA warning*/
        }
    }
    else
    {
        ASSERT(0); /*LDRA warning*/
    }
}

/*-------------------------------------------------------------------------*//**
 * MSS_GPIO_disable_irq
 * See "mss_gpio.h" for details of how to use this function.
 */

void MSS_GPIO_disable_irq
(
    GPIO_TypeDef * gpio,
    mss_gpio_id_t port_id
)
{
    uint32_t cfg_value;

    if (0U == gpio_number_validate(gpio, port_id))
    {
        cfg_value = gpio->GPIO_CFG[(uint8_t)port_id];
        gpio->GPIO_CFG[(uint8_t)port_id] = (cfg_value & (~GPIO_INT_ENABLE_MASK));

        if ((GPIO0_LO == gpio) || (GPIO0_HI == gpio))
        {
            PLIC_DisableIRQ(g_gpio_irqn_lut[port_id]);
        }
        else if ((GPIO1_LO == gpio) || (GPIO1_HI == gpio))
        {
            PLIC_DisableIRQ(g_gpio_irqn_lut[port_id +
                                            GPIO1_BIT0_or_GPIO2_BIT14_PLIC_14]);
        }
        else if ((GPIO2_LO == gpio) || (GPIO2_HI == gpio))
        {
            PLIC_DisableIRQ(GPIO2_NON_DIRECT_PLIC);
        }
        else
        {
            ASSERT(0); /*LDRA warning*/
        }
    }
    else
    {
        ASSERT(0); /*LDRA warning*/
    }
}

/*-------------------------------------------------------------------------*//**
 * MSS_GPIO_enable_nondirect_irq
 * See "mss_gpio.h" for details of how to use this function.
 */
void
MSS_GPIO_enable_nondirect_irq
(
    GPIO_TypeDef const * gpio
)
{
    if ((GPIO0_LO == gpio) || (GPIO0_HI == gpio))
    {
        PLIC_EnableIRQ(GPIO0_NON_DIRECT_PLIC);
    }
    else if ((GPIO1_LO == gpio) || (GPIO1_HI == gpio))
    {
        PLIC_EnableIRQ(GPIO1_NON_DIRECT_PLIC);
    }
    else if ((GPIO2_LO == gpio) || (GPIO2_HI == gpio))
    {
        PLIC_EnableIRQ(GPIO2_NON_DIRECT_PLIC);
    }
    else
    {
        ASSERT(0); /*LDRA warning*/
    }
}

/*-------------------------------------------------------------------------*//**
 * MSS_GPIO_disable_nondirect_irq
 * See "mss_gpio.h" for details of how to use this function.
 */
void
MSS_GPIO_disable_nondirect_irq
(
    GPIO_TypeDef const * gpio
)
{
    if ((GPIO0_LO == gpio) || (GPIO0_HI == gpio))
    {
        PLIC_DisableIRQ(GPIO0_NON_DIRECT_PLIC);
    }
    else if ((GPIO1_LO == gpio) || (GPIO1_HI == gpio))
    {
        PLIC_DisableIRQ(GPIO1_NON_DIRECT_PLIC);
    }
    else if ((GPIO2_LO == gpio) || (GPIO2_HI == gpio))
    {
        PLIC_DisableIRQ(GPIO2_NON_DIRECT_PLIC);
    }
    else
    {
        ASSERT(0); /*LDRA warning*/
    }
}

/*-------------------------------------------------------------------------*//**
 * MSS_GPIO_clear_irq
 * See "mss_gpio.h" for details of how to use this function.
 */
void MSS_GPIO_clear_irq
(
    GPIO_TypeDef * gpio,
    mss_gpio_id_t port_id
)
{
    if (0U == gpio_number_validate(gpio, port_id))
    {
        gpio->GPIO_IRQ = ((uint32_t)1) << port_id;
        __asm("fence");
    }
    else
    {
        ASSERT(0); /*LDRA warning*/
    }
}

static uint8_t gpio_number_validate(GPIO_TypeDef const * gpio, mss_gpio_id_t gpio_idx)
{
    uint8_t ret;

    if (((GPIO0_LO == gpio) || (GPIO0_HI == gpio)) &&
                                                (gpio_idx >= NB_OF_GPIO_GPIO0))
    {
        ret = 1u;
    }
    else if (((GPIO1_LO == gpio) || (GPIO1_HI == gpio)) &&
                                                (gpio_idx >= NB_OF_GPIO_GPIO1))
    {
        ret = 1u;
    }
    else if (((GPIO2_LO == gpio) || (GPIO2_HI == gpio)) &&
                                                (gpio_idx >= NB_OF_GPIO_GPIO2))
    {
        ret = 1u;
    }
    else
    {
        ret = 0u;
    }

    return ret;
}

#ifdef __cplusplus
}
#endif
