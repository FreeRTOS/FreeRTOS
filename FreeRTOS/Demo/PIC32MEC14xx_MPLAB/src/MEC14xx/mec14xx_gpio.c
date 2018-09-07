/*****************************************************************************
* © 2014 Microchip Technology Inc. and its subsidiaries.
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
*****************************************************************************/


/** @file mec14xx_gpio.c
 *MEC14xx GPIO hardware access
 */
/** @defgroup MEC14xx Peripherals GPIO
 *  @{
 */


#include "appcfg.h"
#include "platform.h"
#include "MEC14xx/mec14xx.h"
#include "MEC14xx/mec14xx_gpio.h"



static uint32_t gpio_has_drv_str ( enum gpio_id_t gpio_id );


#ifdef ENABLE_GPIO_PIN_VALIDATION

static const uint32_t gpio_port_bitmaps[NUM_GPIO_PORTS] = 
{
    (GPIO_PORT_A_BITMAP),
    (GPIO_PORT_B_BITMAP),
    (GPIO_PORT_C_BITMAP),
    (GPIO_PORT_D_BITMAP)
};

#endif

// 
// Drive Strength Register bitmap
//
static const uint32_t gpio_drv_str_bitmap[NUM_GPIO_PORTS] = 
{
    (GPIO_PORT_A_DRVSTR_BITMAP),
    (GPIO_PORT_B_DRVSTR_BITMAP),
    (GPIO_PORT_C_DRVSTR_BITMAP),
    (GPIO_PORT_D_DRVSTR_BITMAP)
};


struct gpio_cfg 
{
   uint16_t bit_mask;
   uint8_t bit_pos;
};

static const struct gpio_cfg gpio_cfg_tbl[GPIO_PROP_MAX] = 
{
   { 0x0003u, 0x00u },
   { 0x000Cu, 0x02u },
   { 0x00F0u, 0x04u },
   { 0x0100u, 0x08u },
   { 0x0200u, 0x09u },
   { 0x0400u, 0x0Au },
   { 0x0800u, 0x0Bu },
   { 0x3000u, 0x0Cu },
   { 0x3FFFu, 0x00u }
};

static uint32_t gpio_pin_ctrl_addr(enum gpio_id_t gpio_id)
{
    return ((uint32_t)(GPIO_BASE) + (uint32_t)(gpio_id << 2));
}

#ifdef ENABLE_GPIO_PIN_VALIDATION

/**
 * gpio_is_valid - local helper checks if GPIO pin is 
 * implemented in this hardware. 
 * 
 * @author sworley 
 * 
 * @param gpio_id 0-based GPIO ID
 * 
 * @return uint8_t Non-zero(GPIO Pin implemented), 0(not 
 *         implemented).
 */
static uint8_t gpio_is_valid ( enum gpio_id_t gpio_id )
{
   uint16_t gp_bank;

   gp_bank = 0;

   if ( (uint16_t)gpio_id < (uint16_t)(MAX_GPIO_ID) )
   {
      gp_bank = (uint16_t)gpio_id >> 5;
      if ( gpio_port_bitmaps[gp_bank] & (1 << (gpio_id & 0x001Fu)) )
      { 
         return true;
      }
   }

   return false;
}

#else
static uint32_t gpio_is_valid(enum gpio_id_t gpio_id) { return true; }

#endif

static uint8_t gpio_bank_num(enum gpio_id_t gpio_id)
{
    return (uint8_t)(gpio_id) >> 5;
}


static uint8_t gpio_pin_num(enum gpio_id_t gpio_id)
{
    return (uint8_t)(gpio_id) & 0x1Fu;
}


/**
 * gpio_has_drv_str - Local helper to check if GPIO pin has 
 * associated drive strength register. 
 * 
 * @author sworley 
 * 
 * @param gpio_id 0-based GPIO ID
 * 
 * @return uint32_t 0(No Drive Strength), Non-zero(Physical 
 *         address of Drive Strength Register).
 */
static uint32_t gpio_has_drv_str ( enum gpio_id_t gpio_id )
{
    uint32_t bank, bitpos, addr;
    
    addr = 0ul;
    if ( gpio_id < MAX_GPIO_ID )
    {
        bank = gpio_bank_num(gpio_id);
        bitpos = gpio_pin_num(gpio_id);
        if ( gpio_drv_str_bitmap[bank] & (1ul << bitpos) )
        {
            addr = (GPIO_PCTRL2_BASE) + ((uint32_t)(gpio_id) << 2);
            if ( gpio_id > GPIO_0077_ID )
            {
                addr -= 0x20ul;
            }
        }
    }
    
    return addr;
}


uint16_t GPIOGetConfig(enum gpio_id_t gpio_id)
{
    if (gpio_is_valid(gpio_id)) {
        return  *((volatile uint16_t *)gpio_pin_ctrl_addr(gpio_id));
    } else {
        return 0u;
    }
}


void GPIOSetConfig(enum gpio_id_t gpio_id, uint16_t config)
{
    volatile uint16_t * p;
    
    if (gpio_is_valid(gpio_id)) {
        p = (volatile uint16_t *)gpio_pin_ctrl_addr(gpio_id);
        *p = config;
    }
}


void GPIOConfigAndOr(enum gpio_id_t gpio_id, uint16_t and_mask, uint16_t or_mask)
{
    volatile uint16_t * p;


    if (gpio_is_valid(gpio_id)) {
        p = (volatile uint16_t *)gpio_pin_ctrl_addr(gpio_id);
        *p = (*p & and_mask) | or_mask;
    }
}


uint32_t GPIOGetControl(enum gpio_id_t gpio_id)
{
    if (gpio_is_valid(gpio_id)) {
        return *((volatile uint32_t *)gpio_pin_ctrl_addr(gpio_id));
    } else {
        return 0xFFFFFFFFul;
    }
}


void GPIOSetControl(enum gpio_id_t gpio_id, uint32_t ctrl_val)
{
    volatile uint32_t * p;
    
    if (gpio_is_valid(gpio_id)) {
        p = (volatile uint32_t *)gpio_pin_ctrl_addr(gpio_id);
        *p = ctrl_val;
    }
}


void GPIOControlAndOr(enum gpio_id_t gpio_id, uint32_t and_mask, uint32_t or_mask)
{
    volatile uint32_t * p;

    if (gpio_is_valid(gpio_id)) {
        p = (volatile uint32_t *)gpio_pin_ctrl_addr(gpio_id);
        *p = (*p & and_mask) | or_mask;
    }
}


/**
 * GPIOPropertySet - Program specified GPIO Pin configuration 
 * item. 
 * 
 * @author sworley 
 * 
 * @param gpio_id 0-based GPIO ID
 * @param gpio_prop enumerated GPIO Property(configuration item)
 * @param prop_val new property value
 */
void GPIOPropertySet ( enum gpio_id_t gpio_id, 
                       enum gpio_prop_t gpio_prop,
                       uint16_t prop_val
                     )
{
    volatile uint16_t * p;
    uint16_t gp_cfg;
  
    gp_cfg = 0u;

    if ( gpio_is_valid(gpio_id) && ((uint16_t)gpio_prop < (uint16_t)GPIO_PROP_MAX) )
    {
        p = (volatile uint16_t *)gpio_pin_ctrl_addr(gpio_id);
        gp_cfg = *p;
        gp_cfg &= ~(gpio_cfg_tbl[gpio_prop].bit_mask);
        gp_cfg |= (prop_val << gpio_cfg_tbl[gpio_prop].bit_pos) & 
                  gpio_cfg_tbl[gpio_prop].bit_mask; 
        *p = gp_cfg;
    }
}


/**
 * GPIOGetSlewRate - Return GPIO Pin Slew Rate
 * 
 * @author sworley 
 * 
 * @param gpio_id 0-based GPIO ID
 * 
 * @return uint8_t GPIO Pin Slew Rate: 0(Slow) or 1(Fast)
 */
uint8_t GPIOGetSlewRate( enum gpio_id_t gpio_id )
{
    uint32_t addr;
    uint8_t slew;
    
    addr = gpio_has_drv_str(gpio_id);
    if ( 0ul != addr )
    {
        slew = ((*(volatile uint8_t *)addr) >> GPIO_DRV_SLEW_BITPOS) & 0x01u;
    }
    else
    {
        slew = 0u;
    }
    
    return slew;
}


/**
 * GPIOSetSlewRate - Program GPIO Pin's Slew Rate
 * 
 * @author sworley 
 * 
 * @param gpio_id 0-based GPIO ID
 * @param slew_rate new slew rate: 0(Slow), Non-zero(Fast)
 */
void GPIOSetSlewRate ( enum gpio_id_t gpio_id,
                       enum gpio_slew_rate_t slew_rate )
{
    uint32_t addr;
    
    addr = gpio_has_drv_str(gpio_id );
    if ( addr )
    {
        *(volatile uint8_t *)addr = (*(volatile uint8_t *)addr & 
            ~(GPIO_DRV_SLEW_MASK)) | 
            ((slew_rate << (GPIO_DRV_SLEW_BITPOS)) & (GPIO_DRV_SLEW_MASK));
    }
}


/**
 * GPIOGetDriveStr - Get GPIO Pin's Drive Strength 
 * 
 * @author sworley 
 * 
 * @param gpio_id 0-based GPIO ID
 * 
 * @return uint8_t Pin Drive Strength: 0=2mA, 1=4mA, 2=8mA, 
 *         3=12mA.
 */
uint8_t GPIOGetDriveStr ( enum gpio_id_t gpio_id )
{
    uint32_t addr;
    
    addr = gpio_has_drv_str(gpio_id );
    if ( addr )
    {
        return ((*(volatile uint8_t *)addr) >> GPIO_DRV_STR_BITPOS) & (GPIO_DRV_STR_MASK);
    }
    else
    {
        return 0u;
    }
}


/**
 * GPIOSetDriveStr - Program GPIO Pin's Drive Strength
 * 
 * @author sworley 
 * 
 * @param gpio_id 0-based GPIO ID
 * @param drv_str enumerated drive strength: 0=2mA, 1=4mA, 
 *                2=8mA, 3=12mA
 */
void GPIOSetDriveStr ( enum gpio_id_t gpio_id,
                       enum gpio_drv_str_t drv_str )
{
    uint32_t addr;
    uint8_t r8;
    
    addr = gpio_has_drv_str(gpio_id);
    if ( addr )
    {
        r8 = *(volatile uint8_t *)addr & ~(GPIO_DRV_STR_MASK);
        r8 += ((drv_str << GPIO_DRV_STR_BITPOS) & GPIO_DRV_STR_MASK);
        *(volatile uint8_t *)addr = r8;
    }
}


/**
 * GPIOGetDriveStrAndSlew - Return combined value representing 
 * Drive Strength and Slew Rate. 
 * 
 * @author sworley 
 * 
 * @param gpio_id 0-based GPIO ID
 * 
 * @return uint8_t bit[0] = Slew Rate, bits[3:1]=0(Reserved), 
 *         bits[5:4]=Drive Strength, bits[7:6]=0(Reserved)
 */
uint8_t GPIOGetDriveStrAndSlew ( enum gpio_id_t gpio_id )
{
    uint32_t addr;
    
    addr = gpio_has_drv_str(gpio_id );
    if ( addr )
    {
        return (*(volatile uint8_t *)addr);
    }
    else
    {
        return 0u;
    }
}


/**
 * GPIOSetDriveStrAndSlew - Program GPIO Pin's drive strength 
 * and slew rate. 
 * 
 * @author sworley 
 * 
 * @param gpio_id 0-based GPIO ID
 * @param drv_and_slew bit[0] = Slew Rate, bits[3:1]=0(Reserved), 
 *         bits[5:4]=Drive Strength, bits[7:6]=0(Reserved)
 */
void GPIOSetDriveStrAndSlew ( enum gpio_id_t gpio_id,
                              uint8_t drv_and_slew )
{
    uint32_t addr;
    uint8_t r8;
    
    addr = gpio_has_drv_str(gpio_id);
    if ( addr )
    {
        r8 = *(volatile uint8_t *)addr & ~(GPIO_DRV_SLEW_MASK + GPIO_DRV_STR_MASK);
        r8 |= (drv_and_slew & (GPIO_DRV_SLEW_MASK + GPIO_DRV_STR_MASK));
        *(volatile uint8_t *)addr = r8;
    }
}


/**
 * GPIOSetOutput - Program GPIO Pin's output state using Pin 
 * configuration register (not parallel output register). 
 * 
 * @author sworley 
 * 
 * @param gpio_id 0-based GPIO ID
 * @param gpio_state pin state: actual pin state at pad will 
 *                   depend upon GPIO Output invert
 *                   configuration.
 * @note peforms a byte wide write to byte offset 2 of the GPIO 
 *       Pin's 32-bit configuration register. No
 *       read-modify-write.
 */
void GPIOSetOutput ( enum gpio_id_t gpio_id, 
                     uint8_t gpio_state
                     )
{
    volatile uint8_t * p;
    
    if ( gpio_is_valid(gpio_id) )
    {
        p = (volatile uint8_t *)(gpio_pin_ctrl_addr(gpio_id) + 2ul);
        if (gpio_state) {
            *p = 0x01u;
        } else {
            *p = 0u;
        }
    }
}


void GPIOToggleOutput ( enum gpio_id_t gpio_id )
{
    volatile uint8_t * p;

    if ( gpio_is_valid(gpio_id) )
    {
        p = (volatile uint8_t *)(gpio_pin_ctrl_addr(gpio_id) + 2ul);
        *p ^= 0x01u;
    }
}


/**
 * GPIOReadPin - Read GPIO Pin's Pad Input from configuration 
 * register. 
 * 
 * @author sworley 
 * 
 * @param gpio_id 0-based GPIO ID.
 * 
 * @return uint8_t 0 or 1 depending upon the state of the GPIO 
 *         pad.
 * @note performs a byte read of offset 3 of the GPIO Pin's 
 *       32-bit configuration register.
 */
uint8_t GPIOReadPin( enum gpio_id_t gpio_id )
{
    if ( gpio_is_valid(gpio_id) )
    {
        return *((volatile uint8_t *)(gpio_pin_ctrl_addr(gpio_id) + 3ul));
    } 
    else 
    {
        return 0u;
    }
}


/** GPIOPinLock - Lock specified GPIO's control register.
 *  @param enum gpio_id_t zero based GPIO ID
 *  @note Lock bit is only cleared on POR. Lock registers
 *  are in reverse order, first register is at top address.
 *  GPIO_LOCK_BASE defined to top(first) register address.
 *  */ 
void GPIOPinLock(enum gpio_id_t gpio_id)
{
    uint32_t addr;
    uint8_t bank, bitpos;

    if (gpio_is_valid(gpio_id)) {
        bank = gpio_bank_num(gpio_id);  // 0 - 4
        bitpos = gpio_pin_num(gpio_id); // 0 - 31
        addr = (uint32_t)(GPIO_LOCK_BASE) - (bank << 2);
        *(volatile uint32_t *)addr |= (1ul << bitpos);
    } 
}


/* end mec14xx_gpio.c */
/**   @}
 */

