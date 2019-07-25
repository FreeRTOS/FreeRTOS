/*****************************************************************************
* Copyright 2014 Microchip Technology Inc. and its subsidiaries.
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

/** @file mec14xx_bbled.c
 *MEC14xx Breating-Blinking LED definitions
 */
/** @defgroup MEC14xx Peripherals BBLED
 */

#include "appcfg.h"
#include "platform.h"
#include "MEC14xx/mec14xx.h"
#include "MEC14xx/mec14xx_pcr.h"
#include "MEC14xx/mec14xx_bbled.h"
#include "MEC14xx/mec14xx_gpio.h"
#include "MEC14xx/mec14xx_bbled.h"

#ifdef __cplusplus
extern "C" {
#endif


static uint32_t led_addr(uint8_t led_id) 
{
    if (led_id < (LED_ID_MAX) )
    {
        return ((LED0_BASE) + (led_id << 8));
    }
    else
    {
        return (LED0_BASE);
    }
}

#ifdef LED_ENABLE_VALID_CHECK

static uint8_t led_is_valid(uint8_t led_id)
{
    if (led_id < (LED_ID_MAX)) {
        return true;
    }
    return false;
}

#else

static uint8_t led_is_valid(uint8_t led_id) { ( void ) led_id; return (MEC14XX_TRUE); }

#endif


/** 
    @brief MEC1404 LED are alternate functions of GPIO pins. 
    @note - 
        LED0 is GPIO157 Function 1
        LED1 is GPIO156 Function 1
        LED2 is GPIO104 Function 1
*/

static const uint8_t led_pcr_slp2_bitpos[LED_ID_MAX] = {
    (PCR_EC2_LED0_SLP_BITPOS),
    (PCR_EC2_LED1_SLP_BITPOS),
    (PCR_EC2_LED2_SLP_BITPOS)
};


static const uint16_t led_gpio_tbl[LED_ID_MAX] = {
    (((uint16_t)(GPIO_FUNC_1)<<8) + (uint16_t)GPIO_0157_ID),
    (((uint16_t)(GPIO_FUNC_1)<<8) + (uint16_t)GPIO_0156_ID),
    (((uint16_t)(GPIO_FUNC_1)<<8) + (uint16_t)GPIO_0104_ID)
};



/**
 * led_sleep_en - Enable/Disable gating of clocks on idle to the
 * BBLED block 
 *  
 *
 * @param uint8_t sleep_en (1=Enable sleep on idle), (0=No sleep
 *                on idle).
 * @param uint8_t LED ID (0-3)
 * @note if LED ID > 3 no action taken.
 */
void led_sleep_en(uint8_t led_id, uint8_t sleep_en)
{
    uint32_t slp_mask;
    uint32_t laddr;
    
    slp_mask = 0ul;
    if ( led_is_valid(led_id) ) {
        slp_mask = (1ul << led_pcr_slp2_bitpos[led_id]);
        if ( sleep_en ) {
            PCR->EC_SLEEP_EN2 |= slp_mask;
            laddr = led_addr(led_id);
            ((BBLED_TypeDef *)laddr)->CONFIG &= ~(0x03ul);
        } else {
            PCR->EC_SLEEP_EN2 &= ~(slp_mask);
        }
    }
}


/**
 * led_reset - Reset the specified LED hardware block.
 * 
 * @author sworley 
 * 
 * @param led_id 0-based LED ID 
 * @note Sets the LED's soft reset bit and waits for hardware to 
 *       clear it. Will wait up to 0x10000 times.
 */
void led_reset(uint8_t led_id)
{
    uint32_t p;
    uint32_t cnt;

    p = led_addr(led_id);
    ((BBLED_TypeDef *)p)->CONFIG = (LED_CFG_RESET);

    cnt = 0x100000UL;
    while ( ((BBLED_TypeDef *)p)->CONFIG & (LED_CFG_RESET) ) {
        if ( cnt != 0UL ) {
            cnt--;
        } else {
            break;
        }
    }
} 


uint8_t led_get_gpio_num(uint8_t led_id)
{
    return led_gpio_tbl[(led_id & ((LED_ID_MAX)-1u))];
}


/**
 * led_init - Initialize the specified LED 
 * 
 * @author sworley 
 * 
 * @param led_id 0-based LED ID 
 * @note Configures the LED's GPIO pin for LED function and then 
 *       peforms a soft reset of the LED hardware.
 */
void led_init(uint8_t led_id)
{
    uint16_t ledi;

    if ( led_id < LED_ID_MAX )
    {
        /* bits[7:0] = GPIO_ID, bits[15:8] = GPIO Function */
        ledi = led_gpio_tbl[led_id];
        GPIOPropertySet((ledi & 0xFF), GPIO_PROP_MUX_SEL, (ledi >> 8) & 0xFF);
        led_reset(ledi & 0xFF);
    }
}


/**
 * led_mode_blink - Enable LED hardware blink
 * 
 * @author sworley 
 * 
 * @param led_id 0-based LED ID
 * @param duty_cycle duty cycle (0x80 = 50%)
 * @param prescale sets the blink frequency 
 * @note Blink frequency is (32768 * 255)/(prescale + 1) Hz
 */
void led_mode_blink(uint8_t led_id,
                    uint8_t duty_cycle,
                    uint16_t prescale)
{
    uint32_t pLed;

    pLed = 0UL;

    if (led_is_valid(led_id)) {
        pLed = led_addr(led_id);

        ((BBLED_TypeDef *)pLed)->CONFIG = LED_CFG_CNTL_BLINK;
        ((BBLED_TypeDef *)pLed)->LIMIT = (uint32_t)duty_cycle;
        ((BBLED_TypeDef *)pLed)->DELAY = (uint32_t)prescale;
        ((BBLED_TypeDef *)pLed)->CONFIG |= (LED_CFG_EN_UPDATE);
    }
}


/**
 * led_out_toggle - Toggle the LED output pin.
 * 
 * @author sworley 
 * 
 * @param led_id 0-based LED ID.
 */
void led_out_toggle(uint8_t led_id)
{
    uint32_t p;

    if (led_is_valid(led_id)) {
        p = led_addr(led_id);

        if (((BBLED_TypeDef *)p)->CONFIG & LED_CFG_CNTL_MASK) {
            ((BBLED_TypeDef *)p)->CONFIG = LED_CFG_CNTL_LO;
        } else {
            ((BBLED_TypeDef *)p)->CONFIG = LED_CFG_CNTL_HI;
        }
    }
}


/**
 * led_out_high - Set the LED block to drive the pin High
 * 
 * @author sworley 
 * 
 * @param led_id 0-based LED ID 
 * @note The LED controller will drive the pin High. Depending 
 *       upon the external circuit the LED may be in ON or OFF
 *       state.
 */
void led_out_high(uint8_t led_id)
{
    uint32_t p;

    if (led_is_valid(led_id)) {
        p = led_addr(led_id);
        ((BBLED_TypeDef *)p)->CONFIG = LED_CFG_CNTL_HI;
    }
}


/**
 * led_out_low - Set the LED block to drive the pin Low
 * 
 * @author sworley 
 * 
 * @param led_id 0-based LED ID 
 * @note The LED controller will drive the pin Low. Depending 
 *       upon the external circuit the LED may be in ON or OFF
 *       state.
 */
void led_out_low(uint8_t led_id)
{
    uint32_t p;

    if (led_is_valid(led_id)) {
        p = led_addr(led_id);
        ((BBLED_TypeDef *)p)->CONFIG = LED_CFG_CNTL_LO;
    }
}


#ifdef __cplusplus
}
#endif

/* end mec14xx_bbled.h */
/**   @}
 */
