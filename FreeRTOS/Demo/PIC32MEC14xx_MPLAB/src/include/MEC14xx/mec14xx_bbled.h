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


/** @file mec14xx_bbled.h
 *MEC14xx Blinking Breathing LED definitions
 */
/** @defgroup MEC14xx Peripherals LED
 */

#ifndef _MEC14XX_BBLED_H
#define _MEC14XX_BBLED_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define LED_NUM_BLOCKS                  (3)


#define LED_INSTANCE_OFFSET             (0x100UL)

//
// LED Configuration Register
//
#define LED_CFG_CNTL_MASK               (0x0003u)
#define     LED_CFG_CNTL_LO             (0x0000u)
#define     LED_CFG_CNTL_BREATH         (0x0001u)
#define     LED_CFG_CNTL_BLINK          (0x0002u)
#define     LED_CFG_CNTL_HI             (0x0003u)
#define LED_CFG_CLK_SRC_MCLK            (0x0002u)
#define LED_CFG_CLK_SRC_32K             (0x0000u)
#define LED_CFG_SYNC                    (0x0008u)
#define LED_CFG_PWM_COUNT_WIDTH_MASK    (0x0030u)
#define     LED_CFG_COUNT_WIDTH_8       (0x0000u)
#define     LED_CFG_COUNT_WIDTH_7       (0x0010u)
#define     LED_CFG_COUNT_WIDTH_6       (0x0020u)
#define LED_CFG_EN_UPDATE               (0x0040u)
#define LED_CFG_RESET                   (0x0080u)
#define LED_CFG_WDT_PRELOAD_MASK        (0xFF00u)
#define LED_CFG_WDT_PRELOAD_POR         (0x1400u)
#define LED_CFG_SYMMETRY_EN             (0x10000u)

//
// LED Limit Register
//
#define LED_LIMIT_MIN_BITPOS        (0u)
#define LED_LIMIT_MIN_MASK          (0xFFu)
#define LED_LIMIT_MAX_BITPOS        (8u)
#define LED_LIMIT_MAX_MASK          (0xFF00u)

//
// LED Delay Register
//
#define LED_DELAY_LOW_MASK          (0x0000FFFu)
#define LED_DELAY_HIGH_MASK         (0x0FFF000u)
#define LED_DELAY_HIGH_BITPOS       (12u)

//
// LED Step Size Register
//
#define LED_STEP_FIELD_WIDTH        (4u)
#define LED_STEP0_MASK              (0x0000000Fu)
#define LED_STEP1_MASK              (0x000000F0u)
#define LED_STEP2_MASK              (0x00000F00u)
#define LED_STEP3_MASK              (0x0000F000u)
#define LED_STEP4_MASK              (0x000F0000u)
#define LED_STEP5_MASK              (0x00F00000u)
#define LED_STEP6_MASK              (0x0F000000u)
#define LED_STEP7_MASK              (0xF0000000u)

//
// LED Update Register
//
#define LED_UPDATE_FIELD_WIDTH      (4u)
#define LED_UPDATE0_MASK            (0x0000000Fu)
#define LED_UPDATE1_MASK            (0x000000F0u)
#define LED_UPDATE2_MASK            (0x00000F00u)
#define LED_UPDATE3_MASK            (0x0000F000u)
#define LED_UPDATE4_MASK            (0x000F0000u)
#define LED_UPDATE5_MASK            (0x00F00000u)
#define LED_UPDATE6_MASK            (0x0F000000u)
#define LED_UPDATE7_MASK            (0xF0000000u)


#define BLINK_0P5_HZ_DUTY_CYCLE     (0x010ul)
#define BLINK_0P5_HZ_PRESCALE       (0x0FFul)
#define BLINK_1_HZ_DUTY_CYCLE       (0x020ul)
#define BLINK_1_HZ_PRESCALE         (0x07Ful)


/*****************************************************************************
 * BBLED API
 *****************************************************************************/
#define LED0_ID                     (0x00u)
#define LED1_ID                     (0x01u)
#define LED2_ID                     (0x02u)
#define LED_ID_MAX                  (0x03u)


#define BLINK_0P5_HZ_DUTY_CYCLE     (0x010ul)
#define BLINK_0P5_HZ_PRESCALE       (0x0FFul)
#define BLINK_1_HZ_DUTY_CYCLE       (0x020ul)
#define BLINK_1_HZ_PRESCALE         (0x07Ful)


uint8_t led_get_gpio_num(uint8_t led_id);
void led_init(uint8_t led_id);

void led_sleep_en(uint8_t led_id, uint8_t sleep_en);
void led_reset(uint8_t led_id);

void led_mode_blink(uint8_t led_id,
                    uint8_t duty_cycle,
                    uint16_t prescale);

void led_out_high(uint8_t led_id);
void led_out_low(uint8_t led_id);
void led_out_toggle(uint8_t led_id);

#ifdef __cplusplus
}
#endif

#endif // #ifndef _MEC14XX_BBLED_H
/* end hw_led.h */
/**   @}
 */
