/**
 * \file
 *
 * \brief PWM Normal mode (i.e. non-split) declaration.
 *
 (c) 2018 Microchip Technology Inc. and its subsidiaries.

    Subject to your compliance with these terms,you may use this software and
    any derivatives exclusively with Microchip products.It is your responsibility
    to comply with third party license terms applicable to your use of third party
    software (including open source software) that may accompany Microchip software.

    THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS". NO WARRANTIES, WHETHER
    EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE, INCLUDING ANY IMPLIED
    WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY, AND FITNESS FOR A
    PARTICULAR PURPOSE.

    IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
    INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
    WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
    BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE. TO THE
    FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL CLAIMS IN
    ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF FEES, IF ANY,
    THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
 *
 */

#ifndef PWM_BASIC_H_INCLUDED
#define PWM_BASIC_H_INCLUDED

#include <compiler.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef void (*pwm_irq_cb_t)(void);

#define PWM_0_INTERRUPT_CB_RATE 0

/** The datatype matching the bitwidth of the PWM hardware */
typedef uint8_t PWM_0_register_t;

int8_t PWM_0_init(void);

void PWM_0_enable();

void PWM_0_disable();

void PWM_0_enable_output_ch0();

void PWM_0_disable_output_ch0();

void PWM_0_enable_output_ch1();

void PWM_0_disable_output_ch1();

void PWM_0_load_counter(PWM_0_register_t counter_value);

void PWM_0_load_duty_cycle_ch0(PWM_0_register_t duty_value);

void PWM_0_load_duty_cycle_ch1(PWM_0_register_t duty_value);

void PWM_0_register_callback(pwm_irq_cb_t f);

#ifdef __cplusplus
}
#endif

#endif /* PWM_BASIC_H_INCLUDED */
