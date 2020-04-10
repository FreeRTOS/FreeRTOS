/**
 * \file
 *
 * \brief PWM Basic driver example.
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

#include <atmel_start.h>
#include <pwm_basic_example.h>
#include <pwm_basic.h>
#include <atomic.h>

volatile uint16_t         PWM_0_isr_executed_counter = 0;
volatile PWM_0_register_t PWM_0_duty;

void PWM_0_pwm_handler_cb(void)
{
	PWM_0_duty++;
	// Output duty cycle on PWM CH0
	PWM_0_load_duty_cycle_ch0(PWM_0_duty);
	PWM_0_isr_executed_counter++;
}

uint8_t PWM_0_test_pwm_basic(void)
{

	// Enable pin output
	PWM_0_enable_output_ch0();

	// Set channel 0 duty cycle value register value to specified value
	PWM_0_load_duty_cycle_ch0(0x3f);

	// Set counter register value
	PWM_0_load_counter(0);

	// Test IRQ mode

	ENABLE_INTERRUPTS();

	PWM_0_register_callback(PWM_0_pwm_handler_cb);

	// Wait for ISR to be executed 65000 times
	while (PWM_0_isr_executed_counter < 65000)
		;

	return 1;
}
