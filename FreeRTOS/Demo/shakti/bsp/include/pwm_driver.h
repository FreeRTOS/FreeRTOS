/***************************************************************************
* Project               	 : shakti devt board
* Name of the file	         : pwm_driver.h
* Brief Description of file      : Header file for PWM Driver.
* Name of Author    	         : Abhinav Ramnath
* Email ID                       : abhinavramnath13@gmail.com

Copyright (C) 2019  IIT Madras. All rights reserved.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
***************************************************************************/
/**
 * @file pwm_driver.h
 * @brief Header file for PWM Driver.
 * @detail the header file for the pwm module which is used to change the frequency, period and duty registers
 */

#ifndef PWM_DRIVER_H
#define PWM_DRIVER_H

#include<stdbool.h>
#include<stdint.h>

typedef struct{
	uint16_t period;
	uint16_t reserved1;
	uint16_t duty;
	uint16_t reserved2;
	uint8_t control;
	uint8_t reserved3;
	uint16_t reserved4;
	uint16_t clock;
}pwm_struct;

#define MAX_PWM_COUNT 6
// PWM Registers 
#define PERIOD_REGISTER     0x00000000	//16 bits (short)
#define DUTY_REGISTER       0x00000004	//16 bits (short)
#define CONTROL_REGISTER    0x00000008	//8 bits (char)
#define CLOCK_REGISTER      0x0000000c	//16 bits (short)

// Control Register Individual Bits 
#define CLOCK_SELECTOR      0x00000001
#define PWM_ENABLE          0x00000002
#define PWM_START           0x00000004
#define CONTINUOUS_ONCE     0x00000008
#define PWM_OUTPUT_ENABLE   0x00000010
#define INTERRUPT           0x00000020
#define READ_ONLY           0x00000040
#define RESET_COUNTER       0x00000080

// PWM Modules 
#define PWM_0 0
#define PWM_1 1
#define PWM_2 2
#define PWM_3 3
#define PWM_4 4
#define PWM_5 5

extern pwm_struct *pwm_instance[MAX_PWM_COUNT];

//function prototype
void pwm_configure(uint32_t module_number, uint32_t clock_divisor, uint32_t
		   period, uint32_t duty, bool external_clock);
void pwm_start(uint32_t module_number, uint32_t mode);
uint32_t pwm_check_continuous_mode(uint32_t module_number);
void pwm_clear_registers(uint32_t module_number);
void pwm_init(void);
void pwm_set_external_clock(uint32_t module_number, bool value);
void pwm_set_clock(uint32_t module_number, uint32_t clock_divisor);
void pwm_set_duty_cycle(uint32_t module_number, uint32_t duty);
void pwm_set_periodic_cycle(uint32_t module_number, uint32_t period);
void pwm_stop(uint32_t module_number);
void show_register_values(uint32_t module_number);
uint32_t set_pwm_period_register(uint32_t module_number, uint32_t value);
uint32_t set_pwm_duty_register(uint32_t module_number, uint32_t value);
uint32_t set_pwm_control_register(uint32_t module_number, uint32_t value);
uint32_t set_pwm_clock_register(uint32_t module_number, uint32_t value);
uint32_t configure_control_register_mode(uint32_t mode);
void pwm_use_external_clock(uint32_t module_number, bool value);
#endif
