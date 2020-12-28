/***************************************************************************
* Project               	  : shakti devt board
* Name of the file	          : pwm_driver.c
* Brief Description of file       : PWM Driver Code.
* Name of Author    	          : Abhinav Ramnath
* Email ID                        : abhinavramnath13@gmail.com

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
@file pwm_driver.c
@brief source file for pwm
@detail the device driver for the pwm module which is used to change the frequency, period and duty registers 
*/

#include "pwm_driver.h"
#include "platform.h"
#include "log.h"

#define PERIOD_REGISTER_MAX     0x0000FFFF
#define DUTY_REGISTER_MAX       0x0000FFFF
#define CLOCK_REGISTER_MAX      0x0000FFFF
#define CONTROL_REGISTER_MAX    0x000000FF

pwm_struct* pwm_instance[MAX_PWM_COUNT];

/** @fn uint32_t set_pwm_period_register(uint32_t module_number, uint32_t value)
 * @brief Function to set the period register of the selected pwm module
 * @details This function will be called to set the value of the period
 register for the selected module
 * @param uint32_t module_number- specifies the pwm module to be selected
 * @param uint32_t value - value to be set between 0x0000 to 0xffff.
 * @return uint32_t returns 1 on success, 0 on failure.
 */
uint32_t set_pwm_period_register(uint32_t module_number, uint32_t value)
{
	if (value > PERIOD_REGISTER_MAX)
	{
		log_error("\nPeriod Register Value higher than max value (%x)",
			  PERIOD_REGISTER_MAX);
		return 0;
	}

	pwm_instance[module_number]->period = value;

	log_debug("\n Period Register of module number %d set to %x",
		 module_number, value);

	return 1;
}

/** @fn uint32_t set_pwm_duty_register(uint32_t module_number, uint32_t value)
 * @brief Function to set the duty register of the selected pwm module
 * @details This function will be called to set the value of the duty register for the selected module
 * @param uint32_t module_number- specifies the pwm module to be selected
 * @param uint32_t value - value to be set between 0x0000 to 0xffff.
 * @return uint32_t returns 1 on success, 0 on failure.
 */
uint32_t set_pwm_duty_register(uint32_t module_number, uint32_t value)
{
	if (value > DUTY_REGISTER_MAX) {
		log_error("\nDuty Register Value higher than max value (%x)",
			  DUTY_REGISTER_MAX);
		return 0;
	}

	pwm_instance[module_number]->duty = value;

	log_debug("\n Duty Register of module number %d set to %x",
		 module_number, pwm_instance[module_number]->duty);

	return 1;
}

/** @fn uint32_t set_pwm_control_register(uint32_t module_number, uint32_t value)
 * @brief Function to set the control register of the selected pwm module
 * @details This function will be called to set the value of the control register for the selected module
 * @param uint32_t module_number- specifies the pwm module to be selected
 * @param uint32_t value - value to be set between 0x0000 to 0xff.
 * @return uint32_t returns 1 on success, 0 on failure.
 */
uint32_t set_pwm_control_register(uint32_t module_number, uint32_t value)
{
	if (value > CONTROL_REGISTER_MAX) {
		log_error("\nControl Register Value higher than max value (%x)",
			  CONTROL_REGISTER_MAX);
		return 0;
	}

	pwm_instance[module_number]->control = value;

	log_info("\n Control Register of module number %d set to %x",
		 module_number, pwm_instance[module_number]->control);

	return 1;
}

/** @fn uint32_t pwm_check_continuous_mode(uint32_t module_number)
 * @brief Function to check if continuous mode is set for current pwm module.
 (This function helps in handling interrupts using plic).
 * @details This function will be called to check if continuous mode is set
 for current pwm module
 * @param uint32_t module_number- specifies the pwm module to be selected 
 * @return uint32_t returns 1 if running in continuous mode, 0 if not.
 */
uint32_t pwm_check_continuous_mode(__attribute__ ((unused)) uint32_t module_number)
{
	uint32_t value = pwm_instance[module_number]->control &  CONTINUOUS_ONCE;

	log_debug("\n Running in continuous mode(1/0): %x", (value));

	if(value)
		return 1;
	else
		return 0;
}

/** @fn uint32_t set_pwm_clock_register(uint32_t module_number, uint32_t value)
 * @brief Function to set the clock register of the selected pwm module
 * @details This function will be called to set the value of the clock register(clock divisor) for the selected module
 * @param uint32_t module_number- specifies the pwm module to be selected
 * @param uint32_t value - value to be set between 0x0000 to 0xffff.
 * @return uint32_t returns 1 on success, 0 on failure.
 */
uint32_t set_pwm_clock_register(__attribute__ ((unused)) uint32_t module_number, uint32_t value)
{
	if (value > CLOCK_REGISTER_MAX) {
		log_error("\nClock Register Value higher than max value (%x)",
			  CLOCK_REGISTER_MAX);
		return 0;
	}
	pwm_instance[module_number]->clock = value;

	return 1;
}

/** @fn void pwm_clear_registers(uint32_t module_number)
 * @brief Function to clear all registers in a specific pwm module
 * @details This function will be called to clear all registers in a specific pwm module
 * @param uint32_t module_number- specifies the pwm module to be selected
 */
void pwm_clear_registers(uint32_t module_number)
{
	set_pwm_period_register(module_number, 0);
	set_pwm_duty_register(module_number, 0);
	set_pwm_control_register(module_number, 0);
	set_pwm_clock_register(module_number, 0);

	log_info("\n All registers of module number %d cleared", module_number);
}

/** @fn void pwm_init
 * @brief Function to initialize all pwm modules
 * @details This function will be called to initialize all pwm modules
 */
void pwm_init(void)
{
	uint32_t i;

	for(i=0; i< MAX_PWM_COUNT; i++)
	{
		pwm_instance[i] = (pwm_struct* )(PWM_BASE_ADDRESS + i*PWM_OFFSET);
	}

	for (i = 0; i < MAX_PWM_COUNT; i++) {
		pwm_clear_registers(i);
	}

	log_debug("\n All Register values of all modules cleared");
}

/** @fn uint32_t configure_control_register_mode(uint32_t mode)
 * @brief Function to set value of control register based on mode selected
 * @details This function will set value of control register based on mode selected
 * @param  uint32_t ( mode-
 *                0-PWM Mode.
 *                1-Timer Mode run once.
 *                2-Timer Mode run continuously.)
 * @return uint32_t (returns value to be set in the control register.)
 */
uint32_t configure_control_register_mode(uint32_t mode)
{
	uint32_t value = 0x0;

	if (mode == 0) {
		log_info("\n Current Module is set to PWM mode");

		value += PWM_ENABLE;
		value += PWM_START;
		value += PWM_OUTPUT_ENABLE;
	}
	else if (mode == 1) {
		log_info("\nCurrent Module is set to timer non-continuous \
			 mode");

		value += PWM_START;
	}
	else if(mode == 2) {
		log_info("\nCurrent Module is set to timer continuous mode");

		value += PWM_START;
		value += CONTINUOUS_ONCE;
	}
	return value;
}

/** @fn void pwm_start(uint32_t module_number, uint32_t mode)
 * @brief Function to start a pwm module with a specific mode
 * @details This function will start a pwm module with a specific mode
 * @param uint32_t module_number-  the pwm module to be selected
 * @param uint32_t (mode - mode to be selected
 *                  0-PWM Mode
 *                  1-Timer Mode run once
 *                  2-Timer Mode run contin )
 */
void pwm_start(uint32_t module_number, uint32_t mode)
{
	uint32_t control = configure_control_register_mode(mode);

	if(set_pwm_control_register(module_number, control))
	{
		log_debug("\nPWM module number %d has been entered", module_number);
	}

	if(!set_pwm_control_register(module_number, control))
	{
		log_error("\n PWM module number %d not entered",module_number);
	}
}

/** @fn void pwm_use_external_clock(uint32_t module_number, bool value)
 * @brief Function to set use of external clock
 * @details This function will set clock to external clock if set to true
 * @param uint32_t (module_number-  the pwm module to be selected )
 * @param uint32_t (value -true or 1  - External Clock
 *                    false or 0 - Internal Clock )
 */
void pwm_use_external_clock(__attribute__ ((unused)) uint32_t module_number,
			    bool value)
{
	/*Set control value clock bit to external or internal source*/
	if(value == 1)
	{
		pwm_instance[module_number]->control |= CLOCK_SELECTOR;
	}
	else if(pwm_instance[module_number]->control  && CLOCK_SELECTOR)
	{
		pwm_instance[module_number]->control -= CLOCK_SELECTOR;
	}
}

/** @fn void pwm_set_clock(uint32_t module_number, uint32_t clock_divisor)
 * @brief Function to set the clock divisor value of a specific pwm module
 * @details This function will set the clock divisor value of a specific pwm module
 * @param uint32_t module_number-  the pwm module to be selected
 uint32_t clock_divisor- value of clock divisor to be used to divide base clock speed of 50MHz.
 */
void pwm_set_clock(uint32_t module_number, uint32_t clock_divisor)
{
	if (set_pwm_clock_register(module_number, clock_divisor) == 0)
	{
		log_error("\n Error in setting clock register");
	}
}

/** @fn void pwm_set_duty_cycle(uint32_t module_number, uint32_t duty)
 * @brief Function to set the duty cycle value of a specific pwm module
 * @details This function will set the duty cycles value of a specific pwm module
 * @param uint32_t module_number-  the pwm module to be selected
 * @param uint32_t duty - value of duty cycles to be used to decide how many period cycles the pwm signal is set to 1.
 */
void pwm_set_duty_cycle(uint32_t module_number, uint32_t duty)
{
	if (set_pwm_duty_register(module_number, duty) == 0) {
		log_error("\n Error in setting duty register");
	}
}

/** @fn  void pwm_set_periodic_cycle(uint32_t module_number, uint32_t period)
 * @brief Function to set the period cycles value of a specific pwm module
 * @details This function will set the period cycles value of a specific pwm module
 * @param uint32_t module_number-  the pwm module to be selected
 * @param uint32_t clock_divisor-  value of period cycles which is used to
 *                 further divide the frequency into fixed period cycles.
 */
void pwm_set_periodic_cycle(uint32_t module_number, uint32_t period)
{
	if(set_pwm_period_register(module_number, period) == 0) {
		log_error("\n Error in setting period register");
	}
}

/** @fn void pwm_configure(uint32_t module_number,uint32_t clock_divisor, uint32_t period, uint32_t duty, bool external_clock)
 * @brief Function to configure the pwm module with all the values required like clock divisor, period, duty cycle, and the use of external clock
 * @details This function configure the pwm module
 * @param uint32_t module_number - the pwm module to be selected
 * @param uint32_t clock_divisor - value of clock divisor to be used it divides the base clock frequency by the given value
 * @param uint32_t period - value of periodic cycle to be used. the signal resets after every count of the periodic cycle
 * @param uint32_t duty_cycle - value of duty cycle. It specifies how many cycles the signal is active out of the periodic cycle
 * @param bool external_clock - value of external clock selector. It specifies if external clock is to be used.
 */
void pwm_configure(uint32_t module_number,uint32_t clock_divisor, uint32_t
		   period, uint32_t duty, bool external_clock)
{
	pwm_set_periodic_cycle(module_number, period);
	pwm_set_duty_cycle(module_number, duty);
	pwm_set_clock(module_number, clock_divisor);
	pwm_use_external_clock(module_number, external_clock);
	log_debug("PWM %d succesfully configured",module_number);
}

/** @fn void pwm_stop(uint32_t module_number)
 * @brief Function to stop a specific pwm module
 * @details This function will stop a specific pwm module
 * @param uint32_t module_number-  the pwm module to be selected
 */
void pwm_stop(uint32_t module_number)
{
	set_pwm_control_register(module_number, 0x0);
	log_debug("\n PWM module number %d has been stopped", module_number);
}

/** @fn void show_register_values(uint32_t module_number)
 * @brief Function to pruint32_t the values of all the registers of a specific pwm module
 * @details This function will pruint32_t the values of all the registers of a specific pwm module
 * @param uint32_t module_number-  the pwm module to be selected
 */
void show_register_values(__attribute__ ((unused)) uint32_t module_number)
{
	log_info("\nThe value of period register is %x",
		 pwm_instance[module_number]->period);
	log_info("\nThe value of duty register is %x",
		 pwm_instance[module_number]->duty);
	log_info("\nThe value of control register is %x",
		 pwm_instance[module_number]->control);
	log_info("\nThe value of clock register is %x",
		 pwm_instance[module_number]->clock);
}
