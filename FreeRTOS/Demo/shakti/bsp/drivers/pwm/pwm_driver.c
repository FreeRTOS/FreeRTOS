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

/** @fn int set_pwm_period_register(int module_number, int value)
 * @brief Function to set the period register of the selected pwm module
 * @details This function will be called to set the value of the period register for the selected module 
 * @param int module_number- specifies the pwm module to be selected
 * @param int value - value to be set between 0x0000 to 0xffff.
 * @return int returns 1 on success, 0 on failure.
 */
int set_pwm_period_register(int module_number, int value)
{
	if (value > PERIOD_REGISTER_MAX) {
		log_error("\nPeriod Register Value higher than max value (%x)", PERIOD_REGISTER_MAX);	
		return 0;
	}

	volatile short* period_value;
	period_value = (int*) (PWM_BASE_ADDRESS + module_number*PWM_MODULE_OFFSET + PERIOD_REGISTER);
	*period_value = value;

	log_info("\n Period Register of module number %d set to %x", module_number, value);

	return 1;
}

/** @fn int set_pwm_duty_register(int module_number, int value)
 * @brief Function to set the duty register of the selected pwm module
 * @details This function will be called to set the value of the duty register for the selected module
 * @param int module_number- specifies the pwm module to be selected
 * @param int value - value to be set between 0x0000 to 0xffff.
 * @return int returns 1 on success, 0 on failure.
 */
int set_pwm_duty_register(int module_number, int value)
{
	volatile short* duty_value;

	if (value > DUTY_REGISTER_MAX) {
		log_error("\nDuty Register Value higher than max value (%x)", DUTY_REGISTER_MAX);
		return 0;
	}

	duty_value = PWM_BASE_ADDRESS + module_number*PWM_MODULE_OFFSET + DUTY_REGISTER;
	*duty_value = value;

	log_info("\n Duty Register of module number %d set to %x", module_number, value);

	return 1;
}

/** @fn int set_pwm_control_register(int module_number, int value)
 * @brief Function to set the control register of the selected pwm module
 * @details This function will be called to set the value of the control register for the selected module
 * @param int module_number- specifies the pwm module to be selected
 * @param int value - value to be set between 0x0000 to 0xff.
 * @return int returns 1 on success, 0 on failure.
 */
int set_pwm_control_register(int module_number, int value)
{
	volatile char* control_value;

	if (value > CONTROL_REGISTER_MAX) {
		log_error("\nControl Register Value higher than max value (%x)", CONTROL_REGISTER_MAX);	
		return 0;
	}

	control_value = PWM_BASE_ADDRESS + module_number*PWM_MODULE_OFFSET + CONTROL_REGISTER;
	*control_value = value;

	log_info("\n Control Register of module number %d set to %x", module_number, value);

	return 1;
}

/** @fn int pwm_check_continuous_mode(int module_number)
 * @brief Function to check if continuous mode is set for current pwm module. (This function helps in handling interrupts using plic).
 * @details This function will be called to check if continuous mode is set for current pwm module
 * @param int module_number- specifies the pwm module to be selected 
 * @return int returns 1 if running in continuous mode, 0 if not.
 */
int pwm_check_continuous_mode(int module_number)
{
	volatile char* control_value;
	control_value = PWM_BASE_ADDRESS + module_number*PWM_MODULE_OFFSET + CONTROL_REGISTER;
	int value = *control_value & CONTINUOUS_ONCE;
	log_info("\n Running in continuous mode(1/0): %d", (value>>3));
	if( (value>>3) == 1)
		return 1;
	else
		return 0;
}

/** @fn int set_pwm_clock_register(int module_number, int value)
 * @brief Function to set the clock register of the selected pwm module
 * @details This function will be called to set the value of the clock register(clock divisor) for the selected module
 * @param int module_number- specifies the pwm module to be selected
 * @param int value - value to be set between 0x0000 to 0xffff.
 * @return int returns 1 on success, 0 on failure.
 */
int set_pwm_clock_register(int module_number, int value)
{
	volatile short* clock_value;

	if (value > CLOCK_REGISTER_MAX) {
		log_error("\nClock Register Value higher than max value (%x)", CLOCK_REGISTER_MAX);
		return 0;
	}

	clock_value = PWM_BASE_ADDRESS + module_number*PWM_MODULE_OFFSET + CLOCK_REGISTER;
	*clock_value = value;

	return 1;
}

/** @fn void pwm_clear_registers(int module_number)
 * @brief Function to clear all registers in a specific pwm module
 * @details This function will be called to clear all registers in a specific pwm module
 * @param int module_number- specifies the pwm module to be selected
 */
void pwm_clear_registers(int module_number)
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
	int i;

	for (i = 0; i < 5; i++) {
		pwm_clear_registers(i);
	}

	log_info("\n All Register values of all modules cleared");
}

/** @fn int configure_control_register_mode(int mode)
 * @brief Function to set value of control register based on mode selected 
 * @details This function will set value of control register based on mode selected
 * @param  int ( mode- 
 *                0-PWM Mode.
 *                1-Timer Mode run once.
 *                2-Timer Mode run continuously.)
 * @return int (returns value to be set in the control register.)
 */
int configure_control_register_mode(int mode)
{
	int value = 0x0;

	if (mode == 0) {
		log_info("\n Current Module is set to PWM mode");

		value += PWM_ENABLE;
		value += PWM_START;
		value += PWM_OUTPUT_ENABLE;
	}
	else if (mode == 1) {
		log_info("\n Current Module is set to timer once only mode");

		value += PWM_START;
	}
	else if(mode == 2) {
		log_info("\n Current Module is set to timer continuous mode");

		value += PWM_START;
		value += CONTINUOUS_ONCE;
	}

	return value;
}

/** @fn void pwm_start(int module_number, int mode) 
 * @brief Function to start a pwm module with a specific mode
 * @details This function will start a pwm module with a specific mode
 * @param int module_number-  the pwm module to be selected
 * @param int (mode - mode to be selected
 *                  0-PWM Mode
 *                  1-Timer Mode run once
 *                  2-Timer Mode run contin )
 */
void pwm_start(int module_number, int mode)
{
	int control = configure_control_register_mode(mode);

	if(set_pwm_control_register(module_number, control))
	{
		log_info("\n PWM module number %d has been entered", module_number);
	}

	if(!set_pwm_control_register(module_number, control))
	{
		log_error("\n PWM module number %d not entered",module_number);
	}
}

/** @fn void pwm_use_external_clock(int module_number, bool value)
 * @brief Function to set use of external clock
 * @details This function will set clock to external clock if set to true
 * @param int (module_number-  the pwm module to be selected )
 * @param int (value -true or 1  - External Clock 
 *                    false or 0 - Internal Clock )
 */
void pwm_use_external_clock(int module_number, bool value)
{
	unsigned char* control_value;
	control_value = PWM_BASE_ADDRESS + module_number * PWM_MODULE_OFFSET + CONTROL_REGISTER;
	if(value == 1)
	control_value += CLOCK_SELECTOR;
	else if(control_value && CLOCK_SELECTOR)
	control_value -= CLOCK_SELECTOR;	
}

/** @fn void pwm_set_clock(int module_number, int clock_divisor) 
 * @brief Function to set the clock divisor value of a specific pwm module
 * @details This function will set the clock divisor value of a specific pwm module
 * @param int module_number-  the pwm module to be selected
              int clock_divisor- value of clock divisor to be used to divide base clock speed of 50MHz.
 */
void pwm_set_clock(int module_number, int clock_divisor)
{
	if (set_pwm_clock_register(module_number, clock_divisor) == 0)
	{
		log_error("\n Error in setting clock register");
	}
}

/** @fn void pwm_set_duty_cycle(int module_number, int duty) 
 * @brief Function to set the duty cycle value of a specific pwm module 
 * @details This function will set the duty cycles value of a specific pwm module
 * @param int module_number-  the pwm module to be selected 
 * @param int duty - value of duty cycles to be used to decide how many period cycles the pwm signal is set to 1.
 */
void pwm_set_duty_cycle(int module_number, int duty)
{
	if (set_pwm_duty_register(module_number, duty) == 0) {
		log_error("\n Error in setting duty register");
	}
}

/** @fn  void pwm_set_periodic_cycle(int module_number, int period)
 * @brief Function to set the period cycles value of a specific pwm module
 * @details This function will set the period cycles value of a specific pwm module
 * @param int module_number-  the pwm module to be selected
 * @param int clock_divisor-  value of period cycles which is used to further divide the                                                      
 *         frequency into fixed period cycles.
 */
void pwm_set_periodic_cycle(int module_number, int period)
{
	if(set_pwm_period_register(module_number, period) == 0) {
		log_error("\n Error in setting period register");
	}
}

/** @fn void pwm_configure(int module_number,int clock_divisor, int period, int duty, bool external_clock)
 * @brief Function to configure the pwm module with all the values required like clock divisor, period, duty cycle, and the use of external clock
 * @details This function configure the pwm module
 * @param int module_number - the pwm module to be selected
 * @param int clock_divisor - value of clock divisor to be used it divides the base clock frequency by the given value
 * @param int period - value of periodic cycle to be used. the signal resets after every count of the periodic cycle
 * @param int duty_cycle - value of duty cycle. It specifies how many cycles the signal is active out of the periodic cycle
 * @param bool external_clock - value of external clock selector. It specifies if external clock is to be used.
  */
void pwm_configure(int module_number,int clock_divisor, int period, int duty, bool external_clock)
{
	pwm_set_periodic_cycle(module_number, period);
	pwm_set_duty_cycle(module_number, duty);
	pwm_set_clock(module_number, clock_divisor);
	pwm_use_external_clock(module_number, external_clock);
	log_info("PWM %d succesfully configured",module_number);
}

/** @fn void pwm_stop(int module_number)
 * @brief Function to stop a specific pwm module
 * @details This function will stop a specific pwm module
 * @param int module_number-  the pwm module to be selected
 */
void pwm_stop(int module_number)
{
	set_pwm_control_register(module_number, 0x0);
	log_info("\n PWM module number %d has been stopped", module_number);
}

/** @fn void show_register_values(int module_number)
 * @brief Function to print the values of all the registers of a specific pwm module
 * @details This function will print the values of all the registers of a specific pwm module
 * @param int module_number-  the pwm module to be selected
 */
void show_register_values(int module_number)
{
	volatile unsigned short* period_value;
	volatile unsigned short* duty_value;
	volatile unsigned char*  control_value;
	volatile unsigned short* clock_value;

	period_value = PWM_BASE_ADDRESS + module_number * PWM_MODULE_OFFSET + PERIOD_REGISTER;
	duty_value = PWM_BASE_ADDRESS + module_number * PWM_MODULE_OFFSET + DUTY_REGISTER;
	control_value = PWM_BASE_ADDRESS + module_number * PWM_MODULE_OFFSET + CONTROL_REGISTER;
	clock_value = PWM_BASE_ADDRESS + module_number * PWM_MODULE_OFFSET + CLOCK_REGISTER;

	log_info("\nThe value of period register is %x",  *period_value);
	log_info("\nThe value of duty register is %x",    *duty_value);
	log_info("\nThe value of control register is %x", *control_value);
	log_info("\nThe value of clock register is %x",   *clock_value);
}

