/***************************************************************************
 * Project           		: shakti devt board
 * Name of the file	     	: xadc_driver.c
 * Brief Description of file    : source file for xadc.
 * Name of Author    	        : Sathya Narayanan N
 * Email ID                     : sathya281@gmail.com

 Copyright (C) 2020  IIT Madras. All rights reserved.

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
@file xadc_driver.c
@brief source file for xadc driver
@detail This file contains the driver code for xadc device. The functions to
 setup each xadc registers, isr routine and xadc interrupt handler are here.
*/

#include<stdio.h>
#include "xadc_driver.h"

//Dedicated mode

/**
 * @fn uint32_t xadc_read_data(uint32_t *address)
 * @brief A api to read data from a memory mapped address.
 * @param unsigned int (32-bit) address
 * @return unsigned int (32-bit) *address
 */
uint32_t xadc_read_data(uint32_t *address)
{
	return(*address);
}

/**
 * @fn void xadc_write_ctrl_reg(uint32_t *address, uint32_t data)
 * @brief A api to write data to a memory mapped address.
 * @param unsigned int (32-bit) address
 * @param unsigned int (32-bit) data
 */
void xadc_write_ctrl_reg(uint32_t *address, uint32_t data)
{
	*address = data;
}

/**
 * @fn xadc_onchip_voltage(uint32_t value)
 * @brief Reads the onchip voltage
 * @details Read the voltage in the FPGA chip and returns a value in volts
 * @param unsigned int (32-bit) value
 * @return float
 */
float xadc_onchip_voltage(uint32_t value)
{
	return (((value >> 4)*3.0f)/4096.0f );
}

/**
 * @fn xadc_onchip_temp(uint32_t value)
 * @brief Reads the onchip temperature
 * @details Read the temperature on the FPGA chip and returns a value in
 * celsius.
 * @param unsigned int (32-bit) value
 * @return float
 */
float xadc_onchip_temp(uint32_t value)
{
	return (((value/65536.0f)/0.00198421639f ) - 273.15f);
}

/**
 * @fn  xadc_dedicated_channel(uint32_t value)
 * @brief Reads the data on the dedicated VP/VN pins
 * @param unsigned int (32-bit) value
 * @return float
 */
float xadc_dedicated_channel(uint32_t value)
{
	return ((value >> 4)/4096.0f );
}
