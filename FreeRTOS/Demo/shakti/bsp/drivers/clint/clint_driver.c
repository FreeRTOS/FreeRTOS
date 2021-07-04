/***************************************************************************
* Project                     : shakti devt board
* Name of the file	      : clint_driver.c
* Brief Description of file   : source file for clint.
* Name of Author    	      : Sathya Narayanan N
* Email ID                    : sathya281@gmail.com

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
@file clint_driver.c
@brief source file for clint.
@detail This file is a driver file for clint. The file contains the clint 
interrupt handler, configure the counter and support for e and c class clint timers. 
*/

#include "clint_driver.h"
#include "log.h"
#include "defines.h"

uint32_t* mtime    = 0x0200bff8;
uint32_t* mtimecmp = 0x02004000;

/** @fn static unsigned long mtime_low( )
 * @brief return the lower 32bit of mtime.
 * @details return the lower half of mtime. And this is needed mostly in dealing mtime in 32 bit machines.
 * @return unsigned long
 */
static unsigned long mtime_low(void)
{
  return *(volatile unsigned long *)(CLINT_BASE + MTIME);
}

/*
Get each 32 bit and append for full timer value
*/

/** @fn static uint32_t mtime_high(void)
 * @brief return the upper 32 bit of mtime
 * @details return the upper 32 bit of mtime register. This is very useful incase of 32 bit core.
 *          Incase of 64 bit core this has to be appended with lower 32 bits adn sent.
 * @return unsigned 32bit int
 */
static uint32_t mtime_high(void)
{
  return *(volatile uint32_t *)(CLINT_BASE + MTIME + 4);
}

/** @fn uint64_t get_timer_value()
 * @brief return the mtime value for a 32 bit or 64 bit machine
 * @details return the mtime value based on the __riscv_xlen. Incase of 64 bit, this joins the upper
 *          and lower 32 bits of mtime and return
 * @return unsigned 64bit int
 */
uint64_t get_timer_value()
{

#if __riscv_xlen == 32
   return ( ((uint64_t)mtime_high() << 32) | mtime_low());
#else
  return mtime_low();
#endif
}

/** @fn void configure_counter( uint64_t value)
 * @brief sets up the timer
 * @details sets the mtimecmp to current mtime + delta
 * @param unsigned 64bit int (delta value after which interrupt happens)
 */
void configure_counter( uint64_t value)
{
	log_trace("\nconfigure_counter entered\n");

	*mtimecmp = *mtime + value;

	log_info("mtimecmp value = %d\n", *mtimecmp);
	log_info("mtime value = %d\n", *mtime);

	log_trace("\nconfigure_counter exited\n");
}

/** @fn void mach_clint_handler(uintptr_t int_id, uintptr_t epc)
 * @brief handler for machine timer interrupt
 * @details handler for machine timer interrupt. This handles the timer interrupt and sets mtimecmp to clear timer interrupt.
 * @param unsigned int ptr int_id
 * @param unsigned int ptr epc
 */
void mach_clint_handler( __attribute__((unused)) uintptr_t int_id,  __attribute__((unused)) uintptr_t epc)
{
	log_trace("\nmach_clint_handler entered\n");

	*mtimecmp = -1;

	log_debug("mtimecmp value = %x\n", *mtimecmp);
	log_debug("mtime value = %x\n", *((uint32_t *)(0x0200bff8)));

	log_trace("mach_clint_handler exited\n");
}
