/*
 * FreeRTOS Kernel V10.3.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#include <stdint.h>

extern uint32_t Image$$ER_IROM_FREERTOS_SYSTEM_CALLS$$Base;
extern uint32_t Image$$ER_IROM_FREERTOS_SYSTEM_CALLS$$Limit;

/* Memory map needed for MPU setup. Must must match the one defined in
 * the scatter-loading file (MPUDemo.sct). */
const uint32_t * __FLASH_segment_start__ = ( uint32_t * ) 0x08000000;
const uint32_t * __FLASH_segment_end__ = ( uint32_t * ) 0x08100000;
const uint32_t * __SRAM_segment_start__ = ( uint32_t * ) 0x20000000;
const uint32_t * __SRAM_segment_end__ = ( uint32_t * ) 0x20018000;

const uint32_t * __privileged_functions_start__ = ( uint32_t * ) 0x08000000;
const uint32_t * __privileged_functions_end__ = ( uint32_t * ) 0x08008000;
const uint32_t * __privileged_data_start__ = ( uint32_t * ) 0x20000000;
const uint32_t * __privileged_data_end__ = ( uint32_t * ) 0x20000400;

const uint32_t * __syscalls_flash_start__ = ( uint32_t * ) &( Image$$ER_IROM_FREERTOS_SYSTEM_CALLS$$Base );
const uint32_t * __syscalls_flash_end__ = ( uint32_t * ) &( Image$$ER_IROM_FREERTOS_SYSTEM_CALLS$$Limit );
/*-----------------------------------------------------------*/

/**
 * @brief Mem fault handler.
 */
void MemManage_Handler( void ) __attribute__ (( naked ));
/*-----------------------------------------------------------*/

void MemManage_Handler( void )
{
	__asm volatile
	(
		" tst lr, #4										\n"
		" ite eq											\n"
		" mrseq r0, msp										\n"
		" mrsne r0, psp										\n"
		" ldr r1, handler_address_const						\n"
		" bx r1												\n"
		"													\n"
		" handler_address_const: .word vHandleMemoryFault	\n"
	);
}
/*-----------------------------------------------------------*/
