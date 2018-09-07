/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 *  \file
 *  Implement simple PIT usage as system tick.
 */

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include "board.h"
#include "timer.h"
#include "peripherals/tc.h"
#include "peripherals/pit.h"
#include "peripherals/aic.h"
#include "peripherals/pmc.h"

/*----------------------------------------------------------------------------
 *         Local variables
 *----------------------------------------------------------------------------*/

/** Tick Counter */
static volatile uint32_t _timer = 0;
static uint32_t _resolution = 0;

/*----------------------------------------------------------------------------
 *         Exported Functions
 *----------------------------------------------------------------------------*/

/**
 *  \brief Handler for Sytem Tick interrupt.
 */
static void timer_increment(void)
{
	uint32_t status;

	/* Read the PIT status register */
	status = pit_get_status() & PIT_SR_PITS;
	if (status != 0) {

		/* 1 = The Periodic Interval timer has reached PIV
		 * since the last read of PIT_PIVR. Read the PIVR to
		 * acknowledge interrupt and get number of ticks
		 * Returns the number of occurrences of periodic
		 * intervals since the last read of PIT_PIVR. */
		_timer += (pit_get_pivr() >> 20);
	}
}

uint32_t timer_configure(uint32_t resolution)
{
	pit_disable_it();
	if (!resolution)
		resolution = BOARD_TIMER_RESOLUTION;
	_timer = 0;
	pmc_enable_peripheral(ID_PIT);
	pit_init(resolution);
	aic_set_source_vector(ID_PIT, timer_increment);
	aic_enable(ID_PIT);
	pit_enable_it();
	pit_enable();
	_resolution = resolution;
	return 0;
}

uint32_t timer_get_resolution(void)
{
	return _resolution;
}

uint32_t timer_get_interval(uint32_t start, uint32_t end)
{
	if (end >= start)
		return (end - start);
	return (end + (0xFFFFFFFF - start) + 1);
}

void timer_start_timeout(struct _timeout* timeout, uint32_t count)
{
	timeout->start = _timer;
	timeout->count = count;
}

uint8_t timer_timeout_reached(struct _timeout* timeout)
{
	return timer_get_interval(timeout->start, _timer) >= timeout->count;
}

void timer_wait(uint32_t count)
{
	uint32_t start, current;
	start = _timer;
	do {
		current = _timer;
	} while (timer_get_interval(start, current) < count);
}

void timer_sleep(uint32_t count)
{
	uint32_t start, current;
	asm("CPSIE   I");
	start = _timer;

	do {
		asm("WFI");
		current = _timer;
	} while (timer_get_interval(start, current) < count);
}

uint32_t timer_get_tick(void)
{
	return _timer;
}
