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

/** \file */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#if defined(__ICCARM__)
#include <intrinsics.h>
#endif

#include "cortex-a/cp15_pmu.h"

#include <assert.h>

/*----------------------------------------------------------------------------
 *        Global functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Resets the counter and enables/disables all counters including PMCCNTR.
 * \param ResetCounterType  CounterType: Performance or Cycle counter
 */
static void cp15_pmu_control(uint8_t ResetCounterType, uint8_t EnableCounter)
{
	uint32_t PMU_Value = 0;

	asm("mrc     p15, 0, %0, c9, c12, 0":"=r"(PMU_Value));
	PMU_Value |= ((ResetCounterType << 1) | EnableCounter);
	asm("mcr     p15, 0, %0, c9, c12, 0": :"r"(PMU_Value));
}

/**
 * \brief Select Cycle Count divider
 * \param Divider  0 for increment of counter at every single cycle or 1 for at every 64th cycle
 */
static void cp15_cycle_count_divider(uint8_t Divider)
{
	uint32_t PMU_Value = 0;
	assert((Divider > 1 ? 0 : 1));
	asm("mrc     p15, 0, %0, c9, c12, 0":"=r"(PMU_Value));
	PMU_Value |= (Divider << 3);
	asm("mcr     p15, 0, %0, c9, c12, 0": :"r"(PMU_Value));
}

/**
 * \brief Enables PMCCNTR.
 */
static void cp15_enable_PMCNT(void)
{
	uint32_t CNT_Value = 0;
	asm("mrc     p15, 0, %0, c9, c12, 1":"=r"(CNT_Value));
	CNT_Value |= (uint32_t) ((1 << CP15_PMCNTENSET));
	asm("mcr     p15, 0, %0, c9, c12, 1": :"r"(CNT_Value));
}

/**
 * \brief Enables PMCCNTR.
 */
static void cp15_enable_counter(uint8_t Counter)
{
	uint32_t CNT_Value = 0;
	asm("mrc     p15, 0, %0, c9, c12, 1":"=r"(CNT_Value));
	CNT_Value |= Counter;
	asm("mcr     p15, 0, %0, c9, c12, 1": :"r"(CNT_Value));
}

/**
 * \brief Disables/clear PMCCNTR.
 * \param Counter  0 or 1 to selct counter
 */

static void cp15_clear_PMCNT(void)
{
	uint32_t CNT_Value = 0;
	asm("mrc     p15, 0, %0, c9, c12, 2":"=r"(CNT_Value));
	CNT_Value |= (uint32_t) (1 << CP15_PMCNTENCLEAR);
	asm("mcr     p15, 0, %0, c9, c12, 2": :"r"(CNT_Value));
}

/**
 * \brief Disables/Enables overflow flag.
 * \param Enable  Enables or disables the flag option
 * \param ClearCounterFlag  selects the counter flag to clear
 */
void cp15_overflow_status(uint8_t Enable, uint8_t ClearCounterFlag)
{
	uint32_t OFW_Value = 0;
	asm("mrc     p15, 0, %0, c9, c12, 3":"=r"(OFW_Value));
	OFW_Value |= ((Enable << 31) | ClearCounterFlag);
	asm("mcr     p15, 0, %0, c9, c12, 3": :"r"(OFW_Value));
}

/**
 * \brief Disables/Enables overflow flag.
 * \param EventCounter  Counter of the events
 */
uint32_t cp15_read_overflow_status(uint8_t EventCounter)
{
	uint32_t OFW_Value = 0;
	asm("mrc     p15, 0, %0, c9, c12, 3":"=r"(OFW_Value));
	OFW_Value = ((OFW_Value & EventCounter) >> (EventCounter - 1));
	return OFW_Value;
}

/**
 * \brief Increments the count of a performance monitor count register.
 * \param IncrCounter  0 or 1  counters
 */
void cp15_soft_incr(uint8_t IncrCounter)
{
	uint32_t INRC_Value = 0;
	asm("mrc     p15, 0, %0, c9, c12, 4":"=r"(INRC_Value));
	INRC_Value |= IncrCounter;
	asm("mcr     p15, 0, %0, c9, c12, 4": :"r"(INRC_Value));
}

/**
 * \brief Increments the count of a performance monitor count register.
 * \param EventType  Select Event Type
 * \param Counter  0 or 1  counters
 */
static void cp15_select_event(PerfEventType EventType, uint8_t Counter)
{
	uint32_t CounterSelect = 0;
	assert((Counter == 1) || (Counter == 2));
	CounterSelect = (Counter & 0x1F);
	asm("mcr     p15, 0, %0, c9, c12, 5": :"r"(CounterSelect));
	CounterSelect = (EventType & 0xFF);
	asm("mcr     p15, 0, %0, c9, c13, 1": :"r"(CounterSelect));
	// PMXEVTYPER
	asm("mrc     p15, 0, %0, c9, c13, 1":"=r"(CounterSelect));
	// PMXEVTYPER
}

/**
 * \brief Enables USER mode
 */
void cp15_enable_user_mode(void)
{
	uint8_t Value = 1;
	asm("mcr     p15, 0, %0, c9, c14, 0": :"r"(Value));
}

/**
 * \brief Enables Oveflows interrupt
 * \param Enable  Enables the Interrupt
 * \param Counter  0 or 1  counters
 */
void cp15_enable_interrupt(uint8_t Enable, uint8_t Counter)
{
	uint32_t ITE_Value = 0;
	ITE_Value |= ((Enable << 31) | Counter);
	asm("mcr     p15, 0, %0, c9, c14, 1": :"r"(ITE_Value));
}

/**
 * \brief Disables Oveflows interrupt
 * \param Disable  Disables the Interrupt
 * \param Counter  0 or 1  counters
 */
void cp15_disable_interrupt(uint8_t Disable, uint8_t Counter)
{
	uint32_t ITE_Value = 0;
	ITE_Value |= ((Disable << 31) | Counter);
	asm("mcr     p15, 0, %0, c9, c14, 2": :"r"(ITE_Value));
}

/**
 * \brief Initialize Cycle counter with Divider 64
 */
uint32_t cp15_init_cycle_counter(void)
{
	uint32_t value;
	cp15_clear_PMCNT();
	cp15_enable_PMCNT();
	cp15_overflow_status(true, CP15_BothCounter);
	cp15_cycle_count_divider(CP15_CountDivider64);
	cp15_pmu_control(CP15_ResetCycCounter, true);

	asm("mrc     p15, 0, %0, c9, c13, 0":"=r"(value));
	return value;

}

/**
 * \brief Initialize Performance monitor counter with Divider 64
 * \param Event  Event type
 * \param Counter  0 or 1  counters
 */

void cp15_init_perf_counter(PerfEventType Event, uint8_t Counter)
{
	cp15_pmu_control(CP15_ResetPerCounter, true);
	cp15_select_event(Event, Counter);
	cp15_overflow_status(false, CP15_BothCounter);
	cp15_enable_counter(Counter);
}

/**
 * \brief gives total number of event count
 * \param Counter  0 or 1  counters
 */
uint32_t cp15_count_evt(uint8_t Counter)
{
	uint32_t value;
	asm("mcr     p15, 0, %0, c9, c12, 5": :"r"(Counter));
	asm("mrc     p15, 0, %0, c9, c13, 2":"=r"(value));
	// PMXEVTYPER
	return (value);
}

/**
 * \brief gives total number of cycle count

 */
uint32_t cp15_get_cycle_counter(void)
{
	uint32_t value;
	asm("mrc     p15, 0, %0, c9, c13, 0":"=r"(value));
	return value;
}
