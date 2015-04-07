/* ----------------------------------------------------------------------------
 *         SAM Software Package License  
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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
/*----------------------------------------------------------------------------
 *        Global functions
 *----------------------------------------------------------------------------*/


/**
 * \brief Resets the counter and enables/disables all counters including PMCCNTR.
 * \param ResetCounterType  CounterType: Performance or Cycle counter
 */
static void CP15_PMUControl(uint8_t ResetCounterType, uint8_t EnableCounter)
{
  uint32_t PMU_Value=0;  
  
  asm("mrc     p15, 0, %0, c9, c12, 0" :"=r" (PMU_Value));  
  PMU_Value |= ((ResetCounterType << 1)| EnableCounter);  
  asm("mcr     p15, 0, %0, c9, c12, 0" : : "r" (PMU_Value));  
}

/**
 * \brief Select Cycle Count divider
 * \param Divider  0 for increment of counter at every single cycle or 1 for at every 64th cycle
 */
static void CP15_CycleCountDivider(uint8_t Divider)
{
  uint32_t PMU_Value=0;  
  
  assert((Divider>1?0:1));
  
  asm("mrc     p15, 0, %0, c9, c12, 0" :"=r" (PMU_Value));  
  PMU_Value |= (Divider << 3);  
  asm("mcr     p15, 0, %0, c9, c12, 0" : : "r" (PMU_Value));  
}

/**
 * \brief Enables PMCCNTR.
 */
static void CP15_EnablePMCNT(void) 
{
  uint32_t CNT_Value=0;  
  
  asm("mrc     p15, 0, %0, c9, c12, 1" :"=r" (CNT_Value));  
  CNT_Value |= (uint32_t)((1 << CP15_PMCNTENSET));  
  asm("mcr     p15, 0, %0, c9, c12, 1" : : "r" (CNT_Value));  
}
 
/**
 * \brief Enables PMCCNTR.
 */
static void CP15_EnableCounter(uint8_t Counter)
{
  uint32_t CNT_Value=0;  
  
  asm("mrc     p15, 0, %0, c9, c12, 1" :"=r" (CNT_Value));  
  CNT_Value |= Counter;  
  asm("mcr     p15, 0, %0, c9, c12, 1" : : "r" (CNT_Value));  
}


/**
 * \brief Disables/clear PMCCNTR.
 * \param Counter  0 or 1 to selct counter
 */
   
static void CP15_ClearPMCNT(void)
{
  uint32_t CNT_Value = 0;  
  
  asm("mrc     p15, 0, %0, c9, c12, 2" :"=r" (CNT_Value));  
  CNT_Value |= (uint32_t)(1 << CP15_PMCNTENCLEAR);  
  asm("mcr     p15, 0, %0, c9, c12, 2" : : "r" (CNT_Value));  
}

/**
 * \brief Disables/Enables overflow flag.
 * \param Enable  Enables or disables the flag option
 * \param ClearCounterFlag  selects the counter flag to clear
 */
void CP15_OverflowStatus(uint8_t Enable,  uint8_t ClearCounterFlag)
{
  uint32_t OFW_Value=0;  
  
  asm("mrc     p15, 0, %0, c9, c12, 3" :"=r" (OFW_Value));  
  OFW_Value |= ((Enable << 31)| ClearCounterFlag);  
  asm("mcr     p15, 0, %0, c9, c12, 3" : : "r" (OFW_Value));  
}

/**
 * \brief Disables/Enables overflow flag.
 * \param Enable  Enables or disables the flag option
 * \param ClearCounterFlag  selects the counter flag to clear
 */
uint32_t CP15_ReadOverflowStatus(uint8_t EventCounter)
{
  uint32_t OFW_Value=0;  
  
  asm("mrc     p15, 0, %0, c9, c12, 3" :"=r" (OFW_Value));  
  OFW_Value =  ((OFW_Value & EventCounter) >> (EventCounter - 1));
  return OFW_Value;
}

/**
 * \brief Increments the count of a performance monitor count register.
 * \param IncrCounter  0 or 1  counters
 */
void CP15_SoftINCR(uint8_t IncrCounter)
{
  uint32_t INRC_Value=0;  
  
  asm("mrc     p15, 0, %0, c9, c12, 4" :"=r" (INRC_Value));  
  INRC_Value |= IncrCounter;  
  asm("mcr     p15, 0, %0, c9, c12, 4" : : "r" (INRC_Value));  
}

/**
 * \brief Increments the count of a performance monitor count register.
 * \param EventType  Select Event Type
 * \param Counter  0 or 1  counters
 */
static void CP15_SelectEvent(PerfEventType EventType, uint8_t Counter)
{
  uint32_t CounterSelect=0;
  assert((Counter == 1) || (Counter == 2));
  CounterSelect = (Counter & 0x1F);
  asm("mcr     p15, 0, %0, c9, c12, 5" : : "r" (CounterSelect)); 
  CounterSelect = (EventType & 0xFF);
  asm("mcr     p15, 0, %0, c9, c13, 1" : : "r" (CounterSelect));  // PMXEVTYPER
  asm("mrc     p15, 0, %0, c9, c13, 1" : "=r" (CounterSelect));  // PMXEVTYPER
}

/**
 * \brief Enables USER mode
 */
void CP15_EnableUserMode(void)
{
  uint8_t Value = 1;
  asm("mcr     p15, 0, %0, c9, c14, 0" : : "r" (Value));  
}


/**
 * \brief Enables Oveflows interrupt
 * \param Enable  Enables the Interrupt
 * \param Counter  0 or 1  counters
 */
void CP15_EnableIT(uint8_t Enable, uint8_t Counter)
{
  uint32_t ITE_Value=0;  
  
  ITE_Value |= ((Enable << 31)| Counter);  
  asm("mcr     p15, 0, %0, c9, c14, 1" : : "r" (ITE_Value));  
}

/**
 * \brief Disables Oveflows interrupt
 * \param Disable  Disables the Interrupt
 * \param Counter  0 or 1  counters
 */
void CP15_DisableIT(uint8_t Disable, uint8_t Counter)
{
  uint32_t ITE_Value=0;  
  
  ITE_Value |= ((Disable << 31)| Counter);  
  asm("mcr     p15, 0, %0, c9, c14, 2" : : "r" (ITE_Value));  
}


/**
 * \brief Initialize Cycle counter with Divider 64
 */
uint32_t CP15_CycleCounterInit(void)
{
  uint32_t value;
  CP15_ClearPMCNT();
  CP15_EnablePMCNT();
  CP15_OverflowStatus(ENABLE, CP15_BothCounter);
  CP15_CycleCountDivider(CP15_CountDivider64);
  CP15_PMUControl(CP15_ResetCycCounter, ENABLE);

  asm("mrc     p15, 0, %0, c9, c13, 0" :"=r" (value));
  
  return value;
  
}

/**
 * \brief Initialize Performance monitor counter with Divider 64
 * \param Event  Event type
 * \param Counter  0 or 1  counters
 */

void CP15_PerfCounterInit(PerfEventType Event, uint8_t Counter)
{

  CP15_PMUControl(CP15_ResetPerCounter, ENABLE);  
  CP15_SelectEvent(Event, Counter);  
  CP15_OverflowStatus(DISABLE, CP15_BothCounter);
  CP15_EnableCounter(Counter);
}

/**
 * \brief gives total number of event count
 * \param Counter  0 or 1  counters
 */
uint32_t CP15_CountEvent(uint8_t Counter)
{
  uint32_t value; 
  
  asm("mcr     p15, 0, %0, c9, c12, 5" : : "r" (Counter));  
  asm("mrc     p15, 0, %0, c9, c13, 2" :"=r" (value));  // PMXEVTYPER
  return (value);
}

/**
 * \brief gives total number of cycle count

 */
uint32_t CP15_GetCycleCounter(void)
{
  uint32_t value;
  
  asm("mrc     p15, 0, %0, c9, c13, 0" :"=r" (value));
  return value;
  
}

