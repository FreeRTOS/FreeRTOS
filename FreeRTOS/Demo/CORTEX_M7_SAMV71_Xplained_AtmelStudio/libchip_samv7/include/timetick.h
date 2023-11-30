/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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
 *
 *  \par Purpose
 *
 *  Methods and definitions for Global time tick and wait functions.
 *
 *  Defines a common and simplest use of Time Tick, to increase tickCount
 *  every 1ms, the application can get this value through GetTickCount().
 *
 *  \par Usage
 *
 *  -# Configure the System Tick with TimeTick_Configure() when MCK changed
 *     \note
 *     Must be done before any invoke of GetTickCount(), Wait() or Sleep().
 *  -# Uses GetTickCount to get current tick value.
 *  -# Uses Wait to wait several ms.
 *  -# Uses Sleep to enter wait for interrupt mode to wait several ms.
 *
 */

#ifndef _TIMETICK_
#define _TIMETICK_

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include <stdint.h>

/*----------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/

typedef struct
{
	volatile uint32_t *pTimer1;
	volatile uint32_t *pTimer2;
	volatile uint32_t *pTimer3;
	volatile uint32_t *pTimer4;
}SyTickDelayCounter_t;

/*----------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/
typedef struct _TimeEvent
{
	uint32_t event;
	uint32_t time_tick;
	uint32_t time_start;
	uint32_t occur;
	struct  _TimeEvent *pPreEvent;
	struct  _TimeEvent *pNextEvent;
}TimeEvent;

/*----------------------------------------------------------------------------
 *         Global functions
 *----------------------------------------------------------------------------*/

uint32_t TimeTick_Configure( void ) ;

void TimeTick_Increment( uint32_t dwInc ) ;

uint32_t GetDelayInTicks(uint32_t startTick,uint32_t endTick);

uint32_t GetTicks(void);

void Wait( volatile uint32_t dwMs ) ;

void Sleep( volatile uint32_t dwMs ) ;

extern void SetTimeEvent(TimeEvent* pEvent);

#endif /* _TIMETICK_ */
