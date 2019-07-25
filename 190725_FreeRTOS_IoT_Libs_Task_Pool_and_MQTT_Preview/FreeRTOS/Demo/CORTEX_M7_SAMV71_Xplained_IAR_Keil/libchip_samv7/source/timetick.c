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
 *  Implement simple PIT usage as system tick.
 */

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *         Local variables
 *----------------------------------------------------------------------------*/

/** Tick Counter united by ms */
static volatile uint32_t _dwTickCount = 0 ;

/*----------------------------------------------------------------------------
 *         Exported Functions
 *----------------------------------------------------------------------------*/


/**
 *  \brief Handler for Sytem Tick interrupt.
 *
 *  Process System Tick Event
 *  Increments the timestamp counter.
 */
void SysTick_Handler( void )
{
    _dwTickCount ++;  
}

/**
 *  \brief Handler for Sytem Tick interrupt.
 */
extern void TimeTick_Increment( uint32_t dwInc )
{
    _dwTickCount += dwInc;
}

/**
 *  \brief Configures the PIT & reset tickCount.
 *  Systick interrupt handler will generates 1ms interrupt and increase a
 *  tickCount.
 *  \note IRQ handler must be configured before invoking this function.
 *  \note PIT is enabled automatically in this function.
 *  \param new_mck  Current master clock.
 */
extern uint32_t TimeTick_Configure( uint32_t new_mck )
{
    _dwTickCount = 0 ;
    /* Configure systick for 1 ms. */
    printf( "Configure system tick to get 1ms tick period.\n\r" ) ;
    if ( SysTick_Config( new_mck ) )
    {
        TRACE_ERROR("Systick configuration error\n\r" ) ;
        return 1;
    }
    return 0;
}

/**
 * Get Delayed number of tick
 * \param startTick Start tick point.
 * \param endTick   End tick point.
 */
extern uint32_t GetDelayInTicks(uint32_t startTick, uint32_t endTick)
{
    if (endTick >= startTick) return (endTick - startTick);
    return (endTick + (0xFFFFFFFF - startTick) + 1);
}

/**
 *  \brief Get current Tick Count, in ms.
 */
extern uint32_t GetTickCount( void )
{
    return _dwTickCount ;
}

/**
 *  \brief Sync Wait for several ms
 */
extern void Wait( volatile uint32_t dwMs )
{
    uint32_t dwStart ;
    uint32_t dwCurrent ;

    dwStart = _dwTickCount ;
    do
    {
        dwCurrent = _dwTickCount ;
    } while ( dwCurrent - dwStart < dwMs ) ;
}

/**
 *  \brief Sync Sleep for several ms
 */
extern void Sleep( volatile uint32_t dwMs )
{
    uint32_t dwStart ;
    uint32_t dwCurrent ;
    __ASM("CPSIE   I");
    dwStart = _dwTickCount ;

    do
    {
        dwCurrent = _dwTickCount ;

        if ( dwCurrent - dwStart > dwMs )
        {
            break ;
        }
        __ASM("WFI");
    } while( 1 ) ;
}

