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

#ifndef _PMC_
#define _PMC_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include <stdint.h>


/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** Peripheral clock maxinum frequency */
typedef struct _PeripheralClockMaxFreq {
    uint32_t bPeriphID;             /**< Peripheral ID */
    uint32_t bMaxFrequency;         /**< Max frequency*/
} PeripheralClockMaxFreq;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

#ifdef __cplusplus
 extern "C" {
#endif

extern void PMC_EnablePeripheral( uint32_t dwId ) ;
extern void PMC_DisablePeripheral( uint32_t dwId ) ;

extern void PMC_EnableAllPeripherals( void ) ;
extern void PMC_DisableAllPeripherals( void ) ;

extern uint32_t PMC_IsPeriphEnabled( uint32_t dwId ) ;

extern void PMC_SelectExt32KCrystal(void);
extern void PMC_SelectInt32kCrystal(void);
extern void PMC_SelectExt12M_Osc(void);
extern void PMC_SelectInt12M_Osc(void);
extern void PMC_SwitchMck2Pll(void);
extern void PMC_SwitchMck2Main(void);
extern void PMC_SwitchMck2Slck(void);
extern void PMC_SetPllA(uint32_t pll, uint32_t cpcr);
extern void PMC_SetMckPrescaler(uint32_t prescaler);
extern void PMC_SetMckDivider(uint32_t divider);
extern void PMC_SetMckPllaDiv(uint32_t divider);
extern void PMC_DisablePllA(void);
extern uint32_t PMC_GetPeriMaxFreq( uint32_t dwId );
extern uint32_t PMC_SetPeriMaxClock( uint32_t dwId, uint32_t mck);
#ifdef __cplusplus
}
#endif

#endif /* #ifndef _PMC_ */

