/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
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
 *        Definitions
 *----------------------------------------------------------------------------*/
/* Definition for fast RC frequency */
#define FAST_RC_4MHZ     CKGR_MOR_MOSCRCF_4MHz
#define FAST_RC_8MHZ     CKGR_MOR_MOSCRCF_8MHz
#define FAST_RC_12MHZ    CKGR_MOR_MOSCRCF_12MHz

/* Definitions for startup count.
 * Note: 1 count unit stand for: 1 / 32768 * 8 = 244 us
 */
/* Default startup count for 4/8/12MHz fast RC (startup time: 10us ) */
#define DEFAUTL_FAST_RC_COUNT    1
/* Default startup count for 3-20MHz main oscillator (startup time: 1.4ms ) */
#define DEFAUTL_MAIN_OSC_COUNT   8
/* Default startup count for PLLA (startup time: 200us ) */
#define DEFAUTL_PLLA_COUNT       1
/* Default startup count for UPLL */
#define DEFAUTL_UPLL_COUNT       3
/* No change for default startup count */
#define DEFAUTL_COUNT_NO_CHANGE  0xFFFF


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

extern void PMC_SelectExtOsc(void);
extern void PMC_EnableExtOsc(void);
extern void PMC_DisableExtOsc(void);
extern void PMC_SelectExtBypassOsc(void);
extern void PMC_EnableIntRC4_8_12MHz(uint32_t fastRcFreq);
extern void PMC_DisableIntRC4_8_12MHz(void);
extern void PMC_SetPllaClock(uint32_t mul, uint32_t div);
extern void PMC_SetPllbClock(uint32_t mul, uint32_t div);
extern void PMC_SetMckSelection(uint32_t clockSource, uint32_t prescaler);
extern void PMC_DisableAllClocks(void);
extern void PMC_ConfigureMckWithPlla(uint32_t mul, uint32_t div, 
		uint32_t prescaler);
extern void PMC_ConfigureMckWithPllb(uint32_t mul, uint32_t div, 
		uint32_t prescaler);
extern void PMC_EnableXT32KFME(void);
extern void PMC_ConfigurePCK0(uint32_t MasterClk, uint32_t prescaler);
extern void PMC_ConfigurePCK1(uint32_t MasterClk, uint32_t prescaler);
extern void PMC_ConfigurePCK2(uint32_t MasterClk, uint32_t prescaler);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _PMC_ */
