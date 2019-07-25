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

#ifndef _SUPC_H_
#define _SUPC_H_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include <stdint.h>


/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/



/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

#ifdef __cplusplus
 extern "C" {
#endif



void SUPC_SelectExtCrystal32K(void);
uint8_t SUPC_IsSlowClkExtCrystal32K(void);
uint8_t SUPC_Read_Status(uint32_t status);
void SUPC_DisableSupplyMonitor(void);
void SUPC_DisableVoltageReg(void);
void SUPC_ConfigSupplyMonitor(uint32_t Config);
void SUPC_BrownoutDetectEnable(uint8_t enable);
void SUPC_BrownoutResetEnable(void);
void SUPC_SramBackupMode(uint8_t enable);
void SUPC_BypassXtal32KOsc(void);
void SUPC_EnablesWakeupInput(uint32_t Input, uint8_t enable);
void SUPC_SetLowPowerDebounce(uint8_t period);
void SUPC_SetWakeupDebounce(uint8_t period);
void SUPC_EnablesWakeupMode(uint32_t Regs, uint8_t enable);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _PMC_ */

