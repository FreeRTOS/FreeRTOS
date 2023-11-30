/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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

#ifndef SUPC_H
#define SUPC_H

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

extern void SUPC_EnableSlcd(unsigned char internal);

extern void SUPC_DisableSlcd(void);

extern void SUPC_SetSlcdVoltage(unsigned int voltage);

extern
#ifdef __ICCARM__
__ramfunc // IAR
#endif
void SUPC_EnableFlash(unsigned int time);

extern
#ifdef __ICCARM__
__ramfunc // IAR
#endif
void SUPC_DisableFlash(void);

extern void SUPC_SetVoltageOutput(unsigned int voltage);

extern void SUPC_EnableDeepMode(void);

extern void SUPC_EnableSram(void);

extern void SUPC_DisableSram(void);

extern void SUPC_EnableRtc(void);

extern void SUPC_DisableRtc(void);

extern void SUPC_SetBodSampling(unsigned int mode);

extern void SUPC_DisableDeepMode(void);

extern void SUPC_DisableVoltageRegulator(void);

extern void SUPC_Shutdown(void);

extern void SUPC_SetWakeUpSources(unsigned int sources);

extern void SUPC_SetWakeUpInputs(unsigned int inputs);

#endif //#ifndef SUPC_H

