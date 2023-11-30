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

//------------------------------------------------------------------------------
/// \unit
///
/// !Purpose
/// 
/// Methods to manage the Coprocessor 15. Coprocessor 15, or System Control 
/// Coprocessor CP15, is used to configure and control all the items in the 
/// list below:
/// • ARM core
/// • Caches (ICache, DCache and write buffer)
/// • TCM
/// • MMU
/// • Other system options
/// 
/// !Usage
///
/// -# Enable or disable D cache with Enable_D_Cache and Disable_D_Cache
/// -# Enable or disable I cache with Enable_I_Cache and Disable_I_Cache
///
//------------------------------------------------------------------------------

#ifndef _CP15_H
#define _CP15_H

#ifdef CP15_PRESENT

//-----------------------------------------------------------------------------
//         Exported functions
//-----------------------------------------------------------------------------
extern void CP15_Enable_I_Cache(void);
extern unsigned int CP15_Is_I_CacheEnabled(void);
extern void CP15_Enable_I_Cache(void);
extern void CP15_Disable_I_Cache(void);
extern unsigned int CP15_Is_MMUEnabled(void);
extern void CP15_EnableMMU(void);
extern void CP15_DisableMMU(void);
extern unsigned int CP15_Is_DCacheEnabled(void);
extern void CP15_Enable_D_Cache(void);
extern void CP15_Disable_D_Cache(void);

//-----------------------------------------------------------------------------
//         External functions defined in cp15.S
//-----------------------------------------------------------------------------
extern unsigned int _readControlRegister(void);
extern void _writeControlRegister(unsigned int value);
extern void _waitForInterrupt(void);
extern void _writeTTB(unsigned int value);
extern void _writeDomain(unsigned int value);
extern void _writeITLBLockdown(unsigned int value);
extern void _prefetchICacheLine(unsigned int value);

#endif // CP15_PRESENT

#endif // #ifndef _CP15_H

