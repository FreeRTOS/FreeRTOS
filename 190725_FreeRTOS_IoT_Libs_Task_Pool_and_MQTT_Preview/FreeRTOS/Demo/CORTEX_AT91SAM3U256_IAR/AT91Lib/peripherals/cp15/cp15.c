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

//-----------------------------------------------------------------------------
//         Headers
//-----------------------------------------------------------------------------

#include <board.h>

#ifdef CP15_PRESENT

#include <utility/trace.h>
#include "cp15.h"

#if defined(__ICCARM__)
#include <intrinsics.h>
#endif


//-----------------------------------------------------------------------------
//         Macros
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
//         Defines
//-----------------------------------------------------------------------------
/*
#define CP15_RR_BIT 14 // RR bit Replacement strategy for ICache and DCache: 
                       // 0 = Random replacement 
                       // 1 = Round-robin replacement.
                      
#define CP15_V_BIT  13 // V bit Location of exception vectors: 
                       // 0 = Normal exception vectors selected address range = 0x0000 0000 to 0x0000 001C 
                       // 1 = High exception vect selected, address range = 0xFFFF 0000 to 0xFFFF 001C
*/                       
#define CP15_I_BIT  12 // I bit ICache enable/disable: 
                       // 0 = ICache disabled 
                       // 1 = ICache enabled
/*                       
#define CP15_R_BIT   9 // R bit ROM protection

#define CP15_S_BIT   8 // S bit System protection
                  
#define CP15_B_BIT   7 // B bit Endianness: 
                       // 0 = Little-endian operation 
                       // 1 = Big-endian operation.                  
*/                     
#define CP15_C_BIT   2 // C bit DCache enable/disable: 
                       // 0 = Cache disabled 
                       // 1 = Cache enabled
/*
#define CP15_A_BIT   1 // A bit Alignment fault enable/disable:
                       // 0 = Data address alignment fault checking disabled
                       // 1 = Data address alignment fault checking enabled
*/
#define CP15_M_BIT   0 // M bit MMU enable/disable: 0 = disabled 1 = enabled.
                       // 0 = disabled 
                       // 1 = enabled


//-----------------------------------------------------------------------------
//         Global functions
//-----------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Check Instruction Cache
/// \return 0 if I_Cache disable, 1 if I_Cache enable
//------------------------------------------------------------------------------
unsigned int CP15_Is_I_CacheEnabled(void)
{
    unsigned int control;

    control = _readControlRegister();
    return ((control & (1 << CP15_I_BIT)) != 0);
} 

//------------------------------------------------------------------------------
/// Enable Instruction Cache
//------------------------------------------------------------------------------
void CP15_Enable_I_Cache(void)
{
    unsigned int control;

    control = _readControlRegister();

    // Check if cache is disabled
    if ((control & (1 << CP15_I_BIT)) == 0) {

        control |= (1 << CP15_I_BIT);
        _writeControlRegister(control);        
        TRACE_INFO("I cache enabled.\n\r");
    }
#if !defined(OP_BOOTSTRAP_on)
    else {

        TRACE_INFO("I cache is already enabled.\n\r");
    }
#endif
}

//------------------------------------------------------------------------------
/// Disable Instruction Cache
//------------------------------------------------------------------------------
void CP15_Disable_I_Cache(void)
{
    unsigned int control;

    control = _readControlRegister();

    // Check if cache is enabled
    if ((control & (1 << CP15_I_BIT)) != 0) {

        control &= ~(1 << CP15_I_BIT);
        _writeControlRegister(control);        
        TRACE_INFO("I cache disabled.\n\r");
    }
    else {

        TRACE_INFO("I cache is already disabled.\n\r");
    }
} 

//------------------------------------------------------------------------------
/// Check MMU
/// \return 0 if MMU disable, 1 if MMU enable
//------------------------------------------------------------------------------
unsigned int CP15_Is_MMUEnabled(void)
{
    unsigned int control;

    control = _readControlRegister();
    return ((control & (1 << CP15_M_BIT)) != 0);
} 

//------------------------------------------------------------------------------
/// Enable MMU
//------------------------------------------------------------------------------
void CP15_EnableMMU(void)
{
    unsigned int control;

    control = _readControlRegister();

    // Check if MMU is disabled
    if ((control & (1 << CP15_M_BIT)) == 0) {

        control |= (1 << CP15_M_BIT);
        _writeControlRegister(control);        
        TRACE_INFO("MMU enabled.\n\r");
    }
    else {

        TRACE_INFO("MMU is already enabled.\n\r");
    }
}

//------------------------------------------------------------------------------
/// Disable MMU
//------------------------------------------------------------------------------
void CP15_DisableMMU(void)
{
    unsigned int control;

    control = _readControlRegister();

    // Check if MMU is enabled
    if ((control & (1 << CP15_M_BIT)) != 0) {

        control &= ~(1 << CP15_M_BIT);
        control &= ~(1 << CP15_C_BIT);
        _writeControlRegister(control);        
        TRACE_INFO("MMU disabled.\n\r");
    }
    else {

        TRACE_INFO("MMU is already disabled.\n\r");
    }
}

//------------------------------------------------------------------------------
/// Check D_Cache
/// \return 0 if D_Cache disable, 1 if D_Cache enable (with MMU of course)
//------------------------------------------------------------------------------
unsigned int CP15_Is_DCacheEnabled(void)
{
    unsigned int control;

    control = _readControlRegister();
    return ((control & ((1 << CP15_C_BIT)||(1 << CP15_M_BIT))) != 0);
} 

//------------------------------------------------------------------------------
/// Enable Data Cache
//------------------------------------------------------------------------------
void CP15_Enable_D_Cache(void)
{
    unsigned int control;

    control = _readControlRegister();

    if( !CP15_Is_MMUEnabled() ) {
        TRACE_ERROR("Do nothing: MMU not enabled\n\r");
    }
    else {
        // Check if cache is disabled
        if ((control & (1 << CP15_C_BIT)) == 0) {

            control |= (1 << CP15_C_BIT);
            _writeControlRegister(control);        
            TRACE_INFO("D cache enabled.\n\r");
        }
        else {

            TRACE_INFO("D cache is already enabled.\n\r");
        }
    }
}

//------------------------------------------------------------------------------
/// Disable Data Cache
//------------------------------------------------------------------------------
void CP15_Disable_D_Cache(void)
{
    unsigned int control;

    control = _readControlRegister();

    // Check if cache is enabled
    if ((control & (1 << CP15_C_BIT)) != 0) {

        control &= ~(1 << CP15_C_BIT);
        _writeControlRegister(control);        
        TRACE_INFO("D cache disabled.\n\r");
    }
    else {

        TRACE_INFO("D cache is already disabled.\n\r");
    }
}

#endif // CP15_PRESENT

