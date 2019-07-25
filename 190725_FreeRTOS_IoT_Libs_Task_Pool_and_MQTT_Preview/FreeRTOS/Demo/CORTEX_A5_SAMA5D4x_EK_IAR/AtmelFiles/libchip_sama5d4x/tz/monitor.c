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


#if defined(__ICCARM__)
  #include <intrinsics.h>
#endif
#include "mon.h"
#include "mon_macros.h"
   
#if defined ( __ICCARM__ ) /* IAR Ewarm */
    #pragma default_variable_attributes = @ "region_context_switch"
      WorldContext SW_Context;
      WorldContext NSW_Context;    
    #pragma default_variable_attributes = 
    
#elif defined (  __GNUC__  ) /* GCC CS3 */
    WorldContext SW_Context __attribute__((__section__("region_context_switch")));
    WorldContext NSW_Context __attribute__((__section__("region_context_switch")));
#endif 
/*----------------------------------------------------------------------------
 *        Global functions
 *----------------------------------------------------------------------------*/

void InitMonitor(void)
{
  SW_Context.Mon.Mode_SPSR = 0;
  SecureMonitor_init();
  
  NSW_Context.Mon.Mode_SPSR = INITIAL_NWD_STATE;
  NSW_Context.Mon.Mode_LR = (unsigned int)&nw_start;  
}

