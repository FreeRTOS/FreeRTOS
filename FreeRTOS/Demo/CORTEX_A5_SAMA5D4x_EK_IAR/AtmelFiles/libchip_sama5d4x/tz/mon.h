/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
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
 */
#ifndef __MON_H__
#define __MON_H__


#if defined(__ICCARM__)
  #include <intrinsics.h>
#endif
   
typedef struct {
  unsigned int Mode_SPSR;
  unsigned int Mode_SP;
  unsigned int Mode_LR;
} Mode_Regs;

typedef struct
{
    unsigned int        r4;
    unsigned int        r5;
    unsigned int        r6;
    unsigned int        r7;
    unsigned int        r8;
    unsigned int        r9;
    unsigned int        r10;
    unsigned int        r11;
    unsigned int        r12;
    Mode_Regs           Mon;
    Mode_Regs           Svc;
    Mode_Regs           Fiq;
    Mode_Regs           Irq;
    
} WorldContext, *pWorldContext;
   

extern void monitor_init(void);
extern void SecureMonitor_init(void);
extern void nw_start(void);
extern void InitMonitor(void);
extern void SwitchToNormalWorld(void);
extern void SwitchToSecureWorld(void);

#endif
