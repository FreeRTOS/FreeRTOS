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

        MODULE  ?cp15

        ;; Forward declaration of sections.
        SECTION IRQ_STACK:DATA:NOROOT(2)
        SECTION CSTACK:DATA:NOROOT(3)

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#define __ASSEMBLY__
#include "board.h"

#ifdef CP15_PRESENT

//------------------------------------------------------------------------------
/// Functions to access CP15 coprocessor register
//------------------------------------------------------------------------------

        PUBLIC  _readControlRegister
        PUBLIC  _writeControlRegister
        PUBLIC  _waitForInterrupt
        PUBLIC  _writeTTB
        PUBLIC  _writeDomain
        PUBLIC  _writeITLBLockdown
        PUBLIC  _prefetchICacheLine

//------------------------------------------------------------------------------
/// Control Register c1
/// Register c1 is the Control Register for the ARM926EJ-S processor. 
/// This register specifies the configuration used to enable and disable the 
/// caches and MMU. It is recommended that you access this register using a 
/// read-modify-write sequence.
//------------------------------------------------------------------------------
// CP15 Read Control Register
_readControlRegister:
        mov     r0, #0
        mrc     p15, 0, r0, c1, c0, 0
        bx      lr

// CP15 Write Control Register
_writeControlRegister:
        mcr     p15, 0, r0, c1, c0, 0
        bx      lr

//------------------------------------------------------------------------------
/// CP15 Wait For Interrupt operation
/// The purpose of the Wait For Interrupt operation is to put the processor in
/// to a low power state.
/// This puts the processor into a low-power state and stops it executing more
/// instructions until an interrupt, or debug request occurs, regardless of
/// whether the interrupts are disabled by the masks in the CPSR. 
/// When an interrupt does occur, the MCR instruction completes and the IRQ or
/// FIQ handler is entered as normal. The return link in r14_irq or r14_fiq 
/// contains the address of the MCR instruction plus 8, so that the normal 
/// instruction used for interrupt return (SUBS PC,R14,#4) returns to the 
/// instruction following the MCR.
/// Wait For Interrupt : MCR p15, 0, <Rd>, c7, c0, 4
//------------------------------------------------------------------------------
_waitForInterrupt:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c0, 4
        bx      lr

//------------------------------------------------------------------------------
/// CP15 Translation Table Base Register c2
/// Register c2 is the Translation Table Base Register (TTBR), for the base 
/// address of the first-level translation table.
/// Reading from c2 returns the pointer to the currently active first-level
/// translation table in bits [31:14] and an Unpredictable value in bits [13:0]. 
/// Writing to register c2 updates the pointer to the first-level translation 
/// table from the value in bits [31:14] of the written value. Bits [13:0] 
/// Should Be Zero.
/// You can use the following instructions to access the TTBR:
/// Read TTBR  : MRC p15, 0, <Rd>, c2, c0, 0
/// Write TTBR : MCR p15, 0, <Rd>, c2, c0, 0
//------------------------------------------------------------------------------
_writeTTB:
        MCR     p15, 0, r0, c2, c0, 0
        bx      lr

//------------------------------------------------------------------------------
/// Domain Access Control Register c3
/// Read domain access permissions  : MRC p15, 0, <Rd>, c3, c0, 0
/// Write domain access permissions : MCR p15, 0, <Rd>, c3, c0, 0
//------------------------------------------------------------------------------
_writeDomain:
        MCR     p15, 0, r0, c3, c0, 0
        bx      lr

//------------------------------------------------------------------------------
/// TLB Lockdown Register c10
/// The TLB Lockdown Register controls where hardware page table walks place the
/// TLB entry, in the set associative region or the lockdown region of the TLB, 
/// and if in the lockdown region, which entry is written. The lockdown region 
/// of the TLB contains eight entries. See TLB structure for a description of 
/// the structure of the TLB.
/// Read data TLB lockdown victim  : MRC p15,0,<Rd>,c10,c0,0
/// Write data TLB lockdown victim : MCR p15,0,<Rd>,c10,c0,0
//------------------------------------------------------------------------------
_writeITLBLockdown:
        MCR     p15, 0, r0, c10, c0, 0
        bx      lr

//------------------------------------------------------------------------------
/// Prefetch ICache line
/// Performs an ICache lookup of the specified modified virtual address.
/// If the cache misses, and the region is cacheable, a linefill is performed.
/// Prefetch ICache line (MVA): MCR p15, 0, <Rd>, c7, c13, 1
//------------------------------------------------------------------------------
_prefetchICacheLine:
        MCR     p15, 0, r0, c7, c13, 1
        bx      lr
#endif
    END

