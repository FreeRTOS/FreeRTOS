/*********************************************************************
 *
 *                  General Exception
 *
 *********************************************************************
 * Filename:        general-exception.S
 *
 * Processor:       PIC32
 *
 * Compiler:        MPLAB XC32 v1.00
 *                  MPLAB X IDE
 * Company:         Microchip Technology Inc.
 *
 * Software License Agreement
 *
 * This software is developed by Microchip Technology Inc. and its
 * subsidiaries ("Microchip").
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1.      Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2.      Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3.      Microchip's name may not be used to endorse or promote products
 * derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY MICROCHIP "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL
 * MICROCHIP BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING BUT NOT LIMITED TO
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWSOEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 ********************************************************************/
 
#include <xc.h>
#ifdef __LIBBUILD__
   .file 1 "general-exception.S"
   .loc 1 0
#endif
  ###################
  # Default general exception handler
  ###################

  .extern _general_exception_handler

  .section .text.general_exception, code
  .set noreorder
  .set noat
  .set nomips16
  .globl _general_exception_context
  .ent _general_exception_context

_general_exception_context:

  # Save off the non-callee saved registers that may get mucked with
   addiu sp, sp, -88
   sw $1,  4(sp)
   sw v0,  8(sp)
   sw v1, 12(sp)
   sw a0, 16(sp)
   sw a1, 20(sp)
   sw a2, 24(sp)
   sw a3, 28(sp)
   sw t0, 32(sp)
   sw t1, 36(sp)
   sw t2, 40(sp)
   sw t3, 44(sp)
   sw t4, 48(sp)
   sw t5, 52(sp)
   sw t6, 56(sp)
   sw t7, 60(sp)
   sw t8, 64(sp)
   sw t9, 68(sp)
   sw ra, 72(sp)
   mflo t0
   sw t0, 76(sp)
   mfhi t0
   sw t0, 80(sp)

   la      k0,_general_exception_handler
   nop
   
   # Pass Cause and Status to the handler function
   mfc0 a0, _CP0_CAUSE
   mfc0 a1, _CP0_STATUS
   jalr    k0
   nop

   lw t0, 80(sp)
   mthi t0
   lw t0, 76(sp)
   mtlo t0

   lw $1,  4(sp)
   lw v0,  8(sp)
   lw v1, 12(sp)
   lw a0, 16(sp)
   lw a1, 20(sp)
   lw a2, 24(sp)
   lw a3, 28(sp)
   lw t0, 32(sp)
   lw t1, 36(sp)
   lw t2, 40(sp)
   lw t3, 44(sp)
   lw t4, 48(sp)
   lw t5, 52(sp)
   lw t6, 56(sp)
   lw t7, 60(sp)
   lw t8, 64(sp)
   lw t9, 68(sp)
   lw ra, 72(sp)
   addiu sp, sp, 88

   ehb
   eret

  .end _general_exception_context

