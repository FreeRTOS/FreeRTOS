;*****************************************************************************
;*
;* Copyright 2013 Altera Corporation. All Rights Reserved.
;*
;* Redistribution and use in source and binary forms, with or without
;* modification, are permitted provided that the following conditions are met:
;*
;* 1. Redistributions of source code must retain the above copyright notice,
;* this list of conditions and the following disclaimer.
;*
;* 2. Redistributions in binary form must reproduce the above copyright notice,
;* this list of conditions and the following disclaimer in the documentation
;* and/or other materials provided with the distribution.
;*
;* 3. The name of the author may not be used to endorse or promote products
;* derived from this software without specific prior written permission.
;*
;* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
;* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
;* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
;* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
;* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
;* OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;* WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
;* OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
;* ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;*
;*****************************************************************************/

;; This is a small stub vector put in front of the ARMCC image to support
;; interrupts.

    PRESERVE8
    AREA    VECTORS, CODE, READONLY

    ENTRY

    EXPORT alt_interrupt_vector
    IMPORT __main
    EXPORT alt_int_handler_irq [WEAK]

alt_interrupt_vector

Vectors
    LDR PC, alt_reset_addr
    LDR PC, alt_undef_addr
    LDR PC, alt_svc_addr
    LDR PC, alt_prefetch_addr
    LDR PC, alt_abort_addr
    LDR PC, alt_reserved_addr
    LDR PC, alt_irq_addr
    LDR PC, alt_fiq_addr

alt_reset_addr    DCD alt_int_handler_reset
alt_undef_addr    DCD alt_int_handler_undef
alt_svc_addr      DCD alt_int_handler_svc
alt_prefetch_addr DCD alt_int_handler_prefetch
alt_abort_addr    DCD alt_int_handler_abort
alt_reserved_addr DCD alt_int_handler_reserve
alt_irq_addr      DCD alt_int_handler_irq
alt_fiq_addr      DCD alt_int_handler_fiq

alt_int_handler_reset
    B alt_premain
alt_int_handler_undef
    B alt_int_handler_undef
alt_int_handler_svc
    B alt_int_handler_svc
alt_int_handler_prefetch
    B alt_int_handler_prefetch
alt_int_handler_abort
    B alt_int_handler_abort
alt_int_handler_reserve
    B alt_int_handler_reserve
alt_int_handler_irq
    B alt_int_handler_irq
alt_int_handler_fiq
    B alt_int_handler_fiq

;=====

    AREA ALT_INTERRUPT_ARMCC, CODE, READONLY

alt_premain FUNCTION

; Enable VFP / NEON.
    MRC p15, 0, r0, c1, c0, 2 ; Read CP Access register
    ORR r0, r0, #0x00f00000   ; Enable full access to NEON/VFP (Coprocessors 10 and 11)
    MCR p15, 0, r0, c1, c0, 2 ; Write CP Access register
    ISB
    MOV r0, #0x40000000       ; Switch on the VFP and NEON hardware
    VMSR fpexc, r0            ; Set EN bit in FPEXC
	
    B __main

    ENDFUNC

;=====

    AREA ALT_INTERRUPT_ARMCC, CODE, READONLY

    EXPORT alt_int_fixup_irq_stack

; void alt_int_fixup_irq_stack(uint32_t stack_irq);
    ; This is the same implementation of GNU but for ARMCC.
alt_int_fixup_irq_stack FUNCTION
    ; r4: stack_sys

    PUSH    {lr}
    MOV     r4, sp
    MSR     CPSR_c, #(0x12 :OR: 0x80 :OR: 0x40)
    MOV     sp, r0
    MSR     CPSR_c, #(0x1F :OR: 0x80 :OR: 0x40)
    MOV     sp, r4
    POP     {lr}
    BX      lr

    ENDFUNC

    END
