/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
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

        MODULE  ?cstartup

        ;; Forward declaration of sections.
        SECTION IRQ_STACK:DATA:NOROOT(2)
        SECTION FIQ_STACK:DATA:NOROOT(2)
        SECTION ABT_STACK:DATA:NOROOT(2)
        SECTION UND_STACK:DATA:NOROOT(2)
        SECTION SYS_STACK:DATA:NOROOT(2)
        SECTION CSTACK:DATA:NOROOT(3)

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#define __ASSEMBLY__

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------

AT91C_BASE_AIC  DEFINE 0xFC020000
AT91C_BASE_SAIC DEFINE 0xF803C000
AIC_IVR         DEFINE 0x10
AIC_EOICR       DEFINE 0x38

MODE_MSK        DEFINE 0x1F  ; Bit mask for mode bits in CPSR

ARM_MODE_ABT    DEFINE 0x17
ARM_MODE_FIQ    DEFINE 0x11
ARM_MODE_IRQ    DEFINE 0x12
ARM_MODE_SVC    DEFINE 0x13
ARM_MODE_SYS    DEFINE 0x1F
ARM_MODE_UND    DEFINE 0x1B

I_BIT           DEFINE 0x80
F_BIT           DEFINE 0x40

//------------------------------------------------------------------------------
//         Startup routine
//------------------------------------------------------------------------------

        SECTION .vectors:CODE:NOROOT(2)

        PUBLIC  _reset_vector
        PUBLIC  __iar_program_start
        PUBLIC  irqHandler
        PUBLIC  fiqHandler

        EXTERN  undefined_instruction_irq_handler
        EXTERN  prefetch_abort_irq_handler
        EXTERN  data_abort_irq_handler
        EXTERN  software_interrupt_irq_handler

        DATA

__iar_init$$done:               ; The vector table is not needed
                                ; until after copy initialization is done

_reset_vector:                  ; Make this a DATA label, so that stack usage
                                ; analysis doesn't consider it an uncalled fun

        ARM

        ldr     pc, reset_addr          ; 0x0 Reset
        ldr     pc, undefined_addr      ; 0x4 Undefined instructions
        ldr     pc, soft_int_addr       ; 0x8 Software interrupt (SWI/SVC)
        ldr     pc, prefetch_abt_addr   ; 0xc Prefetch abort
        ldr     pc, data_abt_addr       ; 0x10 Data abort
        DCD     0                       ; 0x14 RESERVED
        ldr     pc, irq_addr            ; 0x18 IRQ
        ldr     pc, fiq_addr            ; 0x1c FIQ

        DATA

; All default handlers (except reset, irq and fiq) are
; defined as weak symbol definitions.
; If a handler is defined by the application it will take precedence.
reset_addr:        DCD   __iar_program_start
undefined_addr:    DCD   undefined_instruction_irq_handler
soft_int_addr:     DCD   software_interrupt_irq_handler
prefetch_abt_addr: DCD   prefetch_abort_irq_handler
data_abt_addr:     DCD   data_abort_irq_handler
irq_addr:          DCD   irqHandler
fiq_addr:          DCD   fiqHandler

;------------------------------------------------------------------------------
; Handles a fast interrupt request by branching to the address defined in the
; AIC.
;------------------------------------------------------------------------------
        SECTION .text:CODE:NOROOT(2)
        ARM
fiqHandler:
        sub         lr, lr, #4
        stmfd       sp!, {lr}
        stmfd       sp!, {r0}

        ; Write in the IVR to support Protect Mode

        ldr         lr, =AT91C_BASE_SAIC
        ldr         r0, [r14, #AIC_IVR]
        str         lr, [r14, #AIC_IVR]

        ; Branch to interrupt handler in Supervisor mode

        msr         CPSR_c, #ARM_MODE_SVC
        stmfd       sp!, { r1-r3, r4, r12, lr}

        blx          r0

        ldmia       sp!, { r1-r3, r4, r12, lr}
        msr         CPSR_c, #ARM_MODE_FIQ | I_BIT | F_BIT

        ; Acknowledge interrupt

        ldr         lr, =AT91C_BASE_SAIC
        str         lr, [r14, #AIC_EOICR]

        ; Restore interrupt context and branch back to calling code
        ldmia       sp!, {r0}
        ldmia       sp!, {pc}^

;------------------------------------------------------------------------------
; Handles incoming interrupt requests by branching to the corresponding
; handler, as defined in the AIC. Supports interrupt nesting.
;------------------------------------------------------------------------------
        SECTION .text:CODE:NOROOT(2)
        ARM
irqHandler:
        ; Save interrupt context on the stack to allow nesting

        sub         lr, lr, #4
        stmfd       sp!, {lr}
        mrs            lr, SPSR
        stmfd       sp!, {r0, lr}

        ; Write in the IVR to support Protect Mode

        ldr         lr, =AT91C_BASE_AIC
        ldr         r0, [r14, #AIC_IVR]
           str         lr, [r14, #AIC_IVR]

        ; Branch to interrupt handler in Supervisor mode

        msr         CPSR_c, #ARM_MODE_SVC
        stmfd       sp!, { r1-r3, r4, r12, lr}

        ; Check for 8-byte alignment and save lr plus a
        ; word to indicate the stack adjustment used (0 or 4)

        and         r1, sp, #4
        sub         sp, sp, r1
        stmfd       sp!, {r1, lr}

        blx         r0

        ldmia       sp!, {r1, lr}
        add            sp, sp, r1

        ldmia       sp!, { r1-r3, r4, r12, lr}
        msr         CPSR_c, #ARM_MODE_IRQ | I_BIT | F_BIT

        ; Acknowledge interrupt

        ldr         lr, =AT91C_BASE_AIC
        str         lr, [r14, #AIC_EOICR]

        ; Restore interrupt context and branch back to calling code

        ldmia       sp!, {r0, lr}
        msr         SPSR_cxsf, lr
        ldmia       sp!, {pc}^

//------------------------------------------------------------------------------
/// Initializes the chip and branches to the main() function.
//------------------------------------------------------------------------------

        SECTION .text:CODE:NOROOT(2)
        PUBLIC    __iar_program_start
        EXTERN  __cmain
        EXTERN     low_level_init
        REQUIRE _reset_vector

        EXTWEAK __iar_init_core
        EXTWEAK __iar_init_vfp

        ARM

__iar_program_start:
?cstartup:

        cpsie   a

        ; Set up the fast interrupt stack pointer

        mrs     r0, CPSR
        bic     r0, r0, #MODE_MSK
        orr     r0, r0, #ARM_MODE_FIQ
        msr     cpsr_c, r0
        ldr     sp, =SFE(FIQ_STACK)
        bic     sp, sp, #0x7

        ; Set up the normal interrupt stack pointer

        bic     r0, r0, #MODE_MSK
        orr     r0, r0, #ARM_MODE_IRQ
        msr     CPSR_c, r0
        ldr     sp, =SFE(IRQ_STACK)
        bic     sp, sp, #0x7

        ; Set up the abort mode stack pointer

        bic     r0, r0, #MODE_MSK
        orr     r0, r0, #ARM_MODE_ABT
        msr     CPSR_c, r0
        ldr     sp, =SFE(ABT_STACK)
        bic     sp, sp, #0x7

        ; Set up the undefined mode stack pointer

        bic     r0, r0, #MODE_MSK
        orr     r0, r0, #ARM_MODE_UND
        msr     CPSR_c, r0
        ldr     sp, =SFE(UND_STACK)
        bic     sp, sp, #0x7

        ; Set up the system mode stack pointer

        bic     r0, r0, #MODE_MSK
        orr     r0, r0, #ARM_MODE_SYS
        msr     CPSR_c, r0
        ldr     sp, =SFE(SYS_STACK)
        bic     sp, sp, #0x7

        ; Set up the supervisor mode stack pointer

        bic     r0 ,r0, #MODE_MSK
        orr     r0 ,r0, #ARM_MODE_SVC
        msr     cpsr_c, r0
        ldr     sp, =SFE(CSTACK)
        bic     sp, sp, #0x7

        ; Perform low-level initialization of the chip using low_level_init()

        ldr     r0, =low_level_init
        blx     r0

        ; Turn on core features assumed to be enabled
        FUNCALL __iar_program_start, __iar_init_core
        bl      __iar_init_core

        ;; Initialize VFP (if needed)
        FUNCALL __iar_program_start, __iar_init_vfp
        bl      __iar_init_vfp

        FUNCALL __iar_program_start, __cmain
        bl      __cmain

       ;; Loop indefinitely when program is finished
loop4:  b       loop4

        END
